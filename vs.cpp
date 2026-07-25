/* Copyright (C) 2014-2019 Emanuele Giaquinta

    This program is free software; you can redistribute it and/or modify it
    under the terms of the GNU General Public License as published by the
    Free Software Foundation; either version 2, or (at your option) any
    later version.

    This program is distributed in the hope that it will be useful,
    but WITHOUT ANY WARRANTY; without even the implied warranty of
    MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
    GNU General Public License for more details.

    You should have received a copy of the GNU General Public License
    along with this program; if not, see <http://www.gnu.org/licenses/>.  */

#include "vs.h"
#include "dfg.h"
#include <cassert>
#include <functional>

static const bool VERIFY = false;

// implementation of the algorithm for subgraph enumeration under
// convexity, input and output constraints described in
// https://doi.org/10.1109/CSE.2009.167

static bool verify_config(const DFG &dfg, const IOSubgraph &config)
{
    // assert no forbidden nodes in config
    if (config.nodes().intersects(dfg.forbidden()))
        return false;

    // assert config is convex
    return config.nodes() == config.closure();
}

// this is the exclude_F function from the paper
// find all nodes for which there is a path from it to a forbidden node
// that does not go through the selected subgraph
static intset config_exclusion(const DFG &dfg, const intset &config)
{
    intset out(dfg.forbidden()); // L <- F

    // enumerate all edges in reverse topological order
    for (int b = dfg.num_nodes() - 1; b >= 0; b--)
        // only care about edges with b in out (L)
        // this works because a) reverse toposort b) we require all nodes with
        // no predecessors are forbidden
        if (out.contains(b))  
            for (auto &a : dfg.in_edges(b)) {
                if (a < dfg.num_nodes() && !config.contains(a))
                    out.add(a);  // if (a not in config (Q)) { L <- L OR {a} }
            }

    return out;
}

class VSFinder {
public:
    VSFinder(const DFG &dfg, const Subgraph &outputs)
        : config_(dfg, outputs.closure())
        , F_(config_exclusion(dfg, outputs.nodes()))
    {
    }

    void visit(int max_num_in,
               const std::function<void(const IOSubgraph &)> &output_cb);

private:
    IOSubgraph config_;
    intset F_;

    void fill_required();
    void fill_forbidden();
};

// this computes valConv from the paper
void VSFinder::visit(int max_num_in,
                     const std::function<void(const IOSubgraph &)> &output_cb)
{
    const DFG &dfg = config_.dfg();
    int num_perm_in = 0;
    for (auto &u : config_.inputs()) {
        if (u >= dfg.num_nodes() || F_.contains(u))
            num_perm_in++;
    }

    // this branch has too many inputs, don't bother looking further
    if (num_perm_in > max_num_in)
        return;

    // find the best-ish (better than optimal) pivot node
    // any predecessor which is not currently-excluded
    int id = -1;
    for (int u : config_.pred()) {
        if (!F_.contains(u)) {
            id = u;
            // NOTE we actually deviate from the paper and pick min(config_.pred() - F_) instead of max
            // (by adding the break stmt)
            // the goal of picking max(config_.pred() - F_) as per the paper is as a simplification for max(config_.anc() - F)
            // which is in turn because this ensures the chosen nodes remain convex at every step
            // however fill_required() and fill_forbidden() fix this differently, right...?
            // the potential benefit of min() could be fewer recursive calls since we can eliminate swaths of nodes all at once with fill_required()
            // though it's not clear that picking max() doesn't have the same effect for maximizing elimination via fill_forbidden()
            // TODO make sure we didn't just backtrack to the paper this paper is improving on...
            break;
        }
    }

    if (id == -1) {
        // no pivot found, this is a leaf! send it!
        output_cb(config_);

        if (VERIFY)
            assert(verify_config(dfg, config_));

        return;
    }

    // recurse twice, once adding the pivot to the working set...
    IOSubgraph config_prev(config_);
    config_.add(id);
    fill_required();
    visit(max_num_in, output_cb);
    config_ = std::move(config_prev);

    //  ...and once adding the pivot to the excluded set
    intset F_prev(F_);
    F_.add(id);
    fill_forbidden();
    visit(max_num_in, output_cb);
    F_ = std::move(F_prev);
}

// we chose to require the pivot
// ensure all descendants of this pivot are also required
// (since by this stage outputs are already fixed)
void VSFinder::fill_required() {
    for (int v = 0; v < config_.dfg().num_nodes(); v++) {
        if (config_.nodes().contains(v) || F_.contains(v)) {
            continue;
        }
        // if there exist an edge(u, v) where u is required, require v
        for (int u : config_.dfg().in_edges(v)) {
            if (config_.nodes().contains(u)) {
                config_.add(v);
            }
        }
    }
}

// we chose to forbid the pivot
// ensure we can never try to go down any path which can lead to the pivot
// (since by this stage outputs are already fixed)
void VSFinder::fill_forbidden() {
    for (int u = config_.dfg().num_nodes() - 1; u >= 0; u--) {
        if (config_.nodes().contains(u) || F_.contains(u)) {
            continue;
        }
        // if there exists an edge (u, v) where v is forbidden, forbid u
        for (int v : config_.dfg().out_edges(u)) {
            if (F_.contains(v)) {
                F_.add(u);
            }
        }
    }
}

namespace {

// this computes valOutputs from the paper
// and then for each valid output set calls VSFinder::visit
void vs_enumerate_(const DFG &dfg,
                   Subgraph &outputs,
                   int size,
                   int max_num_in,
                   int max_num_out,
                   const std::function<void(const IOSubgraph &)> &output_cb)
{
    if (size >= 1) {
        // find convex subgraphs with this output set
        VSFinder finder(dfg, outputs);
        finder.visit(max_num_in, output_cb);
    }

    // don't bother trying to recurse (add output nodes) if we have too many
    if (size < max_num_out) {  
        auto exclusion = config_exclusion(dfg, outputs.nodes());
        auto pred = outputs.pred();

        // valid nodes: currently-excluded nodes which are not globally
        // forbidden and which are not both a predecessor of the current output
        // set and having a successor which is both a predecessor of the
        // current output set and currently-excluded
        intset valid(dfg.num_nodes());
        for (const auto &u : exclusion) {
            if (!dfg.is_forbidden(u) &&
                !(pred.contains(u) && dfg.succ(u).intersects(pred, exclusion)))
                valid.add(u);
        }

        // we only need to enumerate up to the smallest (toposorted)
        // preexisting output
        unsigned min = outputs.nodes().minimum();
        for (int u = 0; u < dfg.num_nodes(); u++) {
            if (min != -1 && u >= min)
                break;
            if (valid.contains(u)) {
                // recurse with the single added output node
                outputs.add(u);
                vs_enumerate_(dfg,
                              outputs,
                              size + 1,
                              max_num_in,
                              max_num_out,
                              output_cb);
                outputs.remove(u);
            }
        }
    }
}

}

// main entry point
void vs_enumerate(DFG &dfg,
                  int max_num_in,
                  int max_num_out,
                  const std::function<void(const IOSubgraph &)> &output_cb)
{
    // begin with an empty output set
    Subgraph outputs(dfg);
    vs_enumerate_(dfg, outputs, 0, max_num_in, max_num_out, output_cb);

    // handle void outputs
    // for each allowed node with no successors, try explicitly adding it to the output set
    // and then trying to enumerate with max_num_out=1
    // to prevent duplicates, we can add each output to the forbidden set after it is exhausted
    // NOTE it's not clear whether order matters here. I don't think so...?
    std::vector<int> stash;
    for (int v = 0; v < dfg.num_nodes(); v++) {
        if (!dfg.out_edges(v).empty() || dfg.is_forbidden(v)) {
            continue;
        }

        outputs.add(v);
        VSFinder finder(dfg, outputs);
        finder.visit(max_num_in, output_cb);
        outputs.remove(v);

        stash.push_back(v);
        dfg.set_forbidden(v);
    }

    for (int v : std::move(stash)) {
        dfg.unset_forbidden(v);
    }
}

extern "C" {
    typedef void (*cse_output_cb)(int num_nodes, int *nodes);
    typedef struct node_t {
        bool forbidden;
    } node_t;
    typedef struct edge_t {
        int u, v;
    } edge_t;
    void cse_vs_enumerate(
        int max_num_in,
        int max_num_out,
        int num_nodes,
        node_t *nodes,
        int num_edges,
        edge_t *edges,
        cse_output_cb output_cb)
    {
        DFG dfg("", num_nodes, 0);
        for (int i = 0; i < num_nodes; i++) {
            if (nodes[i].forbidden) {
                dfg.set_forbidden(i);
            }
        }
        for (int i = 0; i < num_edges; i++) {
            dfg.add_edge(edges[i].u, edges[i].v);
        }
        dfg.index();

        int result[num_nodes];
        vs_enumerate(dfg, max_num_in, max_num_out, [output_cb, &result] (const IOSubgraph &subgraph) {
            int idx = 0;
            for (const auto &u : subgraph.nodes()) {
                result[idx] = u;
                idx++;
            }
            output_cb(idx, result);
        } );
    }
}
