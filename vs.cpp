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
#include <map>

static const bool VERIFY = false;

// implementation of the algorithm for subgraph enumeration under
// convexity, input and output constraints described in
// https://doi.org/10.1109/CSE.2009.167
// Some additions for Audrey's upcoming paper on function outlining

static bool verify_config(const DFG &dfg, const IOSubgraph &config)
{
    // assert no forbidden nodes in config
    if (config.nodes().intersects(dfg.forbidden())) {
        return false;
    }

    // assert config is convex
    return config.nodes() == config.closure();
}

// this is the exclude_F function from the paper
// find all nodes for which there is a path from it to a forbidden node
// that does not go through the selected subgraph
static intset config_exclusion(const intset &forbidden, const DFG &dfg, const intset &config)
{
    // usually out is defined as dfg.forbidden(). however, we parameterize it here
    // because actually we want slightly different definitions between phases.
    // output phase wants to use dead-end nodes as part of the starting set
    // (so their ancestors get treated as potential outputs)
    // divide-and-conquer phase wants to use true forbidden nodes
    // (so we may sneak into an appendix during growth)
    intset out(forbidden);

    // enumerate all edges in reverse topological order
    for (int v = dfg.num_nodes() - 1; v >= 0; v--) {
        // only care about edges with v in out (L)
        // this works because a) reverse toposort b) we require all nodes with
        // no successors are forbidden
        if (out.contains(v)) {
            for (int u : dfg.in_edges(v)) {
                if (!config.contains(u)) {
                    out.add(u);  // if (u not in config (Q)) { L <- L OR {u} }
                }
            }
        }
    }
    // fix up clusters
    for (int u = 0; u < dfg.num_nodes(); u++) {
        if (!out.contains(u)) {
            continue;
        }
        int cluster = dfg.cluster(u);
        if (cluster == -1) {
            continue;
        }
        do {
            out.add(cluster);
            cluster++;
        } while (dfg.is_cluster_trail(cluster));
        u = cluster - 1;
    }
    return out;
}

// overload...
static intset config_exclusion(const intset &forbidden, const DFG &dfg, const vset<int> &config) {
    intset config2(dfg.num_nodes());
    for (int u : config) {
        config2.add(u);
    }
    return config_exclusion(forbidden, dfg, config2);
}

class VSFinder {
public:
    VSFinder(const DFG &dfg, const Subgraph &outputs)
        : original_outputs_(outputs.nodes())
        , config_(dfg, outputs.closure())
        , F_(config_exclusion(dfg.forbidden(), dfg, config_.outputs()))
    {
        dead_on_arrival_ = !fill_forbidden() || !fill_required();
    }

    bool visit(int max_weight_in,
               const std::function<bool(const IOSubgraph &, std::vector<std::vector<int>> &)> &output_cb);
    bool visit_outputs(int max_weight_in,
               const std::function<bool(const IOSubgraph &, std::vector<std::vector<int>> &)> &output_cb);

private:
    bool visit_outputs_(int max_weight_in,
               const std::function<bool(const IOSubgraph &, std::vector<std::vector<int>> &)> &output_cb, int idx);
    intset original_outputs_;
    IOSubgraph config_;
    intset F_;
    bool dead_on_arrival_;

    std::vector<intset> appendices_eager_;
    std::vector<std::vector<int>> appendices_lazy_;

    bool fill_required();
    bool fill_forbidden();
};

// this computes valConv from the paper
bool VSFinder::visit(int max_weight_in,
                     const std::function<bool(const IOSubgraph &, std::vector<std::vector<int>> &)> &output_cb)
{
    if (dead_on_arrival_) {
        return true;
    }

    const DFG &dfg = config_.dfg();
    int weight_in = 0;
    for (int u : config_.inputs()) {
        assert(u < dfg.num_nodes());
        if (F_.contains(u)) {
            weight_in += dfg.weight(u) ;
        }
    }

    // this branch has too many inputs, don't bother looking further
    if (weight_in > max_weight_in)
        return true;

    // find the best-ish (better than optimal) pivot node
    // any predecessor which is not currently-excluded
    int id = -1;
    for (int u : config_.inputs()) {
        if (!F_.contains(u)) {
            id = u;
            // NOTE we actually deviate from the paper and pick min(preds - F_) instead of max(anc - F_)
            // the goal of picking max(ancestors - F_) as per the paper is as a simplification for max(config_.anc() - F)
            // which is in turn because this ensures the chosen nodes remain convex at every step
            // however fill_required() and fill_forbidden() fix this differently, right...?
            // the potential benefit of min() could be fewer recursive calls since we can eliminate swaths of nodes all at once with fill_required()
            // though it's not clear that picking max() doesn't have the same effect for maximizing elimination via fill_forbidden()
            // TODO make sure we didn't just backtrack to the paper this paper is improving on...
            if (id == -1 || u < id) {
                id = u;
            }
        }
    }

    if (id == -1) {
        // no pivot found, this is a leaf! send it!
        if (!output_cb(config_, appendices_lazy_)) {
            return false;
        }

        if (VERIFY)
            assert(verify_config(dfg, config_));

        return true;
    }

    // recurse twice, once adding the pivot to the working set...
    IOSubgraph config_prev(config_);
    int cluster = config_.dfg().cluster(id);
    if (cluster == -1) {
        config_.add(id);
    } else {
        do {
            config_.add(cluster);
            cluster++;
        } while (config_.dfg().is_cluster_trail(cluster));
    }
    if (fill_required()) {
        if (!visit(max_weight_in, output_cb)) {
            return false;
        }
    }
    config_ = std::move(config_prev);

    //  ...and once adding the pivot to the excluded set
    intset F_prev(F_);
    cluster = config_.dfg().cluster(id);
    if (cluster == -1) {
        F_.add(id);
    } else {
        do {
            F_.add(cluster);
            cluster++;
        } while (config_.dfg().is_cluster_trail(cluster));
    }
    if (fill_forbidden()) {
        if (!visit(max_weight_in, output_cb)) {
            return false;
        }
    }
    F_ = std::move(F_prev);
    return true;
}

// we chose to require the pivot
// ensure all descendants of this pivot are also required
// (since by this stage outputs are already fixed)
bool VSFinder::fill_required() {
    auto cdg_pred = config_.cdg_pred();
    for (int v = 0; v < config_.dfg().num_nodes(); v++) {
        if (config_.nodes().contains(v)) {
            if (F_.contains(v)) {
                return false;
            }
            continue;
        }
        if (!F_.contains(v)) {
            // if there exist an edge(u, v) where u is required, require v
            for (int u : config_.dfg().in_edges(v)) {
                if (config_.nodes().contains(u) && !original_outputs_.contains(u)) {
                    int cluster = config_.dfg().cluster(v);
                    if (cluster != -1) {
                        // add all cluster siblings as unit
                        do {
                            config_.add(cluster);
                            cluster++;
                        } while (config_.dfg().is_cluster_trail(cluster));
                        // skip to the end of the cluster
                        v = cluster - 1;
                    } else {
                        config_.add(v);
                    }
                    break;
                }
            }
        }
        if (config_.nodes().contains(v) || !cdg_pred.contains(v)) {
            continue;
        }
        for (int u : config_.dfg().cdg_in_edges(v)) {
            if (config_.nodes().contains(u)) {
                int cluster = config_.dfg().cluster(v);
                if (cluster != -1) {
                    // add all cluster siblings as unit
                    do {
                        if (F_.contains(cluster)) {
                            return false;
                        }
                        config_.add(cluster);
                        cluster++;
                    } while (config_.dfg().is_cluster_trail(cluster));
                    // skip to the end of the cluster
                    v = cluster - 1;
                } else {
                    if (F_.contains(v)) {
                        return false;
                    }
                    config_.add(v);
                }
                break;
            }
        }
    }
    return true;
}

// we chose to forbid the pivot
// ensure we can never try to go down any path which can lead to the pivot
// (since by this stage outputs are already fixed)
bool VSFinder::fill_forbidden() {
    auto cdg_pred = config_.cdg_pred();
    for (int u = config_.dfg().num_nodes() - 1; u >= 0; u--) {
        if (F_.contains(u)) {
            if (config_.nodes().contains(u)) {
                return false;
            }
            continue;
        }
        if (!config_.nodes().contains(u)) {
            // if there exists an edge (u, v) where v is forbidden, forbid u
            for (int v : config_.dfg().out_edges(u)) {
                if (F_.contains(v)) {
                    int cluster = config_.dfg().cluster_end(u);
                    if (cluster != -1) {
                        // forbid all cluster siblings as unit
                        F_.add(cluster);
                        while (config_.dfg().is_cluster_trail(cluster)) {
                            cluster--;
                            F_.add(cluster);
                        }
                        // skip to the end of the cluster
                        u = cluster;
                    } else {
                        F_.add(u);
                    }
                    break;
                }
            }
        }
        if (F_.contains(u) || !cdg_pred.contains(u)) {
            continue;
        }
        for (int v : config_.dfg().cdg_out_edges(u)) {
            if (F_.contains(v) && cdg_pred.contains(v)) {
                int cluster = config_.dfg().cluster_end(u);
                if (cluster != -1) {
                    // forbid all cluster siblings as unit
                    if (config_.nodes().contains(cluster)) {
                        return false;
                    }
                    F_.add(cluster);
                    while (config_.dfg().is_cluster_trail(cluster)) {
                        if (config_.nodes().contains(cluster)) {
                            return false;
                        }
                        cluster--;
                        F_.add(cluster);
                    }
                    // skip to the end of the cluster
                    u = cluster;
                } else {
                    if (config_.nodes().contains(u)) {
                        return false;
                    }
                    F_.add(u);
                }
                break;
            }
        }
    }
    return true;
}

// This handles when an output needs some of its descendants included since
// they are dead ends or lead to dead ends
// Basically a dup of the visit algorithm but going the other way
bool VSFinder::visit_outputs(int max_weight_in,
           const std::function<bool(const IOSubgraph &, std::vector<std::vector<int>> &)> &output_cb) {
    if (dead_on_arrival_) {
        return true;
    }

    // step 1: make sure we haven't shot ourselves in the foot by getting too many outputs
    // we can't ever remove with this process (via cluster completion)
    // this works best here for some reason...
    // step 2: for all the extra outputs which are forbiddable, fill em in!
    vset<int> outputs(config_.outputs());  // make a copy since we're mutating
    for (int u : outputs) {
        if (original_outputs_.contains(u)) {
            continue;
        }
        if (config_.dfg().is_forbiddable(u) ) {
            // lol
            return true;
        }
        for (int v : config_.dfg().succ(u)) {
            // wheeee
            config_.add(v);
        }
    }

    // it's finally time to union-find!
    std::vector<int> representative_succs(config_.dfg().num_nodes(), -1);
    // bool has_other_output = false;
    for (int o : config_.outputs()) {
        for (int u : config_.dfg().out_edges(o)) {
            int ou = u;
            if (config_.dfg().is_forbiddable(u)) {
                // has_other_output = true;
                continue;
            }
            if (representative_succs[u] != -1) {
                continue;
            }
            representative_succs[u] = u;
            for (int v : config_.dfg().succ(u)) { // this actually enumerates descendants
                if (ou != u || representative_succs[v] == -1) {
                    representative_succs[v] = u;
                } else {
                    // uh oh!
                    representative_succs[ou] = representative_succs[v];
                    u = representative_succs[v];
                }
            }
        }
    }

    std::function<int(int)> repr_root = [&representative_succs, &repr_root](int v) {
        int u = representative_succs[v];
        if (u == -1) {
            return -1;
        } else if (u == v) {
            return u;
        } else {
            representative_succs[v] = repr_root(u);
            return representative_succs[v];
        }
    };

    std::map<int, intset> options_map;
    for (int v = 0; v < representative_succs.size(); v++) {
        int u = repr_root(v);
        if (u == -1) {
            continue;
        }
        options_map.try_emplace(u, config_.dfg().num_nodes()).first->second.add(v);
    }

    appendices_eager_.clear();
    appendices_lazy_.clear();
    for (auto pair : std::move(options_map)) {
        bool has_inputs = false;
        for (int v : pair.second) {
            for (int u : config_.dfg().in_edges(v)) {
                if (config_.nodes().contains(u) || pair.second.contains(u)) {
                    continue;
                }
                has_inputs = true;
                break;
            }
            if (has_inputs) {
                break;
            }
        }
        if (has_inputs || config_.dfg().has_cdg_edges()) {
            appendices_eager_.emplace_back(std::move(pair.second));
        } else {
            appendices_lazy_.emplace_back(pair.second.begin(), pair.second.end());
        }
    }

    return visit_outputs_(max_weight_in, output_cb, 0);
}

bool VSFinder::visit_outputs_(int max_weight_in, const std::function<bool(const IOSubgraph &, std::vector<std::vector<int>> &)> &output_cb, int idx) {
    if (idx == appendices_eager_.size()) {
        if (config_.outputs().size() == original_outputs_.size()) {
            return VSFinder::visit(max_weight_in, output_cb);
        }
        return true;
    }

    IOSubgraph config_prev(config_);
    for (int u : appendices_eager_[idx]) {
        config_.add(u);
    }
    // when adding children of the outputs we run the risk of removing our outputs! don't do that
    // also uhhhhhh since we inflate clusters after picking the outputs there
    // might also be too many outputs to start. make sure we whittle down to the right number
    if (config_.outputs().size() >= original_outputs_.size()) {
        if (fill_required()) {
            if (!VSFinder::visit_outputs_(max_weight_in, output_cb, idx + 1)) {
                return false;
            }
        }
    }
    config_ = std::move(config_prev);

    intset F_prev(F_);
    for (int u : appendices_eager_[idx]) {
        F_.add(u);
    }
    if (fill_forbidden()) {
        if (!VSFinder::visit_outputs_(max_weight_in, output_cb, idx + 1)) {
            return false;
        }
    }
    F_ = std::move(F_prev);
    return true;
}

namespace {

// this computes valOutputs from the paper
// and then for each valid output set calls VSFinder::visit
bool vs_enumerate_(const DFG &dfg,
                   const intset &seeds,
                   Subgraph &outputs,
                   int weight,
                   int max_weight_in,
                   int max_weight_out,
                   const std::function<bool(const IOSubgraph &, std::vector<std::vector<int>> &)> &output_cb)
{
    if (weight > 0) {
        // find convex subgraphs with this output set
        VSFinder finder(dfg, outputs);
        if (!finder.visit_outputs(max_weight_in, output_cb)) {
            return false;
        }
    }

    // don't bother trying to recurse (add output nodes) if we have too many
    if (weight >= max_weight_out) {
        return true;
    }

    auto exclusion = config_exclusion(seeds, dfg, outputs.nodes());
    auto anc = outputs.pred();

    // we only need to enumerate up to the smallest (toposorted)
    // preexisting output
    unsigned bound = outputs.nodes().minimum();
    if (bound == -1) {
        bound = dfg.num_nodes();
    }

    // valid nodes: currently-excluded nodes which are not globally
    // forbidden and which are not both a predecessor of the current output
    // set and having a descendant which is both a ancestor of the
    // current output set and currently-excluded
    // (this ensures that the chosen outputs will always stay outputs I think)

    for (int u = 0; u < bound; u++) {
        if (!exclusion.contains(u)) {
            continue;
        }
        if (seeds.contains(u)) {
            continue;
        }
        // what an odd condition
        // TODO with my changes to the config_exclusion inputs it's not clear whether
        // this use of exclusion should actually be the one seeded with just F_
        if (anc.contains(u) && dfg.succ(u).intersects(anc, exclusion)) {
            continue;
        }
        // only let output nodes of clusters be used for outputs
        int cluster_start = dfg.cluster(u);
        if (cluster_start == u) {
            continue;
        }
        weight += dfg.weight(u);
        outputs.add(u);

        if (weight <= max_weight_out) {
            // recurse with the output node(s) added
            if (!vs_enumerate_(dfg,
                          seeds,
                          outputs,
                          weight,
                          max_weight_in,
                          max_weight_out,
                          output_cb)) {
                return false;
            }
        }

        weight -= dfg.weight(u);
        outputs.remove(u);
    }
    return true;
}

}

// main entry point
bool vs_enumerate(DFG &dfg,
                  int max_weight_in,
                  int max_weight_out,
                  const std::function<bool(const IOSubgraph &, std::vector<std::vector<int>> &)> &output_cb)
{
    // begin with an empty output set
    Subgraph outputs(dfg);
    intset seeds(dfg.forbidden());
    for (int u = 0; u < dfg.num_nodes(); u++) {
        if (dfg.out_edges(u).size() == 0) {
            seeds.add(u);
        }
    }
    if (!vs_enumerate_(dfg, seeds, outputs, 0, max_weight_in, max_weight_out, output_cb)) {
        return false;
    }

    // handle void outputs
    // for each allowed node with no successors, try explicitly using it as the only output
    // to prevent duplicates, we can add each output to the forbidden set after it is exhausted
    // NOTE it's not clear whether order matters here. I don't think so...?
    // NOTE by downstream definition there's no such thing as a void cluster
    std::vector<int> stash;
    for (int v = 0; v < dfg.num_nodes(); v++) {
        if (!dfg.out_edges(v).empty() || dfg.is_forbidden(v)) {
            continue;
        }
        outputs.add(v);

        VSFinder finder(dfg, outputs);
        if (!finder.visit(max_weight_in, output_cb)) {
            return false;
        }

        outputs.remove(v);
        stash.push_back(v);
        dfg.set_forbidden(v);
    }

    for (int v : std::move(stash)) {
        dfg.unset_forbidden(v);
    }
    return true;
}

extern "C" {
    typedef struct nodelist_t {
        int *nodes;
        int count;
    } nodelist_t;
    typedef bool (*cse_output_cb)(int num_nodes, int *nodes, int num_appendices, const nodelist_t *appendices);
    typedef struct node_t {
        bool forbidden;
        bool cluster_trail;
        int weight;
    } node_t;
    typedef struct edge_t {
        int u, v;
    } edge_t;
    int cse_vs_enumerate(
        int max_weight_in,
        int max_weight_out,
        int num_nodes,
        node_t *nodes,
        int num_edges,
        edge_t *edges,
        int num_cdg_edges,
        edge_t *cdg_edges,
        cse_output_cb output_cb)
    {
        DFG dfg("", num_nodes, 0);
        bool in_cluster = false;
        for (int i = 0; i < num_nodes; i++) {
            if (nodes[i].forbidden) {
                dfg.set_forbidden(i);
            }
            if (nodes[i].cluster_trail) {
                dfg.set_cluster_trail(i);
            }
            dfg.weight(i) = nodes[i].weight;
        }
        if (in_cluster) {
            return -1;
        }
        for (int i = 0; i < num_edges; i++) {
            dfg.add_edge(edges[i].u, edges[i].v);
        }
        for (int i = 0; i < num_cdg_edges; i++) {
            dfg.add_cdg_edge(cdg_edges[i].u, cdg_edges[i].v);
        }
        dfg.index();

        int result[num_nodes];
        if (!vs_enumerate(dfg, max_weight_in, max_weight_out, [output_cb, &result] (const IOSubgraph &subgraph, std::vector<std::vector<int>> &appendices) {
            int idx = 0;
            nodelist_t appendices_c[appendices.size()];
            for (const auto &u : subgraph.nodes()) {
                result[idx] = u;
                idx++;
            }
            for (int i = 0; i < appendices.size(); i++) {
                appendices_c[i].nodes = &appendices[i][0];
                appendices_c[i].count = appendices[i].size();
            }
            return output_cb(idx, result, appendices.size(), &appendices_c[0]);
        } )) {
            return -2;
        }
        return 0;
    }
}
