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
#include <vector>

static const bool VERIFY = false;

// implementation of the algorithm for subgraph enumeration under
// convexity, input and output constraints described in
// https://doi.org/10.1109/CSE.2009.167

static bool verify_config(const DFG &dfg, const IOSubgraph &config)
{
    if (config.nodes().intersects(dfg.forbidden()))
        return false;

    return config.nodes() == config.closure();
}

static intset config_exclusion(const DFG &dfg, const intset &config)
{
    intset out(dfg.forbidden());

    // The exhaustive enumerator grows subgraphs from candidate outputs.
    // Upstream assumed graph sinks were already forbidden, which seeded this
    // exclusion set. When sinks are allowed, seed with actual sinks instead.
    for (int u = 0; u < dfg.num_nodes(); u++)
        if (dfg.out_edges(u).empty())
            out.add(u);

    for (int b = dfg.num_nodes() - 1; b >= 0; b--)
        if (out.contains(b))
            for (auto &a : dfg.in_edges(b)) {
                if (a < dfg.num_nodes() && !config.contains(a))
                    out.add(a);
            }

    return out;
}

static std::unique_ptr<DFG> reverse_dfg(const DFG &dfg)
{
    auto reversed = std::make_unique<DFG>(
        dfg.name() + "_reversed",
        dfg.num_nodes(),
        0,
        dfg.forbid_sources_and_sinks());

    for (int u = 0; u < dfg.num_nodes(); u++) {
        reversed->weight(u) = dfg.weight(u);
        if (dfg.is_forbidden(u))
            reversed->set_forbidden(u);
        for (const auto &v : dfg.out_edges(u))
            reversed->add_edge(v, u);
    }

    reversed->index();
    return reversed;
}

static bool is_weakly_connected_subgraph(const DFG &dfg, const intset &nodes)
{
    int start = nodes.minimum();
    if (start == -1)
        return true;

    intset visited(dfg.num_nodes());
    std::vector<int> stack;
    stack.push_back(start);
    visited.add(start);

    while (!stack.empty()) {
        int u = stack.back();
        stack.pop_back();

        for (const auto &v : dfg.out_edges(u)) {
            if (nodes.contains(v) && !visited.contains(v)) {
                visited.add(v);
                stack.push_back(v);
            }
        }
        for (const auto &v : dfg.in_edges(u)) {
            if (nodes.contains(v) && !visited.contains(v)) {
                visited.add(v);
                stack.push_back(v);
            }
        }
    }

    return visited.size() == nodes.size();
}

class VSFinder {
public:
    VSFinder(const DFG &dfg, const Subgraph &outputs, bool connected_only = false)
        : config_(dfg, outputs.closure())
        , F_(config_exclusion(dfg, outputs.nodes()))
        , connected_only_(connected_only)
    {
    }

    void visit(int max_num_in,
               const std::function<void(const IOSubgraph &)> &output_cb);

private:
    IOSubgraph config_;
    intset F_;
    bool connected_only_;
};

static bool can_still_be_connected(const IOSubgraph &config)
{
    int start = config.nodes().minimum();
    if (start == -1)
        return true;

    const DFG &dfg = config.dfg();
    intset possible(config.nodes());
    possible.add(config.pred());

    intset visited(dfg.num_nodes());
    std::vector<int> stack;
    stack.push_back(start);
    visited.add(start);

    while (!stack.empty()) {
        int u = stack.back();
        stack.pop_back();

        for (const auto &v : dfg.out_edges(u)) {
            if (possible.contains(v) && !visited.contains(v)) {
                visited.add(v);
                stack.push_back(v);
            }
        }
        for (const auto &v : dfg.in_edges(u)) {
            if (possible.contains(v) && !visited.contains(v)) {
                visited.add(v);
                stack.push_back(v);
            }
        }
    }

    for (const auto &u : config.nodes())
        if (!visited.contains(u))
            return false;
    return true;
}

void VSFinder::visit(int max_num_in,
                     const std::function<void(const IOSubgraph &)> &output_cb)
{
    const DFG &dfg = config_.dfg();
    int num_perm_in = 0;
    for (auto &u : config_.inputs()) {
        if (u >= dfg.num_nodes() || F_.contains(u))
            num_perm_in++;
    }

    if (num_perm_in > max_num_in)
        return;

    if (connected_only_ && !can_still_be_connected(config_))
        return;

    if (max_num_in == 0) {
        while (true) {
            int id = -1;
            auto pred = config_.pred();
            for (const auto &u : pred) {
                if (!F_.contains(u))
                    id = u;
            }
            if (id == -1)
                break;
            config_.add(id);
        }

        for (auto &u : config_.inputs()) {
            if (u >= dfg.num_nodes() || F_.contains(u))
                return;
        }

        if (!connected_only_ ||
            is_weakly_connected_subgraph(dfg, config_.nodes())) {
            output_cb(config_);
        }

        if (VERIFY)
            assert(verify_config(dfg, config_));

        return;
    }

    int id = -1;
    auto pred = config_.pred();
    for (const auto &u : pred) {
        if (!F_.contains(u))
            id = u;
    }

    if (id == -1) {
        if (!connected_only_ ||
            is_weakly_connected_subgraph(dfg, config_.nodes())) {
            output_cb(config_);
        }

        if (VERIFY)
            assert(verify_config(dfg, config_));

        return;
    }

    config_.add(id);
    visit(max_num_in, output_cb);

    config_.remove(id);
    intset F_prev(F_);
    F_.add(id);
    F_.add(dfg.pred(id));
    visit(max_num_in, output_cb);
    F_ = F_prev;
}

namespace {

void add_nodes(IOSubgraph &config, const intset &nodes)
{
    std::vector<int> added;
    added.reserve(nodes.size());
    for (const auto &u : nodes)
        if (!config.nodes().contains(u))
            added.push_back(u);
    for (auto it = added.rbegin(); it != added.rend(); ++it)
        config.add(*it);
}

void remove_nodes(IOSubgraph &config, const intset &nodes)
{
    for (const auto &u : nodes)
        if (config.nodes().contains(u))
            config.remove(u);
}

void vs_enumerate_zero_inputs_(const DFG &dfg,
                               const Subgraph &outputs,
                               const std::function<void(const IOSubgraph &)> &output_cb,
                               bool connected_only)
{
    intset nodes(outputs.closure());
    intset F(config_exclusion(dfg, outputs.nodes()));

    while (true) {
        Subgraph config(dfg, intset(nodes));
        intset pred(config.pred());
        intset addable(pred);
        addable.remove(F);
        if (addable.minimum() == static_cast<unsigned>(-1)) {
            if (pred.intersects(F))
                return;
            break;
        }
        nodes.add(addable);
    }

    if (connected_only && !is_weakly_connected_subgraph(dfg, nodes))
        return;

    IOSubgraph config(dfg, std::move(nodes));
    if (config.num_in() != 0)
        return;

    if (VERIFY)
        assert(verify_config(dfg, config));

    output_cb(config);
}

class ZeroOutputConnectedFinder {
public:
    ZeroOutputConnectedFinder(const DFG &dfg,
                              int max_num_in,
                              const std::function<void(const IOSubgraph &)> &output_cb)
        : dfg_(dfg)
        , max_num_in_(max_num_in)
        , output_cb_(output_cb)
        , config_(dfg)
        , forbidden_(dfg.forbidden())
        , closures_(dfg.num_nodes(), intset(dfg.num_nodes()))
        , valid_(dfg.num_nodes(), false)
    {
        for (int u = 0; u < dfg_.num_nodes(); u++) {
            closures_[u].add(u);
            closures_[u].add(dfg_.succ(u));
            valid_[u] = !closures_[u].intersects(forbidden_);
        }
    }

    void enumerate()
    {
        for (int root = 0; root < dfg_.num_nodes(); root++) {
            if (!valid_[root])
                continue;

            add_nodes(config_, closures_[root]);
            if (config_.num_in() <= max_num_in_)
                output_cb_(config_);

            intset blocked(dfg_.num_nodes());
            blocked.add(root);
            blocked.add(dfg_.pred(root));
            blocked.add(dfg_.succ(root));

            intset frontier(dfg_.num_nodes());
            for (int u = root + 1; u < dfg_.num_nodes(); u++) {
                if (!valid_[u] || blocked.contains(u))
                    continue;
                if (closures_[u].intersects(config_.nodes()))
                    frontier.add(u);
            }

            visit(frontier, blocked);
            remove_nodes(config_, closures_[root]);
        }
    }

private:
    void visit(intset &frontier, const intset &blocked)
    {
        while (true) {
            int next = frontier.minimum();
            if (next == static_cast<unsigned>(-1))
                return;

            frontier.remove(next);

            intset blocked_next(blocked);
            blocked_next.add(next);
            blocked_next.add(dfg_.pred(next));
            blocked_next.add(dfg_.succ(next));

            intset added(closures_[next]);
            added.remove(config_.nodes());
            add_nodes(config_, added);

            if (config_.num_in() <= max_num_in_) {
                output_cb_(config_);

                intset frontier_next(frontier);
                for (int u = next + 1; u < dfg_.num_nodes(); u++) {
                    if (!valid_[u] || blocked_next.contains(u) ||
                        frontier_next.contains(u))
                        continue;
                    if (closures_[u].intersects(config_.nodes()))
                        frontier_next.add(u);
                }

                visit(frontier_next, blocked_next);
            }

            remove_nodes(config_, added);
        }
    }

    const DFG &dfg_;
    int max_num_in_;
    const std::function<void(const IOSubgraph &)> &output_cb_;
    IOSubgraph config_;
    intset forbidden_;
    std::vector<intset> closures_;
    std::vector<bool> valid_;
};

void vs_enumerate_zero_outputs_(const DFG &dfg,
                                int max_num_in,
                                const std::function<void(const IOSubgraph &)> &output_cb,
                                bool connected_only)
{
    if (connected_only) {
        ZeroOutputConnectedFinder(dfg, max_num_in, output_cb).enumerate();
        return;
    }

    auto reversed = reverse_dfg(dfg);
    vs_enumerate(
        *reversed,
        0,
        dfg.num_nodes(),
        [&dfg, max_num_in, connected_only, &output_cb](const IOSubgraph &subgraph) {
            IOSubgraph original_subgraph(dfg);
            original_subgraph.set(subgraph.nodes());
            if (original_subgraph.num_out() == 0 &&
                original_subgraph.num_in() <= max_num_in &&
                (!connected_only ||
                 is_weakly_connected_subgraph(dfg, original_subgraph.nodes()))) {
                output_cb(original_subgraph);
            }
        },
        connected_only);
}

void vs_enumerate_(const DFG &dfg,
                   Subgraph &outputs,
                   int size,
                   int max_num_in,
                   int max_num_out,
                   const std::function<void(const IOSubgraph &)> &output_cb,
                   bool connected_only)
{
    if (size >= 1) {
        if (max_num_in == 0) {
            vs_enumerate_zero_inputs_(dfg, outputs, output_cb, connected_only);
        } else {
            VSFinder finder(dfg, outputs, connected_only);
            finder.visit(max_num_in, output_cb);
        }
    }
    if (size < max_num_out) {
        auto exclusion = config_exclusion(dfg, outputs.nodes());
        auto pred = outputs.pred();
        intset valid(dfg.num_nodes());
        for (const auto &u : exclusion) {
            if (!dfg.is_forbidden(u) &&
                !(pred.contains(u) && dfg.succ(u).intersects(pred, exclusion)))
                valid.add(u);
        }

        unsigned min = outputs.nodes().minimum();
        for (int u = 0; u < dfg.num_nodes(); u++) {
            if (min != -1 && u >= min)
                break;
            if (valid.contains(u)) {
                outputs.add(u);
                vs_enumerate_(dfg,
                              outputs,
                              size + 1,
                              max_num_in,
                              max_num_out,
                              output_cb,
                              connected_only);
                outputs.remove(u);
            }
        }
    }
}

}

void vs_enumerate(const DFG &dfg,
                  int max_num_in,
                  int max_num_out,
                  const std::function<void(const IOSubgraph &)> &output_cb,
                  bool connected_only)
{
    if (max_num_out == 0) {
        vs_enumerate_zero_outputs_(dfg, max_num_in, output_cb, connected_only);
        return;
    }

    Subgraph outputs(dfg);
    vs_enumerate_(
        dfg,
        outputs,
        0,
        max_num_in,
        max_num_out,
        output_cb,
        connected_only);
}
