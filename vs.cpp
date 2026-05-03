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
#include <deque>
#include <functional>
#include <tuple>
#include <unordered_map>
#include <unordered_set>
#include <vector>

static const bool VERIFY = false;

// implementation of the algorithm for subgraph enumeration under
// convexity, input and output constraints described in
// https://doi.org/10.1109/CSE.2009.167

static bool verify_config(const DFG &dfg, const IOSubgraph &config)
{
    if (config.nodes().intersects(dfg.body_forbidden()))
        return false;
    for (const auto &u : config.inputs())
        if (u < dfg.num_nodes() && dfg.is_input_forbidden(u))
            return false;

    return config.nodes() == config.closure();
}

static intset config_exclusion(const DFG &dfg, const intset &config)
{
    intset out(dfg.body_forbidden());

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
        if (dfg.is_body_forbidden(u))
            reversed->set_body_forbidden(u);
        if (dfg.is_input_forbidden(u))
            reversed->set_input_forbidden(u);
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

static intset augmented_nodes(const DFG &dfg, const intset &nodes)
{
    intset augmented(nodes);
    for (const auto &u : nodes) {
        for (const auto &v : dfg.in_edges(u)) {
            if (!nodes.contains(v))
                augmented.add(v);
        }
    }
    return augmented;
}

static intset closure_in_graph(const DFG &dfg, const intset &nodes)
{
    Subgraph subgraph(dfg, intset(nodes));
    return subgraph.closure();
}

static bool is_convex_in_graph(const DFG &dfg, const intset &nodes)
{
    return closure_in_graph(dfg, nodes) == nodes;
}

static intset dual_closure(const DFG &dfg,
                           const DFG *alternate_graph,
                           const intset &nodes)
{
    intset closed(nodes);
    while (true) {
        intset next = closure_in_graph(dfg, closed);
        if (alternate_graph != nullptr)
            next.add(closure_in_graph(*alternate_graph, closed));
        if (next == closed)
            return next;
        closed = std::move(next);
    }
}

static intset zero_output_closure(const DFG &dfg,
                                  const DFG *alternate_graph,
                                  const intset &nodes)
{
    intset closed(nodes);
    while (true) {
        intset next(closed);
        for (const auto &u : closed)
            next.add(dfg.succ(u));
        if (alternate_graph != nullptr)
            next = dual_closure(dfg, alternate_graph, next);
        if (next == closed)
            return next;
        closed = std::move(next);
    }
}

static bool is_weakly_connected_with_inputs(const DFG &dfg,
                                            const IOSubgraph &config)
{
    intset body(config.nodes());
    intset inputs(dfg.num_nodes());
    intset augmented(body);
    for (const auto &u : config.inputs()) {
        if (u < dfg.num_nodes()) {
            inputs.add(u);
            augmented.add(u);
        }
    }

    int start = augmented.minimum();
    if (start == -1)
        return true;

    intset visited(dfg.num_nodes());
    std::vector<int> stack;
    stack.push_back(start);
    visited.add(start);

    auto expand = [&](int u, const auto &neighbors) {
        for (const auto &v : neighbors) {
            if (!augmented.contains(v) || visited.contains(v))
                continue;
            if (inputs.contains(u) && inputs.contains(v))
                continue;
            visited.add(v);
            stack.push_back(v);
        }
    };

    while (!stack.empty()) {
        int u = stack.back();
        stack.pop_back();
        expand(u, dfg.out_edges(u));
        expand(u, dfg.in_edges(u));
    }

    return visited.size() == augmented.size();
}

static bool has_forbidden_inputs(const DFG &dfg, const IOSubgraph &config)
{
    for (const auto &u : config.inputs())
        if (u < dfg.num_nodes() && dfg.is_input_forbidden(u))
            return true;
    return false;
}

namespace {

template <class T>
inline void hash_combine(std::size_t &seed, const T &value)
{
    seed ^= std::hash<T>{}(value) + 0x9e3779b9 + (seed << 6) + (seed >> 2);
}

struct IntsetHash {
    std::size_t operator()(const intset &values) const
    {
        return values.hash();
    }
};

struct SearchStateHash {
    std::size_t operator()(const std::tuple<intset, intset, intset> &state) const
    {
        const auto &[nodes, frontier, blocked] = state;
        std::size_t seed = IntsetHash{}(nodes);
        hash_combine(seed, IntsetHash{}(frontier));
        hash_combine(seed, IntsetHash{}(blocked));
        return seed;
    }
};

struct BucketKeyHash {
    std::size_t operator()(
        const std::tuple<unsigned, unsigned, unsigned> &bucket) const
    {
        const auto &[size_bin, num_inputs, minimal_nodes_bin] = bucket;
        std::size_t seed = std::hash<unsigned>{}(size_bin);
        hash_combine(seed, num_inputs);
        hash_combine(seed, minimal_nodes_bin);
        return seed;
    }
};

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

}

static intset singleton_set(unsigned size, int node)
{
    intset nodes(size);
    nodes.add(node);
    return nodes;
}

class VSFinder {
public:
    VSFinder(const DFG &dfg,
             const Subgraph &outputs,
             const DFG *alternate_graph = nullptr,
             int max_subgraph_size = -1,
             bool connected_only = false)
        : config_(dfg, dual_closure(dfg, alternate_graph, outputs.nodes()))
        , F_(config_exclusion(dfg, outputs.nodes()))
        , alternate_graph_(alternate_graph)
        , max_subgraph_size_(max_subgraph_size)
        , connected_only_(connected_only)
    {
    }

    void visit(int max_num_in,
               const std::function<void(const IOSubgraph &)> &output_cb);

private:
    IOSubgraph config_;
    intset F_;
    const DFG *alternate_graph_;
    int max_subgraph_size_;
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

    if (max_subgraph_size_ >= 0 &&
        config_.nodes().size() > static_cast<unsigned>(max_subgraph_size_))
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
            intset closed = dual_closure(
                dfg, alternate_graph_, config_.nodes() | singleton_set(config_.nodes().max_size(), id));
            if (closed.intersects(F_) || closed.intersects(dfg.body_forbidden()))
                return;
            intset added(closed);
            added.remove(config_.nodes());
            add_nodes(config_, added);
            if (max_subgraph_size_ >= 0 &&
                config_.nodes().size() > static_cast<unsigned>(max_subgraph_size_))
                return;
        }

        for (auto &u : config_.inputs()) {
            if (u >= dfg.num_nodes() || F_.contains(u) ||
                dfg.is_input_forbidden(u))
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
        if (!has_forbidden_inputs(dfg, config_) &&
            (!connected_only_ ||
             is_weakly_connected_subgraph(dfg, config_.nodes()))) {
            output_cb(config_);
        }

        if (VERIFY)
            assert(verify_config(dfg, config_));

        return;
    }

    intset closed = dual_closure(
        dfg, alternate_graph_, config_.nodes() | singleton_set(config_.nodes().max_size(), id));
    if (!closed.intersects(F_) && !closed.intersects(dfg.body_forbidden())) {
        intset added(closed);
        added.remove(config_.nodes());
        add_nodes(config_, added);
        visit(max_num_in, output_cb);
        remove_nodes(config_, added);
    }
    intset F_prev(F_);
    F_.add(id);
    F_.add(dfg.pred(id));
    visit(max_num_in, output_cb);
    F_ = F_prev;
}

namespace {

void vs_enumerate_zero_inputs_(const DFG &dfg,
                               const Subgraph &outputs,
                               int max_subgraph_size,
                               const DFG *alternate_graph,
                               const std::function<void(const IOSubgraph &)> &output_cb,
                               bool connected_only)
{
    intset nodes(dual_closure(dfg, alternate_graph, outputs.nodes()));
    if (max_subgraph_size >= 0 &&
        nodes.size() > static_cast<unsigned>(max_subgraph_size))
        return;
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
        nodes = dual_closure(dfg, alternate_graph, nodes | addable);
        if (nodes.intersects(F) || nodes.intersects(dfg.body_forbidden()))
            return;
        if (max_subgraph_size >= 0 &&
            nodes.size() > static_cast<unsigned>(max_subgraph_size))
            return;
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
                              int max_subgraph_size,
                              const std::function<void(const IOSubgraph &)> &output_cb,
                              const DFG *alternate_graph = nullptr)
        : dfg_(dfg)
        , max_num_in_(max_num_in)
        , max_subgraph_size_(max_subgraph_size)
        , output_cb_(output_cb)
        , alternate_graph_(alternate_graph)
        , config_(dfg)
        , forbidden_(dfg.body_forbidden())
        , closures_(dfg.num_nodes(), intset(dfg.num_nodes()))
        , augmented_closures_(dfg.num_nodes(), intset(dfg.num_nodes()))
        , body_neighbors_(dfg.num_nodes(), intset(dfg.num_nodes()))
        , input_neighbors_(dfg.num_nodes(), intset(dfg.num_nodes()))
        , valid_(dfg.num_nodes(), false)
    {
        for (int u = 0; u < dfg_.num_nodes(); u++) {
            closures_[u] = closure_for(singleton_set(dfg_.num_nodes(), u));
            augmented_closures_[u] = augmented_nodes(dfg_, closures_[u]);
            intset inputs(augmented_closures_[u]);
            inputs.remove(closures_[u]);
            for (const auto &v : closures_[u]) {
                for (const auto &w : dfg_.in_edges(v))
                    body_neighbors_[u].add(w);
                for (const auto &w : dfg_.out_edges(v))
                    body_neighbors_[u].add(w);
            }
            for (const auto &v : inputs) {
                for (const auto &w : dfg_.in_edges(v))
                    input_neighbors_[u].add(w);
                for (const auto &w : dfg_.out_edges(v))
                    input_neighbors_[u].add(w);
            }
            valid_[u] = !closures_[u].intersects(forbidden_);
        }
    }

    void enumerate()
    {
        for (int root = 0; root < dfg_.num_nodes(); root++) {
            if (!valid_[root])
                continue;

            add_nodes(config_, closures_[root]);
            if ((max_subgraph_size_ < 0 ||
                config_.nodes().size() <= static_cast<unsigned>(max_subgraph_size_)) &&
                config_.num_in() <= max_num_in_ &&
                !has_forbidden_inputs(dfg_, config_) &&
                config_.num_out() == 0 &&
                is_weakly_connected_with_inputs(dfg_, config_))
                emit(config_);

            if (max_subgraph_size_ >= 0 &&
                config_.nodes().size() >= static_cast<unsigned>(max_subgraph_size_)) {
                remove_nodes(config_, closures_[root]);
                continue;
            }

            intset blocked(dfg_.num_nodes());
            blocked.add(root);
            blocked.add(dfg_.pred(root));
            blocked.add(dfg_.succ(root));

            intset frontier(dfg_.num_nodes());
            intset current_augmented = augmented_nodes(dfg_, config_.nodes());
            for (int u = root + 1; u < dfg_.num_nodes(); u++) {
                if (!valid_[u] || blocked.contains(u))
                    continue;
                if (closures_[u].is_subset_of(config_.nodes()))
                    continue;
                if (can_connect(u, config_.nodes(), current_augmented))
                    frontier.add(u);
            }

            visit(frontier, blocked);
            remove_nodes(config_, closures_[root]);
        }
    }

private:
    using SearchState = std::tuple<intset, intset, intset>;

    const intset &closure_for(const intset &nodes)
    {
        auto it = closure_cache_.find(nodes);
        if (it != closure_cache_.end())
            return it->second;
        return closure_cache_
            .emplace(intset(nodes), zero_output_closure(dfg_, alternate_graph_, nodes))
            .first->second;
    }

    bool can_connect(int u,
                     const intset &current_nodes,
                     const intset &current_augmented) const
    {
        return augmented_closures_[u].intersects(current_augmented) ||
               body_neighbors_[u].intersects(current_augmented) ||
               input_neighbors_[u].intersects(current_nodes);
    }

    void emit(const IOSubgraph &config)
    {
        if (emitted_.insert(intset(config.nodes())).second)
            output_cb_(config);
    }

    void visit(intset &frontier, const intset &blocked)
    {
        if (max_subgraph_size_ >= 0 &&
            config_.nodes().size() >= static_cast<unsigned>(max_subgraph_size_))
            return;

        SearchState state(config_.nodes(), frontier, blocked);
        if (!visited_states_.insert(std::move(state)).second)
            return;

        while (true) {
            int next = frontier.minimum();
            if (next == static_cast<unsigned>(-1))
                return;

            frontier.remove(next);

            intset blocked_next(blocked);
            blocked_next.add(next);
            blocked_next.add(dfg_.pred(next));
            blocked_next.add(dfg_.succ(next));

            intset seed(config_.nodes() | singleton_set(dfg_.num_nodes(), next));
            intset closed = closure_for(seed);
            if (closed.intersects(forbidden_))
                continue;

            intset added(closed);
            added.remove(config_.nodes());
            if (added.minimum() == static_cast<unsigned>(-1))
                continue;
            add_nodes(config_, added);

            if ((max_subgraph_size_ < 0 ||
                 config_.nodes().size() <= static_cast<unsigned>(max_subgraph_size_)) &&
                config_.num_in() <= max_num_in_ &&
                !has_forbidden_inputs(dfg_, config_) &&
                config_.num_out() == 0) {
                if (is_weakly_connected_with_inputs(dfg_, config_))
                    emit(config_);

                if (max_subgraph_size_ < 0 ||
                    config_.nodes().size() < static_cast<unsigned>(max_subgraph_size_)) {
                    intset frontier_next(frontier);
                    intset current_augmented = augmented_nodes(dfg_, config_.nodes());
                    for (int u = next + 1; u < dfg_.num_nodes(); u++) {
                        if (!valid_[u] || blocked_next.contains(u) ||
                            frontier_next.contains(u))
                            continue;
                        if (closures_[u].is_subset_of(config_.nodes()))
                            continue;
                        if (can_connect(u, config_.nodes(), current_augmented))
                            frontier_next.add(u);
                    }

                    visit(frontier_next, blocked_next);
                }
            }

            remove_nodes(config_, added);
        }
    }

    const DFG &dfg_;
    int max_num_in_;
    int max_subgraph_size_;
    const std::function<void(const IOSubgraph &)> &output_cb_;
    const DFG *alternate_graph_;
    IOSubgraph config_;
    intset forbidden_;
    std::vector<intset> closures_;
    std::vector<intset> augmented_closures_;
    std::vector<intset> body_neighbors_;
    std::vector<intset> input_neighbors_;
    std::vector<bool> valid_;
    std::unordered_map<intset, intset, IntsetHash> closure_cache_;
    std::unordered_set<intset, IntsetHash> emitted_;
    std::unordered_set<SearchState, SearchStateHash> visited_states_;
};

class SampledZeroOutputConnectedFinder {
public:
    SampledZeroOutputConnectedFinder(const DFG &dfg,
                                     int max_num_in,
                                     int max_subgraph_size,
                                     const std::function<void(const IOSubgraph &)> &output_cb,
                                     const DFG *alternate_graph,
                                     int max_states_expanded,
                                     int max_samples,
                                     int max_children_per_state,
                                     int size_bin_width,
                                     int thicken_radius,
                                     bool bucket_by_num_inputs,
                                     int minimal_node_bin_width)
        : dfg_(dfg)
        , max_num_in_(max_num_in)
        , max_subgraph_size_(max_subgraph_size)
        , output_cb_(output_cb)
        , alternate_graph_(alternate_graph)
        , max_states_expanded_(max_states_expanded)
        , max_samples_(max_samples)
        , max_children_per_state_(max_children_per_state)
        , size_bin_width_(size_bin_width)
        , thicken_radius_(thicken_radius)
        , bucket_by_num_inputs_(bucket_by_num_inputs)
        , minimal_node_bin_width_(minimal_node_bin_width)
        , forbidden_(dfg.body_forbidden())
        , closures_(dfg.num_nodes(), intset(dfg.num_nodes()))
        , augmented_closures_(dfg.num_nodes(), intset(dfg.num_nodes()))
        , body_neighbors_(dfg.num_nodes(), intset(dfg.num_nodes()))
        , input_neighbors_(dfg.num_nodes(), intset(dfg.num_nodes()))
        , valid_(dfg.num_nodes(), false)
    {
        for (int u = 0; u < dfg_.num_nodes(); u++) {
            closures_[u] = closure_for(singleton_set(dfg_.num_nodes(), u));
            augmented_closures_[u] = augmented_nodes(dfg_, closures_[u]);
            intset inputs(augmented_closures_[u]);
            inputs.remove(closures_[u]);
            for (const auto &v : closures_[u]) {
                for (const auto &w : dfg_.in_edges(v))
                    body_neighbors_[u].add(w);
                for (const auto &w : dfg_.out_edges(v))
                    body_neighbors_[u].add(w);
            }
            for (const auto &v : inputs) {
                for (const auto &w : dfg_.in_edges(v))
                    input_neighbors_[u].add(w);
                for (const auto &w : dfg_.out_edges(v))
                    input_neighbors_[u].add(w);
            }
            valid_[u] = !closures_[u].intersects(forbidden_);
        }
    }

    void enumerate()
    {
        if (max_states_expanded_ <= 0 || max_samples_ <= 0)
            return;

        for (int root = 0; root < dfg_.num_nodes(); root++) {
            if (!valid_[root])
                continue;

            SearchState root_state(
                intset(closures_[root]),
                intset(dfg_.num_nodes()),
                intset(dfg_.num_nodes()));
            if (max_subgraph_size_ >= 0 &&
                root_state.nodes.size() > static_cast<unsigned>(max_subgraph_size_))
                continue;

            root_state.blocked.add(root);
            root_state.blocked.add(dfg_.pred(root));
            root_state.blocked.add(dfg_.succ(root));

            intset current_augmented = augmented_nodes(dfg_, root_state.nodes);
            for (int u = root + 1; u < dfg_.num_nodes(); u++) {
                if (!valid_[u] || root_state.blocked.contains(u))
                    continue;
                if (closures_[u].is_subset_of(root_state.nodes))
                    continue;
                if (can_connect(u, root_state.nodes, current_augmented))
                    root_state.frontier.add(u);
            }

            enqueue_if_new(std::move(root_state));
        }

        while (!agenda_.empty() && states_expanded_ < max_states_expanded_ &&
               samples_emitted_ < max_samples_) {
            SearchState current(std::move(agenda_.front()));
            agenda_.pop_front();
            maybe_emit(current.nodes);
            expand_with_contraction(std::move(current));
        }
    }

private:
    struct SearchState {
        intset nodes;
        intset frontier;
        intset blocked;

        SearchState(intset nodes_, intset frontier_, intset blocked_)
            : nodes(std::move(nodes_))
            , frontier(std::move(frontier_))
            , blocked(std::move(blocked_))
        {
        }

        SearchState(const SearchState &) = default;
        SearchState(SearchState &&) noexcept = default;
        SearchState &operator=(const SearchState &) = default;
        SearchState &operator=(SearchState &&) noexcept = default;
    };

    struct Candidate {
        SearchState state;
        unsigned delta_size;
        std::tuple<unsigned, unsigned, unsigned> bucket_key;
        unsigned current_bucket_count;
        int first_added;

        Candidate(SearchState state_,
                  unsigned delta_size_,
                  std::tuple<unsigned, unsigned, unsigned> bucket_key_,
                  unsigned current_bucket_count_,
                  int first_added_)
            : state(std::move(state_))
            , delta_size(delta_size_)
            , bucket_key(std::move(bucket_key_))
            , current_bucket_count(current_bucket_count_)
            , first_added(first_added_)
        {
        }

        Candidate(const Candidate &) = default;
        Candidate(Candidate &&) noexcept = default;
        Candidate &operator=(const Candidate &) = default;
        Candidate &operator=(Candidate &&) noexcept = default;
    };

    using SearchStateKey = std::tuple<intset, intset, intset>;

    const intset &closure_for(const intset &nodes)
    {
        auto it = closure_cache_.find(nodes);
        if (it != closure_cache_.end())
            return it->second;
        return closure_cache_
            .emplace(intset(nodes), zero_output_closure(dfg_, alternate_graph_, nodes))
            .first->second;
    }

    bool can_connect(int u,
                     const intset &current_nodes,
                     const intset &current_augmented) const
    {
        return augmented_closures_[u].intersects(current_augmented) ||
               body_neighbors_[u].intersects(current_augmented) ||
               input_neighbors_[u].intersects(current_nodes);
    }

    unsigned num_bins() const
    {
        unsigned limit =
            max_subgraph_size_ >= 0 ? static_cast<unsigned>(max_subgraph_size_) :
                                      static_cast<unsigned>(dfg_.num_nodes());
        return limit / static_cast<unsigned>(size_bin_width_) + 2;
    }

    unsigned size_bin(unsigned size) const
    {
        return size / static_cast<unsigned>(size_bin_width_);
    }

    unsigned minimal_nodes_bin(const intset &nodes) const
    {
        if (minimal_node_bin_width_ <= 0)
            return 0;

        unsigned minimal_nodes = 0;
        for (const auto &u : nodes)
            if (!dfg_.pred(u).intersects(nodes))
                minimal_nodes++;
        return minimal_nodes / static_cast<unsigned>(minimal_node_bin_width_);
    }

    std::tuple<unsigned, unsigned, unsigned> bucket_key(const IOSubgraph &config) const
    {
        return std::make_tuple(
            size_bin(config.nodes().size()),
            bucket_by_num_inputs_ ? static_cast<unsigned>(config.num_in()) : 0U,
            minimal_nodes_bin(config.nodes()));
    }

    void maybe_emit(const intset &nodes)
    {
        if (samples_emitted_ >= max_samples_)
            return;

        IOSubgraph config(dfg_, intset(nodes));
        if (max_subgraph_size_ >= 0 &&
            config.nodes().size() > static_cast<unsigned>(max_subgraph_size_))
            return;
        if (config.num_in() > max_num_in_ || config.num_out() != 0 ||
            has_forbidden_inputs(dfg_, config))
            return;
        if (!is_weakly_connected_with_inputs(dfg_, config))
            return;
        if (!emitted_.insert(intset(config.nodes())).second)
            return;

        output_cb_(config);
        samples_emitted_++;
        sample_count_by_bucket_[bucket_key(config)]++;
    }

    void enqueue_if_new(SearchState state)
    {
        SearchStateKey key(intset(state.nodes), intset(state.frontier), intset(state.blocked));
        if (!visited_states_.insert(std::move(key)).second)
            return;
        agenda_.push_back(std::move(state));
    }

    std::vector<Candidate> build_candidates(const SearchState &state)
    {
        std::vector<Candidate> candidates;
        intset frontier_remaining(state.frontier);

        while (true) {
            int next = frontier_remaining.minimum();
            if (next == static_cast<unsigned>(-1))
                break;
            frontier_remaining.remove(next);

            intset blocked_next(state.blocked);
            blocked_next.add(next);
            blocked_next.add(dfg_.pred(next));
            blocked_next.add(dfg_.succ(next));

            intset seed(state.nodes | singleton_set(dfg_.num_nodes(), next));
            intset closed = closure_for(seed);
            if (closed.intersects(forbidden_))
                continue;

            intset added(closed);
            added.remove(state.nodes);
            int first_added = static_cast<int>(added.minimum());
            if (first_added == -1)
                continue;

            IOSubgraph config(dfg_, intset(closed));
            if (max_subgraph_size_ >= 0 &&
                config.nodes().size() > static_cast<unsigned>(max_subgraph_size_))
                continue;
            if (config.num_in() > max_num_in_ || config.num_out() != 0 ||
                has_forbidden_inputs(dfg_, config))
                continue;

            intset frontier_next(frontier_remaining);
            intset current_augmented = augmented_nodes(dfg_, config.nodes());
            for (int u = next + 1; u < dfg_.num_nodes(); u++) {
                if (!valid_[u] || blocked_next.contains(u) || frontier_next.contains(u))
                    continue;
                if (closures_[u].is_subset_of(config.nodes()))
                    continue;
                if (can_connect(u, config.nodes(), current_augmented))
                    frontier_next.add(u);
            }

            candidates.emplace_back(
                SearchState(intset(closed), std::move(frontier_next), std::move(blocked_next)),
                added.size(),
                bucket_key(config),
                sample_count_by_bucket_[bucket_key(config)],
                first_added);
        }

        return candidates;
    }

    std::vector<Candidate> select_candidates(std::vector<Candidate> candidates) const
    {
        std::unordered_map<
            std::tuple<unsigned, unsigned, unsigned>,
            std::size_t,
            BucketKeyHash>
            best_by_bin;
        std::vector<Candidate> clustered;
        clustered.reserve(candidates.size());

        for (auto &candidate : candidates) {
            auto it = best_by_bin.find(candidate.bucket_key);
            if (it == best_by_bin.end()) {
                best_by_bin.emplace(candidate.bucket_key, clustered.size());
                clustered.push_back(std::move(candidate));
                continue;
            }

            Candidate &current = clustered[it->second];
            if (candidate.current_bucket_count < current.current_bucket_count ||
                (candidate.current_bucket_count == current.current_bucket_count &&
                 candidate.delta_size > current.delta_size) ||
                (candidate.current_bucket_count == current.current_bucket_count &&
                 candidate.delta_size == current.delta_size &&
                 candidate.first_added < current.first_added)) {
                current = std::move(candidate);
            }
        }

        std::sort(
            clustered.begin(),
            clustered.end(),
            [](const Candidate &lhs, const Candidate &rhs) {
                if (lhs.current_bucket_count != rhs.current_bucket_count)
                    return lhs.current_bucket_count < rhs.current_bucket_count;
                if (lhs.delta_size != rhs.delta_size)
                    return lhs.delta_size > rhs.delta_size;
                if (lhs.state.nodes.size() != rhs.state.nodes.size())
                    return lhs.state.nodes.size() < rhs.state.nodes.size();
                return lhs.first_added < rhs.first_added;
            });

        if (clustered.size() > static_cast<std::size_t>(max_children_per_state_)) {
            clustered.erase(
                clustered.begin() + static_cast<std::ptrdiff_t>(max_children_per_state_),
                clustered.end());
        }
        return clustered;
    }

    void emit_thickened(const SearchState &state, int radius)
    {
        maybe_emit(state.nodes);
        if (radius <= 0 || samples_emitted_ >= max_samples_ ||
            (max_subgraph_size_ >= 0 &&
             state.nodes.size() >= static_cast<unsigned>(max_subgraph_size_)))
            return;

        auto candidates = select_candidates(build_candidates(state));
        for (const auto &candidate : candidates) {
            if (samples_emitted_ >= max_samples_)
                return;
            emit_thickened(candidate.state, radius - 1);
        }
    }

    void expand_with_contraction(SearchState state)
    {
        if (max_subgraph_size_ >= 0 &&
            state.nodes.size() >= static_cast<unsigned>(max_subgraph_size_))
            return;

        while (states_expanded_ < max_states_expanded_ &&
               samples_emitted_ < max_samples_) {
            states_expanded_++;

            auto candidates = select_candidates(build_candidates(state));
            if (candidates.empty())
                return;

            for (const auto &candidate : candidates) {
                if (samples_emitted_ >= max_samples_)
                    return;
                emit_thickened(candidate.state, thicken_radius_);
            }

            if (samples_emitted_ >= max_samples_)
                return;

            if (candidates.size() == 1) {
                state = std::move(candidates.front().state);
                continue;
            }

            for (auto &candidate : candidates)
                enqueue_if_new(std::move(candidate.state));
            return;
        }
    }

    const DFG &dfg_;
    int max_num_in_;
    int max_subgraph_size_;
    const std::function<void(const IOSubgraph &)> &output_cb_;
    const DFG *alternate_graph_;
    int max_states_expanded_;
    int max_samples_;
    int max_children_per_state_;
    int size_bin_width_;
    int thicken_radius_;
    bool bucket_by_num_inputs_;
    int minimal_node_bin_width_;
    intset forbidden_;
    std::vector<intset> closures_;
    std::vector<intset> augmented_closures_;
    std::vector<intset> body_neighbors_;
    std::vector<intset> input_neighbors_;
    std::vector<bool> valid_;
    std::unordered_map<intset, intset, IntsetHash> closure_cache_;
    std::unordered_set<intset, IntsetHash> emitted_;
    std::unordered_set<SearchStateKey, SearchStateHash> visited_states_;
    std::deque<SearchState> agenda_;
    std::unordered_map<std::tuple<unsigned, unsigned, unsigned>, unsigned, BucketKeyHash>
        sample_count_by_bucket_;
    int states_expanded_ = 0;
    int samples_emitted_ = 0;
};

void vs_sample_zero_output_connected_(
    const DFG &dfg,
    int max_num_in,
    int max_subgraph_size,
    const DFG *alternate_graph,
    const std::function<void(const IOSubgraph &)> &output_cb,
    int max_states_expanded,
    int max_samples,
    int max_children_per_state,
    int size_bin_width,
    int thicken_radius,
    bool bucket_by_num_inputs,
    int minimal_node_bin_width)
{
    SampledZeroOutputConnectedFinder(
        dfg,
        max_num_in,
        max_subgraph_size,
        output_cb,
        alternate_graph,
        max_states_expanded,
        max_samples,
        max_children_per_state,
        size_bin_width,
        thicken_radius,
        bucket_by_num_inputs,
        minimal_node_bin_width)
        .enumerate();
}

class ZeroOutputGrower {
public:
    ZeroOutputGrower(const DFG &dfg,
                     int max_num_in,
                     int max_subgraph_size,
                     const DFG *alternate_graph,
                     std::size_t initial_state_token,
                     const std::function<std::optional<std::size_t>(
                         const IOSubgraph &, std::size_t)> &visit_cb)
        : dfg_(dfg)
        , max_num_in_(max_num_in)
        , max_subgraph_size_(max_subgraph_size)
        , alternate_graph_(alternate_graph)
        , initial_state_token_(initial_state_token)
        , visit_cb_(visit_cb)
        , forbidden_(dfg.body_forbidden())
        , closures_(dfg.num_nodes(), intset(dfg.num_nodes()))
        , augmented_closures_(dfg.num_nodes(), intset(dfg.num_nodes()))
        , body_neighbors_(dfg.num_nodes(), intset(dfg.num_nodes()))
        , input_neighbors_(dfg.num_nodes(), intset(dfg.num_nodes()))
        , valid_(dfg.num_nodes(), false)
    {
        for (int u = 0; u < dfg_.num_nodes(); u++) {
            closures_[u] = closure_for(singleton_set(dfg_.num_nodes(), u));
            augmented_closures_[u] = augmented_nodes(dfg_, closures_[u]);
            intset inputs(augmented_closures_[u]);
            inputs.remove(closures_[u]);
            for (const auto &v : closures_[u]) {
                for (const auto &w : dfg_.in_edges(v))
                    body_neighbors_[u].add(w);
                for (const auto &w : dfg_.out_edges(v))
                    body_neighbors_[u].add(w);
            }
            for (const auto &v : inputs) {
                for (const auto &w : dfg_.in_edges(v))
                    input_neighbors_[u].add(w);
                for (const auto &w : dfg_.out_edges(v))
                    input_neighbors_[u].add(w);
            }
            valid_[u] = !closures_[u].intersects(forbidden_);
        }
    }

    void enumerate(const intset &seed)
    {
        intset canonical_seed = closure_for(seed);
        if (!(canonical_seed == seed))
            throw std::invalid_argument(
                "seed must already be a canonical dual-convex zero-output subgraph");
        if (!is_valid_state(seed))
            throw std::invalid_argument(
                "seed does not satisfy the zero-output growth constraints");

        std::vector<std::pair<intset, std::size_t>> stack;
        stack.emplace_back(seed, initial_state_token_);
        seen_.insert(intset(seed));

        while (!stack.empty()) {
            auto [current, state_token] = std::move(stack.back());
            stack.pop_back();

            IOSubgraph config(dfg_, intset(current));
            auto next_state_token = visit_cb_(config, state_token);
            if (!next_state_token.has_value())
                continue;

            intset current_augmented = augmented_nodes(dfg_, current);
            std::vector<std::pair<intset, std::size_t>> next_states;
            std::unordered_set<intset, IntsetHash> sibling_seen;

            for (int u = 0; u < dfg_.num_nodes(); u++) {
                if (!valid_[u])
                    continue;
                if (closures_[u].is_subset_of(current))
                    continue;
                if (!can_connect(u, current, current_augmented))
                    continue;

                intset next_state = closure_for(
                    current | singleton_set(dfg_.num_nodes(), u));
                if (next_state == current)
                    continue;
                if (!is_valid_state(next_state))
                    continue;
                if (!sibling_seen.insert(intset(next_state)).second)
                    continue;
                if (!seen_.insert(intset(next_state)).second)
                    continue;
                next_states.emplace_back(std::move(next_state), *next_state_token);
            }

            std::sort(
                next_states.begin(),
                next_states.end(),
                [](const auto &lhs, const auto &rhs) {
                    if (lhs.first.size() != rhs.first.size())
                        return lhs.first.size() > rhs.first.size();
                    return lhs.first.minimum() > rhs.first.minimum();
                });

            for (auto &next_state : next_states)
                stack.push_back(std::move(next_state));
        }
    }

private:
    const intset &closure_for(const intset &nodes)
    {
        auto it = closure_cache_.find(nodes);
        if (it != closure_cache_.end())
            return it->second;
        return closure_cache_
            .emplace(intset(nodes), zero_output_closure(dfg_, alternate_graph_, nodes))
            .first->second;
    }

    bool can_connect(int u,
                     const intset &current_nodes,
                     const intset &current_augmented) const
    {
        return augmented_closures_[u].intersects(current_augmented) ||
               body_neighbors_[u].intersects(current_augmented) ||
               input_neighbors_[u].intersects(current_nodes);
    }

    bool is_valid_state(const intset &nodes) const
    {
        if (nodes.intersects(forbidden_))
            return false;
        IOSubgraph config(dfg_, intset(nodes));
        if (max_subgraph_size_ >= 0 &&
            config.nodes().size() > static_cast<unsigned>(max_subgraph_size_))
            return false;
        if (config.num_in() > max_num_in_ || config.num_out() != 0 ||
            has_forbidden_inputs(dfg_, config))
            return false;
        return is_weakly_connected_with_inputs(dfg_, config);
    }

    const DFG &dfg_;
    int max_num_in_;
    int max_subgraph_size_;
    const DFG *alternate_graph_;
    std::size_t initial_state_token_;
    const std::function<std::optional<std::size_t>(const IOSubgraph &,
                                                   std::size_t)> &visit_cb_;
    intset forbidden_;
    std::vector<intset> closures_;
    std::vector<intset> augmented_closures_;
    std::vector<intset> body_neighbors_;
    std::vector<intset> input_neighbors_;
    std::vector<bool> valid_;
    std::unordered_map<intset, intset, IntsetHash> closure_cache_;
    std::unordered_set<intset, IntsetHash> seen_;
};

void vs_enumerate_zero_outputs_(const DFG &dfg,
                                int max_num_in,
                                int max_subgraph_size,
                                const DFG *alternate_graph,
                                const std::function<void(const IOSubgraph &)> &output_cb,
                                bool connected_only)
{
    if (connected_only && alternate_graph == nullptr) {
        ZeroOutputConnectedFinder(
            dfg, max_num_in, max_subgraph_size, output_cb).enumerate();
        return;
    }
    if (connected_only) {
        ZeroOutputConnectedFinder(
            dfg,
            max_num_in,
            max_subgraph_size,
            output_cb,
            alternate_graph).enumerate();
        return;
    }

    auto reversed = reverse_dfg(dfg);
    auto reversed_alternate =
        alternate_graph != nullptr ? reverse_dfg(*alternate_graph) : nullptr;
    vs_enumerate(
        *reversed,
        0,
        dfg.num_nodes(),
        max_subgraph_size,
        reversed_alternate.get(),
        [&dfg, max_num_in, max_subgraph_size, connected_only, &output_cb](const IOSubgraph &subgraph) {
            IOSubgraph original_subgraph(dfg);
            original_subgraph.set(subgraph.nodes());
            if ((max_subgraph_size < 0 ||
                 original_subgraph.nodes().size() <= static_cast<unsigned>(max_subgraph_size)) &&
                original_subgraph.num_out() == 0 &&
                original_subgraph.num_in() <= max_num_in &&
                !has_forbidden_inputs(dfg, original_subgraph) &&
                (!connected_only ||
                 is_weakly_connected_with_inputs(dfg, original_subgraph))) {
                output_cb(original_subgraph);
            }
        },
        false);
}

void vs_enumerate_(const DFG &dfg,
                   Subgraph &outputs,
                   int size,
                   int max_num_in,
                   int max_num_out,
                   int max_subgraph_size,
                   const DFG *alternate_graph,
                   const std::function<void(const IOSubgraph &)> &output_cb,
                   bool connected_only)
{
    if (max_subgraph_size >= 0 &&
        dual_closure(dfg, alternate_graph, outputs.nodes()).size() >
            static_cast<unsigned>(max_subgraph_size))
        return;

    if (size >= 1) {
        if (max_num_in == 0) {
            vs_enumerate_zero_inputs_(
                dfg, outputs, max_subgraph_size, alternate_graph, output_cb, connected_only);
        } else {
            VSFinder finder(
                dfg, outputs, alternate_graph, max_subgraph_size, connected_only);
            finder.visit(max_num_in, output_cb);
        }
    }
    if (size < max_num_out) {
        auto exclusion = config_exclusion(dfg, outputs.nodes());
        auto pred = outputs.pred();
        intset valid(dfg.num_nodes());
        for (const auto &u : exclusion) {
            if (!dfg.is_body_forbidden(u) &&
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
                              max_subgraph_size,
                              alternate_graph,
                              output_cb,
                              connected_only);
                outputs.remove(u);
            }
        }
    }
}

}

void vs_sample_zero_output_connected(
    const DFG &dfg,
    int max_num_in,
    int max_subgraph_size,
    const DFG *alternate_graph,
    const std::function<void(const IOSubgraph &)> &output_cb,
    int max_states_expanded,
    int max_samples,
    int max_children_per_state,
    int size_bin_width,
    int thicken_radius,
    bool bucket_by_num_inputs,
    int minimal_node_bin_width)
{
    vs_sample_zero_output_connected_(
        dfg,
        max_num_in,
        max_subgraph_size,
        alternate_graph,
        output_cb,
        max_states_expanded,
        max_samples,
        max_children_per_state,
        size_bin_width,
        thicken_radius,
        bucket_by_num_inputs,
        minimal_node_bin_width);
}

void vs_grow_zero_output_connected(
    const DFG &dfg,
    const intset &seed,
    int max_num_in,
    int max_subgraph_size,
    const DFG *alternate_graph,
    std::size_t initial_state_token,
    const std::function<std::optional<std::size_t>(const IOSubgraph &,
                                                   std::size_t)> &visit_cb)
{
    ZeroOutputGrower(
        dfg,
        max_num_in,
        max_subgraph_size,
        alternate_graph,
        initial_state_token,
        visit_cb)
        .enumerate(seed);
}

void vs_enumerate(const DFG &dfg,
                  int max_num_in,
                  int max_num_out,
                  int max_subgraph_size,
                  const DFG *alternate_graph,
                  const std::function<void(const IOSubgraph &)> &output_cb,
                  bool connected_only)
{
    if (max_num_out == 0) {
        vs_enumerate_zero_outputs_(
            dfg, max_num_in, max_subgraph_size, alternate_graph, output_cb, connected_only);
        return;
    }

    Subgraph outputs(dfg);
    vs_enumerate_(
        dfg,
        outputs,
        0,
        max_num_in,
        max_num_out,
        max_subgraph_size,
        alternate_graph,
        output_cb,
        connected_only);
}
