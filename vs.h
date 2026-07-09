#pragma once

#include "dfg.h"
#include <cstddef>
#include <optional>

void vs_enumerate(const DFG &dfg,
                  int max_num_in,
                  int max_num_out,
                  int max_subgraph_size,
                  const DFG *alternate_graph,
                  const std::function<void(const IOSubgraph &)> &output_cb,
                  bool connected_only = false,
                  bool broaden_output_seeds = true,
                  bool seed_sinks = false,
                  std::size_t max_work = 0,
                  bool *work_limit_hit = nullptr,
                  bool relax_output_seed_limit = false);

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
    int minimal_node_bin_width,
    std::size_t max_work = 0);

void vs_grow_zero_output_connected(
    const DFG &dfg,
    const intset &seed,
    int max_num_in,
    int max_subgraph_size,
    const DFG *alternate_graph,
    std::size_t initial_state_token,
    const std::function<std::optional<std::size_t>(const IOSubgraph &,
                                                   std::size_t)> &visit_cb);

void vs_sample_nonzero_output_connected(
    const DFG &dfg,
    int max_num_in,
    int max_num_out,
    int max_subgraph_size,
    const DFG *alternate_graph,
    const std::function<void(const IOSubgraph &)> &output_cb,
    int max_states_expanded,
    int max_samples,
    int max_children_per_state,
    int size_bin_width,
    int thicken_radius,
    bool bucket_by_num_inputs,
    bool bucket_by_num_outputs,
    int minimal_node_bin_width,
    int boundary_pair_samples,
    std::size_t max_work = 0);

void vs_grow_nonzero_output_connected(
    const DFG &dfg,
    const intset &seed,
    int max_num_in,
    int max_num_out,
    int max_subgraph_size,
    const DFG *alternate_graph,
    std::size_t initial_state_token,
    const std::function<std::optional<std::size_t>(const IOSubgraph &,
                                                   std::size_t)> &visit_cb);
