#pragma once

#include "dfg.h"

void vs_enumerate(const DFG &dfg,
                  int max_num_in,
                  int max_num_out,
                  int max_subgraph_size,
                  const DFG *alternate_graph,
                  const std::function<void(const IOSubgraph &)> &output_cb,
                  bool connected_only = false);

void vs_sample_zero_output_connected(
    const DFG &dfg,
    int max_num_in,
    int max_subgraph_size,
    const DFG *alternate_graph,
    const std::function<void(const IOSubgraph &)> &output_cb,
    int max_states_expanded,
    int max_samples,
    int max_children_per_state,
    int size_bin_width);
