#pragma once

#include "dfg.h"

void vs_enumerate(const DFG &dfg,
                  int max_num_in,
                  int max_num_out,
                  int max_subgraph_size,
                  const DFG *alternate_graph,
                  const std::function<void(const IOSubgraph &)> &output_cb,
                  bool connected_only = false);
