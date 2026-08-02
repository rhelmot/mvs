#pragma once

#include "dfg.h"

void vs_enumerate(const DFG &dfg,
                  int max_num_in,
                  int max_num_out,
                  const std::function<void(const IOSubgraph &, const std::vector<std::vector<int>> &)> &output_cb);
