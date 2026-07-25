#pragma once

#include "cluster.h"
#include "dfg.h"
#include "intset.h"
#include <string>
#include <vector>

bool parse_integer(const std::string &str, int &v, int a, int b);
std::vector<std::string> split(const std::string &s, char c);
bool fp_eq(double x, double y, double eps);

#ifndef NO_JSON
#include <nlohmann/json.hpp>
void to_json(nlohmann::json &j, const SCluster &cluster);
void to_json(nlohmann::json &j, const IOSubgraph &config);
void to_json(nlohmann::json &j, const intset &s);
#endif
