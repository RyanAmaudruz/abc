/**CFile****************************************************************

  FileName    [subcircuit.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Subcircuit representation]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/

#include <algorithm>
#include <set>
#include <iostream>
#include <fstream>

#include "subcircuit.hpp"


ABC_NAMESPACE_IMPL_START
namespace eSLIM {

  Subcircuit Subcircuit::getSubcircuit(eSLIMCirMan& es_man, const std::set<int>& nodes) {
    Subcircuit scir = getSubcircuitBare(es_man, nodes.begin(), nodes.end());
    es_man.markCones(scir.nodes);
    scir.setForbiddenPairs(es_man);
    return scir;
  }

  Subcircuit Subcircuit::getEmptySubcircuit() {
    Subcircuit scir;
    return scir;
  }



  void Subcircuit::setIO(eSLIMCirMan& es_man) {
    std::set<int> input_set;
    std::set<int> output_set;
    for (int n : nodes) {
      const auto& obj = es_man.getObj(n);
      for (const auto& f : obj.fanins) {
        if (!es_man.inSubcircuit(*f) && !es_man.isConst(*f)) {
          input_set.insert(f->node_id);
        }
      }
      for (const auto& f : obj.fanouts) {
        if (!es_man.inSubcircuit(*f)) {
          output_set.insert(obj.node_id);
        }
      }
    }
    inputs.insert(inputs.end(), input_set.begin(), input_set.end());
    outputs.insert(outputs.end(), output_set.begin(), output_set.end());
  }

  void Subcircuit::setForbiddenPairs(const eSLIMCirMan& es_man) {
    std::unordered_set<int> seen;
    for (int inp : inputs) {
      getForbiddenPairsRec(inp, seen, es_man.getObj(inp), es_man);
      seen.clear();
    }
  }

  void Subcircuit::getForbiddenPairsRec(int inp, std::unordered_set<int>& seen, const eSLIMCirObj& obj, const eSLIMCirMan& es_man) {
    if (seen.find(obj.node_id) != seen.end()) {
      return;
    }
    seen.insert(obj.node_id);
    for (const auto& f : obj.fanins) {
      if (es_man.inSubcircuit(*f)) {
        forbidden_pairs[f->node_id].emplace(inp);
      } else if (es_man.inTFI(*f) && es_man.inTFO(*f)) {
        getForbiddenPairsRec(inp, seen, *f, es_man);
      }
    }
  }

  int Subcircuit::setupTimings(eSLIMCirMan& es_man) {
    // es_man.setupTimings();
    for (int in : inputs) {
      arrival_times.push_back(es_man.getObj(in).depth);
    }
    int max_crossing_path = 0;
    for (int out : outputs) {
      remaining_times.push_back(es_man.getObj(out).remaining_time); 
      max_crossing_path = std::max(max_crossing_path, es_man.getObj(out).remaining_time + es_man.getObj(out).depth);
    }
    // #region agent log
    {
      std::ofstream lf("/home/ramaudruz/Projects/abc/.cursor/debug-ded95c.log", std::ios::app);
      lf << "{\"sessionId\":\"ded95c\",\"hypothesisId\":\"B-C\",\"location\":\"subcircuit.cpp:setupTimings\",\"message\":\"setupTimings\",\"data\":{"
         << "\"max_crossing_path\":" << max_crossing_path
         << ",\"n_inputs\":" << inputs.size()
         << ",\"n_outputs\":" << outputs.size()
         << ",\"n_nodes\":" << nodes.size()
         << ",\"circuit_depth\":" << es_man.getDepth();
      lf << ",\"out_depth_rem\":\"";
      for (size_t i = 0; i < outputs.size(); i++) {
        if (i) lf << ";";
        const auto& o = es_man.getObj(outputs[i]);
        lf << o.depth << "+" << o.remaining_time << "=" << (o.depth + o.remaining_time);
      }
      lf << "\",\"in_arrivals\":\"";
      for (size_t i = 0; i < inputs.size(); i++) {
        if (i) lf << ",";
        lf << es_man.getObj(inputs[i]).depth;
      }
      // Check if each output depth is representable as arrival+d for d in 0..n_nodes
      bool all_repr = true;
      for (int out : outputs) {
        int od = es_man.getObj(out).depth;
        bool repr = false;
        for (int in : inputs) {
          int d = od - es_man.getObj(in).depth;
          if (d >= 0 && d <= (int)nodes.size()) { repr = true; break; }
        }
        // also allow const path: depth from 0
        if (od >= 0 && od <= (int)nodes.size()) repr = true;
        if (!repr) all_repr = false;
      }
      lf << "\",\"all_out_depth_repr\":" << (all_repr ? "true" : "false");
      lf << "},\"timestamp\":0}\n";
      lf.close();
    }
    // #endregion
    return max_crossing_path;
  }

  void Subcircuit::print() const {
    std::cout << "Inputs:";
    for (int i : inputs) {
      std::cout << " " << i;
    }
    std::cout << "\nOutputs:";
    for (int o : outputs) {
      std::cout << " " << o;
    }
    std::cout << "\nArrival times:";
    for (int ar : arrival_times) {
      std::cout << " " << ar;
    }
    std::cout << "\nRemaining times:";
    for (int re : remaining_times) {
      std::cout << " " << re;
    }
    std::cout << "\nNodes:";
    for (int n : nodes) {
      std::cout << " " << n;
    }
    std::cout << "\nForbidden pairs:";
    for (const auto & [out,inps] : forbidden_pairs) {
      std::cout << "\n" << out << " :";
      for (int inp : inps) {
        std::cout << " " << inp;
      }
    }
    std::cout << "\n";
  }

}
ABC_NAMESPACE_IMPL_END