/**CFile****************************************************************

  FileName    [eSLIM.cpp]

  SystemName  [ABC: Logic synthesis and verification system.]

  PackageName [Using Exact Synthesis with the SAT-based Local Improvement Method (eSLIM).]

  Synopsis    [Interface to the eSLIM package.]

  Author      [Franz-Xaver Reichl]
  
  Affiliation [University of Freiburg]

  Date        [Ver. 1.0. Started - April 2026.]

  Revision    [$Id: eSLIM.cpp,v 1.00 2025/04/14 00:00:00 Exp $]

***********************************************************************/


#include "utils.hpp"
#include "eSLIMMan.hpp"
#include "relationGeneration.hpp"
#include "selectionStrategies.hpp"
#include "windowMan.hpp"

#include "misc/util/abc_namespaces.h"
#include "opt/mfs/mfs.h"
#include "base/main/main.h"

#include "eSLIM.h"
#include "eslimCirMan.hpp"
#include "synthesisEngines.hpp"
#include "selectionStrategies.hpp"

ABC_NAMESPACE_HEADER_START
  int Abc_NtkMfs( Abc_Ntk_t * pNtk, Mfs_Par_t * pPars );
ABC_NAMESPACE_HEADER_END

ABC_NAMESPACE_IMPL_START

static Gia_DeepSynObj_t eSLIM_ResolveDeepSynObj(const eSLIM_ParamStruct* params) {
  if (params->deepsyn_obj >= 0)
    return (Gia_DeepSynObj_t)params->deepsyn_obj;
  return params->synthesis_approach == 0 ? GIA_DEEPSYN_AREA : GIA_DEEPSYN_BALANCED;
}

eSLIM::eSLIMConfig getCfg(const eSLIM_ParamStruct* params) {
  eSLIM::eSLIMConfig config;
  config.apply_strash = params->apply_strash;
  config.fill_subcircuits = params->fill_subcircuits;
  config.fix_seed = params->fix_seed;
  config.trial_limit_active = params->trial_limit_active;
  config.timeout = params->timeout;
  config.iterations = params->iterations;
  config.subcircuit_max_size = params->subcircuit_max_size;
  config.additional_gates = params->additional_gates;
  config.strash_intervall = params->strash_intervall;
  config.nselection_trials = params->nselection_trials;
  config.seed = params->seed;
  config.verbosity_level = params->verbosity_level;
  config.expansion_probability = params->expansion_probability;
  config.approximate_relation = params->approximate_relation;
  config.relation_tfo_bound = params->relation_tfo_bound;
  config.generate_relation_with_tfi_limit = params->generate_relation_with_tfi_limit;
  config.relation_tfi_bound = params->relation_tfi_bound;
  config.nwindows = params->nWindows;
  config.window_size = params->window_size;

  config.aig = params->aig;
  config.gate_size = params->gate_size;
  config.deepsyn_before_frac = params->deepsyn_before_frac;
  config.deepsyn_after_frac = params->deepsyn_after_frac;
  config.deepsyn_obj = (int)eSLIM_ResolveDeepSynObj(params);

  if (params->use_taboo_list) {
    config.apply_strash = false;
  }

  if (params->pValidity != NULL) {
    // Global external don't-cares require the exact relation-generation path: the
    // approximate path cuts the cone before reaching the primary inputs, so a
    // PI-level validity constraint would have no effect there.
    if (config.approximate_relation) {
      std::cout << "Warning: global don't-cares (-G) force the exact relation "
                   "generation; ignoring the approximate relation options.\n";
      config.approximate_relation = false;
      config.generate_relation_with_tfi_limit = false;
    }
    config.validity_circuit = std::make_shared<const eSLIM::eSLIMCirMan>(params->pValidity);
  }

  return config;
}

void seteSLIMParams(eSLIM_ParamStruct* params) {

  params->fill_subcircuits = 0;
  params->apply_strash = 1;
  params->fix_seed = 0;
  params->trial_limit_active = 1;
  params->apply_inprocessing = 1;
  params->synthesis_approach = 0;
  params->seed = 0;
  params->verbosity_level = 1;
  params->use_taboo_list = 0;
  params->forward_search = 0;

  params->nWindows = 0;
  params->window_size = 500;

  params->criticial_path_selection_bias = 0;

  params->timeout = 1800;
  params->iterations = 0;
  params->subcircuit_max_size = 6;
  params->additional_gates = 0;
  params->strash_intervall = 100;
  params->nselection_trials = 100;
  params->nruns = 1;

  params->expansion_probability = 0.5;    
  params->approximate_relation = 0;
  params->relation_tfo_bound = 0;   
  params->generate_relation_with_tfi_limit = 0;
  params->relation_tfi_bound = 0;
  
  params->aig = 1;
  params->gate_size = 2;

  params->pValidity = NULL;
  params->assume_pi_order = 0;

  params->deepsyn_before_frac = 0.0;
  params->deepsyn_after_frac = -1.0;
  params->deepsyn_obj = -1;
}

namespace eSLIM {

  static const char* DeepSynObjName(int obj) {
    switch (obj) {
      case GIA_DEEPSYN_AREA:     return "area";
      case GIA_DEEPSYN_BALANCED: return "balanced";
      case GIA_DEEPSYN_DELAY:    return "delay";
      default:                   return "unknown";
    }
  }

  static void eSLIM_RunDeepSyn(eSLIMCirMan& es_man, int timeout_sec, int seed,
                               Gia_DeepSynObj_t obj, int verbosity) {
    Gia_Man_t* pGia = es_man.eSLIMCirManToGia();
    int fVerbose = verbosity > 1 ? 1 : 0;
    Gia_Man_t* pRes = (obj == GIA_DEEPSYN_DELAY)
      ? Gia_ManDeepSyn2(pGia, 1, ABC_INFINITY, timeout_sec, 0, seed, 0, 0, fVerbose)
      : Gia_ManDeepSyn (pGia, 1, ABC_INFINITY, timeout_sec, 0, seed, 0, 0, fVerbose, obj);
    if (pRes) {
      es_man = eSLIMCirMan(pRes);
      Gia_ManStop(pRes);
    }
    Gia_ManStop(pGia);
  }

  static void eSLIM_RunDeepSynStep(eSLIMCirMan& es_man, int timeout_sec, int seed,
                                   Gia_DeepSynObj_t obj, int verbosity,
                                   int& area_change, int& delay_change,
                                   const char* label) {
    int size_before = es_man.getNofGates();
    int delay_before = es_man.getDepth();
    eSLIM_RunDeepSyn(es_man, timeout_sec, seed, obj, verbosity);
    int size_after = es_man.getNofGates();
    int delay_after = es_man.getDepth();
    area_change += size_after - size_before;
    delay_change += delay_after - delay_before;
    if (verbosity > 0)
      std::cout << label << " -- size: " << size_after << " delay: " << delay_after << "\n";
  }

  static void printGateChange(const char* who, int delta) {
    if (delta <= 0)
      std::cout << "#Gates reduced by " << who << ": " << -delta << "\n";
    else
      std::cout << "#Gates introduced by " << who << ": " << delta << "\n";
  }

  static void printDelayChange(const char* who, int delta) {
    if (delta <= 0)
      std::cout << "Delay reduction " << who << ": " << -delta << "\n";
    else
      std::cout << "Delay increase " << who << ": " << delta << "\n";
  }

  class DeepsynInprocessor {
    public:
      DeepsynInprocessor(eSLIMConfig& config);
      void setTimeout(int timeout) {this->timeout = timeout;}
      void runInprocessing(eSLIMCirMan& es_man);
    private:
      eSLIMConfig& config;
      int timeout;
  };

  class MfsInprocessor {
    public:
      MfsInprocessor(eSLIMConfig& config) {}
      void runInprocessing(eSLIMCirMan& es_man);
  };

  class EmptyInprocessor {
    public:
      EmptyInprocessor(eSLIMConfig& config) {}
      void runInprocessing(eSLIMCirMan& es_man) {}
  };

  template <bool IncreaseSize>
  class DelayInprocessor {
    public:
      DelayInprocessor(eSLIMConfig& config);
      void setTimeout(int timeout) {this->timeout = timeout;}
      void runInprocessing(eSLIMCirMan& es_man);
    private:
      eSLIMConfig& config;
      int timeout;
  };

  class Resyn2Inprocessor {
    public:
      Resyn2Inprocessor(eSLIMConfig& config);
      void runInprocessing(eSLIMCirMan& es_man);
    private:
      // eSLIMConfig& config;
  };


  template <typename Approach, typename Inprocessor>
  class eSLIMRun {

    public:
      static Gia_Man_t* runeSLIM(Gia_Man_t* cir, const eSLIM_ParamStruct* params);
      static Abc_Ntk_t * runeSLIM(Abc_Ntk_t * cir, const eSLIM_ParamStruct* params);
      static Abc_Ntk_t * runeSLIMCells(Abc_Ntk_t * cir, const eSLIM_ParamStruct* params);

    private:
      eSLIMCirMan es_man;
      eSLIMConfig config;
      eSLIMLog log;
      Inprocessor inprocessor;

      int initial_area;
      int initial_delay;

      int area_change_eslim = 0;
      int area_change_inprocessing = 0;

      int delay_change_eslim = 0;
      int delay_change_inprocessing = 0;

      int area_change_pre_deepsyn = 0;
      int delay_change_pre_deepsyn = 0;
      int area_change_post_deepsyn = 0;
      int delay_change_post_deepsyn = 0;

      int pre_sec = 0;
      int post_sec = 0;
      int core_sec = 0;

      int nruns = 0;

      eSLIMRun(Gia_Man_t* cir, const eSLIM_ParamStruct* params);
      eSLIMRun(Abc_Ntk_t* cir, const eSLIM_ParamStruct* params, bool simplify);

      void setUpInprocessor();
      void runInprocessing();

      void printSettings();
      void printLog();

      void run();
  };


  template <typename Approach, typename Inprocessor>
  eSLIMRun<Approach, Inprocessor>::eSLIMRun(Abc_Ntk_t* cir, const eSLIM_ParamStruct* params, bool simplify_circuit)
                            : es_man(cir, simplify_circuit), config(getCfg(params)), log(params->subcircuit_max_size), inprocessor(config)  {
    nruns = params->nruns;
    config.aig = false;
    config.apply_strash = false;
  }

  template <typename Approach, typename Inprocessor>
  eSLIMRun<Approach, Inprocessor>::eSLIMRun(Gia_Man_t* cir, const eSLIM_ParamStruct* params)
                            : es_man(cir), config(getCfg(params)), log(params->subcircuit_max_size), inprocessor(config)  {
    nruns = params->nruns;
  }

  template <typename Approach, typename Inprocessor>
  Gia_Man_t* eSLIMRun<Approach, Inprocessor>::runeSLIM(Gia_Man_t* cir, const eSLIM_ParamStruct* params) {

    eSLIMRun<Approach, Inprocessor> eslim_run(cir, params);
    // It seems like the variables are freed by abc during preprocessing. Thus,we copy them
    char* name = Abc_UtilStrsav( cir->pName );
    char* spec = Abc_UtilStrsav( cir->pSpec );
    eslim_run.run();
    Gia_Man_t* gia_res = eslim_run.es_man.eSLIMCirManToGia();
    gia_res->pName = name;
    gia_res->pSpec = spec;
    return gia_res;
  }

  template <typename Approach, typename Inprocessor>
  Abc_Ntk_t* eSLIMRun<Approach, Inprocessor>::runeSLIM(Abc_Ntk_t* cir, const eSLIM_ParamStruct* params) {
    bool simplify_circuit = true;
    eSLIMRun<Approach, Inprocessor> eslim_run(cir, params, simplify_circuit);
    eslim_run.config.aig = false;
    eslim_run.config.apply_strash = false;
    eslim_run.run();
    Abc_Ntk_t* ntk_res = eslim_run.es_man.eSLIMCirManToNtk();
    ntk_res->pName = Extra_UtilStrsav(cir->pName);
    ntk_res->pSpec = Extra_UtilStrsav(cir->pSpec);
    return ntk_res;
  }

  template <typename Approach, typename Inprocessor>
  Abc_Ntk_t * eSLIMRun<Approach, Inprocessor>::runeSLIMCells(Abc_Ntk_t * cir, const eSLIM_ParamStruct* params) {
    bool simplify_circuit = false;
    eSLIMRun<Approach, Inprocessor> eslim_run(cir, params, simplify_circuit);
    eslim_run.config.aig = false;
    eslim_run.config.apply_strash = false;
    eslim_run.run();
    Abc_Ntk_t* ntk_res = eslim_run.es_man.eSLIMCirManToMappedNtk();
    if (!ntk_res) {
      return ntk_res;
    }
    ntk_res->pName = Extra_UtilStrsav(cir->pName);
    ntk_res->pSpec = Extra_UtilStrsav(cir->pSpec);
    return ntk_res;
  }

  template <typename Approach, typename Inprocessor>
  void eSLIMRun<Approach, Inprocessor>::run() {
    unsigned int total = config.timeout;
    pre_sec = (int)(total * config.deepsyn_before_frac);
    if (config.deepsyn_before_frac > 0.0 && pre_sec == 0)
      pre_sec = 1;

    double post_frac = 0.0;
    if (config.deepsyn_after_frac >= 0.0)
      post_frac = config.deepsyn_after_frac;
    else {
      if constexpr ( std::is_same_v<DeepsynInprocessor, Inprocessor> )
        post_frac = 0.1;
    }

    post_sec = (int)(total * post_frac);
    if (post_frac > 0.0 && post_sec == 0)
      post_sec = 1;

    core_sec = (int)total - pre_sec - post_sec;
    if (pre_sec + post_sec > (int)(total * 0.5)) {
      std::cout << "Warning: pre+post DeepSyn uses more than 50% of -T ("
                << pre_sec << "s + " << post_sec << "s of " << total << "s).\n";
    }
    if (core_sec < 1) {
      std::cout << "Warning: SAT core timeout would be " << core_sec
                << "s; clamping to 1s.\n";
      core_sec = 1;
    }
    config.timeout = (unsigned int)core_sec;

    if constexpr ( std::is_same_v<DeepsynInprocessor, Inprocessor> ) {
      inprocessor.setTimeout(post_sec);
    } else if constexpr ( std::is_same_v<DelayInprocessor<true>, Inprocessor> || std::is_same_v<DelayInprocessor<false>, Inprocessor> ) {
      int time_out_inprocessing = (int)(config.timeout * 0.02);
      config.timeout -= time_out_inprocessing;
      inprocessor.setTimeout(time_out_inprocessing);
    }

    initial_area = es_man.getNofGates();
    initial_delay = es_man.getDepth();
    printSettings();

    Gia_DeepSynObj_t obj = (Gia_DeepSynObj_t)config.deepsyn_obj;
    if (pre_sec > 0 && config.aig) {
      eSLIM_RunDeepSynStep(es_man, pre_sec, config.seed, obj, config.verbosity_level,
                           area_change_pre_deepsyn, delay_change_pre_deepsyn, "pre-DeepSyn");
    }

    const bool explicit_post = config.deepsyn_after_frac >= 0.0 && post_sec > 0 && config.aig;

    for (int i = 0; i < nruns; i++) {

      int size_iteration_start = es_man.getNofGates();
      int delay_iteration_start = es_man.getDepth();
      if (config.verbosity_level > 0) {
        std::cout << "Start eslim run " << i + 1 << "\n";
      }
      Approach::applyeSLIM(es_man, config, log);
      int size_eslim = es_man.getNofGates();
      int delay_eslim = es_man.getDepth();
      area_change_eslim += size_eslim - size_iteration_start;
      delay_change_eslim += delay_eslim - delay_iteration_start;
      if (config.verbosity_level > 0) {
        std::cout << "eslim -- size: " << size_eslim << " delay: " << delay_eslim << "\n";
      }
      runInprocessing();
      if constexpr ( !std::is_same_v<EmptyInprocessor, Inprocessor> ) {
        int size_inprocessing = es_man.getNofGates();
        int delay_inprocessing = es_man.getDepth();
        area_change_inprocessing += size_inprocessing - size_eslim;
        delay_change_inprocessing += delay_inprocessing - delay_eslim;
        if (config.verbosity_level > 0) {
          std::cout << "inprocessing -- size: " << size_inprocessing << " delay: " << delay_inprocessing << "\n";
        }
      }
      if (explicit_post) {
        eSLIM_RunDeepSynStep(es_man, post_sec, config.seed + i, obj, config.verbosity_level,
                             area_change_post_deepsyn, delay_change_post_deepsyn, "post-DeepSyn");
      }
      if (config.fix_seed) {
        config.seed++;
      }
    }
    printLog();
  }

  template <typename Approach, typename Inprocessor>
  void eSLIMRun<Approach, Inprocessor>::printSettings() {
    std::cout << "Apply eSLIM (timeout: " << config.timeout << ") ";
    std::cout << nruns << " times.\n";
    if (pre_sec > 0 || config.deepsyn_after_frac >= 0.0) {
      std::cout << "DeepSyn budget: pre " << pre_sec << "s, core " << core_sec
                << "s, post " << post_sec << "s, objective "
                << DeepSynObjName(config.deepsyn_obj) << "\n";
    }
    if constexpr ( !std::is_same_v<EmptyInprocessor, Inprocessor> ) {
      std::cout << "Apply inprocessing\n";
    }
    if (config.iterations > 0) {
      std::cout << "Stop eSLIM runs after " << config.iterations << " iterations.\n";
    }
    std::cout << "Consider subcircuits with up to " << config.subcircuit_max_size << " gates.\n";
    printf("When expanding subcircuits, select gates with a probability of %.2f %%.\n", 100 * config.expansion_probability);
  }

  template <typename Approach, typename Inprocessor>
  void eSLIMRun<Approach, Inprocessor>::printLog() {
    if (config.verbosity_level > 0) {
      int size = es_man.getNofGates();
      int delay = es_man.getDepth();
      int total_area_change = area_change_eslim + area_change_inprocessing
                            + area_change_pre_deepsyn + area_change_post_deepsyn;
      int total_delay_change = delay_change_eslim + delay_change_inprocessing
                             + delay_change_pre_deepsyn + delay_change_post_deepsyn;
      std::cout << "Final size: " << size << " change: " << total_area_change << "\n";
      std::cout << "Final depth: " << delay << " change: " << total_delay_change << "\n";

      const bool log_deepsyn = pre_sec > 0 || (config.deepsyn_after_frac >= 0.0 && post_sec > 0);
      if (pre_sec > 0) {
        printGateChange("pre-DeepSyn", area_change_pre_deepsyn);
        printDelayChange("pre-DeepSyn", delay_change_pre_deepsyn);
      }
      if constexpr ( !std::is_same_v<EmptyInprocessor, Inprocessor> ) {
        printGateChange("eSLIM", area_change_eslim);
        printGateChange("inprocessing", area_change_inprocessing);
        printDelayChange("eSLIM", delay_change_eslim);
        printDelayChange("inprocessing", delay_change_inprocessing);
      } else if (log_deepsyn) {
        printGateChange("eSLIM", area_change_eslim);
        printDelayChange("eSLIM", delay_change_eslim);
      }
      if (config.deepsyn_after_frac >= 0.0 && post_sec > 0) {
        printGateChange("post-DeepSyn", area_change_post_deepsyn);
        printDelayChange("post-DeepSyn", delay_change_post_deepsyn);
      }
    }
    if (config.verbosity_level > 1) {
      std::cout << "Total #iterations: " << log.iteration_count << "\n";
      std::cout << "Total relation generation time (s): " << log.relation_generation_time << "\n";
      std::cout << "Total synthesis time (s): " << log.synthesis_time << "\n";
      std::cout << "#Iterations with forbidden pairs: " << log.subcircuits_with_forbidden_pairs << "\n";
      printf("Relation generation: #SAT-calls: %lu, Total SAT-time: %.2f sec, Max SAT-time: %.4f sec, Avg. SAT-time: %.4f sec\n",  
            log.nof_sat_calls_relation_generation, log.cummulative_sat_runtime_relation_generation, log.max_sat_runtime_relation_generation, 
            log.cummulative_sat_runtime_relation_generation/log.nof_sat_calls_relation_generation);
      printf("Synthesis: #SAT-calls: %lu, Total SAT-time: %.2f sec, Max SAT-time: %.4f sec, Avg. SAT-time: %.4f sec\n",  
            log.nof_sat_calls_synthesis, log.cummulative_sat_runtime_synthesis / 1000, log.max_sat_runtime_synthesis / 1000,
            log.cummulative_sat_runtime_synthesis / (log.nof_sat_calls_synthesis*1000));
    }
    if (config.verbosity_level > 2) {
      for (int i = 2; i < log.nof_analyzed_circuits_per_size.size(); i++) {
        int replaced = log.nof_replaced_circuits_per_size.size() > i ? log.nof_replaced_circuits_per_size[i] : 0;
        int reduced = log.nof_reduced_circuits_per_size.size() > i ? log.nof_reduced_circuits_per_size[i] : 0;
        std::cout << "#gates: " << i << " - #analysed: " << log.nof_analyzed_circuits_per_size[i] << " - #replaced: " << replaced << " - #reduced: " << reduced;
        std::cout << " - avg. relation time: ";
        if (log.nof_relation_generations_per_size[i] == 0) {
          std::cout << "-";
        } else {
          printf("%.2f sec",  static_cast<double>(log.cummulative_relation_generation_times_per_size[i]) / (log.nof_relation_generations_per_size[i]));
        }
        std::cout << "\n";
      }
      for (int i = 0; i < log.nof_sat_calls_per_size.size(); i++) {
        std::cout << "#gates: " << i << " - avg. sat time: ";
        if (log.nof_sat_calls_per_size[i] == 0) {
          std::cout << "-";
        } else {
          printf("%.2f sec",  static_cast<double>(log.cummulative_sat_runtimes_per_size[i]) / (1000 * log.nof_sat_calls_per_size[i]));
        }
        std::cout << " / avg. unsat time: ";
        if (log.nof_unsat_calls_per_size[i] == 0) {
          std::cout << "-";
        } else {
          printf("%.2f sec",  static_cast<double>(log.cummulative_unsat_runtimes_per_size[i]) / (1000 * log.nof_unsat_calls_per_size[i]));
        }
        std::cout << "\n";
      }
    }
  }

  template <typename Approach, typename Inprocessor>
  void eSLIMRun<Approach, Inprocessor>::runInprocessing() {
    inprocessor.runInprocessing(es_man);
  }

  template <typename Approach, typename Inprocessor>
  void setUpInprocessor();

  DeepsynInprocessor::DeepsynInprocessor(eSLIMConfig& config)
                    : config(config), timeout(0) {
  }

  void DeepsynInprocessor::runInprocessing(eSLIMCirMan& es_man) {
    eSLIM_RunDeepSyn(es_man, timeout, config.seed, (Gia_DeepSynObj_t)config.deepsyn_obj,
                     config.verbosity_level);
  }

  void MfsInprocessor::runInprocessing(eSLIMCirMan& es_man) {
    Abc_Ntk_t* pNtk = es_man.eSLIMCirManToNtk();
    int nnodes = Abc_NtkNodeNum(pNtk);
    Mfs_Par_t Pars, * pPars = &Pars;
    Abc_NtkMfsParsDefault( pPars );
    if ( Abc_NtkMfs( pNtk, pPars ) ) {
      Abc_NtkToSop( pNtk, -1, ABC_INFINITY );
      if (Abc_NtkNodeNum(pNtk) <= nnodes) {
        es_man = eSLIMCirMan(pNtk, true);
      }
    }
    Abc_NtkDelete(pNtk);
  }

  template <bool IncreaseSize>
  DelayInprocessor<IncreaseSize>::DelayInprocessor(eSLIMConfig& config)
                                : config(config) {
  }

  template <bool IncreaseSize>
  void DelayInprocessor<IncreaseSize>::runInprocessing(eSLIMCirMan& es_man) {
    abctime clkStart    = Abc_Clock();
    abctime nTimeToStop = clkStart + timeout * CLOCKS_PER_SEC;
    Gia_Man_t* pGia = es_man.eSLIMCirManToGia();
    int nand = Gia_ManAndNum(pGia);
    int nlevel = Gia_ManLevelNum(pGia);
    char * resyn2 = "balance; rewrite; rewrite -z; balance; rewrite -z; balance";
    char Command[2000];
    sprintf( Command, "strash; if -g -K 6; %s; if -K 6", resyn2 );
    bool reset_batch_mode = false ;
    if ( !Abc_FrameIsBatchMode() ) {
      reset_batch_mode = true;
      Abc_FrameSetBatchMode( 1 );
    }
    Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), pGia );
    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), "&put") ) {
      return;
    }
    while (Abc_Clock() <= nTimeToStop) {
      if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), Command) ) {
        Abc_Print( 1, "Something did not work out with the command \"%s\".\n", Command );
        return;
      }
    }
    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), "&get") ) {
      return;
    }
    if (reset_batch_mode) {
      Abc_FrameSetBatchMode( 0 );
    }
    Gia_Man_t* tmp = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
    if constexpr (!IncreaseSize) {
      if (Gia_ManAndNum(tmp) > nand) {
        return;
      }
    }
    if (Gia_ManLevelNum(tmp) <= nlevel) {
      es_man = eSLIMCirMan(tmp);
    }
  }

  Resyn2Inprocessor::Resyn2Inprocessor(eSLIMConfig& config)
                    // : config(config) 
                    {
  }

  void Resyn2Inprocessor::runInprocessing(eSLIMCirMan& es_man) {
    Gia_Man_t* pGia = es_man.eSLIMCirManToGia();
    int nand = Gia_ManAndNum(pGia);
    int nlevel = Gia_ManLevelNum(pGia);
    char * resyn2 = "balance; rewrite; rewrite -z; balance; rewrite -z; balance";
    bool reset_batch_mode = false ;
    if ( !Abc_FrameIsBatchMode() ) {
      reset_batch_mode = true;
      Abc_FrameSetBatchMode( 1 );
    }
    Abc_FrameUpdateGia( Abc_FrameGetGlobalFrame(), pGia );
    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), "&put") ) {
      return;
    }
    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), resyn2) ) {
      Abc_Print( 1, "Something did not work out with the command \"%s\".\n", resyn2 );
      return;
    }
    if ( Cmd_CommandExecute(Abc_FrameGetGlobalFrame(), "&get") ) {
      return;
    }
    if (reset_batch_mode) {
      Abc_FrameSetBatchMode( 0 );
    }
    Gia_Man_t* tmp = Abc_FrameReadGia(Abc_FrameGetGlobalFrame());
    if (Gia_ManAndNum(tmp) <= nand && Gia_ManLevelNum(tmp) <= nlevel) {
      es_man = eSLIMCirMan(tmp);
    }
  }



  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Approach>
  Circuitrepresentation* runeSLIM(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
    return eSLIMRun<Approach, Inprocessor>::runeSLIM(cir, params); 
  }

  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator, typename SearchDirection, typename BiasSelector, typename RootSelector>
  Circuitrepresentation* toggleWindowing(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
    if (params->nWindows > 0) {
      return runeSLIM<Circuitrepresentation, Inprocessor, Minimizer, WindowMan<Minimizer, RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector>>>(cir, params);
    } else {
      return runeSLIM<Circuitrepresentation, Inprocessor, Minimizer, eSLIM_Man<Minimizer, RandomizedBFSSelection<Validator, RootSelector, SearchDirection, BiasSelector>>>(cir, params);
    }
  }


  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator, typename SearchDirection, typename BiasSelector>
  Circuitrepresentation* setTabooApproach(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
    if (params->use_taboo_list) {
      return toggleWindowing<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, BiasSelector, TabooRootSelector>(cir, params);
    } else {
      return toggleWindowing<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, BiasSelector, BaseRootSelector>(cir, params);
    }
  }

  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator, typename SearchDirection>
  Circuitrepresentation* setBiasApproach(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
    if (params->criticial_path_selection_bias) {
      return toggleWindowing<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, CriticalPathBiasSelector, CriticalPathSelector>(cir, params);
    } else {
      return setTabooApproach<Circuitrepresentation, Inprocessor, Minimizer, Validator, SearchDirection, NoBiasSelector>(cir, params);
    }
  }



  template <typename Circuitrepresentation, typename Inprocessor, typename Minimizer, typename Validator>
  Circuitrepresentation* setSearchDirection(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
    if (params->forward_search) {
      return setBiasApproach<Circuitrepresentation, Inprocessor, Minimizer, Validator, ForwardSearch>(cir, params);
    } else {
      return setBiasApproach<Circuitrepresentation, Inprocessor, Minimizer, Validator, BackwardSearch>(cir, params);
    }
  }

  template <typename Circuitrepresentation>  
  Circuitrepresentation* setMinimizer(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
    switch (params->synthesis_approach) {
      case 0:
        if (params->apply_inprocessing) {
          if constexpr ( std::is_same_v<Gia_Man_t, Circuitrepresentation> ) {
            if (params->deepsyn_after_frac < 0)
              return setSearchDirection<Circuitrepresentation, DeepsynInprocessor, AreaMinimizer, SubcircuitValidator>(cir, params);
            return setSearchDirection<Circuitrepresentation, EmptyInprocessor, AreaMinimizer, SubcircuitValidator>(cir, params);
          } else {
            return setSearchDirection<Circuitrepresentation, MfsInprocessor, AreaMinimizer, SubcircuitValidator>(cir, params);
          }
        }
        return setSearchDirection<Circuitrepresentation, EmptyInprocessor, AreaMinimizer, SubcircuitValidator>(cir, params);
      case 1:
        if constexpr ( std::is_same_v<Gia_Man_t, Circuitrepresentation> ) {
          if (params->apply_inprocessing) {
            return setSearchDirection<Circuitrepresentation, Resyn2Inprocessor, AreaDelayConstraintMinimizer, SubcircuitNoFBValidator>(cir, params);
          } 
        }
        return setSearchDirection<Circuitrepresentation, EmptyInprocessor, AreaDelayConstraintMinimizer, SubcircuitNoFBValidator>(cir, params);
      case 2:
        if constexpr ( std::is_same_v<Gia_Man_t, Circuitrepresentation> ) {
          if (params->apply_inprocessing) {
            return setSearchDirection<Circuitrepresentation, DelayInprocessor<false>, AreaDelayMinimizer, SubcircuitNoFBValidator>(cir, params);
          } 
        }
        return setSearchDirection<Circuitrepresentation, EmptyInprocessor, AreaDelayMinimizer, SubcircuitNoFBValidator>(cir, params);
      case 3:
        if constexpr ( std::is_same_v<Gia_Man_t, Circuitrepresentation> ) {
          if (params->apply_inprocessing) {
            return setSearchDirection<Circuitrepresentation, DelayInprocessor<false>, DelayMinimizer, SubcircuitNoFBValidator>(cir, params);
          } 
        }
        return setSearchDirection<Circuitrepresentation, EmptyInprocessor, DelayMinimizer, SubcircuitNoFBValidator>(cir, params);
      default:
        assert(false);
        return NULL;
    }
  }
}

template <typename Circuitrepresentation> 
Circuitrepresentation* runeSLIM(Circuitrepresentation * cir, const eSLIM_ParamStruct* params) {
  // Windowing does currently not support Deleyconstraints/Delayoptimisation
  if (params->nWindows && params->synthesis_approach != 0) {
    return NULL;
  }
  return eSLIM::setMinimizer(cir, params);
}


Gia_Man_t* applyeSLIM(Gia_Man_t * pGia, const eSLIM_ParamStruct* params) {
  if (Gia_ManHasDangling(pGia)) {
    std::cout << "Warning: Circuit must not contain dangling nodes.\n";
    return pGia;
  }
  return runeSLIM(pGia, params);
}

Abc_Ntk_t* applyelSLIM(Abc_Ntk_t * ntk, const eSLIM_ParamStruct* params) {
  return runeSLIM(ntk, params);
}




ABC_NAMESPACE_IMPL_END
