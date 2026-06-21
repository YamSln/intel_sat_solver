#include <utility>
#include "ToporIpamir.h"
#include "Topor.hpp"
#include <vector>
#include <string>
#include <unordered_map>
#include <cstdint>
#include <cmath>
#include "algorithms/Alg_nuwls.h"
#include "algorithms/LSU.hpp"
#include "algorithms/MrsBeaver.hpp"

using namespace std;

namespace Topor
{
    class CToporIpamirWrapper : public CTopor<>
    {
    public:
        void AddHard(int lit_or_zero)
        {
            m_Result.valid = false;

            if (lit_or_zero == 0)
            {
                if (!m_CurrHardCls.empty())
                {
                    AddClause(m_CurrHardCls);
                    m_AllHardClauses.push_back(m_CurrHardCls); // keep for post-solvers
                    m_CurrHardCls.clear();
                }
            }
            else
            {
                m_CurrHardCls.emplace_back(lit_or_zero);
                const int v = lit_or_zero > 0 ? lit_or_zero : -lit_or_zero;
                if (v > m_MaxVarSeen) m_MaxVarSeen = v;
            }
        }

        void AddSoftLit(int lit, uint64_t weight)
        {
            m_Result.valid = false;

            m_SoftLit2Weight[lit] = weight;

            const int v = lit > 0 ? lit : -lit;
            if (v > m_MaxVarSeen) m_MaxVarSeen = v;

            CreateInternalLit(v);
            FixPolarity(-lit, false);
        }

        void Assume(int lit)
        {
            m_Result.valid = false;

            const int v = lit > 0 ? lit : -lit;
            if (v > m_MaxVarSeen) m_MaxVarSeen = v;

            if (m_Assump2Ind.find(lit) == m_Assump2Ind.end())
            {
                m_Assump2Ind.insert(make_pair(lit, m_CurrAssumps.size()));
                m_CurrAssumps.push_back(lit);
            }
        }

        int Solve()
        {
            const vector<int> assumpsForPost = m_CurrAssumps;

            TToporReturnVal trv = CTopor::Solve(m_CurrAssumps);

            m_Result = TSolverResult();

            int retVal = 0;

            if (trv == Topor::TToporReturnVal::RET_SAT)
            {
                CaptureToporAssignment();
                ComputeObjFromAssignment();


                RunNuwlsPostSolve(assumpsForPost);
                RunMrsBeaverPostSolve(assumpsForPost);

                  

                if (!m_SoftLit2Weight.empty() && m_Result.cost > 0)
                {
                    lsu::TLinearSUResult lsuResult = RunLsuOptimization(assumpsForPost, m_Result.cost);

                    if (lsuResult.LastSolveRet == Topor::TToporReturnVal::RET_SAT)
                    {
                        if (lsuResult.BestCost < m_Result.cost)
                        {
                            m_Result.assignment = lsuResult.BestModel01;
                            m_Result.cost = lsuResult.BestCost;
                            m_Result.valid = true;
                        }
                    }
                    else if (lsuResult.LastSolveRet == Topor::TToporReturnVal::RET_UNSAT)
                    {
                       
                        if (lsuResult.BestCost < m_Result.cost)
                        {
                            m_Result.assignment = lsuResult.BestModel01;
                            m_Result.cost = lsuResult.BestCost;
                            m_Result.valid = true;
                        }

                        m_Result.is_optimal = true;
                        retVal = 30;
                    }
                }

                if (retVal != 20)
                {
                    m_Result.is_optimal = (m_Result.cost == 0);
                    retVal = m_Result.is_optimal ? 30 : 10;
                }
            }
            else if (trv == Topor::TToporReturnVal::RET_UNSAT)
            {
                retVal = 20;
            }
            else
            {
                retVal = 0;
            }

            m_PrevAssump2Ind = move(m_Assump2Ind);
            m_Assump2Ind.clear();
            m_CurrAssumps.clear();

            return retVal;
        }

        uint64_t ValObj() const
        {
            return m_Result.cost;
        }

        int ValLit(int lit)
        {
            if (!m_Result.valid)
            {
                return 0;
            }

            const int v = lit > 0 ? lit : -lit;
            if (v <= 0 || v >= (int)m_Result.assignment.size())
            {
                return 0;
            }

            const int val = m_Result.assignment[v]; // 0/1
            const bool litSatisfied = (lit > 0) ? (val == 1) : (val == 0);
            return litSatisfied ? lit : -lit;
        }

        void SetTerminate(void* state, int (*terminate)(void* state))
        {
            if (terminate == nullptr)
            {
                m_CurrTerminateFunc = nullptr;
                m_CurrTerminateState = nullptr;
                return;
            }

            m_CurrTerminateFunc = terminate;
            m_CurrTerminateState = state;

            auto StopTopor = [&]()
                {
                    if (m_CurrTerminateFunc && m_CurrTerminateFunc(m_CurrTerminateState))
                    {
                        return TStopTopor::VAL_STOP;
                    }
                    else
                    {
                        return TStopTopor::VAL_CONTINUE;
                    }
                };

            SetCbStopNow(StopTopor);
        }

    protected:
        struct TSolverResult
        {
            vector<int> assignment;   // index by var id, [1..maxVar], value in {0,1}
            uint64_t cost = 0;
            bool is_optimal = false;
            bool valid = false;
        };

        static bool IsLitSatisfiedByAssignment(int lit, const vector<int>& assignment)
        {
            const int v = lit > 0 ? lit : -lit;
            if (v <= 0 || v >= (int)assignment.size()) return false;
            return lit > 0 ? assignment[v] == 1 : assignment[v] == 0;
        }

        void CaptureToporAssignment()
        {
            m_Result.assignment.assign(m_MaxVarSeen + 1, 0);

            for (int v = 1; v <= m_MaxVarSeen; ++v)
            {
                const TToporLitVal lv = GetLitValue(v);
                if (lv == TToporLitVal::VAL_SATISFIED) m_Result.assignment[v] = 1;
                else m_Result.assignment[v] = 0; // UNSAT/DONT_CARE/UNASSIGNED -> 0
            }

            m_Result.valid = true;
        }

        void ComputeObjFromAssignment()
        {
            uint64_t c = 0;
            for (const auto& p : m_SoftLit2Weight)
            {
                if (IsLitSatisfiedByAssignment(p.first, m_Result.assignment))
                {
                    c += p.second;
                }
            }
            m_Result.cost = c;
        }

        uint64_t InitialSoftCost() const
        {
            uint64_t cost = 0;

            for (const auto& p : m_SoftLit2Weight)
            {
                cost += p.second;
            }

            return cost;
        }

        lsu::TLinearSUResult RunLsuOptimization()
        {
            CTopor<> lsuTopor(m_MaxVarSeen);

            vector<lsu::TWeightedRelaxLit> relaxLits;
            relaxLits.reserve(m_SoftLit2Weight.size());

            int32_t nextFreeVar = m_MaxVarSeen + 1;

            for (const vector<int>& hardClause : m_AllHardClauses)
            {
                lsuTopor.AddClause(hardClause);
            }

            for (const auto& p : m_SoftLit2Weight)
            {
                const int softLit = p.first;
                const uint64_t weight = p.second;

                const int32_t relaxLit = nextFreeVar++;

                // IPAMIR soft literal 'lit' means cost is paid when lit is true.
                // This is equivalent to the soft clause (-lit).
                vector<int> relaxedSoftClause;
                relaxedSoftClause.push_back(-softLit);
                relaxedSoftClause.push_back(relaxLit);

                lsuTopor.AddClause(relaxedSoftClause);

                relaxLits.push_back(lsu::TWeightedRelaxLit{ relaxLit, weight });
            }

            const lsu::TAddClauseFn addClause =
                [&lsuTopor](const vector<int32_t>& clause)
                {
                    lsuTopor.AddClause(clause);
                };

            const lsu::TSolveFn solve =
                [&lsuTopor](const vector<int32_t>& assumptions)
                {
                    return lsuTopor.Solve(assumptions);
                };

            const lsu::TGetLitValueFn getLitValue =
                [&lsuTopor](int32_t lit)
                {
                    return lsuTopor.GetLitValue(lit);
                };

            lsu::TLinearSUOptions options;
            options.Verbose = false;

            return lsu::RunWeightedLinearSatUnsat(
                relaxLits,
                m_CurrAssumps,
                nextFreeVar,
                m_MaxVarSeen,
                InitialSoftCost(),
                addClause,
                solve,
                getLitValue,
                options
            );
        }

        void RunMrsBeaverPostSolve(const vector<int>& assumpsForPost)
        {
            if (m_MaxVarSeen <= 0) return;
            if (m_SoftLit2Weight.empty()) return;
            if (!m_Result.valid) return;

            CTopor<> wmbTopor(m_MaxVarSeen);

            vector<lsu::TWeightedRelaxLit> relaxLits;
            relaxLits.reserve(m_SoftLit2Weight.size());

            bool isWeighted = false;
            int32_t nextFreeVar = m_MaxVarSeen + 1;

            for (const vector<int>& hardClause : m_AllHardClauses)
            {
                wmbTopor.AddClause(hardClause);
            }

            for (const auto& p : m_SoftLit2Weight)
            {
                const int softLit = p.first;
                const uint64_t weight = p.second;

                if (weight != 1)
                {
                    isWeighted = true;
                }

                const int32_t relaxLit = nextFreeVar++;

                vector<int> relaxedSoftClause;
                relaxedSoftClause.push_back(-softLit);
                relaxedSoftClause.push_back(relaxLit);

                wmbTopor.AddClause(relaxedSoftClause);
                relaxLits.push_back(lsu::TWeightedRelaxLit{ relaxLit, weight });
            }

            const lsu::TSolveFn solve =
                [&wmbTopor](const vector<int32_t>& assumptions)
                {
                    return wmbTopor.Solve(assumptions);
                };

            const lsu::TGetLitValueFn getLitValue =
                [&wmbTopor](int32_t lit)
                {
                    return wmbTopor.GetLitValue(lit);
                };

            wmb::WMBOptions options;
            options.enable = true;
            options.gtl = 10;

            wmb::WMBResult wmbResult = wmb::RunMrsBeaver(
                isWeighted,
                relaxLits,
                assumpsForPost,
                m_Result.cost,
                m_Result.assignment,
                solve,
                getLitValue,
                options,
                false
            );

            if (wmbResult.bestCost < m_Result.cost)
            {
                m_Result.cost = wmbResult.bestCost;
                m_Result.assignment = std::move(wmbResult.bestModel01);
                m_Result.valid = true;
            }
        }

        void RunNuwlsPostSolve(const vector<int>& assumpsForPost)
        {
            if (m_MaxVarSeen <= 0) return;
            if (m_AllHardClauses.empty() && m_SoftLit2Weight.empty()) return;

            vector<pair<uint64_t, vector<int>>> softClauses;
            softClauses.reserve(m_SoftLit2Weight.size());

            unsigned long long sumW = 0;
            bool isWeighted = false;
            for (const auto& p : m_SoftLit2Weight)
            {
                // soft lit 'l' => penalty if l=true => soft clause (~l)
                softClauses.push_back({ p.second, vector<int>{ -p.first } });
                sumW += (unsigned long long)p.second;
                if (p.second != 1) isWeighted = true;
            }

            const unsigned long long topClauseWeight = sumW + 1ULL;

            auto built = nuwls::SanitizeAndBuildNuwlsInstance(
                m_MaxVarSeen,
                topClauseWeight,
                m_AllHardClauses,
                softClauses,
                &assumpsForPost);

            if (built.numClauses > 0)
            {
                NUWLS nuwls_solver;
                nuwls_solver.problem_weighted = isWeighted ? 1 : 0;
                nuwls_solver.build_instance(
                    built.numVars,
                    built.numClauses,
                    built.topClauseWeight,
                    built.clauseLit,
                    built.clauseLitCount,
                    built.clauseWeight);
                nuwls_solver.settings();

                nuwls_solver.init(m_Result.assignment);

                unsigned long long improvedCost = m_Result.cost;
                nuwls_solver.RunLocalSearch(m_Result.assignment, improvedCost, 0);

                if (improvedCost < m_Result.cost)
                {
                    m_Result.cost = improvedCost;
                }

                nuwls_solver.free_memory();
            }

            nuwls::FreeNuwlsBuiltInstance(built);
        }

        vector<int> m_CurrHardCls;
        vector<int> m_CurrAssumps;
        unordered_map<int, size_t> m_Assump2Ind;
        unordered_map<int, size_t> m_PrevAssump2Ind;

        unordered_map<int, uint64_t> m_SoftLit2Weight;

        TSolverResult m_Result;
        int m_MaxVarSeen = 0;

        void* m_CurrTerminateState = nullptr;
        int (*m_CurrTerminateFunc)(void* state) = nullptr;

        // post-solver inputs
        vector<vector<int>> m_AllHardClauses;
    };
}

using namespace Topor;

extern "C" {

    const char* ipamir_signature()
    {
        return "IntelSatSolver";
    }

    void* ipamir_init()
    {
        CToporIpamirWrapper* tw = new CToporIpamirWrapper();
        return (void*)tw;
    }

    void ipamir_release(void* solver)
    {
        CToporIpamirWrapper* tw = reinterpret_cast<CToporIpamirWrapper*>(solver);
        delete tw;
    }

    void ipamir_add_hard(void* solver, int32_t lit_or_zero)
    {
        CToporIpamirWrapper* tw = reinterpret_cast<CToporIpamirWrapper*>(solver);
        tw->AddHard(lit_or_zero);
    }

    void ipamir_add_soft_lit(void* solver, int32_t lit, uint64_t weight)
    {
        CToporIpamirWrapper* tw = reinterpret_cast<CToporIpamirWrapper*>(solver);
        tw->AddSoftLit(lit, weight);
    }

    void ipamir_assume(void* solver, int32_t lit)
    {
        CToporIpamirWrapper* tw = reinterpret_cast<CToporIpamirWrapper*>(solver);
        tw->Assume(lit);
    }

    int ipamir_solve(void* solver)
    {
        CToporIpamirWrapper* tw = reinterpret_cast<CToporIpamirWrapper*>(solver);
        return tw->Solve();
    }

    uint64_t ipamir_val_obj(void* solver)
    {
        CToporIpamirWrapper* tw = reinterpret_cast<CToporIpamirWrapper*>(solver);
        return tw->ValObj();
    }

    int32_t ipamir_val_lit(void* solver, int32_t lit)
    {
        CToporIpamirWrapper* tw = reinterpret_cast<CToporIpamirWrapper*>(solver);
        return tw->ValLit(lit);
    }

    void ipamir_set_terminate(void* solver, void* state, int (*terminate)(void* state))
    {
        CToporIpamirWrapper* tw = reinterpret_cast<CToporIpamirWrapper*>(solver);
        tw->SetTerminate(state, terminate);
    }
}