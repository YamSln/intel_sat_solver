#include "LSU.hpp"
#include <algorithm>
#include <unordered_map>
#include <chrono>
#include <iostream>
#include <cmath>

#ifdef DPRINT
#define DLOG(x) std::cout << "c [DPRINT] " << x << std::endl
#else
#define DLOG(x) // Compiles to literally nothing when DPRINT is off
#endif

extern double MainWallTimePassed();

namespace lsu
{
    namespace
    {
        static std::vector<int> SnapshotModel01(int32_t maxVar, const TGetLitValueFn& getLitValue)
        {
            std::vector<int> m((size_t)maxVar + 1, 0);
            for (int32_t v = 1; v <= maxVar; ++v) {
                m[v] = (getLitValue(v) == Topor::TToporLitVal::VAL_UNSATISFIED) ? 0 : 1;
            }
            return m;
        }

        // =========================================================================
        // BOUNDED UNWEIGHTED TOTALIZER (Cardinality Network)
        // =========================================================================
        class BoundedUnweightedTotalizerBuilder
        {
        public:
            BoundedUnweightedTotalizerBuilder(int32_t firstFreeVar, uint64_t cap, const TAddClauseFn& addClause)
                : m_nextVar(firstFreeVar - 1), m_cap(cap), m_addClause(addClause) {
            }

            int32_t NextFreeVar() const { return m_nextVar + 1; }

            // Returns vector where index i represents the literal for (Sum >= i + 1)
            std::vector<int32_t> Build(const std::vector<int32_t>& relaxLits)
            {
                if (m_cap == 0 || relaxLits.empty()) return {};

                std::vector<std::vector<int32_t>> leaves;
                leaves.reserve(relaxLits.size());
                for (int32_t lit : relaxLits) {
                    if (lit > 0) leaves.push_back({ lit });
                }

                while (leaves.size() > 1) {
                    std::vector<std::vector<int32_t>> next;
                    next.reserve((leaves.size() + 1) / 2);
                    for (size_t i = 0; i < leaves.size(); i += 2) {
                        if (i + 1 == leaves.size()) next.push_back(std::move(leaves[i]));
                        else next.push_back(Merge(leaves[i], leaves[i + 1]));
                    }
                    leaves = std::move(next);
                }
                return leaves.empty() ? std::vector<int32_t>{} : leaves.front();
            }

        private:
            int32_t m_nextVar;
            uint64_t m_cap;
            TAddClauseFn m_addClause;

            std::vector<int32_t> Merge(const std::vector<int32_t>& L, const std::vector<int32_t>& R)
            {
                uint64_t outSize = std::min(m_cap + 1, (uint64_t)(L.size() + R.size()));
                std::vector<int32_t> out(outSize);
                for (size_t i = 0; i < outSize; ++i) out[i] = ++m_nextVar;

                for (size_t i = 0; i < L.size() && i < outSize; ++i)
                    m_addClause({ -L[i], out[i] });

                for (size_t j = 0; j < R.size() && j < outSize; ++j)
                    m_addClause({ -R[j], out[j] });

                for (size_t i = 0; i < L.size(); ++i) {
                    for (size_t j = 0; j < R.size(); ++j) {
                        if (i + j + 1 < outSize) {
                            m_addClause({ -L[i], -R[j], out[i + j + 1] });
                        }
                    }
                }
                return out;
            }
        };

        // =========================================================================
        // BOUNDED WEIGHTED TOTALIZER (Generalized Totalizer)
        // =========================================================================
        struct NodeOut { uint64_t Sum; int32_t Lit; };

        class BoundedWeightedTotalizerBuilder
        {
        public:
            BoundedWeightedTotalizerBuilder(int32_t firstFreeVar, uint64_t cap, const TAddClauseFn& addClause)
                : m_nextVar(firstFreeVar - 1), m_cap(cap), m_addClause(addClause) {
            }

            int32_t NextFreeVar() const { return m_nextVar + 1; }

            std::vector<NodeOut> Build(const std::vector<TWeightedRelaxLit>& relaxLits)
            {
                if (m_cap == 0 || relaxLits.empty()) return {};

                std::vector<std::vector<NodeOut>> leaves;
                leaves.reserve(relaxLits.size());
                for (const auto& r : relaxLits) {
                    if (r.Lit > 0 && r.Weight > 0) {
                        leaves.push_back({ NodeOut{ r.Weight, r.Lit } });
                    }
                }

                while (leaves.size() > 1) {
                    std::vector<std::vector<NodeOut>> next;
                    next.reserve((leaves.size() + 1) / 2);
                    for (size_t i = 0; i < leaves.size(); i += 2) {
                        if (i + 1 == leaves.size()) next.push_back(std::move(leaves[i]));
                        else next.push_back(Merge(leaves[i], leaves[i + 1]));
                    }
                    leaves = std::move(next);
                }

                auto out = leaves.front();
                std::sort(out.begin(), out.end(), [](const NodeOut& a, const NodeOut& b) { return a.Sum < b.Sum; });
                return out;
            }

        private:
            int32_t m_nextVar;
            uint64_t m_cap;
            TAddClauseFn m_addClause;

            uint64_t Clip(uint64_t s) const { return (s > m_cap) ? (m_cap + 1) : s; }
            int32_t NewVar() { return ++m_nextVar; }

            std::vector<NodeOut> Merge(const std::vector<NodeOut>& L, const std::vector<NodeOut>& R)
            {
                std::unordered_map<uint64_t, int32_t> outMap;

                auto EnsureOut = [&](uint64_t sum) {
                    auto it = outMap.find(sum);
                    if (it != outMap.end()) return it->second;
                    int32_t v = NewVar();
                    outMap.emplace(sum, v);
                    return v;
                    };

                for (const auto& lo : L) m_addClause({ -lo.Lit, EnsureOut(Clip(lo.Sum)) });
                for (const auto& ro : R) m_addClause({ -ro.Lit, EnsureOut(Clip(ro.Sum)) });

                for (const auto& lo : L) {
                    for (const auto& ro : R) {
                        m_addClause({ -lo.Lit, -ro.Lit, EnsureOut(Clip(lo.Sum + ro.Sum)) });
                    }
                }

                std::vector<NodeOut> res;
                res.reserve(outMap.size());
                for (auto& kv : outMap) res.push_back(NodeOut{ kv.first, kv.second });
                return res;
            }
        };
    }

    // =========================================================================
    // SEARCH ALGORITHMS
    // =========================================================================

    TLinearSUResult RunUnweightedLinearSatUnsat(
        const std::vector<int32_t>& relaxLits, const std::vector<int32_t>& baseAssumps,
        int32_t firstFreeVar, int32_t maxUserVarToStore, uint64_t initialCost, uint64_t commonWeight,
        const TAddClauseFn& addClause, const TSolveFn& solve, const TGetLitValueFn& getLitValue, const TLinearSUOptions& options)
    {
        TLinearSUResult res{ true, false, initialCost, initialCost, {}, firstFreeVar, Topor::TToporReturnVal::RET_SAT };
        if (maxUserVarToStore > 0) res.BestModel01 = SnapshotModel01(maxUserVarToStore, getLitValue);

        DLOG("=== ENTERING LSU (UNWEIGHTED) ===");

        if (relaxLits.empty() || initialCost == 0) return res;

        BoundedUnweightedTotalizerBuilder builder(firstFreeVar, initialCost, addClause);
        auto root = builder.Build(relaxLits);
        res.NextFreeVar = builder.NextFreeVar();

        std::vector<int32_t> base;
        for (auto a : baseAssumps) if (a != 0) base.push_back(a);

        auto start = std::chrono::steady_clock::now();
        uint64_t best = initialCost;

        while (best > 0)
        {
            if (options.TimeLimitSeconds > 0) {
                auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now() - start).count();
                if (elapsed >= options.TimeLimitSeconds) break;
            }

            uint64_t target = best / commonWeight - 1;
            std::vector<int32_t> assumps = base;

            if (target < root.size()) assumps.push_back(-root[target]);

            res.LastSolveRet = solve(assumps);
            if (res.LastSolveRet != Topor::TToporReturnVal::RET_SAT) break;

            uint64_t cost = 0;
            for (auto r : relaxLits) {
                if (getLitValue(r) == Topor::TToporLitVal::VAL_SATISFIED) cost += commonWeight;
            }

            if (cost >= best) break; // Failsafe

            DLOG("  [LSU] Bound improved: " << best << " -> " << cost);
            best = cost;
            res.BestCost = cost;
            res.Improved = true;
            if (maxUserVarToStore > 0) res.BestModel01 = SnapshotModel01(maxUserVarToStore, getLitValue);

            //std::cout << "o " << best << std::endl;
            std::cout << "c timeo " << (unsigned)std::ceil(MainWallTimePassed()) << " " << best << std::endl;
        }

        DLOG("=== EXITING LSU ===");
        return res;
    }

    TLinearSUResult RunWeightedLinearSatUnsat(
        const std::vector<TWeightedRelaxLit>& relaxLits, const std::vector<int32_t>& baseAssumps,
        int32_t firstFreeVar, int32_t maxUserVarToStore, uint64_t initialCost,
        const TAddClauseFn& addClause, const TSolveFn& solve, const TGetLitValueFn& getLitValue, const TLinearSUOptions& options)
    {
        TLinearSUResult res{ true, false, initialCost, initialCost, {}, firstFreeVar, Topor::TToporReturnVal::RET_SAT };
        if (maxUserVarToStore > 0) res.BestModel01 = SnapshotModel01(maxUserVarToStore, getLitValue);

        DLOG("=== ENTERING LSU (WEIGHTED) ===");

        if (relaxLits.empty() || initialCost == 0) return res;

        // Filter out clauses that are too heavy to ever be satisfied
        std::vector<TWeightedRelaxLit> treeLits;
        std::vector<int32_t> hardenedAssumps;
        treeLits.reserve(relaxLits.size());

        for (const auto& r : relaxLits) {
            if (r.Weight >= initialCost) {
                hardenedAssumps.push_back(-r.Lit); // Temporarily harden via assumptions
            }
            else if (r.Weight > 0 && r.Lit > 0) {
                treeLits.push_back(r);
            }
        }

        if (treeLits.empty() && hardenedAssumps.empty()) return res;

        BoundedWeightedTotalizerBuilder builder(firstFreeVar, initialCost, addClause);
        auto root = builder.Build(treeLits); // Only build the tree using valid literals
        res.NextFreeVar = builder.NextFreeVar();

        std::vector<int32_t> base;
        for (auto a : baseAssumps) if (a != 0) base.push_back(a);

        auto start = std::chrono::steady_clock::now();
        uint64_t best = initialCost;

        while (best > 0)
        {
            if (options.TimeLimitSeconds > 0) {
                auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now() - start).count();
                if (elapsed >= options.TimeLimitSeconds) break;
            }

            uint64_t target = best - 1;
            std::vector<int32_t> assumps = base;

            // 1. Cap the tree nodes
            for (const auto& o : root) {
                if (o.Sum > target) assumps.push_back(-o.Lit);
            }

            // 2. Append the hardened heavy clauses incrementally
            assumps.insert(assumps.end(), hardenedAssumps.begin(), hardenedAssumps.end());

            res.LastSolveRet = solve(assumps);
            if (res.LastSolveRet != Topor::TToporReturnVal::RET_SAT) break;

            uint64_t cost = 0;
            for (const auto& r : relaxLits) {
                if (getLitValue(r.Lit) == Topor::TToporLitVal::VAL_SATISFIED) cost += r.Weight;
            }

            if (cost >= best) break; // Failsafe

            DLOG("  [LSU] Bound improved: " << best << " -> " << cost);
            best = cost;
            res.BestCost = cost;
            res.Improved = true;
            if (maxUserVarToStore > 0) res.BestModel01 = SnapshotModel01(maxUserVarToStore, getLitValue);

            //std::cout << "o " << best << std::endl;
            std::cout << "c timeo " << (unsigned)std::ceil(MainWallTimePassed()) << " " << best << std::endl;
        }

        DLOG("=== EXITING LSU ===");
        return res;
    }
}