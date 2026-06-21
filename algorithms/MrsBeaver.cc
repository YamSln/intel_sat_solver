#include "MrsBeaver.hpp"
#include <algorithm>
#include <chrono>
#include <iostream>
#include <cmath>
#include <random>

extern double MainWallTimePassed();

namespace wmb
{
    WMBResult RunMrsBeaver(
        bool isWeighted,
        std::vector<lsu::TWeightedRelaxLit> relaxLits,
        const std::vector<int32_t>& baseAssumps,
        uint64_t initialCost,
        const std::vector<int>& initialModel,
        const lsu::TSolveFn& solve,
        const lsu::TGetLitValueFn& getLitValue,
        const WMBOptions& options,
        bool forceLoop)
    {
        WMBResult res;
        res.bestCost = initialCost;
        res.bestModel01 = initialModel;
        res.skipCompletePhase = forceLoop;

        if (relaxLits.empty() || initialCost == 0) return res;

        // Skip sorting entirely for unweighted problems
        if (isWeighted) {
            std::sort(relaxLits.begin(), relaxLits.end(),
                [](const lsu::TWeightedRelaxLit& a, const lsu::TWeightedRelaxLit& b) {
                    return a.Weight > b.Weight;
                });
        }

        auto start = std::chrono::steady_clock::now();
        int iteration = 0;

        std::mt19937 rng(1337);
        std::uniform_real_distribution<double> unif(0.0, 1.0);

        std::vector<int32_t> base;
        for (auto a : baseAssumps) {
            if (a != 0) base.push_back(a);
        }

        struct WeightedKey {
            lsu::TWeightedRelaxLit lit;
            double key;
        };
        std::vector<WeightedKey> weightedItems;
        if (isWeighted) {
            weightedItems.reserve(relaxLits.size());
        }

        while (true)
        {
            iteration++;

            auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now() - start).count();
            if (elapsed >= options.timeLimitSeconds) break;

            if (iteration > options.gtl && !res.skipCompletePhase) {
                uint64_t expectedNodes = relaxLits.size() * res.bestCost;
                if (expectedNodes < options.gtThr) {
                    break;
                }
                else {
                    res.skipCompletePhase = true;
                }
            }

            std::vector<int32_t> currentAssumps = base;
            uint64_t currentPassCost = 0;

            std::vector<int> candidateModel01 = res.bestModel01;



            auto snapshotCandidate = [&]() {

                for (int32_t v = 1; v < static_cast<int32_t>(candidateModel01.size()); ++v) {

                    candidateModel01[v] = (getLitValue(v) == Topor::TToporLitVal::VAL_UNSATISFIED) ? 0 : 1;

                }

                };



            for (size_t i = 0; i < relaxLits.size(); ++i) {

                auto elapsed = std::chrono::duration_cast<std::chrono::seconds>(std::chrono::steady_clock::now() - start).count();
                if (elapsed >= options.timeLimitSeconds) break;


                int32_t targetLit = relaxLits[i].Lit;
                uint64_t weight = relaxLits[i].Weight;


                currentAssumps.push_back(-targetLit);
                Topor::TToporReturnVal ret = solve(currentAssumps);


                if (ret == Topor::TToporReturnVal::RET_SAT) {
                    snapshotCandidate();
                    continue;
                }
                else {
                    currentAssumps.pop_back();
                    currentAssumps.push_back(targetLit);
                    currentPassCost += weight;

                }
                if (currentPassCost >= res.bestCost) break;
            }

            if (currentPassCost < res.bestCost) {
                res.bestCost = currentPassCost;
                res.bestModel01 = std::move(candidateModel01); 

                std::cout << "o " << res.bestCost << std::endl;
                std::cout << "c timeo " << (unsigned)std::ceil(MainWallTimePassed()) << " " << res.bestCost << std::endl;
                if (res.bestCost == 0) break;
            }

            // --- Perturbation / Shuffle Phase ---
            bool doShuffle = (iteration % 2 != 0);

            if (isWeighted) {
                if (!doShuffle) {
                    size_t n = relaxLits.size();

                    size_t i = 0;
                    while (i < n) {
                        size_t j = i + 1;
                        while (j < n && relaxLits[j].Weight == relaxLits[i].Weight) {
                            j++;
                        }
                        if (j - i > 1) {
                            std::reverse(relaxLits.begin() + i, relaxLits.begin() + j);
                        }
                        i = j;
                    }

                    for (size_t k = 0; k + 1 < n; ) {
                        bool k_isolated = (k == 0 || relaxLits[k].Weight != relaxLits[k - 1].Weight) &&
                            (relaxLits[k].Weight != relaxLits[k + 1].Weight);
                        bool k1_isolated = (relaxLits[k + 1].Weight != relaxLits[k].Weight) &&
                            (k + 2 >= n || relaxLits[k + 1].Weight != relaxLits[k + 2].Weight);

                        if (k_isolated && k1_isolated) {
                            std::swap(relaxLits[k], relaxLits[k + 1]);
                            k += 2;
                        }
                        else {
                            k++;
                        }
                    }
                }
                else {
                    weightedItems.clear();
                    for (const auto& lit : relaxLits) {
                        double u = unif(rng);
                        if (u == 0.0) u = 0.000000001;
                        double key = std::pow(u, 1.0 / static_cast<double>(lit.Weight));
                        weightedItems.push_back({ lit, key });
                    }

                    std::sort(weightedItems.begin(), weightedItems.end(),
                        [](const WeightedKey& a, const WeightedKey& b) {
                            return a.key > b.key;
                        });

                    for (size_t k = 0; k < weightedItems.size(); ++k) {
                        relaxLits[k] = weightedItems[k].lit;
                    }
                }
            }
            else {
                // --- Unweighted Branch ---
                if (!doShuffle) {
                    // UBS Heuristic: Push satisfied bits toward the MSB (front)
                    std::stable_partition(relaxLits.begin(), relaxLits.end(),
                        [&](const lsu::TWeightedRelaxLit& rlit) {
                            // The soft clause is satisfied if -targetLit is true in the model
                            int32_t satisfyingLit = -rlit.Lit;
                            int var = std::abs(satisfyingLit);
                            bool expectedValue = (satisfyingLit > 0);
                            return res.bestModel01[var] == (expectedValue ? 1 : 0);
                        });
                }
                else {
                    // Uniform fast shuffle
                    std::shuffle(relaxLits.begin(), relaxLits.end(), rng);
                }
            }
        }

        return res;
    }
}