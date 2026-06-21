#pragma once

#include <vector>
#include <cstdint>
#include <functional>
#include "LSU.hpp" // Reuse LSU types for callbacks and literals

namespace wmb
{
    struct WMBOptions
    {
        bool enable = true;
        int gtl = 10;
        uint64_t gtThr = 1000000;
        int timeLimitSeconds = 60;
        uint64_t conflictThreshold = 10000;
    };

    struct WMBResult
    {
        uint64_t bestCost = 0;
        std::vector<int> bestModel01;
        bool skipCompletePhase = false; // True if gtThr exceeded
    };

    WMBResult RunMrsBeaver(
        bool isWeighted,
        std::vector<lsu::TWeightedRelaxLit> relaxLits,
        const std::vector<int32_t>& baseAssumps,
        uint64_t initialCost,
        const std::vector<int>& initialModel,
        const lsu::TSolveFn& solve,
        const lsu::TGetLitValueFn& getLitValue,
        const WMBOptions& options,
        bool forceLoop = false // Used if LSU falls back to WMB
    );
}