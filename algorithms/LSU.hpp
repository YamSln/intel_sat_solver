#pragma once

#include <cstdint>
#include <functional>
#include <vector>
#include <span>
#include "../ToporExternalTypes.hpp"

namespace lsu
{
    struct TWeightedRelaxLit
    {
        int32_t Lit = 0;
        uint64_t Weight = 0;
    };

    struct TLinearSUOptions
    {
        bool Verbose = false;
        int TimeLimitSeconds = 15;
    };

    struct TLinearSUResult
    {
        bool Ran = false;
        bool Improved = false;

        uint64_t InitialCost = 0;
        uint64_t BestCost = 0;

        // 1-indexed, 0/1 assignment for variables [1..MaxUserVarToStore]
        std::vector<int> BestModel01;

        // next free var after totalizer auxiliaries
        int32_t NextFreeVar = 0;

        Topor::TToporReturnVal LastSolveRet = Topor::TToporReturnVal::RET_EXOTIC_ERROR;
    };

    using TAddClauseFn = std::function<void(const std::vector<int32_t>&)>;
    using TSolveFn = std::function<Topor::TToporReturnVal(const std::vector<int32_t>&)>;
    using TGetLitValueFn = std::function<Topor::TToporLitVal(int32_t)>;

    // For unweighted problems (Pure Cardinality Network)
    TLinearSUResult RunUnweightedLinearSatUnsat(
        const std::vector<int32_t>& relaxLits,
        const std::vector<int32_t>& baseAssumps,
        int32_t firstFreeVar,
        int32_t maxUserVarToStore,
        uint64_t initialCost,
        uint64_t commonWeight,
        const TAddClauseFn& addClause,
        const TSolveFn& solve,
        const TGetLitValueFn& getLitValue,
        const TLinearSUOptions& options = {});

    // For weighted problems (Generalized Totalizer)
    TLinearSUResult RunWeightedLinearSatUnsat(
        const std::vector<TWeightedRelaxLit>& relaxLits,
        const std::vector<int32_t>& baseAssumps,
        int32_t firstFreeVar,
        int32_t maxUserVarToStore,
        uint64_t initialCost,
        const TAddClauseFn& addClause,
        const TSolveFn& solve,
        const TGetLitValueFn& getLitValue,
        const TLinearSUOptions& options = {});
}