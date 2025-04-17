#pragma once

#include <span>
#include <vector>
#include <cassert>

namespace Topor
{
	enum class CardinalityPredicate
	{
		LT, LEQ, EQ, GEQ, GT
	};

	enum class CCEncoding
	{
		TOTALIZER
	};

	template <typename TLit = int32_t>
	class CToporCardinality
	{
	private:
		CCEncoding encoding;
		/* Totalizer */
		
		std::vector<std::vector<TLit>> TotalizerEncode(const std::vector<TLit> inVars, const std::vector<TLit> outVars, int32_t currentLinkC);
		std::vector<std::vector<TLit>> ComparatorEncode(const std::vector<TLit> outVars, CardinalityPredicate cp, uint64_t k);
		
		/* ********* */

	public:
		CToporCardinality(CCEncoding encoding) : encoding(encoding) {}

		std::vector<std::vector<TLit>> encode(std::span<TLit> lits, CardinalityPredicate cp, uint64_t k, TLit maxVar)
		{
			std::vector<TLit> lts(lits.begin(), lits.end());
			return encode(lts, cp, k, maxVar);
		}

		std::vector<std::vector<TLit>> encode(std::vector<TLit> lits, CardinalityPredicate cp, uint64_t k, TLit maxVar);
	};
}