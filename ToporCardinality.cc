#include "ToporCardinality.hpp"

#include <cassert>

using namespace Topor;
using namespace std;

template <typename TLit>
vector<vector<TLit>> CToporCardinality<TLit>::encode(vector<TLit> lits, CardinalityPredicate cp, uint64_t k, TLit maxVar)
{
	switch (encoding)
	{
	case Topor::CCEncoding::TOTALIZER:
	default:
		if (lits.size() == 1)
		{
			switch (cp)
			{
			case CardinalityPredicate::LEQ:
				if (k == 1)
					break;
			case CardinalityPredicate::LT:
				return { { -1 * lits[0] } };
			case CardinalityPredicate::EQ:
				if (k == 0)
					return { {  -1 * lits[0] } };
				return { { lits[0] } };
			case CardinalityPredicate::GEQ:
				if (k != 1)
					break;
			case CardinalityPredicate::GT:
				return { { lits[0] } };
			default:
				return { { 0 } };
			}
		}
		else
		{
			assert(lits.size() > 1);
			TLit currentLink = maxVar + 1;
			std::vector<TLit> outVars;
			for (int v = currentLink; v < currentLink + lits.size(); v++)
			{
				outVars.push_back(v);
			}
			std::vector<std::vector<TLit>> clauses;
			TotalizerEncode(lits, outVars, lits.size(), 0, currentLink + lits.size(), clauses);
			std::vector<std::vector<TLit>> comparator = ComparatorEncode(outVars, cp, k);
			clauses.insert(clauses.end(), comparator.begin(), comparator.end());
			return clauses;
		}
	}
}

template <typename TLit>
int32_t CToporCardinality<TLit>::TotalizerEncode(const vector<TLit> inVars, const vector<TLit> rootLinks, int32_t rootSize, int32_t currentInputI, int32_t currentLinkC, vector<vector<TLit>>& cls)
{
	int leftSize = rootSize / 2;
	int rightSize = rootSize - rootSize / 2;
	std::vector<TLit> leftLinks, rightLinks;
	if (leftSize == 1)
	{
		leftLinks.push_back(inVars[currentInputI]);
		++currentInputI;
	}
	else
	{
		for (int v = 0; v < leftSize; v++)
		{
			leftLinks.push_back(currentLinkC);
			++currentLinkC;
		}
		currentInputI = TotalizerEncode(inVars, leftLinks, leftSize, currentInputI, currentLinkC, cls);
	}
	if (rightSize == 1)
	{
		rightLinks.push_back(inVars[currentInputI]);
		++currentInputI;
	}
	else
	{
		for (int v = 0; v < rightSize; v++)
		{
			rightLinks.push_back(currentLinkC);
			++currentLinkC;
		}
		currentInputI = TotalizerEncode(inVars, rightLinks, rightSize, currentInputI, currentLinkC, cls);
	}

	std::vector<TLit> c1, c2;
	for (int a = 0; a < leftSize + 1; a++)
	{
		for (int b = 0; b < rightSize + 1; b++)
		{
			if (0 < a + b)
			{
				if (a > 0)
					c1.push_back(-1 * leftLinks[a - 1]);
				if (b > 0)
					c1.push_back(-1 * rightLinks[b - 1]);
				c1.push_back(rootLinks[a + b - 1]);
				cls.push_back(c1);
			}
			if (a + b < rootSize)
			{
				if (a < leftSize)
					c2.push_back(leftLinks[a]);
				if (b < rightSize)
					c2.push_back(rightLinks[b]);
				c2.push_back(-1 * rootLinks[a + b]);
				cls.push_back(c2);
			}
			c1.clear();
			c2.clear();
		}
	}
	return currentInputI;
}

template <typename TLit>
vector<vector<TLit>> CToporCardinality<TLit>::ComparatorEncode(const vector<TLit> outVars, CardinalityPredicate cp, uint64_t k)
{
	std::vector<std::vector<TLit>> cls;
	switch (cp)
	{
	case CardinalityPredicate::LT:
		for (uint64_t j = k - 1; j < outVars.size(); j++)
		{
			cls.push_back({ -1 * outVars[j] });
		}
		break;
	case CardinalityPredicate::LEQ:
		for (uint64_t j = k; j < outVars.size(); j++)
		{
			cls.push_back({ -1 * outVars[j] });
		}
		break;
	case CardinalityPredicate::EQ:
		for (uint64_t i = 0; i < k; i++)
		{
			cls.push_back({ outVars[i] });
		}
		for (uint64_t j = k; j < outVars.size(); j++)
		{
			cls.push_back({ -1 * outVars[j] });
		}
		break;
	case CardinalityPredicate::GEQ:
		for (uint64_t i = 0; i < k; i++)
		{
			cls.push_back({ outVars[i] });
		}
		break;
	case CardinalityPredicate::GT:
		for (uint64_t i = 0; i < k + 1; i++)
		{
			cls.push_back({ outVars[i] });
		}
		break;
	default:
		break;
	}
	return cls;
}

template class Topor::CToporCardinality<int32_t>;