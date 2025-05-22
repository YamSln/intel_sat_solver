#include "ToporCardinality.hpp"

#include <stack>
#include <cassert>

using namespace Topor;
using namespace std;

template <typename TLit>
vector<vector<TLit>> CToporCardinality<TLit>::encode(vector<TLit> lits, CardinalityPredicate cp, uint64_t k, TLit nextAvailableVar)
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
					return { };
			case CardinalityPredicate::LT:
				return { { -lits[0] } };
			case CardinalityPredicate::EQ:
				if (k == 0)
					return { { -lits[0] } };
				return { { lits[0] } };
			case CardinalityPredicate::GEQ:
				if (k != 1)
					return { };
			case CardinalityPredicate::GT:
				return { { lits[0] } };
			default:
				return { };
			}
		}
		else
		{
			assert(lits.size() > 1);
			TLit currentLink = nextAvailableVar;
			vector<TLit> outVars;
			for (TLit v = currentLink; v < currentLink + (TLit)lits.size(); v++)
			{
				outVars.push_back(v);
			}
			
			vector<vector<TLit>> clauses = TotalizerEncode(lits, outVars, currentLink + lits.size());
			vector<vector<TLit>> comparator = ComparatorEncode(outVars, cp, k);
			clauses.insert(clauses.end(), comparator.begin(), comparator.end());
			
			return clauses;
		}
	}
}

template <typename TLit>
vector<vector<TLit>> CToporCardinality<TLit>::TotalizerEncode(const vector<TLit> inVars, const vector<TLit> outVars, int32_t currentLinkC)
{
	vector<vector<TLit>> clauses;
	stack<vector<TLit>> linkVarsNodes;
	vector<TLit> leftLinkVars, rightLinkVars;
	int currentInputI = 0;
	vector<TLit> c1, c2;
	
	linkVarsNodes.push(outVars);

	while (!linkVarsNodes.empty())
	{
		vector<TLit> rootLinkVars = linkVarsNodes.top();
		linkVarsNodes.pop();
		int rootSize = rootLinkVars.size();
		int leftSize = rootSize / 2;
		int rightSize = rootSize - rootSize / 2;
		if (leftSize == 1)
		{
			leftLinkVars.push_back(inVars[currentInputI]);
			currentInputI++;
		}
		else
		{
			for (int v = 0; v < leftSize; v++)
			{
				leftLinkVars.push_back(currentLinkC);
				currentLinkC++;
			}
			linkVarsNodes.push(leftLinkVars);
		}
		if (rightSize == 1)
		{
			rightLinkVars.push_back(inVars[currentInputI]);
			currentInputI++;
		}
		else
		{
			for (int v = 0; v < rightSize; v++)
			{
				rightLinkVars.push_back(currentLinkC);
				currentLinkC++;
			}
			linkVarsNodes.push(rightLinkVars);
		}

		for (int a = 0; a < leftSize + 1; a++)
		{
			for (int b = 0; b < rightSize + 1; b++)
			{
				if (0 < a + b)
				{
					if (a > 0)
						c1.push_back(-leftLinkVars[a - 1]);
					if (b > 0)
						c1.push_back(-rightLinkVars[b - 1]);
					c1.push_back(rootLinkVars[a + b - 1]);
					clauses.push_back(c1);
					c1.clear();
				}
				if (a + b < rootSize)
				{
					if (a < leftSize)
						c2.push_back(leftLinkVars[a]);
					if (b < rightSize)
						c2.push_back(rightLinkVars[b]);
					c2.push_back(-rootLinkVars[a + b]);
					clauses.push_back(c2);
					c2.clear();
				}
			}
		}
		leftLinkVars.clear();
		rightLinkVars.clear();
	}

	return clauses;
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
			cls.push_back({ -outVars[j] });
		}
		break;
	case CardinalityPredicate::LEQ:
		for (uint64_t j = k; j < outVars.size(); j++)
		{
			cls.push_back({ -outVars[j] });
		}
		break;
	case CardinalityPredicate::EQ:
		for (uint64_t i = 0; i < k; i++)
		{
			cls.push_back({ outVars[i] });
		}
		for (uint64_t j = k; j < outVars.size(); j++)
		{
			cls.push_back({ -outVars[j] });
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