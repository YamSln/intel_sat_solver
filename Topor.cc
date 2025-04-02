// Copyright(C) 2021-2023 Intel Corporation
// SPDX - License - Identifier: MIT

#include "Topor.hpp"
#include "Topi.hpp"
#include <fstream> 

using namespace Topor;
using namespace std;

template <typename TLit, typename TUInd, bool Compress>
CTopor<TLit,TUInd,Compress>::CTopor(TLit varsNumHint) : m_Topi(new CTopi<TLit, TUInd, Compress>(varsNumHint)) 
{
	// TLit must be a signed integer
	static_assert(std::is_signed<TLit>::value);
	// TLit must be a power of 2
	static_assert(std::has_single_bit(sizeof(TLit)));
	// TUInd must be an unsigned integer
	static_assert(std::is_unsigned<TUInd>::value);
	// TUInd must be a power of 2
	static_assert(std::has_single_bit(sizeof(TUInd)));
	// TUInd must be at least as wide as TLit (since the clause and watch buffers will store literals, amongst others)
	static_assert(sizeof(TUInd) >= sizeof(TLit));
	// TUInd must not be wider than size_t
	static_assert(sizeof(TUInd) <= sizeof(size_t));
}

template <typename TLit, typename TUInd, bool Compress>
CTopor<TLit,TUInd,Compress>::~CTopor()
{
	delete m_Topi;
	m_Topi = nullptr;
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit,TUInd,Compress>::AddClause(const span<TLit> c)
{
	m_Topi->AddUserClause(c);
}

template <typename TLit, typename TUInd, bool Compress>
int32_t CTopor<TLit, TUInd, Compress>::TotalizerEncode(const span<TLit> inVars, const span<TLit> rootLinks, int32_t rootSize, int32_t currentInputI, int32_t currentLinkC)
{
	int leftSize = rootSize / 2;
	int rightSize = rootSize - rootSize / 2;
	vector<TLit> leftLinks, rightLinks;
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
		currentInputI = TotalizerEncode(inVars, leftLinks, leftSize, currentInputI, currentLinkC);
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
		currentInputI = TotalizerEncode(inVars, rightLinks, rightSize, currentInputI, currentLinkC);
	}

	vector<TLit> c1, c2;
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
				AddClause(c1);
			}
			if (a + b < rootSize)
			{
				if (a < leftSize)
					c2.push_back(leftLinks[a]);
				if (b < rightSize)
					c2.push_back(rightLinks[b]);
				c2.push_back(-1 * rootLinks[a + b]);
				AddClause(c2);
			}
			c1.clear();
			c2.clear();
		}
	}
	return currentInputI;
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit, TUInd, Compress>::ComparatorEncode(const span<TLit> outVars, CardinalityPredicate cp, uint64_t k)
{
	switch (cp)
	{
	case CardinalityPredicate::LT:
		for (uint64_t j = k - 1; j < outVars.size(); j++)
		{
			AddClause({ -1 * outVars[j] });
		}
		break;
	case CardinalityPredicate::LEQ:
		for (uint64_t j = k; j < outVars.size(); j++)
		{
			AddClause({ -1 * outVars[j] });
		}
		break;
	case CardinalityPredicate::EQ:
		for (uint64_t i = 0; i < k; i++)
		{
			AddClause({ outVars[i] });
		}
		for (uint64_t j = k; j < outVars.size(); j++)
		{
			AddClause({ -1 * outVars[j] });
		}
		break;
	case CardinalityPredicate::GEQ:
		for (uint64_t i = 0; i < k; i++)
		{
			AddClause({ outVars[i] });
		}
		break;
	case CardinalityPredicate::GT:
		for (uint64_t i = 0; i < k + 1; i++)
		{
			AddClause({ outVars[i] });
		}
		break;
	default:
		break;
	}
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit, TUInd, Compress>::AddCardinalityConstraint(const span<TLit> lits, CardinalityPredicate cp, uint64_t k)
{
	if (lits.size() == 1)
	{
		switch (cp)
		{
		case CardinalityPredicate::LEQ:
			if (k == 1)
				break;
		case CardinalityPredicate::LT:
			AddClause({ -1 * lits[0] });
			break;
		case CardinalityPredicate::EQ:
			if (k == 0)
				AddClause({ -1 * lits[0] });
			else
				AddClause({ lits[0] });
			break;
		case CardinalityPredicate::GEQ:
			if (k != 1)
				break;
		case CardinalityPredicate::GT:
			AddClause({ lits[0] });
			break;
		default:
			break;
		}
	}
	else
	{
		assert(lits.size() > 1);
		TLit currentLink = GetMaxUserVar() + 1;
		vector<TLit> outVars;
		for (int v = currentLink; v < currentLink + lits.size(); v++)
		{
			outVars.push_back(v);
		}
		TotalizerEncode(lits, outVars, lits.size(), 0, currentLink + lits.size());
		ComparatorEncode(outVars, cp, k);
	}
}

template <typename TLit, typename TUInd, bool Compress>
TToporReturnVal CTopor<TLit,TUInd,Compress>::Solve(const span<TLit> assumps, pair<double, bool> toInSecIsCpuTime, uint64_t confThr)
{
	return m_Topi->Solve(assumps, toInSecIsCpuTime, confThr);
}

template <typename TLit, typename TUInd, bool Compress>
bool CTopor<TLit,TUInd,Compress>::IsAssumptionRequired(size_t assumpInd)
{
	return m_Topi->IsAssumptionRequired(assumpInd);
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit,TUInd,Compress>::BoostScore(TLit v, double value)
{
	m_Topi->BoostScore(v, value);
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit,TUInd,Compress>::FixPolarity(TLit l, bool onlyOnce)
{
	m_Topi->FixPolarity(l, onlyOnce);
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit, TUInd, Compress>::CreateInternalLit(TLit l)
{
	m_Topi->CreateInternalLit(l);
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit,TUInd,Compress>::ClearUserPolarityInfo(TLit v)
{
	m_Topi->ClearUserPolarityInfo(v);
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit,TUInd,Compress>::SetParam(const string& paramName, double newVal)
{
	m_Topi->SetParam(paramName, newVal);
}

template <typename TLit, typename TUInd, bool Compress>
Topor::TToporLitVal CTopor<TLit,TUInd,Compress>::GetLitValue(TLit l) const
{
	return m_Topi->GetValue(l);
}

template <typename TLit, typename TUInd, bool Compress>
TLit CTopor<TLit, TUInd, Compress>::GetLitDecLevel(TLit l) const
{
	return m_Topi->GetLitDecLevel(l);
}

template <typename TLit, typename TUInd, bool Compress>
uint64_t CTopor<TLit, TUInd, Compress>::GetSolveInvs() const
{
	return m_Topi->GetSolveInvs();
}

template <typename TLit, typename TUInd, bool Compress>
TLit CTopor<TLit, TUInd, Compress>::GetMaxUserVar() const
{
	return m_Topi->GetMaxUserVar();
}

template <typename TLit, typename TUInd, bool Compress>
std::string CTopor<TLit, TUInd, Compress>::GetStatStrShort(bool forcePrintingHead)
{
	return m_Topi->GetStatStrShort(forcePrintingHead);
}

template <typename TLit, typename TUInd, bool Compress>
uint64_t CTopor<TLit, TUInd, Compress>::GetConflictsNumber() const
{
	return m_Topi->GetConflictsNumber();
}

template <typename TLit, typename TUInd, bool Compress>
uint64_t CTopor<TLit, TUInd, Compress>::GetActiveClss() const
{
	return m_Topi->GetActiveClss();
}

template <typename TLit, typename TUInd, bool Compress>
uint64_t CTopor<TLit, TUInd, Compress>::GetBacktracks() const
{
	return m_Topi->GetBacktracks();
}

template <typename TLit, typename TUInd, bool Compress>
uint64_t CTopor<TLit, TUInd, Compress>::GetAssumpReuseBacktrackLevelsSaved() const
{
	return m_Topi->GetAssumpReuseBacktrackLevelsSaved();
}

template <typename TLit, typename TUInd, bool Compress>
uint64_t CTopor<TLit, TUInd, Compress>::GetPropagations() const
{
	return m_Topi->GetPropagations();
}

template <typename TLit, typename TUInd, bool Compress>
TLit CTopor<TLit, TUInd, Compress>::GetMaxInternalVar() const
{
	return m_Topi->GetMaxInternalVar();
}

template <typename TLit, typename TUInd, bool Compress>
uint64_t CTopor<TLit, TUInd, Compress>::GetActiveLongLearntClss() const
{
	return m_Topi->GetActiveLongLearntClss();
}

template <typename TLit, typename TUInd, bool Compress>
std::vector<TToporLitVal> CTopor<TLit,TUInd,Compress>::GetModel() const
{
	return m_Topi->GetModel();
}

template <typename TLit, typename TUInd, bool Compress>
bool CTopor<TLit,TUInd,Compress>::IsError() const
{
	return m_Topi->IsError();
}

template <typename TLit, typename TUInd, bool Compress>
std::string CTopor<TLit,TUInd,Compress>::GetStatusExplanation() const
{
	return m_Topi->GetStatusExplanation();
}

template <typename TLit, typename TUInd, bool Compress>
std::string CTopor<TLit,TUInd,Compress>::GetParamsDescr() const
{
	return m_Topi->GetParamsDescr();
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit,TUInd,Compress>::DumpDrat(ofstream& openedDratFile, bool isDratBinary, bool dratSortEveryClause)
{
	m_Topi->DumpDrat(openedDratFile, isDratBinary, dratSortEveryClause);
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit,TUInd,Compress>::SetCbStopNow(TCbStopNow CbStopNow)
{
	m_Topi->SetCbStopNow(CbStopNow);
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit,TUInd,Compress>::InterruptNow()
{
	m_Topi->InterruptNow();
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit,TUInd,Compress>::SetCbNewLearntCls(TCbNewLearntCls<TLit> CbNewLearntCls)
{
	m_Topi->SetCbNewLearntCls(CbNewLearntCls);
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit,TUInd,Compress>::Backtrack(TLit decLevel)
{
	m_Topi->Backtrack(decLevel, false, true);
}

template <typename TLit, typename TUInd, bool Compress>
string CTopor<TLit,TUInd,Compress>::ChangeConfigToGiven(uint16_t configNum)
{
	return m_Topi->ChangeConfigToGiven(configNum);
}

template <typename TLit, typename TUInd, bool Compress>
void CTopor<TLit, TUInd, Compress>::SetParallelData(unsigned threadId, std::function<void(unsigned threadId, int lit)> ReportUnitClause, std::function<int(unsigned threadId, bool reinit)> GetNextUnitClause)
{
	m_Topi->SetParallelData(threadId, ReportUnitClause, GetNextUnitClause);
}

namespace Topor
{
	std::ostream& operator << (std::ostream& os, const TToporReturnVal& trv)
	{
		switch (trv)
		{
		case TToporReturnVal::RET_SAT: os << "SAT"; break;
		case TToporReturnVal::RET_UNSAT: os << "UNSAT"; break;
		case TToporReturnVal::RET_TIMEOUT_LOCAL: os << "TIMEOUT_LOCAL"; break;
		case TToporReturnVal::RET_CONFLICT_OUT: os << "CONFLICT_OUT"; break;
		case TToporReturnVal::RET_MEM_OUT: os << "MEM_OUT"; break;
		case TToporReturnVal::RET_USER_INTERRUPT: os << "USER_INTERRUPT"; break;
		case TToporReturnVal::RET_INDEX_TOO_NARROW: os << "INDEX_TOO_NARROW"; break;
		case TToporReturnVal::RET_PARAM_ERROR: os << "PARAM_ERROR"; break;
		case TToporReturnVal::RET_ASSUMPTION_REQUIRED_ERROR: os << "ASSUMPTION_REQUIRED_ERROR"; break;
		case TToporReturnVal::RET_TIMEOUT_GLOBAL: os << "TIMEOUT_GLOBAL"; break;
		case TToporReturnVal::RET_DRAT_FILE_PROBLEM: os << "DRAT_FILE_PROBLEM"; break;
		case TToporReturnVal::RET_EXOTIC_ERROR: os << "EXOTIC_ERROR"; break;
		default: os << "TToporReturnVal : undefined value!";
		}
		return os;
	}
}

template class Topor::CTopor<int32_t, uint32_t, false>;
template class Topor::CTopor<int32_t, uint64_t, false>;
template class Topor::CTopor<int32_t, uint64_t, true>;
