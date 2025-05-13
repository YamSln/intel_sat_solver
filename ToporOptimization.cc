#include "ToporOptimization.hpp"

#include <unordered_set>

using namespace std;
using namespace Topor;

template <typename TLit, typename TUInd, bool Compress>
optional<tuple<TToporReturnVal, vector<TToporLitVal>, double>> CToporOptimization<TLit, TUInd, Compress>::Polosat(CTopor<TLit, TUInd, Compress>* solver, function<double(const vector<TToporLitVal>)> pb, vector<TLit> assumps)
{
	TToporReturnVal ret = solver->Solve(assumps);
	if (ret != TToporReturnVal::RET_SAT)
	{
		return nullopt;
	}
	vector<TToporLitVal> currentAssignment = solver->GetModel();
	double currentValue = pb(currentAssignment);
	bool isGoodEpoch = true;

	while (isGoodEpoch)
	{
		deque<TLit> satLits = GetSatLits(currentAssignment);
		isGoodEpoch = false;

		while (!satLits.empty())
		{
			TLit l = satLits.front();
			satLits.pop_front();
			for (TLit v = 1; v < (TLit)currentAssignment.size(); v++)
			{
				solver->FixPolarity(currentAssignment[v] != TToporLitVal::VAL_SATISFIED ? v : -v, true);
			}
			assumps.push_back(-l);
			ret = solver->Solve(assumps);
			if (ret == TToporReturnVal::RET_SAT)
			{
				vector<TToporLitVal> newAssignment = solver->GetModel();
				double newValue = pb(newAssignment);
				if (newValue < currentValue)
				{
					currentAssignment = newAssignment;
					currentValue = newValue;
					isGoodEpoch = true;
					satLits = GetSatLits(currentAssignment, satLits);
				}
			}
			else if (ret != TToporReturnVal::RET_UNSAT)
			{
				isGoodEpoch = false;
				break;
			}
			assumps.pop_back();
		}
	}
	return make_tuple(ret, currentAssignment, currentValue);
}

template<typename TLit, typename TUInd, bool Compress>
optional<tuple<TToporReturnVal, vector<TToporLitVal>, double>> CToporOptimization<TLit, TUInd, Compress>::StrictlyMonotonePolosat(CTopor<TLit, TUInd, Compress>* solver, function<double(const vector<TToporLitVal>)> pb, vector<TLit> obs, vector<TLit> assumps)
{
	unordered_set<TLit> obs_uset;
	for (TLit lit : obs)
	{
		solver->FixPolarity(-lit, true);
		obs_uset.insert(lit);
	}
	TToporReturnVal ret = solver->Solve(assumps);
	if (ret != TToporReturnVal::RET_SAT)
	{
		return nullopt;
	}
	vector<TToporLitVal> currentAssignment = solver->GetModel();
	double currentValue = pb(currentAssignment);
	bool isGoodEpoch = true;

	while (isGoodEpoch)
	{
		deque<TLit> satLits = GetSatLits(currentAssignment, obs);
		isGoodEpoch = false;

		while (!satLits.empty())
		{
			TLit l = satLits.front();
			satLits.pop_front();
			for (TLit v = 1; v < (TLit)currentAssignment.size(); v++)
			{
				bool sat = obs_uset.find(v) != obs_uset.end();
				bool unsat = obs_uset.find(-v) != obs_uset.end();
				if (sat || unsat)
				{
					solver->FixPolarity(unsat ? v : -v, true);
				}
				else
				{
					solver->FixPolarity(currentAssignment[v] != TToporLitVal::VAL_SATISFIED ? v : -v, true);
				}
			}
			assumps.push_back(-l);
			ret = solver->Solve(assumps);
			if (ret == TToporReturnVal::RET_SAT)
			{
				vector<TToporLitVal> newAssignment = solver->GetModel();
				double newValue = pb(newAssignment);
				if (newValue < currentValue)
				{
					currentAssignment = newAssignment;
					currentValue = newValue;
					isGoodEpoch = true;
				}
				satLits = GetSatLits(newAssignment, satLits);
			}
			else if (ret != TToporReturnVal::RET_UNSAT)
			{
				isGoodEpoch = false;
				break;
			}
			assumps.pop_back();
		}
	}

	return make_tuple(ret, currentAssignment, currentValue);
}

template class Topor::CToporOptimization<int32_t, uint32_t, false>;
template class Topor::CToporOptimization<int32_t, uint64_t, false>;
template class Topor::CToporOptimization<int32_t, uint64_t, true>;