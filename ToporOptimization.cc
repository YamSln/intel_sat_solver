#include "ToporOptimization.hpp"

#include <unordered_set>

using namespace std;
using namespace Topor;

template <typename TLit, typename TUInd, bool Compress>
optional<pair<vector<TToporLitVal>, double>> CToporOptimization<TLit, TUInd, Compress>::Polosat(CTopor<TLit, TUInd, Compress>* solver, function<double(const vector<TToporLitVal>)> pb, vector<TLit> assumps, bool anytime)
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
		if (anytime)
		{
			PrintModel(currentAssignment);
			if (!AnytimeContinue(pb(currentAssignment)))
				break;
		}

		while (!satLits.empty())
		{
			TLit l = satLits.front();
			satLits.pop_front();
			for (TLit v = 1; v < (TLit)currentAssignment.size(); v++)
			{
				solver->FixPolarity(currentAssignment[v] != TToporLitVal::VAL_SATISFIED ? v : -1 * v, true);
			}
			assumps.push_back(-1 * l);
			TToporReturnVal ret = solver->Solve(assumps);
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
			assumps.pop_back();
		}
	}
	if (anytime)
	{
		PrintModel(currentAssignment);
		cout << "Optimal value: " << pb(currentAssignment) << endl;
	}
	return make_pair(currentAssignment, currentValue);
}

template<typename TLit, typename TUInd, bool Compress>
optional<pair<vector<TToporLitVal>, double>> CToporOptimization<TLit, TUInd, Compress>::StrictlyMonotonePolosat(CTopor<TLit, TUInd, Compress>* solver, function<double(const vector<TToporLitVal>)> pb, vector<TLit> obs, vector<TLit> assumps, bool anytime)
{
	unordered_set<TLit> obs_uset;
	for (TLit lit : obs)
	{
		solver->FixPolarity(-1 * lit, true);
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
		if (anytime)
		{
			PrintModel(currentAssignment);
			if (!AnytimeContinue(pb(currentAssignment)))
				break;
		}

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
					solver->FixPolarity(unsat ? v : -1 * v, true);
				}
				else
				{
					solver->FixPolarity(currentAssignment[v] != TToporLitVal::VAL_SATISFIED ? v : -1 * v, true);
				}
			}
			assumps.push_back(-1 * l);
			TToporReturnVal ret = solver->Solve(assumps);
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
			assumps.pop_back();
		}
	}
	if (anytime)
	{
		PrintModel(currentAssignment);
		cout << "Optimal value: " << pb(currentAssignment) << endl;
	}
	return make_pair(currentAssignment, currentValue);
}

template class Topor::CToporOptimization<int32_t, uint32_t, false>;
template class Topor::CToporOptimization<int32_t, uint64_t, false>;
template class Topor::CToporOptimization<int32_t, uint64_t, true>;