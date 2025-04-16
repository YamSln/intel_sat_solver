#include "ToporOptimization.hpp"

using namespace std;
using namespace Topor;

template <typename TLit, typename TUInd, bool Compress>
TToporReturnVal CToporOptimization<TLit, TUInd, Compress>::polosat(CTopor<TLit, TUInd, Compress>* solver, double (*pb)(const vector<TToporLitVal>), bool anytime)
{
	TToporReturnVal ret = solver->Solve();
	if (ret == TToporReturnVal::RET_UNSAT)
	{
		return ret;
	}
	std::vector<TToporLitVal> currentAssignment = solver->GetModel();
	bool isGoodEpoch = true;

	while (isGoodEpoch)
	{
		std::deque<TLit> satLits = getSatLits<TLit>(currentAssignment);
		isGoodEpoch = false;
		PrintModel<TLit>(currentAssignment);
		if (anytime && !AnytimeContinue(pb(currentAssignment)))
			break;

		while (!satLits.empty())
		{
			TLit l = satLits.front();
			satLits.pop_front();
			for (TLit v = 1; v < (TLit)currentAssignment.size(); v++)
			{
				solver->FixPolarity(currentAssignment[v] != TToporLitVal::VAL_SATISFIED ? v : -1 * v, true);
			}
			std::vector<TLit> litAssump = { -1 * l };
			TToporReturnVal ret = solver->Solve(litAssump);
			if (ret == TToporReturnVal::RET_SAT)
			{
				std::vector<TToporLitVal> newAssignment = solver->GetModel();
				if (pb(newAssignment) < pb(currentAssignment))
				{
					currentAssignment = newAssignment;
					isGoodEpoch = true;
					satLits = getSatLits<TLit>(currentAssignment);
				}
			}
		}
	}

	PrintModel<TLit>(currentAssignment);
	std::cout << "Optimal value: " << pb(currentAssignment) << std::endl;
	return ret;
}

template class Topor::CToporOptimization<int32_t, uint32_t, false>;
template class Topor::CToporOptimization<int32_t, uint64_t, false>;
template class Topor::CToporOptimization<int32_t, uint64_t, true>;