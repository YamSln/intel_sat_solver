#pragma once

#include <vector>
#include <deque>
#include <iostream>

#include "ToporExternalTypes.hpp"

namespace Topor
{
	class CToporOptimization
	{
	public:
		template <typename TLit, typename TUInd, bool Compress>
		TToporReturnVal polosat(CTopor<TLit, TUInd, Compress>* solver, double (*pb)(const std::vector<TToporLitVal>), bool anytime)
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
	protected:
		template <typename TLit>
		std::deque<TLit> getSatLits(std::vector<TToporLitVal> model)
		{
			std::deque<TLit> satLits;
			for (TLit v = 1; v < (TLit)model.size(); v++)
			{
				satLits.push_back(model[v] == TToporLitVal::VAL_SATISFIED ? v : -1 * v);
			}
			return satLits;
		}

		template <typename TLit>
		void PrintModel(std::vector<TToporLitVal> model)
		{
			std::cout << "v ";
			for (TLit v = 1; v < (TLit)model.size(); v++)
			{
				std::cout << (model[v] == TToporLitVal::VAL_SATISFIED ? v : -1 * v) << " ";
			}
			std::cout << std::endl;
		}

		bool AnytimeContinue(double pbVal)
		{
			std::cout << "Current objective value: " << pbVal << ". Continue? [Y/n]\n";
			char input;
			std::cin >> input;
			return std::tolower(input) == 'y';
		}
	};
}