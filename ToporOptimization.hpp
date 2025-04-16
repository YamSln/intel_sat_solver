#pragma once

#include <vector>
#include <deque>
#include <iostream>

#include "Topor.hpp"
#include "ToporExternalTypes.hpp"

namespace Topor
{
	template <typename TLit = int32_t, typename TUInd = uint32_t, bool Compress = false>
	class CToporOptimization
	{
	public:
		TToporReturnVal polosat(CTopor<TLit, TUInd, Compress>* solver, double (*pb)(const std::vector<TToporLitVal>), bool anytime = false);
		
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