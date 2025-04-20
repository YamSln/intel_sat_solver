#pragma once

#include <vector>
#include <deque>
#include <iostream>
#include <optional>
#include <functional>

#include "Topor.hpp"
#include "ToporExternalTypes.hpp"

namespace Topor
{
	template <typename TLit = int32_t, typename TUInd = uint32_t, bool Compress = false>
	class CToporOptimization
	{
	public:
		std::optional<std::pair<std::vector<TToporLitVal>, double>> Polosat(CTopor<TLit, TUInd, Compress>* solver, std::function<double(const std::vector<TToporLitVal>)> pb, bool anytime = false);
		std::optional<std::pair<std::vector<TToporLitVal>, double>> StrictlyMonotonePolosat(CTopor<TLit, TUInd, Compress>* solver, std::function<double(const std::vector<TToporLitVal>)> pb, std::vector<TLit> obs, bool anytime = false);
		
	protected:
		std::deque<TLit> GetSatLits(std::vector<TToporLitVal> model)
		{
			std::deque<TLit> satLits;
			for (TLit v = 1; v < (TLit)model.size(); v++)
			{
				satLits.push_back(model[v] == TToporLitVal::VAL_SATISFIED ? v : -1 * v);
			}
			return satLits;
		}

		template <typename Container>
		std::deque<TLit> GetSatLits(std::vector<TToporLitVal> model, const Container lits)
		{
			std::deque<TLit> satLits;
			for (TLit lit : lits)
			{
				if (model[lit < 0 ? -1 * lit : lit] == TToporLitVal::VAL_SATISFIED)
				{
					if (lit > 0)
						satLits.push_back(lit);
				}
				else
				{
					if (lit < 0)
						satLits.push_back(lit);
				}
			}
			return satLits;
		}

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