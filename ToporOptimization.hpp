#pragma once

#include <vector>
#include <deque>
#include <optional>
#include <functional>
#include <tuple>

#include "Topor.hpp"
#include "ToporExternalTypes.hpp"
#include "ToporVarMap.hpp"

namespace Topor
{
	template <typename TLit = int32_t, typename TUInd = uint32_t, bool Compress = false>
	class CToporOptimization
	{
	public:
		std::optional<std::tuple<TToporReturnVal, std::vector<TToporLitVal>, double>> Polosat(CTopor<TLit, TUInd, Compress>* solver, std::function<double(const std::vector<TToporLitVal>)> pb, std::vector<TLit> assumps = {}, VarMap<TLit>* mapping = nullptr);
		std::optional<std::tuple<TToporReturnVal, std::vector<TToporLitVal>, double>> StrictlyMonotonePolosat(CTopor<TLit, TUInd, Compress>* solver, std::function<double(const std::vector<TToporLitVal>)> pb, std::vector<TLit> obs, std::vector<TLit> assumps = {}, VarMap<TLit>* mapping = nullptr);
		
	protected:
		std::deque<TLit> GetSatLits(std::vector<TToporLitVal> model)
		{
			std::deque<TLit> satLits;
			for (TLit v = 1; v < (TLit)model.size(); v++)
			{
				satLits.push_back(model[v] == TToporLitVal::VAL_SATISFIED ? v : -v);
			}
			return satLits;
		}

		template <typename Container>
		std::deque<TLit> GetSatLits(std::vector<TToporLitVal> model, const Container lits)
		{
			std::deque<TLit> satLits;
			for (TLit lit : lits)
			{
				if (model[lit < 0 ? -lit : lit] == TToporLitVal::VAL_SATISFIED)
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
	};
}