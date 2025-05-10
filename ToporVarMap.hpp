#pragma once

#include <unordered_map>
#include <optional>

namespace Topor
{
	template <typename TLit = int32_t>
	class VarMap
	{
	private:
		std::unordered_map<TLit, TLit> mapping;

	public:
		TLit Insert(TLit fileVar, TLit userVar)
		{
			mapping[fileVar] = userVar;
			return userVar;
		}

		TLit GetUserVar(TLit fileVar)
		{
			return mapping[fileVar];
		}

		bool MappingExists(TLit fileVar)
		{
			return mapping.find(fileVar) != mapping.end();
		}

		std::optional<TLit> GetMaxMappedFileVar()
		{
			if (mapping.empty())
			{
				return std::nullopt;
			}
			auto maxVarIt = mapping.begin();
			for (auto it = mapping.begin(); it != mapping.end(); ++it)
			{
				if (it->first > maxVarIt->first)
				{
					maxVarIt = it;
				}
			}
			return maxVarIt->first;
		}
	};
}