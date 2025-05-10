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
		TLit maxFileVar = 0;

	public:
		TLit Insert(TLit fileVar, TLit userVar)
		{
			mapping[fileVar] = userVar;
			maxFileVar = std::max(maxFileVar, fileVar);
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
			return maxFileVar != 0 ? std::optional{ maxFileVar } : std::nullopt;
		}
	};
}