#pragma once

#include <vector>

#include "ToporExternalTypes.hpp"

namespace Topor
{
	// The pseudo-boolean function for optimization mode
	double pb(std::vector<TToporLitVal> assignment)
	{
		if (assignment[1] == TToporLitVal::VAL_SATISFIED)
		{
			if (assignment[2] == TToporLitVal::VAL_SATISFIED)
			{
				return assignment[3] == TToporLitVal::VAL_SATISFIED ? 20.4 : 1.35;
			}
			else
			{
				return assignment[3] == TToporLitVal::VAL_SATISFIED ? 75 : 96.3;
			}
		}
		else
		{
			if (assignment[2] == TToporLitVal::VAL_SATISFIED)
			{
				return assignment[3] == TToporLitVal::VAL_SATISFIED ? 100.1 : 8;
			}
			else
			{
				return assignment[3] == TToporLitVal::VAL_SATISFIED ? 3.5 : 2.3;
			}
		}
	};
}