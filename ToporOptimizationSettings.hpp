#pragma once

#include <vector>
#include <any>
#include <cassert>
#include <optional>

#include "ToporExternalTypes.hpp"
#include "ToporVarMap.hpp"

namespace Topor
{
	// The pseudo-boolean function for optimization mode
	template <typename TLit = int32_t>
	double pb(std::vector<TToporLitVal> assignment, std::any userData)
	{
		static const int numClasses = 7;
		static const std::vector<int> classesPenalty = { 5, 5, 5, 4, 3, 2, 1 };
		static const int numStudents = 14;
		static const std::vector<std::vector<int>> studentTimes = {
			{1, 6}, {4, 10}, {2, 8}, {7, 12}, {5, 9}, {8, 13}, {0, 4},
			{3, 7}, {10, 15}, {12, 18}, {6, 11}, {9, 14}, {16, 19}, {17, 20}
		};

		auto Overlap = [&](int s1, int s2)
		{
			return studentTimes[s1][0] < studentTimes[s2][1] && studentTimes[s2][0] < studentTimes[s1][1];
		};

		auto MapAssignment = [&](std::vector<TToporLitVal> assignment)
		{
			if (userData.has_value())
			{
				assert(userData.type() == typeid(VarMap<TLit>*));
				VarMap<TLit>* mapping = any_cast<VarMap<TLit>*>(userData);
				auto maxVar = mapping->GetMaxMappedFileVar();
				if (maxVar != std::nullopt)
				{
					std::vector<TToporLitVal> mappedAssignment = { TToporLitVal::VAL_SATISFIED };
					for (TLit v = 1; v <= maxVar; ++v)
					{
						TLit userVar = mapping->GetUserVar(v);
						mappedAssignment.push_back(assignment[userVar]);
					}
					return mappedAssignment;
				}
			}
			return assignment;
		};

		assignment = MapAssignment(assignment);

		std::vector<int> studentsClasses;
		bool assigned;
		for (int i = 0; i < numStudents; i++)
		{
			assigned = false;
			for (int j = 1 + i * numClasses; j <= numClasses + i * numClasses; j++)
			{
				if (assignment[j] == TToporLitVal::VAL_SATISFIED)
				{
					studentsClasses.push_back((j-1) % numClasses);
					assigned = true;
					break;
				}
			}
			if (!assigned)
			{
				studentsClasses.push_back(-1);
			}
		}

		int totalPenalty = 0;
		for (int i = 0; i < studentsClasses.size(); i++)
		{
			for (int j = i + 1; j < studentsClasses.size(); j++)
			{
				if (studentsClasses[i] != -1 && studentsClasses[i] == studentsClasses[j] && Overlap(i, j))
				{
					totalPenalty += classesPenalty[studentsClasses[i]];
				}
			}
		}

		return totalPenalty;
	};
}