#pragma once

#include <vector>

#include "ToporExternalTypes.hpp"

namespace Topor
{
	// The pseudo-boolean function for optimization mode
	double pb(std::vector<TToporLitVal> assignment)
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

		std::vector<int> studentsClasses;
		for (int i = 0; i < numStudents; i++)
		{
			for (int j = 1 + i * numClasses; j <= numClasses + i * numClasses; j++)
			{
				if (assignment[j] == TToporLitVal::VAL_SATISFIED)
				{
					studentsClasses.push_back((j-1) % numClasses);
					break;
				}
			}
		}

		

		int totalPenalty = 0;
		for (int i = 0; i < studentsClasses.size(); i++)
		{
			for (int j = i + 1; j < studentsClasses.size(); j++)
			{
				
				if (studentsClasses[i] == studentsClasses[j] && Overlap(i, j))
				{
					totalPenalty += classesPenalty[studentsClasses[i]];
				}
				
			}
		}

		return totalPenalty;
	};
}