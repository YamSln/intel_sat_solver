#include "pch.h"

#include <iostream>

#include "Topor.hpp"
#include "ToporOptimization.hpp"

using namespace std;
using namespace Topor;

class ToporOptimizationTest : public ::testing::Test {
protected:
	CToporOptimization<int32_t, uint32_t, false> opt;

	void SetUp() override {

	}

	void TearDown() override {

	}

	bool ModelsEqual(vector<TToporLitVal> actual, vector<int> expected)
	{
		for (int i = 1; i < actual.size(); i++)
		{
			if (actual[i] == TToporLitVal::VAL_SATISFIED && expected[i - 1] == 0 ||
				actual[i] == TToporLitVal::VAL_UNSATISFIED && expected[i - 1] == 1)
				return false;
		}
		return true;
	}
};

double Seminar(std::vector<TToporLitVal> assignment)
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

TEST_F(ToporOptimizationTest, ExampleFromSeminar) {
	CTopor topor;
	topor.AddClause({ 1, 2 });
	topor.AddClause({ 1, -3 });
	topor.AddClause({ -1, 3 });

	auto res = opt.Polosat(&topor, Seminar);
	ASSERT_TRUE(res);

	auto [model, value] = *res;
	vector<int> expectedModel = { 0, 1, 0 };
	EXPECT_TRUE(ModelsEqual(model, expectedModel));
	EXPECT_EQ(value, 8);
}