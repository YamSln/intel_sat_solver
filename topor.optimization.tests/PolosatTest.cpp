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

	void PrintModel(vector<TToporLitVal> model)
	{
		for (int i = 1; i < model.size(); i++)
		{
			if (model[i] == TToporLitVal::VAL_SATISFIED)
				cout << "1 ";
			else
				cout << "0 ";
		}
		cout << endl;
	}
};

double Seminar(vector<TToporLitVal> assignment)
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

double SumSAT(vector<TToporLitVal> assignment)
{
	int sum = 0;
	for (int i = 1; i < assignment.size(); i++)
	{
		sum += (assignment[i] == TToporLitVal::VAL_SATISFIED ? 1 : 0);
	}
	return sum;
}

TEST_F(ToporOptimizationTest, SumOfSAT) {
	CTopor topor;
	topor.AddClause({ 1, 2, 3 });
	topor.AddClause({ 2, 4, 9 });
	topor.AddClause({ 5, 7, 6, 8 });

	auto res = opt.Polosat(&topor, SumSAT);
	ASSERT_TRUE(res);

	auto [model, value] = *res;
	EXPECT_EQ(value, 2);
}

TEST_F(ToporOptimizationTest, SumOfSAT0) {
	CTopor topor;
	topor.AddClause({ 1, 2, -3 });
	topor.AddClause({ 2, -4, 9 });
	topor.AddClause({ -5, 7, 6, 8 });

	auto res = opt.Polosat(&topor, SumSAT);
	ASSERT_TRUE(res);

	auto [model, value] = *res;
	EXPECT_EQ(value, 0);
}

double WeightedVariables(vector<TToporLitVal> assignment)
{
	return
		(assignment[1] == TToporLitVal::VAL_SATISFIED ? 5 : 0) +
		(assignment[2] == TToporLitVal::VAL_SATISFIED ? 1 : 0) +
		(assignment[3] == TToporLitVal::VAL_SATISFIED ? 10 : 0);
}

TEST_F(ToporOptimizationTest, WeightedVariablePreference) {
	CTopor topor;
	topor.AddClause({ 1, 2 });
	topor.AddClause({ -1, 3 });
	topor.AddClause({ -2, -3 });

	auto res = opt.Polosat(&topor, WeightedVariables);
	ASSERT_TRUE(res);

	auto [model, value] = *res;

	EXPECT_EQ(value, 1);
	vector<int> expectedModel = { 0, 1, 0 };
	EXPECT_TRUE(ModelsEqual(model, expectedModel));
}

double XORBehavior(vector<TToporLitVal> assignment)
{
	bool a = assignment[1] == TToporLitVal::VAL_SATISFIED;
	bool b = assignment[2] == TToporLitVal::VAL_SATISFIED;
	bool out = assignment[3] == TToporLitVal::VAL_SATISFIED;

	return (a ^ b) == out ? 1 : 0;
}

TEST_F(ToporOptimizationTest, XORLogicRewarded) {
	CTopor topor;
	topor.AddClause({ -1, -2, -3 });
	topor.AddClause({ -1, 2, 3 });
	topor.AddClause({ 1, -2, 3 });
	topor.AddClause({ 1, 2, -3 });

	auto res = opt.Polosat(&topor, XORBehavior);
	ASSERT_TRUE(res);

	auto [model, value] = *res;

	EXPECT_EQ(value, 1);
}
