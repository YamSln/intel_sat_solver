// Copyright(C) 2021 Intel Corporation
// SPDX - License - Identifier: MIT

#ifdef DPRINT
#define DLOG(x) std::cout << "c [DPRINT] " << x << std::endl
#else
#define DLOG(x) // Compiles to literally nothing when DPRINT is off
#endif

#include <iostream>
#include <cassert>
#include <fstream>
#include <vector>
#include <array>
#include <string>
#include <filesystem>
#include <functional>
#include <cstring>
#include <iterator>
#include <cstdio>
#include <unordered_set>
#include <type_traits>
#include "algorithms/Alg_nuwls.h"
#include "algorithms/LSU.hpp"
#include "algorithms/MrsBeaver.hpp"

#ifdef __CYGWIN__
extern "C" FILE * popen(const char* command, const char* mode);
extern "C" void pclose(FILE * pipe);
#endif

#ifndef SKIP_ZLIB
#ifdef WIN32
#   include "win/zlib.h"
#else
#   include <zlib.h>
#endif
#endif
#include "SetInScope.h"

#ifdef _WIN32
#define popen _popen
#define pclose _pclose
#define fileno _fileno
#endif

template<char delimiter>
class WordDelimitedBy : public std::string
{};

namespace fs = std::filesystem;

#include "Topor.hpp"

using namespace std;
using namespace Topor;
using namespace nuwls;

// Converts enum class to the underlying type
template <typename E>
constexpr auto U(E e) noexcept
{
	return static_cast<std::underlying_type_t<E>>(e);
}

// The supported archive file types
enum class TArchiveFileType : uint8_t
{
	XZ = 0,
	LZMA = 1,
	BZ = 2,
	GZ = 3,
	SevenZ = 4,
	None = 5
};

// The supported archive file types' file signatures
constexpr uint8_t MaxSigLength = 7;
constexpr static array<array<int, MaxSigLength + 1>, U(TArchiveFileType::None)> fileSig = { {
	 { 0xFD, 0x37, 0x7A, 0x58, 0x5A, 0x00, 0x00, EOF},
	 { 0x5D, 0x00, 0x00, 0x80, 0x00, EOF, EOF, EOF},
	 { 0x42, 0x5A, 0x68, EOF, EOF, EOF, EOF, EOF },
	 { 0x1F, 0x8B, EOF, EOF, EOF, EOF, EOF, EOF },
	 { 0x37, 0x7A, 0xBC, 0xAF, 0x27, 0x1C, EOF, EOF }
} };

static constexpr bool AllSigsDifferByFirstInt()
{
	for (size_t i = 0; i < fileSig.size(); ++i)
	{
		for (size_t j = i + 1; j < fileSig.size(); ++j)
		{
			if (fileSig[i][0] == fileSig[j][0])
			{
				return false;
			}
		}
	}
	return true;
}

// We count all signatures' first integer being different in the code, which determines the file's type
static_assert(AllSigsDifferByFirstInt());

// Strings before and after the command for each archive type
static array<pair<string, string>, U(TArchiveFileType::None)> commandStringBeforeAndAfter = {
	make_pair("xz -c -d",""),
	make_pair("lzma -c -d",""),
	make_pair("bzip2 -c -d",""),
	make_pair("gzip -c -d",""),
	make_pair("7z x -so","2>/dev/null"),
};

static constexpr int BadRetVal = -1;
using TLit = int32_t;

// MaxSAT variables
bool isMaxsat = false;
unsigned long long cumulativeWeight = 0;
long long maxAllowedWeight = numeric_limits<signed long long>::max();
unsigned long long maxCumulativeWeight = numeric_limits<unsigned long long>::max();
int minAllowedWeight = 1;
long long maxLit = 0;
long long currRelaxLit;
unsigned long long bestCost = numeric_limits<unsigned long long>::max();
vector<int> globalBestModel;
bool optimal = false;

// NuWLS variables
bool enableNuwls = true;
bool isWeighted = false;
unsigned long nuwlsMaxFlips = 2000000000;
unsigned long nuwlsMaxNonImprove = 10000000;
unsigned long nuwlsTimeLimit = 15;
vector<vector<TLit>> rawHardClauses;
vector<pair<uint64_t, vector<TLit>>> rawSoftClauses;
long long lastWeight = -1;

static std::chrono::steady_clock::time_point gSolverStartTime = std::chrono::steady_clock::now();

// LSU variables
bool enableLSU = true;
int lsuTimeLimit = 120;
int lsuVerbosity = 1;

double MainWallTimePassed()
{
	return std::chrono::duration<double>(std::chrono::steady_clock::now() - gSolverStartTime).count();
}

struct TRelaxVars
{
	long long Weight;
	TLit RelaxVar;
};
vector<TRelaxVars> relaxVars;

// Mrs Beaver variables
wmb::WMBOptions wmbOptions;

template <typename TTopor>
int OnFinishingSolving(TTopor& topor, TToporReturnVal ret, bool printModel, bool printUcore, bool isMaxsat, TLit maxLit, const std::vector<TRelaxVars>& relaxVars, const std::span<TLit> assumps = {}, vector<TLit>* varsToPrint = nullptr)
{
	CApplyFuncOnExitFromScope<> printStatusExplanation([&]()
		{
			const string expl = topor.GetStatusExplanation();
			if (!expl.empty())
			{
				cout << "c " << expl << endl;
			}
		});

	switch (ret)
	{
	case Topor::TToporReturnVal::RET_SAT:
		if (isMaxsat)
		{
			unsigned long long cost = 0;
			for (const auto& rv : relaxVars)
			{
				const TToporLitVal v = topor.GetLitValue(rv.RelaxVar);
				if (v == TToporLitVal::VAL_SATISFIED)
				{
					cost += (unsigned long long)rv.Weight;
				}
			}
			bestCost = cost;
			std::cout << "c timeo " << (unsigned)std::ceil(MainWallTimePassed()) << " " << cost << std::endl;
			return 10;
		}

		cout << "s SATISFIABLE" << endl;
		if (printModel)
		{
			auto PrintVal = [&](TLit v)
				{
					const auto vVal = topor.GetLitValue(v);
					assert(vVal != TToporLitVal::VAL_UNASSIGNED);
					if (!isMaxsat) 
					{
						cout << " " << (vVal != TToporLitVal::VAL_UNSATISFIED ? v : -v);
					}
					else
					{
						cout << " " << (vVal != TToporLitVal::VAL_UNSATISFIED ? 1 : 0);
					}
				};

			cout << "v";
			if (!varsToPrint)
			{
				const TLit maxV = isMaxsat ? maxLit : topor.GetMaxUserVar();
				for (TLit v = 1; v <= maxV; ++v)
				{
					PrintVal(v);
				}
			}
			else
			{
				for (auto v : *varsToPrint)
				{
					if (!isMaxsat || v <= maxLit)
					{
						PrintVal(v);
					}
				}
			}
			if (!isMaxsat)
			{
				cout << " 0" << endl;
			}
			else
			{
				cout << endl;
			}
		}
		return 10;

	case Topor::TToporReturnVal::RET_UNSAT:
		cout << "s UNSATISFIABLE" << endl;
		if (printUcore)
		{
			cout << "v";
			for (size_t assumpInd = 0; assumpInd < assumps.size(); ++assumpInd)
			{
				TLit currAssump = assumps[assumpInd];
				if (topor.IsAssumptionRequired(assumpInd))
				{
					cout << " " << currAssump;
				}
			}
			cout << " 0" << endl;
		}
		return 20;

	case Topor::TToporReturnVal::RET_TIMEOUT_LOCAL:
		cout << "s TIMEOUT_LOCAL" << endl;
		return BadRetVal;
	case Topor::TToporReturnVal::RET_CONFLICT_OUT:
		cout << "s CONFLICT_OUT" << endl;
		return 30;
	case Topor::TToporReturnVal::RET_MEM_OUT:
		cout << "s MEMORY_OUT" << endl;
		return BadRetVal;
	case Topor::TToporReturnVal::RET_USER_INTERRUPT:
		cout << "s USER_INTERRUPT" << endl;
		return BadRetVal;
	case Topor::TToporReturnVal::RET_INDEX_TOO_NARROW:
		cout << "s INDEX_TOO_NARROW" << endl;
		return BadRetVal;
	case Topor::TToporReturnVal::RET_PARAM_ERROR:
		cout << "s PARAM_ERROR" << endl;
		return BadRetVal;
	case Topor::TToporReturnVal::RET_TIMEOUT_GLOBAL:
		cout << "s TIMEOUT_GLOBAL" << endl;
		return BadRetVal;
	case Topor::TToporReturnVal::RET_DRAT_FILE_PROBLEM:
		cout << "s DRAT_FILE_PROBLEM" << endl;
		return BadRetVal;
	case Topor::TToporReturnVal::RET_EXOTIC_ERROR:
		cout << "s EXOTIC_ERROR" << endl;
		return BadRetVal;
	default:
		cout << "s UNEXPECTED_ERROR" << endl;
		return BadRetVal;
	}
}



int main(int argc, char** argv)
{
	gSolverStartTime = std::chrono::steady_clock::now();
	if (argc == 1 || strcmp(argv[1], "-help") == 0 || strcmp(argv[1], "--help") == 0 || strcmp(argv[1], "-h") == 0)
	{
		cout << print_as_color <ansi_color_code::red>("c Usage:") << endl;
		cout << "\tc <Intel(R) SAT Solver Executable> <CNF> OPTIONAL: -M <MVal> <Param1> <Val1> <Param2> <Val2> ... <ParamN> <ValN>" << endl;
		cout << "\tc <CNF> can either be a text file or an archive file in one of the following formats: .xz, .lzma, .bz2, .gz, .7z (the test is based on the file signature)" << endl;
		cout << "\tc <CNF> is expected to be in simplified DIMACS format, used at SAT Competitions (http://www.satcompetition.org/2011/format-benchmarks2011.html) with the following optional extension to support incrementality:" << endl;
		cout << "\tc -M <Mval> : MaxSAT mode toggle (0 = SAT, 1 = MaxSAT); default = 0" << endl;
		cout << "\tc The following Intel(R) SAT Solver Executable-specific commands are also legal (ignore \"c \" below): " << endl;
		cout << "\tc r <ParamName> <ParamVal>" << endl;
		cout << "\tc ot <TimeOut> <IsCpuTimeOut>" << endl;
		cout << "\tc oc <ConflictThreshold>" << endl;
		cout << "\tc lb <BoostScoreLit> <Mult>" << endl;
		cout << "\tc lf <FixPolarityLit> <OnlyOnce>" << endl;
		cout << "\tc ll <LitToCreateInternalLit>" << endl;
		cout << "\tc lc <ClearUserPolarityInfoLit>" << endl;
		cout << "\tc b <BacktrackLevel>" << endl;
		cout << "\tc n <ConfigNumber>" << endl;
		cout << "\tc s <Lit1 <Lit2> ... <Litn>: solve under the assumptions {<Lit1 <Lit2> ... <Litn>}" << endl;
		cout << "\tc The solver parses the p cnf vars clss line, but it ignores the number of clauses and uses the number of variables as a non-mandatory hint" << endl;
		cout << print_as_color <ansi_color_code::red>("c Intel(R) SAT Solver executable parameters:") << endl;
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/solver_mode") << " : enum (0, 1, or 2); default = " << print_as_color<ansi_color_code::green>("0") << " : " << "what type of solver to use in terms of clause buffer indexing and compression: 0 -- 32-bit index, uncompressed, 1 -- 64-bit index, uncompressed, 2 -- 64-bit index, bit-array compression \n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/bin_drat_file") << " : string; default = " << print_as_color<ansi_color_code::green>("\"\"") << " : " << "path to a file to write down a binary DRAT proof\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/text_drat_file") << " : string; default = " << print_as_color<ansi_color_code::green>("\"\"") << " : " << "path to a file to write down a text DRAT proof (if more than one /topor_tool/bin_drat_file and /topor_tool/text_drat_file parameters provided, only the last one is applied, rest are ignored)\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/drat_sort_every_clause") << " : bool (0 or 1); default = " << print_as_color<ansi_color_code::green>("0") << " : " << "sort every clause in DRAT proof (can be helpful for debugging)\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/print_model") << " : bool (0 or 1); default = " << print_as_color<ansi_color_code::green>("1") << " : " << "print the models for satisfiable invocations?\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/print_ucore") << " : bool (0 or 1); default = " << print_as_color<ansi_color_code::green>("1") << " : " << "print the indices of the assumptions in the unsatisfiable core for unsatisfiable invocations (0-indexed)?\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/verify_model") << " : bool (0 or 1); default = " << print_as_color<ansi_color_code::green>("0") << " : " << "verify the models for satisfiable invocations?\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/verify_ucore") << " : bool (0 or 1); default = " << print_as_color<ansi_color_code::green>("0") << " : " << "verify the unsatisfiable cores in terms of assumptions for unsatisfiable invocations?\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/ignore_file_params") << " : bool (0 or 1); default = " << print_as_color<ansi_color_code::green>("0") << " : " << "ignore parameter settings in the input file (lines starting with 'r')?\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/allsat_models_number") << " : unsigned long integer; default = 1" << print_as_color<ansi_color_code::green>("1") << " : " << "the maximal number of models for AllSAT. AllSAT with blocking clauses over /topor_tool/allsat_blocking_variables's variables is invoked if: (1) this parameter is greater than 1; (2) the CNF format is DIMACS without Topor-specific commands; (3) /topor_tool/allsat_blocking_variables is non-empty\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/allsat_blocking_variables") << " : string; default = " << print_as_color<ansi_color_code::green>("\"\"") << " : " << "if /topor_tool/allsat_models_number > 1, specifies the variables which will be used for blocking clauses, sperated by a comma, e.g., 1,4,5,6,7,15.\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/allsat_blocking_variables_file_alg") << " : string; default = " << print_as_color<ansi_color_code::green>("3") << " : " << "if /topor_tool/allsat_models_number > 1 and our parameter > 0, read the blocking variables from the first comment line in the file (format: c 1,4,5,6,7,15), where the value means: 1 -- assign lowest internal SAT variables to blocking; 2 -- assign highest internal SAT variables to blocking; >=3 -- assign their own internal SAT variables to blocking \n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/maxsat/nuwls/enable") << " : bool (0 or 1); default = " << print_as_color<ansi_color_code::green>("1") << " : enable NuWLS local search (warm start)\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/maxsat/nuwls/max_flips") << " : unsigned long; default = " << print_as_color<ansi_color_code::green>("2000000000") << " : NUWLS max flips\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/maxsat/nuwls/max_non_improve") << " : unsigned long; default = " << print_as_color<ansi_color_code::green>("10000000") << " : NUWLS non-improve flips\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/maxsat/nuwls/time_limit") << " : unsigned long; default = " << print_as_color<ansi_color_code::green>("15") << " : NUWLS time limit (seconds)\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/maxsat/lsu/enable") << " : bool (0 or 1); default = " << print_as_color<ansi_color_code::green>("1") << " : enable weighted totalizer + linear SAT-UNSAT\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/maxsat/lsu/time_limit") << " : unsigned long; default = " << print_as_color<ansi_color_code::green>("120") << " : LSU time limit (seconds). Use 0 for no timeout.\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/maxsat/lsu/verbosity") << " : int (0 or 1); default = " << print_as_color<ansi_color_code::green>("1") << " : LSU verbosity\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/maxsat/wmb/enable") << " : bool (0 or 1); default = " << print_as_color<ansi_color_code::green>("1") << " : enable Weighted Mrs. Beaver (WMB)\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/maxsat/wmb/gtl") << " : unsigned long; default = " << print_as_color<ansi_color_code::green>("10") << " : WMB minimum iterations before attempting complete phase\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/maxsat/wmb/gt_thr") << " : unsigned long; default = " << print_as_color<ansi_color_code::green>("1000000") << " : WMB max generalized totalizer expected size threshold\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/maxsat/wmb/time_limit") << " : unsigned long; default = " << print_as_color<ansi_color_code::green>("60") << " : WMB incomplete phase time limit (seconds)\n";
		cout << "\tc " << print_as_color <ansi_color_code::cyan>("/topor_tool/maxsat/wmb/conflict_threshold") << " : unsigned long; default = " << print_as_color<ansi_color_code::green>("10000") << " : WMB conflict threshold per bit during OBV-BS\n";

		CTopor topor;
		cout << topor.GetParamsDescr();
		return 0;
	}

	cout << "c Intel(R) SAT Solver started" << endl;

	if (argc & 1)
	{
		cout << "c topor_tool ERROR: the number of arguments (excluding the executable name) must be odd. Run without parameters for more information." << endl;
		return BadRetVal;
	}

	bool isDratBinary = true;
	string dratName("");
	bool dratSortEveryClause = false;
	bool printModel = true;
	bool printUcore = false;
	bool verifyModel = false;
	bool verifyUcore = false;
	bool ignoreFileParams = false;
	unsigned long allsatModels = 0;
	vector<TLit> blockingVars;
	unsigned long allsatBlockingFromInstanceAlg = 3;
	// 0: 32-bit clause buffer index; 1: 64-bit clause buffer index; 2: 64-bit clause buffer index & bit-array-compression
	uint8_t type_indexing_and_compression = 0;

	/*
	* Identify the input file type, read it, read the parameters too
	*/

	const string inputFileName = argv[1];
	if (!filesystem::exists(inputFileName))
	{
		cout << "c topor_tool ERROR: the input file " << inputFileName << " doesn't exist" << endl;
		return BadRetVal;
	}

	// Early scan for -M (optional; default is 0 / SAT). This does not modify argv or parsing order.
	for (int currArgNum = 2; currArgNum < argc; currArgNum += 2)
	{
		const string paramNameStr = (string)argv[currArgNum];
		const string paramValStr = (string)argv[currArgNum + 1];

		if (paramNameStr != "-M")
		{
			continue;
		}

		int intVal = 0;
		try
		{
			intVal = stoi(paramValStr);
		}
		catch (...)
		{
			cout << "c topor_tool ERROR: couldn't convert -M " << paramValStr << " to an integer" << endl;
			return BadRetVal;
		}

		if (intVal != 0 && intVal != 1)
		{
			cout << "c topor_tool ERROR: -M must be 0 or 1" << endl;
			return BadRetVal;
		}

		isMaxsat = (intVal != 0);
		break;
	}

	cout << "c running in " << (isMaxsat ? "MaxSAT mode" : "SAT mode") << endl;
	// Does the signature match one of the archive types we support?

	FILE* tmp = fopen(inputFileName.c_str(), "r");
	if (tmp == nullptr)
	{
		cout << "c topor_tool ERROR: couldn't open the input file " << inputFileName << " to verify the signature" << endl;
		return BadRetVal;
	}

	TArchiveFileType aFileType = TArchiveFileType::None;

	int c = getc(tmp);
	for (size_t currType = 0; c != EOF && currType < fileSig.size() && aFileType == TArchiveFileType::None; ++currType)
	{
		const auto& currSig = fileSig[currType];

		if (c == currSig[0])
		{
			bool rightType = true;
			c = getc(tmp);
			for (uint8_t i = 1; c != EOF && currSig[i] != EOF; ++i, c = getc(tmp))
			{
				if (c != currSig[i])
				{
					rightType = false;
					break;
				}
			}

			if (rightType)
			{
				aFileType = (TArchiveFileType)currType;
				cout << "c topor_tool: file type determined to an archive file.";
#ifndef SKIP_ZLIB
				if (aFileType != TArchiveFileType::GZ)
				{
					cout << " The following command will be used to read it through a pipe : " <<
						commandStringBeforeAndAfter[U(aFileType)].first << " " << inputFileName << " " << commandStringBeforeAndAfter[U(aFileType)].second;
				}
				else
				{
					cout << " It will be read using gzlib.";
				}
#else
				cout << " The following command will be used to read it through a pipe : " <<
					commandStringBeforeAndAfter[U(aFileType)].first << " " << inputFileName << " " << commandStringBeforeAndAfter[U(aFileType)].second;
#endif
				cout << endl;
			}
		}
	}

	fclose(tmp);

	// Open the input file: it can be an archive file, in which case it is read as a pipe
	// or a plain text file, which is read as a file
#ifndef SKIP_ZLIB
	const auto useZlib = aFileType == TArchiveFileType::GZ || aFileType == TArchiveFileType::None;
	FILE* f = useZlib ? (FILE*)gzopen(inputFileName.c_str(), "r") :
		popen((commandStringBeforeAndAfter[U(aFileType)].first + " " + inputFileName + " " + commandStringBeforeAndAfter[U(aFileType)].second).c_str(), "r");
#else
	const auto useFopen = aFileType == TArchiveFileType::None;
	FILE* f = useFopen ? (FILE*)fopen(inputFileName.c_str(), "r") : popen((commandStringBeforeAndAfter[U(aFileType)].first + " " + inputFileName + " " + commandStringBeforeAndAfter[U(aFileType)].second).c_str(), "r");
#endif
	if (f == nullptr)
	{
		cout << "c topor_tool ERROR: couldn't open the input file" << endl;
		return BadRetVal;
	}

	CTopor<int32_t, uint32_t, false>* topor32 = nullptr;
	CTopor<int32_t, uint64_t, false>* topor64 = nullptr;
	CTopor<int32_t, uint64_t, true>* toporc = nullptr;

	auto AllToporsNull = [&] { return topor32 == nullptr && topor64 == nullptr && toporc == nullptr; };

	auto ToporSetParam = [&](const std::string& paramName, double newVal)
	{
		assert(!AllToporsNull());
		topor32 ? topor32->SetParam(paramName, newVal) : topor64 ? topor64->SetParam(paramName, newVal) : toporc->SetParam(paramName, newVal);
	};

	auto ToporIsError = [&]()
	{
		assert(!AllToporsNull());
		return topor32 ? topor32->IsError() : topor64 ? topor64->IsError() : toporc->IsError();
	};

	auto ToporGetStatusExplanation = [&]()
	{
		assert(!AllToporsNull());
		return topor32 ? topor32->GetStatusExplanation() : topor64 ? topor64->GetStatusExplanation() : toporc->GetStatusExplanation();
	};

	auto ToporDumpDrat = [&](std::ofstream& openedDratFile, bool isDratBinary, bool dratSortEveryClause)
	{
		assert(!AllToporsNull());
		topor32 ? topor32->DumpDrat(openedDratFile, isDratBinary, dratSortEveryClause) : topor64 ? topor64->DumpDrat(openedDratFile, isDratBinary, dratSortEveryClause) : toporc->DumpDrat(openedDratFile, isDratBinary, dratSortEveryClause);
	};

	auto ToporGetLitValue = [&](TLit l)
	{
		assert(!AllToporsNull());
		return topor32 ? topor32->GetLitValue(l) : topor64 ? topor64->GetLitValue(l) : toporc->GetLitValue(l);
	};

	auto ToporClearUserPolarityInfo = [&](TLit v)
	{
		assert(!AllToporsNull());
		topor32 ? topor32->ClearUserPolarityInfo(v) : topor64 ? topor64->ClearUserPolarityInfo(v) : toporc->ClearUserPolarityInfo(v);
	};

	auto ToporFixPolarity = [&](TLit l, bool onlyOnce = false)
	{
		assert(!AllToporsNull());
		topor32 ? topor32->FixPolarity(l, onlyOnce) : topor64 ? topor64->FixPolarity(l, onlyOnce) : toporc->FixPolarity(l, onlyOnce);
	};

	auto ToporCreateInternalLit = [&](TLit v)
	{
		assert(!AllToporsNull());
		topor32 ? topor32->CreateInternalLit(v) : topor64 ? topor64->CreateInternalLit(v) : toporc->CreateInternalLit(v);
	};

	auto ToporBoostScore = [&](TLit v, double value = 1.0)
	{
		assert(!AllToporsNull());
		topor32 ? topor32->BoostScore(v, value) : topor64 ? topor64->BoostScore(v, value) : toporc->BoostScore(v, value);
	};

	auto ToporBacktrack = [&](TLit decLevel)
	{
		assert(!AllToporsNull());
		topor32 ? topor32->Backtrack(decLevel) : topor64 ? topor64->Backtrack(decLevel) : toporc->Backtrack(decLevel);
	};

	auto ToporChangeConfigToGiven = [&](uint16_t configNum)
	{
		assert(!AllToporsNull());
		return topor32 ? topor32->ChangeConfigToGiven(configNum) : topor64 ? topor64->ChangeConfigToGiven(configNum) : toporc->ChangeConfigToGiven(configNum);
	};

	auto ToporGetLitDecLevel = [&](TLit l)
	{
		assert(!AllToporsNull());
		return topor32 ? topor32->GetLitDecLevel(l) : topor64 ? topor64->GetLitDecLevel(l) : toporc->GetLitDecLevel(l);
	};

	auto ToporSolve = [&](const std::span<TLit> assumps = {}, std::pair<double, bool> toInSecIsCpuTime = std::make_pair((std::numeric_limits<double>::max)(), true), uint64_t confThr = (std::numeric_limits<uint64_t>::max)())
	{
		assert(!AllToporsNull());
		return topor32 ? topor32->Solve(assumps, toInSecIsCpuTime, confThr) : topor64 ? topor64->Solve(assumps, toInSecIsCpuTime, confThr) : toporc->Solve(assumps, toInSecIsCpuTime, confThr);
	};

	auto ToporAddClause = [&](const std::span<TLit> c)
	{
		assert(!AllToporsNull());
		topor32 ? topor32->AddClause(c) : topor64 ? topor64->AddClause(c) : toporc->AddClause(c);
	};

	auto ToporGetSolveInvs = [&]()
	{
		assert(!AllToporsNull());
		return topor32 ? topor32->GetSolveInvs() : topor64 ? topor64->GetSolveInvs() : toporc->GetSolveInvs();
	};

	auto ToporOnFinishedSolving = [&](TToporReturnVal ret, bool printModel, bool printUcore, const std::span<TLit> assumps, vector<TLit>& varsToPrint)
		{
			return topor32 ? OnFinishingSolving(*topor32, ret, printModel, printUcore, isMaxsat, (TLit)maxLit, relaxVars, assumps, varsToPrint.empty() ? nullptr : &varsToPrint) :
				topor64 ? OnFinishingSolving(*topor64, ret, printModel, printUcore, isMaxsat, (TLit)maxLit, relaxVars, assumps, varsToPrint.empty() ? nullptr : &varsToPrint) :
				OnFinishingSolving(*toporc, ret, printModel, printUcore, isMaxsat, (TLit)maxLit, relaxVars, assumps, varsToPrint.empty() ? nullptr : &varsToPrint);
		};

	auto ToporIsAssumptionRequired = [&](size_t assumpInd)
	{
		assert(!AllToporsNull());
		return topor32 ? topor32->IsAssumptionRequired(assumpInd) : topor64 ? topor64->IsAssumptionRequired(assumpInd) : toporc->IsAssumptionRequired(assumpInd);
	};

	TToporReturnVal ret = TToporReturnVal::RET_EXOTIC_ERROR;

	ofstream dratFile;

	CApplyFuncOnExitFromScope<> onExit([&]()
	{
#ifndef SKIP_ZLIB
		useZlib ? gzclose(gzFile(f)) : pclose(f);
#else
		pclose(f);
#endif
		if (dratName != "")
		{
			dratFile.close();
		}
		delete topor32;
		delete topor64;
		delete toporc;
	});

	/*
	* File reading loop
	*/

	// Inside the loop, we expect to read either:
	// c...: a comment
	// p cnf vars clss: the header (must appear before clauses; handled as recommendation only)
	// Lit1 Lit2 ... LitN 0: 0-ended clause
	// "s Lit1 Lit2 ... LitN": solve under the given assumption

	uint64_t lineNum = 1;
	bool pLineRead = false;
	int retValBasedOnLatestSolve = BadRetVal;

	auto ReadCommaSeparatedVarList = [&](string& errMsg, const string& s)
	{
		vector<TLit> varList;
		stringstream ss;
		try
		{
			stringstream ss(s); //create string stream from the string
			while (ss.good())
			{
				string substr;
				// Get first string delimited by comma
				getline(ss, substr, ',');
				TLit l = (TLit)stoll(substr);
				if (l <= 0)
				{
					ss << "c ERROR: couldn't convert " << s << " to a variable list, since " << l << " is not a positive variable" << endl;
				}
				varList.push_back(l);
			}
		}
		catch (...)
		{
			ss << "c ERROR: couldn't convert " << s << " to a variable list" << endl;
		}

		errMsg = move(ss.str());

		return varList;
	};


	auto CreateToporInst = [&](TLit varsNumHint = 0)
	{
		pLineRead = true;

		auto CreateToporsIfRequired = [&]()
		{
			if (AllToporsNull())
			{
				if (type_indexing_and_compression == 2)
				{
					toporc = new CTopor<int32_t, uint64_t, true>(varsNumHint);
				}
				else if (type_indexing_and_compression == 1)
				{
					topor64 = new CTopor<int32_t, uint64_t, false>(varsNumHint);
				}
				else
				{
					topor32 = new CTopor<int32_t, uint32_t, false>(varsNumHint);
				}
			}
		};

		auto ParseParameters = [&]()
		{
			// Parse parameters
			for (int currArgNum = 2; currArgNum < argc; currArgNum += 2)
			{
				const string paramNameStr = (string)argv[currArgNum];
				const string paramValStr = (string)argv[currArgNum + 1];

				// -M is a front-end flag (handled before file parsing). Skip it here so it is not treated as a solver lib param.
				if (paramNameStr == "-M")
				{
					continue;
				}

				auto ReadBoolParam = [&](string& errMsg)
				{
					int intVal = 0;
					stringstream ss;
					try
					{
						intVal = stoi(paramValStr);
					}
					catch (...)
					{
						ss << "c ERROR: couldn't convert " << paramValStr << " to an integer" << endl;
					}

					if (intVal != 0 && intVal != 1)
					{
						ss << "c ERROR: " << paramValStr << " must be 0 or 1" << endl;
					}

					errMsg = move(ss.str());

					return (bool)intVal;
				};

				auto Read0to2Param = [&](string& errMsg)
				{
					int intVal = 0;
					stringstream ss;
					try
					{
						intVal = stoi(paramValStr);
					}
					catch (...)
					{
						ss << "c ERROR: couldn't convert " << paramValStr << " to an integer" << endl;
					}

					if (intVal != 0 && intVal != 1 && intVal != 2)
					{
						ss << "c ERROR: " << paramValStr << " must be 0 or 1 or 2" << endl;
					}

					errMsg = move(ss.str());

					return (uint8_t)intVal;
				};

				auto ReadULongParam = [&](string& errMsg)
				{
					unsigned long ulVal = 0;
					stringstream ss;
					try
					{
						ulVal = stoul(paramValStr);
					}
					catch (...)
					{
						ss << "c ERROR: couldn't convert " << paramValStr << " to an unsigned long" << endl;
					}

					errMsg = move(ss.str());

					return ulVal;
				};

				// /topor_tool/ prefix length
				static constexpr size_t ttPrefixLen = 12;
				if (paramNameStr.substr(0, ttPrefixLen) == "/topor_tool/")
				{
					const string param = paramNameStr.substr(ttPrefixLen, paramNameStr.size() - ttPrefixLen);
					if (param == "bin_drat_file")
					{
						dratName = paramValStr;
						isDratBinary = true;
						cout << "c /topor_tool/bin_drat_file " << dratName << endl;
					}
					else if (param == "text_drat_file")
					{
						dratName = paramValStr;
						isDratBinary = false;
						cout << "c /topor_tool/text_drat_file " << dratName << endl;
					}
					else if (param == "drat_sort_every_clause")
					{
						cout << "c /topor_tool/drat_sort_every_clause " << paramValStr << endl;
						string errMsg;
						dratSortEveryClause = ReadBoolParam(errMsg);
						if (!errMsg.empty())
						{
							cout << errMsg;
							return true;
						}
					}
					else if (param == "print_model")
					{
						cout << "c /topor_tool/print_model " << paramValStr << endl;
						string errMsg;
						printModel = ReadBoolParam(errMsg);
						if (!errMsg.empty())
						{
							cout << errMsg;
							return true;
						}
					}
					else if (param == "print_ucore")
					{
						cout << "c /topor_tool/print_ucore " << paramValStr << endl;
						string errMsg;
						printUcore = ReadBoolParam(errMsg);
						if (!errMsg.empty())
						{
							cout << errMsg;
							return true;
						}
					}
					else if (param == "verify_model")
					{
						cout << "c /topor_tool/verify_model " << paramValStr << endl;
						string errMsg;
						verifyModel = ReadBoolParam(errMsg);
						if (!errMsg.empty())
						{
							cout << errMsg;
							return true;
						}
					}
					else if (param == "verify_ucore")
					{
						cout << "c /topor_tool/verify_ucore " << paramValStr << endl;
						string errMsg;
						verifyUcore = ReadBoolParam(errMsg);
						if (!errMsg.empty())
						{
							cout << errMsg;
							return true;
						}
					}
					else if (param == "ignore_file_params")
					{
						cout << "c /topor_tool/ignore_file_params " << paramValStr << endl;
						string errMsg;
						ignoreFileParams = ReadBoolParam(errMsg);
						if (!errMsg.empty())
						{
							cout << errMsg;
							return true;
						}
					}
					else if (param == "solver_mode")
					{
						cout << "c /topor_tool/solver_mode " << paramValStr << endl;
						string errMsg;
						type_indexing_and_compression = Read0to2Param(errMsg);
						if (!errMsg.empty())
						{
							cout << errMsg;
							return true;
						}

						if (!AllToporsNull())
						{
							cout << "c topor_tool ERROR: /topor_tool/solver_mode should be provided before any other parameters" << endl;
							return true;
						}
					}
					else if (param == "allsat_models_number")
					{
						cout << "c /topor_tool/allsat_models_number " << paramValStr << endl;
						string errMsg;
						allsatModels = ReadULongParam(errMsg);
						if (!errMsg.empty())
						{
							cout << errMsg;
							return true;
						}
					}
					else if (param == "allsat_blocking_variables")
					{
						cout << "c /topor_tool/allsat_blocking_variables " << paramValStr << endl;
						string errMsg;
						blockingVars = ReadCommaSeparatedVarList(errMsg, paramValStr);
						if (!errMsg.empty())
						{
							cout << errMsg;
							return true;
						}
					}
					else if (param == "allsat_blocking_variables_file_alg")
					{
						cout << "c /topor_tool/allsat_blocking_variables_file_alg " << paramValStr << endl;
						string errMsg;
						allsatBlockingFromInstanceAlg = ReadULongParam(errMsg);
						if (!errMsg.empty())
						{
							cout << errMsg;
							return true;
						}
					}
					else if (param.rfind("maxsat/", 0) == 0)
					{
						std::string sub = param.substr(7); // after "maxsat/"
						if (sub.rfind("nuwls/", 0) == 0)
						{
							std::string p = sub.substr(6);
							if (p == "enable") { string err; enableNuwls = ReadBoolParam(err); if (!err.empty()) { cout << err; return true; } }
							else if (p == "max_flips") { string err; nuwlsMaxFlips = ReadULongParam(err); if (!err.empty()) { cout << err; return true; } }
							else if (p == "max_non_improve") { string err; nuwlsMaxNonImprove = ReadULongParam(err); if (!err.empty()) { cout << err; return true; } }
							else if (p == "time_limit") { string err; nuwlsTimeLimit = ReadULongParam(err); if (!err.empty()) { cout << err; return true; } }
							else { cout << "c ERROR: unrecognized /topor_tool/maxsat/nuwls parameter: " << p << endl; return true; }
						}
						else if (sub.rfind("lsu/", 0) == 0)
						{
							std::string p = sub.substr(4);
							if (p == "enable") { string err; enableLSU = ReadBoolParam(err); if (!err.empty()) { cout << err; return true; } }
							else if (p == "time_limit") { string err; lsuTimeLimit = (int)ReadULongParam(err); if (!err.empty()) { cout << err; return true; } }
							else if (p == "verbosity") { string err; lsuVerbosity = (int)ReadULongParam(err); if (!err.empty()) { cout << err; return true; } }
							else { cout << "c ERROR: unrecognized /topor_tool/maxsat/lsu parameter: " << p << endl; return true; }
						}
						else if (sub.rfind("wmb/", 0) == 0)
						{
							std::string p = sub.substr(4);
							if (p == "enable") { string err; wmbOptions.enable = ReadBoolParam(err); if (!err.empty()) { cout << err; return true; } }
							else if (p == "gtl") { string err; wmbOptions.gtl = (int)ReadULongParam(err); if (!err.empty()) { cout << err; return true; } }
							else if (p == "gt_thr") { string err; wmbOptions.gtThr = ReadULongParam(err); if (!err.empty()) { cout << err; return true; } }
							else if (p == "time_limit") { string err; wmbOptions.timeLimitSeconds = (int)ReadULongParam(err); if (!err.empty()) { cout << err; return true; } }
							else if (p == "conflict_threshold") { string err; wmbOptions.conflictThreshold = ReadULongParam(err); if (!err.empty()) { cout << err; return true; } }
							else { cout << "c ERROR: unrecognized /topor_tool/maxsat/wmb parameter: " << p << endl; return true; }
						}
						else
						{
							cout << "c ERROR: unrecognized /topor_tool/maxsat parameter: " << sub << endl;
							return true;
						}
					}
					else
					{
						cout << "c ERROR: unrecognized /topor_tool/ parameter: " << paramNameStr << endl;
						return true;
					}
				}
				else
				{
					CreateToporsIfRequired();
					if (AllToporsNull())
					{
						cout << "c topor_tool ERROR: couldn't create Topor instance" << endl;
						return true;
					}

					auto [paramName, paramValue] = make_pair(paramNameStr, (double)0.0);

					try
					{
						paramValue = std::stod(paramValStr);
					}
					catch (...)
					{
						cout << "c topor_tool ERROR: could not convert " << argv[currArgNum + 1] << " to double" << endl;
						return true;
					}

					ToporSetParam(paramName, paramValue);
					const bool isError = ToporIsError();
					if (isError)
					{
						const string errorDescr = ToporGetStatusExplanation();
						cout << "c ERROR in Topor parameter: " << errorDescr << endl;
						return true;
					}
				}
			}

			CreateToporsIfRequired();
			if (AllToporsNull())
			{
				cout << "c topor_tool ERROR: couldn't create Topor instance" << endl;
				return true;
			}

			return false;
		};

		if (ParseParameters()) return BadRetVal;

		if (dratName != "")
		{
			dratFile.open(dratName.c_str());
			if (dratFile.bad())
			{
				cout << "c topor_tool ERROR: couldn't open DRAT file " << dratName << endl;
				return BadRetVal;
			}
			ToporDumpDrat(dratFile, isDratBinary, dratSortEveryClause);
		}

		return 0;
	};

	// Populated if verify_model is on
	vector<vector<TLit>> vmClss;
	// Returns 10 upon success and BadRetVal upon failure
	auto VerifyModel = [&](vector<TLit>* assumps = nullptr)
	{
		// Verify the model
		cout << "c topor_tool: before verifying that the model satisfies " << (assumps == nullptr ? "the clauses" : "the assumptions and the clauses") << endl;
		if (assumps != nullptr)
		{

			// Verify the assumptions first
			for (TLit a : *assumps)
			{
				if (a != 0)
				{
					TToporLitVal v = ToporGetLitValue(a);
					if (v != TToporLitVal::VAL_SATISFIED && v != TToporLitVal::VAL_DONT_CARE)
					{
						cout << "c ERROR: assumptions " << a << " is not satisfied!" << endl;
						return BadRetVal;
					}
				}
			}
			cout << "c topor_tool: assumptions verified!" << endl;
		}
		for (vector<TLit>& cls : vmClss)
		{
			bool isVerified = false;
			for (TLit l : cls)
			{
				if (l != 0)
				{
					TToporLitVal v = ToporGetLitValue(l);
					if (v == TToporLitVal::VAL_SATISFIED || v == TToporLitVal::VAL_DONT_CARE)
					{
						isVerified = true;
						break;
					}
				}
			}
			if (!isVerified)
			{
				cout << "c ERROR: the following clause is not satisfied:";
				for (TLit l : cls)
				{
					cout << " " << l;
				}
				cout << endl;
				return BadRetVal;
			}
		}
		cout << "c topor_tool: clauses verified!" << endl;
		return 10;
	};

	constexpr size_t maxSz = (size_t)1 << 28;
	char* line = (char*)malloc(maxSz);
	if (line == nullptr)
	{
		cout << "c topor_tool ERROR: couldn't allocate " + to_string(maxSz) + " bytes for reading the lines" << endl;
		return BadRetVal;
	}

	auto ReadLine = [&](FILE* f, char* l, size_t maxChars)
	{
#ifndef SKIP_ZLIB
		return useZlib ? gzgets((gzFile)f, line, maxSz) : fgets(line, maxSz, f);
#else
		return fgets(line, (int)maxSz, f);
#endif
	};

	pair<double, bool> nextSolveToInSecIsCpuTime = make_pair(numeric_limits<double>::max(), false);
	uint64_t nextSolveConfThr = numeric_limits<uint64_t>::max();
	TLit varsInPCnf = 0;
	
	auto Solve = [&](vector<TLit>* assumpsPtr)
	{
		vector<TLit> assumpsEmpty;
		optimal = false;
		bestCost = numeric_limits<unsigned long long>::max();
		if (isMaxsat) printModel = false;
		ret = ToporSolve(assumpsPtr ? *assumpsPtr : assumpsEmpty, nextSolveToInSecIsCpuTime, nextSolveConfThr);
		nextSolveToInSecIsCpuTime = make_pair(numeric_limits<double>::max(), false);
		nextSolveConfThr = numeric_limits<uint64_t>::max();

		retValBasedOnLatestSolve = AllToporsNull() ? BadRetVal :
			topor32 ? OnFinishingSolving(*topor32, ret, printModel, printUcore, isMaxsat, (TLit)maxLit, relaxVars, assumpsPtr ? *assumpsPtr : assumpsEmpty) :
			topor64 ? OnFinishingSolving(*topor64, ret, printModel, printUcore, isMaxsat, (TLit)maxLit, relaxVars, assumpsPtr ? *assumpsPtr : assumpsEmpty) :
			OnFinishingSolving(*toporc, ret, printModel, printUcore, isMaxsat, (TLit)maxLit, relaxVars, assumpsPtr ? *assumpsPtr : assumpsEmpty);

		if (verifyModel && retValBasedOnLatestSolve == 10)
		{
			if (VerifyModel(assumpsPtr) == BadRetVal) return BadRetVal;
		}

		if (verifyUcore && retValBasedOnLatestSolve == 20)
		{
			vector<TLit> ucAssumps;
			for (unsigned i = 0; i < assumpsPtr->size() && (*assumpsPtr)[i] != 0; ++i)
			{
				cout << "Assumption #" << to_string(i) << " -- " << (*assumpsPtr)[i] << " : " << ToporIsAssumptionRequired(i) << endl;
				if (ToporIsAssumptionRequired(i))
				{
					ucAssumps.emplace_back((*assumpsPtr)[i]);
				}
			}
			ret = ToporSolve(ucAssumps, nextSolveToInSecIsCpuTime, nextSolveConfThr);
			retValBasedOnLatestSolve = AllToporsNull() ? BadRetVal :
				topor32 ? OnFinishingSolving(*topor32, ret, printModel, printUcore, isMaxsat, (TLit)maxLit, relaxVars, assumpsPtr ? *assumpsPtr : assumpsEmpty) :
				topor64 ? OnFinishingSolving(*topor64, ret, printModel, printUcore, isMaxsat, (TLit)maxLit, relaxVars, assumpsPtr ? *assumpsPtr : assumpsEmpty) :
				OnFinishingSolving(*toporc, ret, printModel, printUcore, isMaxsat, (TLit)maxLit, relaxVars, assumpsPtr ? *assumpsPtr : assumpsEmpty);
			if (retValBasedOnLatestSolve != 20)
			{
				cout << "ret == " << to_string(retValBasedOnLatestSolve) << ": UNSAT CORE BUG!!!!!\n";
				return BadRetVal;
			}
		}
		if (isMaxsat && retValBasedOnLatestSolve == 10) {
			globalBestModel.resize(currRelaxLit+1, 0);
			if(bestCost==0){optimal=true;}
			for (int i = 1; i <= currRelaxLit; ++i) {
				globalBestModel[i] = (ToporGetLitValue(i) == TToporLitVal::VAL_SATISFIED) ? 1 : 0;
			}
		}
		if (isMaxsat && enableNuwls && retValBasedOnLatestSolve == 10 && !optimal)
		{
			DLOG(">> Handing off to NuWLS. Topor's initial upper bound: " << bestCost);
			NUWLS nuwls_solver;
			nuwls_solver.problem_weighted = (int)isWeighted;
			nuwls_solver.param_max_flips = nuwlsMaxFlips;
			nuwls_solver.param_max_non_improve_flip = nuwlsMaxNonImprove;
			nuwls_solver.param_time_limit = nuwlsTimeLimit;

			int numVars = currRelaxLit - 1;
			unsigned long long topClauseWeight = cumulativeWeight + 1;

			auto built = nuwls::SanitizeAndBuildNuwlsInstance(
				numVars,
				topClauseWeight,
				rawHardClauses,
				rawSoftClauses,
				assumpsPtr);

			nuwls_solver.build_instance(
				built.numVars,
				built.numClauses,
				built.topClauseWeight,
				built.clauseLit,
				built.clauseLitCount,
				built.clauseWeight);

			nuwls_solver.settings();

			nuwls_solver.init(globalBestModel);
			unsigned long long current_cost = bestCost;

			nuwls_solver.RunLocalSearch(globalBestModel, current_cost, 1);
			if (current_cost < bestCost) {
				bestCost = current_cost;
				if (bestCost == 0) { optimal = true; }
			}
			nuwls_solver.free_memory();
		}
		bool skipLSU = false;

		// --- MRS BEAVER INCOMPLETE PHASE ---
		if (isMaxsat && wmbOptions.enable && retValBasedOnLatestSolve == 10 && !optimal)
		{
			DLOG(">> Handing off to Mrs Beaver. Current bound: " << bestCost);

			// Re-wrap solve callback to inject WMB's conflict threshold
			auto wmbSolveCb = [&](const std::vector<int32_t>& a) {
				return ToporSolve(std::span<TLit>(const_cast<TLit*>(a.data()), a.size()),
					std::make_pair(numeric_limits<double>::max(), false),
					wmbOptions.conflictThreshold);
				};
			auto getValCb = [&](int32_t l) { return ToporGetLitValue(l); };

			std::vector<lsu::TWeightedRelaxLit> wr;
			for (const auto& rv : relaxVars) {
				if (rv.Weight > 0 && rv.RelaxVar != 0)
					wr.push_back(lsu::TWeightedRelaxLit{ (int32_t)rv.RelaxVar, (uint64_t)rv.Weight });
			}

			wmb::WMBResult wmbRes = wmb::RunMrsBeaver(
				isWeighted, wr, assumpsPtr ? *assumpsPtr : std::vector<TLit>{},
				bestCost, globalBestModel, wmbSolveCb, getValCb, wmbOptions, false
			);

			if (wmbRes.bestCost < bestCost) {
				bestCost = wmbRes.bestCost;
				globalBestModel = std::move(wmbRes.bestModel01);
				if (bestCost == 0) optimal = true;
			}

			skipLSU = wmbRes.skipCompletePhase; // True if gtThr check failed
		}

		// --- LSU COMPLETE PHASE (with bad_alloc fallback) ---
		if (isMaxsat && enableLSU && !skipLSU && retValBasedOnLatestSolve == 10 && !optimal)
		{
			DLOG(">> Handing off to LSU. Bound: " << bestCost);
			lsu::TLinearSUOptions opt;
			opt.Verbose = (lsuVerbosity != 0);
			opt.TimeLimitSeconds = lsuTimeLimit;

			auto addClauseCb = [&](const std::vector<int32_t>& c) {
				ToporAddClause(std::span<TLit>(const_cast<TLit*>(c.data()), c.size()));
				};
			auto solveCb = [&](const std::vector<int32_t>& a) {
				return ToporSolve(std::span<TLit>(const_cast<TLit*>(a.data()), a.size()));
				};
			auto getValCb = [&](int32_t l) { return ToporGetLitValue(l); };

			lsu::TLinearSUResult lsuRes;

			try {
				if (!isWeighted) {
					std::vector<int32_t> ur;
					for (const auto& rv : relaxVars) {
						if (rv.Weight > 0 && rv.RelaxVar != 0) ur.push_back((int32_t)rv.RelaxVar);
					}
					uint64_t commonWeight = (lastWeight > 0) ? (uint64_t)lastWeight : 1;
					lsuRes = lsu::RunUnweightedLinearSatUnsat(
						ur, assumpsPtr ? *assumpsPtr : std::vector<TLit>{}, (int32_t)currRelaxLit, (int32_t)maxLit,
						bestCost, commonWeight, addClauseCb, solveCb, getValCb, opt);
				}
				else {
					std::vector<lsu::TWeightedRelaxLit> wr;
					for (const auto& rv : relaxVars) {
						if (rv.Weight > 0 && rv.RelaxVar != 0)
							wr.push_back(lsu::TWeightedRelaxLit{ (int32_t)rv.RelaxVar, (uint64_t)rv.Weight });
					}
					lsuRes = lsu::RunWeightedLinearSatUnsat(
						wr, assumpsPtr ? *assumpsPtr : std::vector<TLit>{}, (int32_t)currRelaxLit, (int32_t)maxLit,
						bestCost, addClauseCb, solveCb, getValCb, opt);
				}

				if (lsuRes.NextFreeVar > currRelaxLit) currRelaxLit = lsuRes.NextFreeVar;
				if (lsuRes.Improved) {
					bestCost = lsuRes.BestCost;
					globalBestModel = std::move(lsuRes.BestModel01);
				}

				if (lsuRes.LastSolveRet == Topor::TToporReturnVal::RET_UNSAT || bestCost == 0) {
					optimal = true;
					retValBasedOnLatestSolve = 30;
				}
				else if (lsuRes.LastSolveRet == Topor::TToporReturnVal::RET_TIMEOUT_LOCAL || lsuRes.LastSolveRet == Topor::TToporReturnVal::RET_TIMEOUT_GLOBAL) {
					cout << "c TIME LIMIT REACHED DURING LSU" << endl;
				}

			}
			catch (const std::bad_alloc& e) {
				// Fallback: Totalizer blew up memory. Resume Mrs. Beaver until timeout.
				cout << "c [WARNING] memory allocation failed in LSU (totalizer too large). Falling back to Mrs. Beaver incomplete loop." << endl;

				std::vector<lsu::TWeightedRelaxLit> wr;
				for (const auto& rv : relaxVars) if (rv.Weight > 0 && rv.RelaxVar != 0) wr.push_back(lsu::TWeightedRelaxLit{ (int32_t)rv.RelaxVar, (uint64_t)rv.Weight });

				auto wmbSolveCb = [&](const std::vector<int32_t>& a) {
					return ToporSolve(std::span<TLit>(const_cast<TLit*>(a.data()), a.size()), std::make_pair(numeric_limits<double>::max(), false), wmbOptions.conflictThreshold);
					};

				wmb::WMBResult wmbRes = wmb::RunMrsBeaver(
					isWeighted, wr, assumpsPtr ? *assumpsPtr : std::vector<TLit>{},
					bestCost, globalBestModel, wmbSolveCb, getValCb, wmbOptions, true // force loop
				);

				if (wmbRes.bestCost < bestCost) {
					bestCost = wmbRes.bestCost;
					globalBestModel = std::move(wmbRes.bestModel01);
					if (bestCost == 0) optimal = true;
				}
			}
		}
		if (isMaxsat && (retValBasedOnLatestSolve == 30 || retValBasedOnLatestSolve == 10) ){
			cout << "o " << bestCost << endl;
			cout << "v";
			for (int i = 1; i <= (int)maxLit; ++i) {
				cout << " " << globalBestModel[i];
			}
			cout << endl;
			cout << "s" << (optimal ? " OPTIMUM FOUND" : " SATISFIABLE") << endl;
		}
		cout << endl;
		return retValBasedOnLatestSolve;
	};

	// First pass: determine maxLit for MaxSAT mode
	if (isMaxsat)
	{
		uint64_t firstPassLineNum = 1;

		auto ParseNumberFirstPass = [](size_t& idx, const char* lineBuffer, size_t lineLen) -> long long
			{
				while (idx < lineLen && lineBuffer[idx] == ' ')
				{
					++idx;
				}
				if (idx >= lineLen)
				{
					return 0;
				}

				bool isNeg = lineBuffer[idx] == '-';
				if (isNeg)
				{
					++idx;
				}
				if (idx >= lineLen || !isdigit(lineBuffer[idx]))
				{
					return 0;
				}

				long long res = 0;
				while (idx < lineLen && isdigit(lineBuffer[idx]))
				{
					const auto currDigit = lineBuffer[idx++] - '0';
					res = res * 10 + (long long)(currDigit);
				}

				// Return absolute value - we only care about variable numbers
				return res;
			};

		while (ReadLine(f, line, maxSz) != nullptr)
		{
			const size_t len = strlen(line);
			size_t currLineI = 0;

			// Skip whitespaces
			while (currLineI < len && line[currLineI] == ' ')
			{
				++currLineI;
			}

			if (currLineI >= len || line[currLineI] == 'c' || line[currLineI] == 'r' ||
				line[currLineI] == 'o' || line[currLineI] == 'l' || line[currLineI] == 'b' ||
				line[currLineI] == 'n' || line[currLineI] == 'p' || line[currLineI] == 's')
			{
				++firstPassLineNum;
				continue;
			}

			// Process clause line (either 'h' for hard clause or weight for soft clause)
			if (line[currLineI] == 'h')
			{
				++currLineI;
			}
			else
			{
				// Skip weight
				long long weight = ParseNumberFirstPass(currLineI, line, len);
				// Bounds check for weight
				if (weight < minAllowedWeight || weight > maxAllowedWeight)
				{
					cout << "c topor_tool ERROR: Clause weight range violated in line " << to_string(firstPassLineNum) << endl;
					free(line);
					return BadRetVal;
				}
			}

			// Parse literals to find max
			long long currLit = numeric_limits<long long>::max();
			while (currLit != 0)
			{
				currLit = ParseNumberFirstPass(currLineI, line, len);
				if (currLit != 0)
				{
					// Bounds check for literal
					if (currLit > numeric_limits<TLit>::max() || currLit < numeric_limits<TLit>::min())
					{
						cout << "c topor_tool ERROR: the literal " << to_string(currLit) << " is too big or too small at line " << to_string(firstPassLineNum) << endl;
						free(line);
						return BadRetVal;
					}
					// Take absolute value for max calculation
					long long absLit = currLit < 0 ? -currLit : currLit;
					maxLit = max(maxLit, absLit);
				}
			}

			++firstPassLineNum;
		}

		// Reset file position for second pass
#ifndef SKIP_ZLIB
		if (useZlib)
		{
			// For gzip files, use gzseek
			gzseek((gzFile)f, 0, SEEK_SET);
		}
		else
		{
			// For pipes (compressed archives), must reopen
			pclose(f);
			f = popen((commandStringBeforeAndAfter[U(aFileType)].first + " " + inputFileName + " " + commandStringBeforeAndAfter[U(aFileType)].second).c_str(), "r");
			if (f == nullptr)
			{
				cout << "c topor_tool ERROR: couldn't reopen the input file for second pass" << endl;
				free(line);
				return BadRetVal;
			}
		}
#else
		if (useFopen)
		{
			// For regular files, use rewind
			rewind(f);
		}
		else
		{
			// For pipes (compressed archives), must reopen
			pclose(f);
			f = popen((commandStringBeforeAndAfter[U(aFileType)].first + " " + inputFileName + " " + commandStringBeforeAndAfter[U(aFileType)].second).c_str(), "r");
			if (f == nullptr)
			{
				cout << "c topor_tool ERROR: couldn't reopen the input file for second pass" << endl;
				free(line);
				return BadRetVal;
			}
		}
#endif

		lineNum = 1; // Reset line number for second pass
		currRelaxLit = maxLit + 1;
	}

	while (ReadLine(f, line, maxSz) != nullptr)
	{
		const size_t len = strlen(line);
		CApplyFuncOnExitFromScope<> beforeNextLoop([&]() { ++lineNum; });

		size_t currLineI = 0;
		auto SkipWhitespaces = [&]()
			{
				while (line[currLineI] == ' ' && currLineI < len)
				{
					++currLineI;
				}
			};

		SkipWhitespaces();
		if (currLineI >= len)
		{
			// Empty line
			continue;
		}

		if (line[currLineI] == 'c')
		{
			// A comment
			if (allsatModels > 1 && allsatBlockingFromInstanceAlg > 0 && blockingVars.empty())
			{
				string errMsg, blockingVarsStr;
				blockingVarsStr.assign(line + 2, line + strlen(line));
				blockingVars = ReadCommaSeparatedVarList(errMsg, blockingVarsStr);
				if (!errMsg.empty() || blockingVars.empty())
				{
					throw logic_error("c topor_tool ERROR: expected the first comment to contain blocking variables at line number " + to_string(lineNum) + ". Error message: " + errMsg);
				}

				if (allsatBlockingFromInstanceAlg == 1)
				{
					for (TLit l : blockingVars)
					{
						ToporCreateInternalLit(l);
					}
				}

				if (allsatBlockingFromInstanceAlg == 2)
				{
					unordered_set<TLit> blockingVarsSet(blockingVars.begin(), blockingVars.end());
					for (TLit l = 1; l < varsInPCnf; ++l)
					{
						if (blockingVarsSet.find(l) == blockingVarsSet.end())
						{
							ToporCreateInternalLit(l);
						}
					}
				}
			}
			continue;
		}

		if (line[currLineI] == 'r')
		{
			if (!ignoreFileParams)
			{
				string lStr = line;

				const size_t paramNameStart = 2;
				const size_t paramNameEnd = lStr.find(' ', 2);
				if (paramNameEnd == string::npos)
				{
					throw logic_error("c topor_tool ERROR: expected <paramName> never ended at line number " + to_string(lineNum));
				}
				const string paramName = lStr.substr(paramNameStart, paramNameEnd - paramNameStart);
				const string paramVal = lStr.substr(paramNameEnd + 1);

				double paramValDouble = numeric_limits<double>::infinity();
				try
				{
					paramValDouble = stod(paramVal);
				}
				catch (...)
				{
					throw logic_error("c topor_tool ERROR: couldn't convert the parameter value to double at line number " + to_string(lineNum));
				}

				ToporSetParam(paramName, paramValDouble);
			}

			continue;
		}

		if (line[currLineI] == 'o')
		{
			string lStr = line;

			// cout << "\tc ot <TimeOut> <IsCpuTimeOut>" << endl;
			// cout << "\tc oc <ConflictThreshold>" << endl;
			if (lStr[1] != 't' && lStr[1] != 'c')
			{
				throw logic_error("c topor_tool ERROR: The 2nd character must be either t or c at line number " + to_string(lineNum));
			}

			if (lStr[2] != ' ')
			{
				throw logic_error("c topor_tool ERROR: The 3nd character must be a space at line number " + to_string(lineNum));
			}

			if (lStr[1] == 't')
			{
				const size_t toNameStart = 2;
				const size_t toNameEnd = lStr.find(' ', 3);
				if (toNameEnd == string::npos)
				{
					throw logic_error("c topor_tool ERROR: expected <TimeOut> <IsCpuTimeOut> at line number " + to_string(lineNum));
				}
				const string toStr = lStr.substr(toNameStart, toNameEnd - toNameStart);
				double to = numeric_limits<double>::infinity();
				try
				{
					to = stod(toStr);
				}
				catch (...)
				{
					throw logic_error("c topor_tool ERROR: couldn't convert <TimeOut> to double at line number " + to_string(lineNum));
				}

				const string isCpuTimeOutStr = lStr.substr(toNameEnd + 1);
				int isCpuTimeOut = numeric_limits<int>::max();
				try
				{
					isCpuTimeOut = stoi(isCpuTimeOutStr);
				}
				catch (...)
				{
					throw logic_error("c topor_tool ERROR: couldn't convert <IsCpuTimeOut> to int at line number " + to_string(lineNum));
				}

				if (isCpuTimeOut < 0 || isCpuTimeOut > 1)
				{
					throw logic_error("c topor_tool ERROR: couldn't convert <IsCpuTimeOut> to 0 or 1 at line number " + to_string(lineNum));
				}
				nextSolveToInSecIsCpuTime = make_pair(to, (bool)isCpuTimeOut);
			}
			else
			{
				assert(lStr[1] == 'c');
				const string cThrStr = lStr.substr(3);

				try
				{
					nextSolveConfThr = (uint64_t)stoull(cThrStr);
				}
				catch (...)
				{
					throw logic_error("c topor_tool ERROR: couldn't convert <ConflictThreshold> to uint64_t at line number " + to_string(lineNum));
				}
			}

			continue;
		}

		auto ParseNumber = [&]()
			{
				SkipWhitespaces();
				if (currLineI >= len)
				{
					throw logic_error("c topor_tool ERROR: no number after skipping white-spaces at line number " + to_string(lineNum));
				}
				bool isNeg = line[currLineI] == '-';
				if (isNeg)
				{
					++currLineI;
				}
				if (!isdigit(line[currLineI]))
				{
					throw logic_error("c topor_tool ERROR: the first character is expected to be a digit at line number " + to_string(lineNum));
				}

				long long res = 0;

				while (isdigit(line[currLineI]))
				{
					const auto currDigit = line[currLineI++] - '0';
					res = res * 10 + (long long)(currDigit);
				}

				if (isNeg)
				{
					res = -res;
				}

				return res;
			};

		if (line[currLineI] == 'l')
		{
			string lStr = line;

			// cout << "\tc lb <BoostScoreLit> <Mult>" << endl;
			// cout << "\tc lf <FixPolarityLit> <OnlyOnce>" << endl;
			// cout << "\tc lc <ClearUserPolarityInfoLit>" << endl;
			// cout << "\tc ll <LitToCreateInternalLit>" << endl;
			if (lStr[1] != 'b' && lStr[1] != 'f' && lStr[1] != 'c' && lStr[1] != 'l')
			{
				throw logic_error("c topor_tool ERROR: The 2nd character must be either b or f or c at line number " + to_string(lineNum));
			}

			if (lStr[2] != ' ')
			{
				throw logic_error("c topor_tool ERROR: The 3nd character must be a space at line number " + to_string(lineNum));
			}

			currLineI += 2;
			TLit lit = (TLit)ParseNumber();

			if (lStr[1] == 'c')
			{
				ToporClearUserPolarityInfo(lit);
			}
			else if (lStr[1] == 'f')
			{
				const string isOnlyOnceStr = lStr.substr(currLineI + 1);
				int isOnlyOnce = numeric_limits<int>::max();
				try
				{
					isOnlyOnce = stoi(isOnlyOnceStr);
				}
				catch (...)
				{
					throw logic_error("c topor_tool ERROR: couldn't convert <FixPolarityLit> to int at line number " + to_string(lineNum));
				}

				if (isOnlyOnce < 0 || isOnlyOnce > 1)
				{
					throw logic_error("c topor_tool ERROR: couldn't convert <FixPolarityLit> to 0 or 1 at line number " + to_string(lineNum));
				}
				ToporFixPolarity(lit, (bool)isOnlyOnce);
			}
			else if (lStr[1] == 'l')
			{
				ToporCreateInternalLit(lit);
			}
			else
			{
				assert(lStr[1] == 'b');
				const string multStr = lStr.substr(currLineI + 1);

				double mult = numeric_limits<double>::infinity();
				try
				{
					mult = stod(multStr);
				}
				catch (...)
				{
					throw logic_error("c topor_tool ERROR: couldn't convert the <Mult> value to double at line number " + to_string(lineNum));
				}

				ToporBoostScore(lit, mult);
			}

			continue;
		}

		if (line[currLineI] == 'b')
		{
			// cout << "\tc b <BacktrackLevel>" << endl;
			if (line[1] != ' ')
			{
				throw logic_error("c topor_tool ERROR: The 2nd character must be a space at line number " + to_string(lineNum));
			}

			++currLineI;
			auto dl = ParseNumber();

			ToporBacktrack((TLit)dl);

			continue;
		}

		if (line[currLineI] == 'n')
		{
			// cout << "\tc n <ConfigNum>" << endl;
			if (line[1] != ' ')
			{
				throw logic_error("c topor_tool ERROR: The 2nd character must be a space at line number " + to_string(lineNum));
			}

			++currLineI;
			auto configNum = ParseNumber();
			if (configNum < 0 || configNum > numeric_limits<uint16_t>::max())
			{
				throw logic_error("c topor_tool ERROR: The configuration number " + to_string(configNum) + " must be a uint_16 integer at line number " + to_string(lineNum));
			}

			string str = ToporChangeConfigToGiven((uint16_t)configNum);

			// Erase all Occurrences of given substring from main string.
			auto EraseAllSubStr = [&](string& mainStr, const string& toErase)
				{
					size_t pos = std::string::npos;
					// Search for the substring in string in a loop until nothing is found
					while ((pos = mainStr.find(toErase)) != std::string::npos)
					{
						// If found then erase it from string
						mainStr.erase(pos, toErase.length());
					}
				};

			EraseAllSubStr(str, "/topor");

			cout << "c converted configuration number " << to_string(configNum) << " to parameters " << str << endl;

			continue;
		}

		if (line[currLineI] == 'p')
		{
			if (isMaxsat)
			{
				cout << "c topor_tool ERROR: MaxSAT format should not contain a p line (found at line number " << lineNum << "). Run in SAT mode or update the file";
				return BadRetVal;
			}
			if (pLineRead)
			{
				cout << "c topor_tool ERROR: second line starting with p at line number " << lineNum << endl;
				return BadRetVal;
			}

			currLineI += 6;
			// currLineI should be at the first number now
			if (line[currLineI - 5] != ' ' || line[currLineI - 4] != 'c' || line[currLineI - 3] != 'n' || line[currLineI - 2] != 'f' || line[currLineI - 1] != ' ')
			{
				cout << "c topor_tool ERROR: couldn't parse the p-line as 'p cnf <VARS> <CLSS>' at line number " << lineNum << endl;
				return BadRetVal;
			}

			try
			{
				long long varsLL = ParseNumber();
				long long clssLL = ParseNumber();
				cout << "c topor_tool: suggested #variables : " << varsLL << "; suggested #clauses : " << clssLL << endl;
				if (varsLL > numeric_limits<TLit>::max() || varsLL <= 0)
				{
					cout << "c topor_tool warning: the suggested #variables " << varsLL << " is greater than the maximal number or is <=0, thus it will be ignored" << endl;
				}
				else
				{
					varsInPCnf = (TLit)varsLL;
				}
			}
			catch (const logic_error& le)
			{
				cout << "c topor_tool ERROR: couldn't parse the p-line as 'p cnf <VARS> <CLSS>': " << le.what() << " at line number " << lineNum << endl;
				return BadRetVal;
			}
			catch (...)
			{
				cout << "c topor_tool ERROR: couldn't parse the p-line as 'p cnf <VARS> <CLSS>': couldn't read the variables or the clauses at line number " << lineNum << endl;
				return BadRetVal;
			}

			SkipWhitespaces();
			if (line[currLineI] != '\n')
			{
				cout << "c topor_tool ERROR: couldn't parse the p-line as 'p cnf <VARS> <CLSS>': new-line wasn't found where expected at line number " << lineNum << endl;
				return BadRetVal;
			}

			assert(AllToporsNull());
			if (CreateToporInst(varsInPCnf) == BadRetVal)
			{
				return BadRetVal;
			}

			continue;
		}

		// If we're here and topor is still missing, create it without the number-of-variables hint -- no p-line is expected anymore
		if (AllToporsNull())
		{
			if (CreateToporInst() == BadRetVal)
			{
				return BadRetVal;
			}
		}

		vector<TLit> lits;

		auto BufferToLits = [&]()
			{
				string errorString = "";

				lits.clear();

				long long currLit = numeric_limits<long long>::max();
				while (currLit != 0)
				{
					try
					{
						currLit = ParseNumber();
						if (currLit > numeric_limits<TLit>::max() || currLit < numeric_limits<TLit>::min())
						{
							errorString = "c topor_tool ERROR: the literal " + to_string(currLit) + " is too big or too small\n";
							lits.clear();
							break;
						}
						maxLit = max(maxLit, currLit);
						lits.push_back(TLit(currLit));
					}
					catch (...)
					{
						errorString = "c topor_tool ERROR: couldn't translate the following line or parts of it into a vector of literals at line number " + to_string(lineNum) + "\n";
						lits.clear();
						break;
					}
				}

				return make_pair(errorString, lits);
			};

		if (line[currLineI] == 's')
		{
			++currLineI;
			SkipWhitespaces();

			auto [errString, assumps] = BufferToLits();
			if (!errString.empty())
			{
				cout << errString;
				return BadRetVal;
			}

			if (Solve(&assumps) == BadRetVal)
			{
				return BadRetVal;
			}
			continue;
		}

		// New SAT clause
		if (!isMaxsat)
		{
			auto [errString, cls] = BufferToLits();
			if (!errString.empty())
			{
				cout << errString;
				return BadRetVal;
			}
			if (verifyModel)
			{
				vmClss.push_back(cls);
			}
			ToporAddClause(cls);
		}
		// new MaxSAT clause
		else
		{
			if (line[currLineI] == 'h')
			{
				currLineI++;
				SkipWhitespaces();
				auto [errString, cls] = BufferToLits();
				if (!errString.empty())
				{
					cout << errString;
					return BadRetVal;
				}
				if (verifyModel)
				{
					vmClss.push_back(cls);
				}
				rawHardClauses.push_back(cls);
				ToporAddClause(cls);
			}
			else
			{
				if (currRelaxLit > numeric_limits<TLit>::max())
				{
					cout << "c topor_tool ERROR: failed to assign relaxation literal " << to_string(currRelaxLit) << " in line " << to_string(lineNum)<<", out of range\n";
					lits.clear();
					return BadRetVal;
				}
				auto weight = ParseNumber();
				if (weight < minAllowedWeight || weight > maxAllowedWeight)
				{
					cout << "c topor_tool ERROR: Clause weight range violated in line " << to_string(lineNum);
					return BadRetVal;
				}
				else if (maxAllowedWeight - cumulativeWeight < weight)
				{
					cout << "c topor_tool ERROR: Cumulative weight limit exceeded in line " << to_string(lineNum);
					return BadRetVal;

				}
				if (lastWeight == -1) lastWeight = weight;
				if (weight != lastWeight) isWeighted = true;

				cumulativeWeight += weight;
				SkipWhitespaces();
				auto [errString, cls] = BufferToLits();
				if (!errString.empty())
				{
					cout << errString;
					return BadRetVal;
				}
				rawSoftClauses.push_back({ weight, cls });
				cls.pop_back();
				cls.push_back(TLit(currRelaxLit));
				cls.push_back(0);
				relaxVars.push_back({ weight, TLit(currRelaxLit) });
				ToporFixPolarity(-TLit(currRelaxLit), false);
				currRelaxLit++;

				if (verifyModel)
				{
					vmClss.push_back(cls);
				}
				ToporAddClause(cls);
			}
		}
	}

	free(line);

	if (!AllToporsNull() && ToporGetSolveInvs() == 0)
	{
		if (allsatModels > 1 && !blockingVars.empty())
		{
			vector<TLit> assumpsEmpty;
			ret = ToporSolve();
			retValBasedOnLatestSolve = ToporOnFinishedSolving(ret, printModel, printUcore, assumpsEmpty, blockingVars);
			if (verifyModel && retValBasedOnLatestSolve == 10)
			{
				if (VerifyModel() == BadRetVal) return BadRetVal;
			}

			vector<TLit> cls;
			for (unsigned long currModelNum = 1; currModelNum < allsatModels && retValBasedOnLatestSolve == 10; ++currModelNum)
			{
				cout << "c topor_tool: before adding a blocking clause and calling the solver for time " << currModelNum + 1 << " out of " << allsatModels << endl;
				cls.clear();
				cls.reserve(blockingVars.size());
				for (TLit v : blockingVars)
				{
					TToporLitVal toporLitVal = ToporGetLitValue(v);
					assert(toporLitVal != TToporLitVal::VAL_UNASSIGNED);
					cls.push_back(toporLitVal == TToporLitVal::VAL_SATISFIED ? -v : v);
				}
				ToporAddClause(cls);
				ret = ToporSolve();
				retValBasedOnLatestSolve = ToporOnFinishedSolving(ret, printModel, printUcore, assumpsEmpty, blockingVars);
				if (verifyModel && retValBasedOnLatestSolve == 10)
				{
					if (VerifyModel() == BadRetVal) return BadRetVal;
				}
			}
		}
		else
		{
			if (Solve(nullptr) == BadRetVal)
			{
				return BadRetVal;
			}
		}

	}

	return retValBasedOnLatestSolve;
}
