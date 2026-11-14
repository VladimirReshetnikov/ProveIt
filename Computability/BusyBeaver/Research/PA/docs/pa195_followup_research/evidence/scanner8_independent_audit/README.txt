PA195S8 independent audit and bounded local minimization evidence
================================================================

What is certified here
----------------------
The input/ directory is a byte-for-byte copy of the alternative PA195S8
construction. It has 195 working states, two tape symbols and one separate
halting control. Its dense-table SHA-256 is:

df6ec639713c4ae7bb3656e59c833dd55ca6336a46bea8327eca639341b34662

The machine adds an eighth-zero return-scanner stage (native state 1999),
uses a different 68-reader AX grammar, and performs eight contextual folds:
135 inherited/fixed controls + 68 readers - 8 folds = 195. It is a verified
alternative at the supplied bound, not a construction below 195 states.

independent_audit_scanner8.py does not import the candidate compiler or
symbolic runtime. It independently parses the pinned Lean Tree definitions,
expands the modified source, resolves every continuation structurally, and
checks equality of all 3,700 source instructions and ordinal successors to
the original PA195 package. It also checks the exact 191-token emitter word,
the seed site, independently compiles the 203-control parent, reconstructs
the quotient table, and independently executes all 32 two-cell cases with
exact cycle detection. It compares the published local traces literally.
The local block lengths are twelve cases of length 1, eighteen of length 3,
and two of length 5.

The script checks dense/native conjugacy and all 46 unchanged inherited
register-engine rows, including the 45 premises required by the pinned
Native.boxLemmas theorem. It independently constructs the complete intended
startup tape from the physical register-file definition, then simulates both
raw and folded native tables from blank input for exactly 59,164 steps.
Both end at native control 84, head -2, with precisely the intended 66 one
cells and all other cells zero. A separate dense bytearray simulation agrees.

recheck_runtime.py deliberately reuses the pinned PA195 symbolic executor.
It is a repeated verification rather than an independently written symbolic
engine. It passes all 4,815 source contracts for both raw203 and folded195:

  raw203:    maximum 544 symbolic ticks; total 1,585,685 ticks
  folded195: maximum 568 symbolic ticks; total 1,616,840 ticks

These are finite executable certificates supporting the written transfer
argument. They are not a newly elaborated Lean/Rocq kernel theorem. The
ordinary PA consistency calibration is inherited through the common source
program and the prior PA195 argument, not recomputed from this table alone.

Bounded local deletion search
-----------------------------
screen_two_cell.py checks every working control except the start as a
possible deletion source. It uses the exact preceding-cell bit implied by
ALL incoming rows, in either direction. It checks 32,010 asymmetric aliases
whose keeper rows remain unchanged, with arbitrary finite two-cell local
execution and exact cycle detection. No alias succeeds.

It also checks all 2,784 opposite-history contextual pairs, allowing any
initial binary write, direction and existing target. The first screen
allows arbitrary finite excursions through unchanged helpers, but does
not re-enter a merged control before the target. It checks 2,194,920 initial
branch actions and finds no fold.

recursive_pairs.cpp removes that last restriction: either overwritten
keeper row may be used recursively. It assigns the two rows on demand and
checks all four local source cases, rejecting only an out-of-window read,
a wrong halt, or an exact repeated configuration. It checks all 2,784 pairs,
5,451,830 row assignments and 29,074,603 local transition steps, with no fold.
The positive-control invocation on the raw203 table rediscovers the known
2018 -> 2024 fold, with local lengths 3,1,3,1. The same recursive screen on
the original PA195 table checks 2,887 pairs and also finds no fold.

All these negative statements concern the stated two-cell transformation
families. They are not lower bounds for arbitrary machines or grammars.

Reproduction
-------------
Python 3 standard library and a C++17 compiler are sufficient. The original
PA195 reference folder must be extracted from the supplied PA195 archive;
it is the folder containing build_verify.py, source.json, vendor/, etc.
Its sibling reference_sources/ folder must remain present.

From this directory, replacing /path/to/pa195_conpa/pa195 as appropriate:

  python3 independent_audit_scanner8.py input /path/to/pa195_conpa/pa195
  python3 recheck_runtime.py input /path/to/pa195_conpa/pa195
  python3 screen_two_cell.py input/pa195_scanner8.native.tm
  g++ -O3 -std=c++17 recursive_pairs.cpp -o recursive_pairs
  ./recursive_pairs input/pa195_scanner8.native.tm recursive_pairs
  ./recursive_pairs input/unfolded203.native.tm recursive_pairs_positive_control

Receipts are JSON; the two-cell traces are in
pa195_scanner8.independent_traces.json. The native table uses native start 74
and halt 254. The dense table uses start 0 and halt 195. Direction fields in
the literal tables are L/R; the auxiliary recursive-pair action JSON uses
-1/+1 for L/R.
