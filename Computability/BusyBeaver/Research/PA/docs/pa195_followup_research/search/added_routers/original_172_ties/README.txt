Added-router search over 172 PA195 grammar ties
=============================================

Result
------
No construction below 195 states was found in the enumerated family. The
search starts with 172 distinct grammars retained by the earlier exact
allocator search at a 195-state score. A score tie and the inherited address
gates do not by themselves certify a new consistency machine; these 172
inputs are search seeds, not 172 independently proved PA calibrations.

For each grammar the search adds either one or two read-only history routers.
Each new control has rows (0,R,u0), (1,R,u1), with both children chosen among
old controls. New routers do not call one another. It then applies the
reference allocator's contextual folding options, using either AX readers
alone or all old controls except the start. A differing branch uses a
left step to a router, which inspects the preceding bit and returns right
to a child that realizes the desired old transition. Options are collected
from the raw table; compatible simultaneous choices are then checked in the
final quotient. The latter traces may contain additional detours introduced
by other folds.

Completed exact checks
----------------------
Mode                      Concrete router assignments checked
AX readers, one router                312
AX readers, two routers              1,376
All controls, one router              890
All controls, two routers           11,655

Every one of these optimistic candidates fails the exact simultaneous local
certificate. The modes overlap; the four counts must not be added and called
a count of distinct machines. For two routers, the optimistic-hit count in
the detailed receipt refers to pairs of signature groups; the concrete
assignment count expands each group's distinct child-state implementations.

One-router matching has an optimistic 194-state score on 24 of the 172
grammars in either mode. Two-router matching does so on 16 grammars in the
AX-only mode and 24 in the all-control mode. These are upper bounds on the
number of simultaneous folds, not certificates. None survives compatibility.

The exact checker uses every raw incoming row to establish predecessor-bit
histories. It uses exact repeated-configuration detection on the two cells,
with no finite fuel cutoff. A matching is used only to discard impossible
cases, never to assert a valid quotient. The minimum baseline optimistic
score is 194 in both modes; the minimum one-router optimistic score is also
194. Consequently, routers that provide no missing raw branch, and pairs
with identical branch-mask signatures, cannot improve the requested bound.

Native start control 74 is omitted from the router pair list. Its read-zero
row (1,R,0) is unique among read-zero rows in every one of the 172 raw tables.
In this provider family any purported replacement for that branch would
have to route back through 74 itself; after identifying the pair it loops
on the same zero branch. Thus the omitted start cannot supply an improving
fold in this particular router family. A separate arbitrary-row recursive
two-cell search on the original PA195 and PA195S8 tables includes native74;
its receipts are provided by the separate start-control audit.

Scope
-----
This is a bounded search of one/two added read-only routers with old-state
children and the stated raw provider options. It does not exclude arbitrary
extra controls, routers that call each other, longer-window transforms,
other grammars, or a differently compiled consistency proof. It is not a
lower bound for the requested mathematical construction. No candidate passes
local compatibility, so there is no new candidate requiring full source
runtime or blank-start validation in this batch.

Reproduction
------------
The input/ directory contains the two seed NDJSON files, the symbol map,
and the selected line indices. The raw tables are reconstructed from the
original PA195 package's pinned compiler inputs. Python 3 standard library
and a C++17 compiler are sufficient.

From this directory:

  g++ -O3 -std=c++17 router_filter.cpp -o router_filter
  python3 run_router_ties_cpp.py /path/to/pa195_conpa/pa195
  python3 compare_filters.py /path/to/pa195_conpa/pa195

The reference path is the original extracted directory containing
build_verify.py, vendor/, source.json, etc. Run without Python -O.
The script writes cpp_receipt.json and prints one status line per grammar.

router_filter.cpp is the fast optimistic graph filter; cpp_router_filter.py
is its subprocess bridge. router_fast_snapshot.py supplies the Python
reference filter and exact fold-set enumerator. exact_router_support.py
replaces the inherited limited-fuel checker and read-preserving incoming
filter with exact cycle detection and strict all-incoming histories.

cpp_filter_comparison.json records six independent executions comparing
complete concrete candidate-router sets between the C++ filter and Python
reference filter: one and two helpers on seeds 0,20,22. These include cases
with 40,74,373 and 1,687 optimistic concrete candidates, not only empty sets.
The detailed receipt records all 172 completed searches; cpp_summary.json
contains compact totals. SHA256SUMS pins this evidence snapshot.
