Additional physical reduction searches
=====================================

These searches did not establish a machine below 194 states. They are separate
from the accepted optional PA194CSZ construction. All negative statements below
are confined to the supplied template, contexts and bounds, not lower bounds.

1. Exact closure under the bounded local quotient rule

Starting with the 202-control CSZ parent, the all-control first-action rewrite
rule at radius 5 and up to 300 local transitions generated exactly 576 distinct
tables and exhausted its queue. Four endpoints have 194 controls; none has fewer.
The rule computes conservative windows reachable from native start 74 on arbitrary
initial tapes, then requires each replacement to reproduce the old single-step
endpoint and complete local tape. Every changed control except start 74 is allowed.

2. Neutral helper rewrites before quotient search

All 459 nonidentity choices of two individually verified equivalent action rows
at a single control of CSZ were enumerated. Every resulting table was screened
again for a state-pair quotient. No candidate pair was emitted. The neutral paths
avoid revisiting the changed control before reaching the old one-step endpoint,
so the two row choices compose. This permits helper behaviors under new contexts
that pure state-pair closure does not explore.

3. Scanner-chain permutations

The nine physical register-selection counters were permuted on CSZ and on a
cached I-tree zero-jump seed. All 36 simple transpositions were screened on each
basis, followed by fixed-seed random distinct orders until the 90-second budget.
The recorded run checked 1,275 tables, and none yielded a local quotient at
radius 5 / 300. These permutations were search seeds only; no unchecked permutation
is presented as a consistency machine. Exact source-frame and blank initialization
checks would still be required for a surviving reduction.

4. More proved-zero jumps and a startup counterexample

The source invariant permits replacing all eight guard/cleanup node1 jumps by
a decrement of logical register 3 (A), and permits four zero-register choices
at the axiom tail. Nine CSZ-based and ten cached-I-based variants pass the
construction-level universal physical checker and whole-tape startup. They stay
at 194 and are exploratory same-size tables, without a new independent replay.
Their successful receipts and scope are preserved; they are not primary results.

Replacing node1 jumps by decX (register 6) is a useful rejected case. It preserves
the source execution from the clean logical seed and passes universal source
contracts, but the literal blank machine halts after 1,361 steps. This happens before
native 2066/read 1, so every tested AX-tail choice has the same early halt. The
counterexample is supplied as inputs/REJECTED_node1_X.native.tm. It illustrates
why a clean-source invariant cannot be applied retroactively to initialization.
The suggested dec7 entry 62 at the axiom tail fails its zero physical branch and
is also excluded.

Optional reproduction, from this directory (C++17 and Python 3 required):

  g++ -O3 -std=c++17 action_merge_all.cpp -o action_merge_all
  python3 quotients_all.py inputs/csz_raw202.native.tm fresh_closure 10000

  g++ -O3 -std=c++17 action_neutral.cpp -o action_neutral
  ./action_neutral pa194CSZ.native.tm 5 300 > csz_neutral.jsonl
  python3 neutral_fold.py

  python3 scanner_permutations.py

The scanner run is time bounded, so a replay can have a different tested-table
count. The checked.json receipt freezes the exact orders from the recorded run.
The source-invariant positive variants are research evidence, not included here
as additional accepted output machines. The complete optional CSZ companion is in ../pa194CSZ. It has its own
independent verifier and source invariant. See its README.txt for reproduction.

Portability notes
-----------------

The Python programs locate all fixed input files and the compiled action_merge_all
executable relative to their own directory, so they can be called from another
working directory. The compilation commands above assume this directory as the
working directory. Newly generated search files are written under generated/.
No executable binary is shipped; build the C++ executable before optional searches.
Historical receipts and logs deliberately retain their original temporary paths
as provenance. Those paths are not runtime dependencies. research_summary.json
uses the packaged relative paths. The counterexample replay is inexpensive:

  python3 -B check_rejected.py
