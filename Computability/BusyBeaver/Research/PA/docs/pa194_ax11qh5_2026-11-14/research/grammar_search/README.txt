AX11QH5 grammar-search experiments
=================================

Outcome and role in the release
------------------------------

Four completed, bounded stochastic searches found no qualifying grammar
with a proved state count below 194. The accepted PA194AX11QH5 machine is
constructed and verified elsewhere in this release. Replaying these search
experiments is optional and is not part of verifying that delivered table.

The searches made 2,307,676 proposal attempts in total and accepted 114,282
annealing moves. Every run reported zero hits. These are counts of attempted
and accepted search moves, which can repeat grammars and include inapplicable
rotation proposals. They are not counts of distinct grammars, certified
machines, or independently verified consistency constructions. The negative
result is not a state-count lower bound.

Inputs and portable preparation
-------------------------------

input.txt freezes the 135-control engine and one AX11QH5 source grammar.
Its encoded syntax contains 78 nodes including leaves, with root index 77;
compiling the initial grammar produces 67 AX-reader controls. The 13 entries
in leaf_attrs.txt give the source-shape attributes of the available macros.

prepare.py loads the frozen construction inputs through ../../construction.
It performs no network access. Its --output argument allows regenerated
inputs to be written into a fresh directory. The default remains this
search directory for compatibility, so use --output when preserving the
recorded files. Python 3 standard libraries are sufficient.

The portable preparation was replayed after fixing that import path. Both
outputs were byte-identical to the original recorded search inputs:

  input.txt       3,150 bytes
  SHA-256 aa44e0a7ec5ee2fac53ceee05f479e0323c7bd42d5b262f8565e66092d241793

  leaf_attrs.txt    181 bytes
  SHA-256 f418cbb32f295069716b9b640532c2d13374129c4c696a3e593a28a0e94a1f7f

The input is derived from the QH5 engine and the AX11 closing-emission
composition in this release, pinned to ProveIt commit
4be5c6e3a10292a7466f5d3687e3b39615ff049b.

What is varied
--------------

The search chooses a reachable, shared grammar node and applies one of the
associativity rotations

  ((a,b),c) -> (a,(b,c))
  (a,(b,c)) -> ((a,b),c).

Replacing a shared node affects all of its occurrences. The flattened macro
word is preserved. Subtrees are interned so identical subtrees share a
reader control. A pool of promising grammars and an annealing acceptance
rule permit movement across equally scored layouts and small temporary
penalties.

The source contains code for axiom-head permutations, but the corresponding
branches are disabled in these four runs. These experiments therefore do
not explore head permutations, arbitrary changes to the logical calculus,
new arithmetic-engine rows, or all possible program representations.

Two fold domains and their different scores
------------------------------------------

Write n for the number of allocated AX-reader controls and f for the number
of compatible folds selected by the scorer. The effective score is n-f.
A nonnegative scanner penalty is added to rank a grammar:

  4*bad + 4*max(m-6,0) + 4*max(mi-5,0) + max(h-38,0).

The fields are computed from the source trees in search.cpp/search_all.cpp.
They penalize disallowed macro orientations, excessive scanner demands, and
large source-path height. This heuristic is not a complete correctness
criterion.

1. AX-only runs: search.cpp includes screen.cpp. Both members of every fold
   must be newly allocated AX-reader controls. The initial grammar has
   n=67 and f=7, so its score is 60. This score omits the delivered machine's
   additional fixed-control fold 41 -> 99. Counting just the folds in this
   restricted screen gives 135+60=195; the existing extra fold produces the
   delivered 194-state table. A new grammar cannot automatically retain that
   extra fold: compatibility must be checked on its final table.

2. All-eligible-control runs: search_all.cpp includes screen_all.cpp. The
   fold candidates include fixed non-arithmetic controls as well as the new
   readers. The 23 arithmetic-engine controls remain blocked from deletion.
   Here the total proposed control count is exactly 135+n-f when the proposed
   folds are realized. The initial grammar has n=67 and f=8, so its effective
   score 59 corresponds to 194 states. Reaching at most 193 states requires
   an effective score at most 58.

Both scorers check compatibility of promising fold sets by short simultaneous
traces on the final quotient. The initial graph can therefore score 60 in
an AX-only run and 59 in an all-eligible-control run without representing
a different initial machine.

The recorded program uses effective<=58 with zero scanner penalty as its
hit condition in ALL four runs. This is conservative for the AX-only domain
if a fixed fold could subsequently be retained. Neither AX-only run found
a zero-penalty score 59: its recorded best score remained 60. Such a score
would have improved the best value and been recorded even though the hit
threshold itself is 58.

Optional exact three-increment reuse
------------------------------------

The two runs with "triple" in their names enable this compiler rewrite:

  ordered child controls (61,99) -> existing control 330.

In the frozen table the exact two rows are

  330 0 0 R 61
  330 1 1 R 99.

Control 61 supplies the one-increment macro and 99 the two-increment macro.
Thus the exact right-associated three-increment tree can reuse 330, rather
than allocate another reader. This is a dictionary reuse of existing rows,
not a claim that arbitrary triples of source instructions are interchangeable.

The actual preprocessor condition in BOTH screen sources is

  #ifdef REUSE_TRIPLE

The correct command-line flag is therefore -DREUSE_TRIPLE. The flag
-DTRIPLE by itself does not enable this optimization. The reproduction
commands below use the actual source macro.

The coefficient-five control 190 is not a four-increment macro. The obsolete
four-increment reuse rule has been disabled. This distinction is necessary
for the QH5 input; confusing those macros would invalidate the compilation.

Recorded completed runs
-----------------------

All runs requested 180 seconds. The following values come from the preserved
INITIAL and DONE lines; the reported times include small cutoff overshoots.

  ordinary: AX-only; no three-increment reuse
    Seed:                 2026111401
    Requested / reported: 180 s / 180.193 s
    Proposal attempts:    605,342
    Accepted moves:       33,219
    Initial / best score: 60 / 60
    Hits:                 0

  triple: AX-only; three-increment reuse enabled
    Seed:                 2026111402
    Requested / reported: 180 s / 180.070 s
    Proposal attempts:    841,114
    Accepted moves:       44,413
    Initial / best score: 60 / 60
    Hits:                 0

  all: all eligible non-arithmetic controls; no three-increment reuse
    Seed:                 2026111403
    Requested / reported: 180 s / 180.058 s
    Proposal attempts:    467,997
    Accepted moves:       19,783
    Initial / best score: 59 / 59
    Hits:                 0

  all_triple: all eligible non-arithmetic controls; reuse enabled
    Seed:                 2026111404
    Requested / reported: 180 s / 180.031 s
    Proposal attempts:    393,223
    Accepted moves:       16,867
    Initial / best score: 59 / 59
    Hits:                 0

  Total proposal attempts:  2,307,676
  Total accepted moves:       114,282
  Total requested time:          720 s
  Sum of reported times:     720.352 s

Each *.csv contains its header and no hit rows. Each run saved 30 terminal
search seeds as *.seedN.grammar.json. These files are unverified discovery
artifacts, not additional accepted machines. No *.hitN.grammar.json files
were produced.

Compile and rerun without replacing recorded evidence
-----------------------------------------------------

Run the following from this grammar_search directory. Use a new directory
name if replay_01 already exists. The preserved *.log, *.csv, input.txt and
leaf_attrs.txt in this directory remain unchanged.

  mkdir -p replay_01/bin replay_01/inputs replay_01/runs
  python3 -B prepare.py --output replay_01/inputs > replay_01/prepare.json
  cmp input.txt replay_01/inputs/input.txt
  cmp leaf_attrs.txt replay_01/inputs/leaf_attrs.txt

  g++ -O3 -std=c++17 search.cpp -o replay_01/bin/search_ax
  g++ -O3 -std=c++17 -DREUSE_TRIPLE search.cpp -o replay_01/bin/search_ax_triple
  g++ -O3 -std=c++17 search_all.cpp -o replay_01/bin/search_all
  g++ -O3 -std=c++17 -DREUSE_TRIPLE search_all.cpp -o replay_01/bin/search_all_triple

  replay_01/bin/search_ax replay_01/inputs/input.txt replay_01/inputs/leaf_attrs.txt replay_01/runs/ordinary 180 2026111401 > replay_01/runs/ordinary.log
  replay_01/bin/search_ax_triple replay_01/inputs/input.txt replay_01/inputs/leaf_attrs.txt replay_01/runs/triple 180 2026111402 > replay_01/runs/triple.log
  replay_01/bin/search_all replay_01/inputs/input.txt replay_01/inputs/leaf_attrs.txt replay_01/runs/all 180 2026111403 > replay_01/runs/all.log
  replay_01/bin/search_all_triple replay_01/inputs/input.txt replay_01/inputs/leaf_attrs.txt replay_01/runs/all_triple 180 2026111404 > replay_01/runs/all_triple.log

The command syntax is:

  executable input.txt leaf_attrs.txt output_prefix seconds random_seed

Each executable writes its CSV and terminal grammar seeds beside its output
prefix. It does not modify the frozen construction or machine. The screen
files are included directly by their corresponding search source; do not
compile them as separate translation units for these commands.

Because the stopping condition uses wall-clock time, exact proposal counts,
accepted counts, and terminal seed files can vary by hardware, compiler,
load, and library implementation even with the same random seed. The stated
counts describe the preserved completed logs, not a promised invariant of
all 180-second reruns. The search is optional discovery evidence; the main
machine verifier has no dependency on these counts.

Validation of this portable export
----------------------------------

The four commands were compiled with GNU g++ (Debian 14.2.0-19) 14.2.0.
All four resulting binary SHA-256 values exactly matched the executables
used for the recorded searches, confirming both source selection and the
two REUSE_TRIPLE builds. Zero-time initialization replays reproduced initial
scores 60,60,59,59. The regenerated inputs matched byte-for-byte, as recorded
above. This export check did not rerun the four 180-second searches or alter
their recorded evidence. Binary hashes and input/log identities are included
in summary.json; compiled binaries are not needed in the release.

Mathematical limits and use of a future hit
-----------------------------------------

A shared-tree rotation preserves the ordered macro word, but the macros
contain structured break/continue instructions whose resolved destinations
can depend on the surrounding tree. Consequently, preserving the word and
having zero scanner penalty do not prove source equivalence for an arbitrary
rotation. A discovered grammar still requires complete source resolution,
an appropriate source-level correctness argument, exact simultaneous-fold
certificates, literal/source runtime verification, and complete blank-start
verification. No such end-to-end proof is claimed for the saved search seeds.

If a future candidate uses three-increment reuse, its Python reconstruction
must register the exact (inc,(inc,inc)) tree as macro 330 and regenerate fold
labels for the new grammar. The saved JSON contains the expanded tree, so
simply applying the original grammar's fold labels would not reproduce the
search scorer's proposed quotient.

Provenance and scope
--------------------

The discovery engines adapt the supplied QN6 grammar-search framework to the
frozen AX11QH5 source and engine. Existing attributions and licenses are in
the release's licenses directory. This directory preserves the actual four
runs, their precise seeds and search domains. It does not imply novelty for
the underlying compiler, a formal minimality result, or an unreported
193-state construction.
