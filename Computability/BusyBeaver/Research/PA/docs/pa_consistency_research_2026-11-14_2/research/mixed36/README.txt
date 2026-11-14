Mixed-radix 3/6 source experiment
================================

Result and limits
-----------------
No machine below 194 states is obtained. Two new explicit source compilation
profiles were explored. The saved best source grammars pass an exact symbolic
emitter check, but their most favorable nominal state counts are 208 and 205.
These counts already assume that all pairwise local fold opportunities can be
used together. No such simultaneous physical quotient, complete source-to-tape
simulation, blank-tape initialization, or consistency theorem is claimed here.

The proposal uses Cantor pairing p(a,b)=(a+b)(a+b+1)/2+b and constructors

  I(a,b)=3p(a,b),         U(d,A)=3p(A,d)+2,
  M(a,b)=6p(a,b)+1,       E(a,b)=6p(a,b)+4.

The four constructor classes are disjoint. Their inverse algorithms cover every
natural number, taking 0 as the distinguished zero formula. This removes the
coding collisions of the rejected uniform coefficient-three shortcut. See
mixed36_math.tex for the mathematical scope and the remaining proof boundary.

Recorded profiles
-----------------

                            cons6             double
  Emitter macro tokens        193                206
  Fixed physical controls     139                137
  Best raw AX readers          81                 80
  Nominal matching size        12                 12
  Optimistic total            208                205
  Expanded source sites      3635               3687
  Primitive outcomes         4736               4814
  Max source path length       36                 37
  Initial greedy grammars     304                219
  Search proposals        3245431            2905346
  Accepted proposals       196168             219757
  RNG seed                   3613               3614
  Wall-time budget (s)         180                180

The inherited search reports hits relative to its original hardcoded score
threshold. Both runs recorded zero hits. That field is not a global exhaustive
search result. The counts above come from the saved grammars, audited again in
Python including the new fixed helper states in the fold-opportunity matching.

cons6 changes the existing coefficient-four constructor to coefficient three,
and adds a separately selectable coefficient-six constructor for M and E. The
pairing prefix is shared. The second constructor still requires five new fixed
reader controls: a macro-selection path plus its multiplier body. Reusing a
six-increment body alone does not supply the selection path for free.

double retains the coefficient-three constructor, then doubles its result for
the thirteen atomic constructors. It uses a three-reader doubling macro that
reuses the existing double-increment reader, at the cost of thirteen additional
macro tokens. Both profiles use no-push successful MP and the original sum
Shift guard, matching the starting N protocol. The equality offset becomes
four increments. The full 190-token baseline emitter contains 59 explicit
constructor calls (31 I, 15 U, 10 M, 3 E); two further implications are buried
in node75 and correctly keep coefficient three.

Reproduction
------------
Python 3 and a C++17 compiler are sufficient. All imported inputs required by
the commands below are included. Their origins and hashes are in PROVENANCE.json.

  python3 prepare.py
  python3 audit_profiles.py

prepare.py deterministically reconstructs both profiles' fixed native tables,
emitter words, source node dictionaries, initial grammar templates, leaf
attributes, and small adaptations of the inherited C++ search code. It does
not change the saved best grammar. audit_profiles.py checks those saved best
grammars, reconstructs raw tables and expanded source instructions, and writes
the audit JSON records. It checks exact free-constructor expressions for the
complete AX output, including all heads and the closing guard; this is not a
numerical sampling test. It does not run the physical symbolic executor.

Both scripts accept --construction-dir and --profiles-dir. prepare.py also
accepts --search-dir, whose default is upstream/nested2. For example, to avoid
overwriting included input records:

  python3 prepare.py --profiles-dir /tmp/mixed36_replay

The included replay_receipt.json records a successful rerun from these portable
inputs: all sixteen prepared files matched the original experiment byte for
byte, and both saved grammar audits succeeded. Python's generated __pycache__
files are not part of the scientific input.

Optional bounded search replay from this directory:

  g++ -O3 -std=c++17 profiles/cons6/search.cpp -o /tmp/mixed36_cons6
  /tmp/mixed36_cons6 profiles/cons6/templates.txt profiles/cons6/leaf_attrs.txt /tmp/mixed36_cons6 180 3613
  g++ -O3 -std=c++17 profiles/double/search.cpp -o /tmp/mixed36_double
  /tmp/mixed36_double profiles/double/templates.txt profiles/double/leaf_attrs.txt /tmp/mixed36_double 180 3614

These are time-bounded randomized searches, so proposal totals and discovered
grammars depend on machine speed. The archived search.log, run.best.grammar.json
and audit.json give the exact evidence used in the reported comparison. The
score penalties and target threshold are inherited heuristics, not theorems
about minimal state count. Reproduction of the substantive saved-grammar
counts does not require rerunning the searches.

Artifact interpretation
-----------------------
profiles/*/raw.native.tm are complete *unfolded* research tables with native
start 74 and halt 254. They have 220 and 217 working controls respectively.
They are not the alleged 208/205 quotient tables and must not be relabeled or
presented as verified machines of those sizes. The full physical source and
startup obligations remain unchecked.

Attribution
-----------
The source/table lineage, Python compiler and symbolic executor, and C++ search
are inherited. NOTICE.txt, PROVENANCE.json and licenses/ preserve their origins.
The new work is the mixed-radix encoding and the two concrete compiler profiles,
their emitter audit, and the bounded measurements. Nothing here establishes a
general lower bound for PA consistency machines or for this mixed encoding.
