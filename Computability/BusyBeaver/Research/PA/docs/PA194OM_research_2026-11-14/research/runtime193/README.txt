RUNTIME193: ALL-START ALLOCATION THEOREM AND UNRESTRICTED ONE-ROW REPAIR SCREEN

Result: no new 193-state blank-start consistency machine is claimed. This
folder documents an exact new obstruction for a narrowly specified family,
and a broader finite bootstrap search. research_notes.tex is an editable
report section with the proof, counts, comparison to prior searches, and
explicit limits.

EXACT THEOREM
allocation_all_starts.py replays the inherited 193-state table under all
193 initial controls and all 9! physical selector permutations. Only the 11
specified external selector targets may change. The 70,035,840 cases split
into 725,760 finite halts, 3,628,800 all-zero cycles, and 65,681,280 outward rays.
The complete proof certificate has 193 zero-prefix records and 16 adaptive
allocation leaves. No fuel exhaustion is used in this theorem. All
certificates are reached within 94 transitions; the finite prefixes contain
at most 5 one-cells. A clean source frame needs at least 12.

This extends the supplied native 74 allocation obstruction to all starts.
It is not a general 193-state lower bound. It does not exclude other
bootstrap rows, tape representations, source programs, or runtime tables.

FINITE SEARCH
pair_startup.cpp was used in its max_edits=1 mode to screen 297,607 arbitrary
single-row rewrites with working-state destinations. The unchanged table is
also included. Every initial control is covered by its first write of 1.
Every clean frame at any of 3,673 source sites is accepted, regardless of the
nine register values; logical seed correctness is a separate question.

Clock checkpoints are t < 200000. Runs also stop after head displacement or
one-cell count exceeds 20,000. All 198 recorded complete-frame hits replay
exactly. They represent 163 edits; none was validated as a repair. See the
LaTeX note for the 97 marker-test failures, 66 symbolic-contract failures,
and the concrete countercheck classifications. Failure to close within a
finite test is never labeled a divergence proof.

PORTABLE QUICK REPLAY
Python 3.10+; standard library only. Keep assertions enabled.

  python3 -B allocation_all_starts.py
  python3 -B replay_startup_hits.py
  python3 -B verify_candidate_hits.py
  python3 -B verify_counterchecks.py

The first command verifies the exact narrow obstruction. The second checks
all 198 whole-tape startup witnesses. The third replays the published
validation failures; the fourth checks the concrete full-frame examples.
These default commands are read-only. The counterchecks include 20,000-step
bounded runs and may take longer than the other checks.

FULL STARTUP SCREEN
A C++17 compiler is required. From this folder, choose a temporary output:

  python3 single_edits.py /tmp/pa193-edits.tsv
  python3 -c 'import json; s=json.load(open("pa194.sites.json")); open("/tmp/pa193-paths.tsv","w").write("".join(str(i)+" "+x[0]+"\n" for i,x in enumerate(s)))'
  g++ -std=c++17 -O3 pair_startup.cpp -o /tmp/pa193-screen
  /tmp/pa193-screen runtime193.native.tm /tmp/pa193-edits.tsv /tmp/pa193-paths.tsv 200000 1 > /tmp/pa193-hits.jsonl 2> /tmp/pa193-search.log

The final DONE line must agree with single_search_summary.txt except for
elapsed seconds. The hit file must agree exactly with arbitrary_single_hits.jsonl.
The original run took approximately 107 seconds on the research host; this
is descriptive, not a portable runtime guarantee. The C++ mode 2 interface
also exists, but no additional pair search needs to be run for these results.

ATTRIBUTION AND PROVENANCE
The 193 runtime, primary 194 table, source grammar, compiler, symbolic runtime,
and source-program definitions are inherited from ProveIt. The runtime
origin and exact source Git identities are recorded in PROVENANCE.json.
The vendored source files are unchanged, and the applicable imported
licenses remain under licenses/. The new contributions in this folder are
the all-start extension and certificate, the unrestricted one-row screen
with all-source-site acceptance, the witness replay, and the diagnostic
validation records. No end-to-end Lean or Rocq compilation is claimed.
