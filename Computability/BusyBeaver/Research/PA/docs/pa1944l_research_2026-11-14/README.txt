PA1944L: comparison, a new decoder, and the iPRA proof boundary
=============================================================
Research dated 14 November 2026, Pacific time.
Repository snapshot: VladimirReshetnikov/ProveIt
1c9524d8bf2e0a27b9a16ff622359927f536e663

READ FIRST
----------
report/main.pdf is the integrated report. report/main.tex and every local
input needed to compile it are included. The PDF includes the complete new
transition table, all 72 delivery records, and all 82 recognized historical
194-state graph classes. The separate theory PDF contains the detailed
arithmetic arguments in a convenient standalone form.

RESULT AND LIMITATION
---------------------
No machine below 194 working states with the requested property is established.
No unconditional new theorem

  iPRA proves: not Halt(PA1944L, blank) iff Con(PA)

is established. The current repository itself identifies the primary
machine-specific iPRA/Con(PA) calibration as open. This package does not
promote an inherited PA proof or a conditional endpoint to that stronger
result.

The new concrete artifact is PA1944L, a structurally new 194-state physical
decoder for exactly the primary PA194 source program. Both full independent
literal-tape checks have passed (4,780 source outcomes for each machine).
The report supplies an ordinary computer-assisted mathematical proof of

  iPRA proves: Halt(PA1944L, blank) iff Halt(primary PA194, blank),

and hence the equivalence of their nonhalting. This relative theorem uses
explicit primitive-recursive positive trace lengths and quantifier-free
soundness proofs for the symbolic run/list rules. It does not supply the
still-missing PA-refutation compiler. No new Lean/Rocq build is claimed.

Two additional written results are included:
  * A bounded-store replacement for one full-PA compiler induction,
    conditional on the stated local word identities.
  * Explicit primitive-recursive Boolean countermodels to deleting the
    equality interface at radix three, or only its witness head at radix
    four. These rule out those particular shortcuts; they are not global
    state-count lower bounds.

THE NEW MACHINE
---------------
Authoritative table: machine/machine.tm
194 working states, numbered 0..193; terminal halt label 194.
Start: state 0, head coordinate 0, all-zero two-way infinite binary tape.
Every row is: state read_bit write_bit L_or_R next_state.
There are 388 rows. No program or nonblank input is preloaded.

Dense SHA-256:
c5787c6f2350e77183ca0d3ff25d2733ba87e8bb52cd54092d7fa26fcf4d5253

The native table uses initial label 74 and halt 254. machine/labels.json binds the
native and dense labels exactly. The change is the recurring association
((i,(i,i)),i) of four increments, one extra helper, and one extra contextual
fold: 135 fixed controls + 67 AX readers - 8 folds = 194. Every resolved
source instruction and jump target matches the primary source. This is a
physical decoder variation, not a new calculus or proof-search algorithm.

New table independent check: 1,084,060 symbolic operations; maximum 397 per case;
minimum positive-duration constant 3; full blank startup 58,320 steps.
Primary table independent check: 1,078,198 operations; maximum 397; minimum 3;
startup 58,154 steps. Four list lemmas are rederived from each literal table.

REPRODUCE
---------
Python 3.10+ and the standard library suffice. Keep assertions enabled.
From this directory:

  python3 -B reproduce.py --receipt /absolute/path/fresh_receipt.json

The default reconstructs both machines, runs both independent literal-tape
passes, compares all source instructions and startup frames, checks the
Boolean identities and affine durations, and compares the new graph against
all 82 historical frontier representatives under broad graph symmetries.
It uses temporary files and leaves this release unchanged.

  python3 -B reproduce.py --quick --receipt /absolute/path/quick_receipt.json

Quick mode skips only the two independent literal-tape replays and reports
that omission. It verifies the packaged full receipts against the literal
table and contract hashes. It must not be described as a fresh full replay.

Fresh full passes were performed separately on both literal tables during
construction. Their original logs are in provenance/. The final combined
assembly replay is separately labeled in RELEASE_RECEIPT.json.

The complete corpus scan additionally needs the pinned Git repository:

  python3 comparison/audit_corpus.py --git-repo /path/to/ProveIt --out /tmp/census

The frozen frontier novelty replay is self-contained. The optional bounded
grammar search is under search/; mutation counts include revisits and are
not lower bounds or counts of distinct machines.

CONTENTS
--------
report/       Integrated TeX/PDF, generated table/ledger inputs, build helper.
machine/      New dense/native tables, source graph, folds and full evidence.
baseline/     Pinned primary table, source graph and fresh independent evidence.
construction/ Deterministic builders and pinned offline source dependencies.
verification/ Independent literal-tape checker and generic symbolic rules.
theory/       Written arithmetic proofs, Boolean checker, durations and review.
comparison/   Complete ledgers, census, source locators, representative tables.
search/       Bounded unsuccessful decoder search and precise scope.
provenance/   Current repository status, attribution and original replay logs.
licenses/     Preserved upstream license notices.
SHA256SUMS    Hashes of all release files except this checksum manifest.
RESULTS.json  Machine-readable results, proof scope and remaining obligation.

PDF REBUILD
-----------
In a standard TeX Live installation:

  cd report
  python3 -B generate_inputs.py
  pdflatex -interaction=nonstopmode -halt-on-error main.tex
  pdflatex -interaction=nonstopmode -halt-on-error main.tex

An additional pass may be needed for the table of contents. The included
PDF is already compiled. No repository was published or remote file changed.
