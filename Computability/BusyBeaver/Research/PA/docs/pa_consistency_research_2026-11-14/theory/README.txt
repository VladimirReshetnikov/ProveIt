PA consistency bridge and closing-instruction supplement
=======================================================

Status and scope
----------------
This supplement does not contain a machine with fewer than 196 states.
It contains an explicit, reproducible 196-working-state binary one-tape
machine, an arithmetic bridge argument with stated compilation hypotheses,
and finite experiments with different physical implementations of the final
AX closing jump. The three left-moving closing alternatives and the
unconditional right-moving padding detour have short local tape proofs in
closing_lemmas.tex. The main research comparison should report failure to
meet the requested state threshold if no separate smaller construction is
found.

No new end-to-end Lean or Rocq theorem is claimed. The supplied executable
checks are complete symbolic instruction-contract checks, not tests of a
bounded number of numerical register values. Their register-engine steps
use the unchanged imported macro interfaces documented by the included
M6/Runtime.lean excerpt. The proof that these interfaces and finite symbolic
certificates are arithmetically uniform is discussed in pa_bridge.tex.

Selected machine
----------------
selected196/machine.tm has working states 0,...,195 and terminal control 196.
The initial state is0, the head starts at integer tape cell 0, and the
bi-infinite tape is initially all 0. Each line has:

    current-state  read-bit  written-bit  L-or-R  next-state

There are 392 rows. The terminal control has no outgoing row. The native
state labels are in machine.native.tm; labels.json maps the dense labels
to native labels (initial native 74, terminal native 254). This is the prior
190-token separate-head emitter under a different tied grammar, with seven
compatible contextual reader folds, and with the closing action changed
from native 0 L302 to 1 R113. The latter change is unconditional on the
register file and costs exactly two extra literal transitions when the
next address-padding cell is 0.

The dense table SHA-256 is:
 a29c050910c30f1b15dc4bbfb1035abb5cb60d7a1a85f21242dbdc0ffa02eb4e

Reproduction
------------
Python3 standard library only is required. Run from this directory:

    python reproduce.py

Do not use python -O: assertions in the imported parsers are part of their
input validation. The check reconstructs the raw reader table, applies the
exact supplied folds, compares every native and dense transition, verifies
the protected register-engine rows, verifies the exact 190-token word and
its free-algebra formula emission, checks the primitive source binding,
checks all 4780 whole-register-file instruction contracts for both raw and
folded tables, and checks the complete 58154-step blank startup including
every nonzero tape cell. It also checks that all 196 working states are
reachable in the transition graph. Graph reachability does not assert
that each state occurs on the blank computation.

The resulting receipt is reproduced_r113196.json. The reported symbolic
execution counts are abstract checker steps, not literal TM run times.
The only startup bound here is an exact finite initialization calculation;
it is not evidence from simulating a long prefix of the proof search.

For the archived tied-grammar family, run:

    python rerun_archived_ties.py

This rescans 98 supplied grammars under seven closing modes, giving 686
cases, and checks a selected minimum per mode. Add --include-current to
include the four distinct current layouts and reproduce the 102-layout,
714-case family. Results go to rerun_output/.
The historical discovery receipt also includes four distinct current
search layouts, for 102 layouts and 714 cases. That receipt is preserved as
experiments/closing_ties_receipt.json. A further 392 cases used the three
left-moving alternatives and one register-6-zero variant; see
experiments/extra_closing_ties_receipt.json. All these finite families had
minimum 196 under the specified matching-based reader folds. Their failure
provides no global lower bound.

Files ending .discovery.txt preserve the original investigation programs
as provenance. They contain original workspace paths and are not the
portable entry points. Use reproduce.py and rerun_archived_ties.py instead.
The selected machine's complete grammar, folds, labels and prior receipt
are in selected196/. JSON files under experiments/ record the broader
finite candidate families; only selected196 is the chosen table here.

Mathematical proof status
-------------------------
pa_bridge.tex is a LaTeX section fragment. It requires amsmath, amssymb,
amsthm and hyperref and uses no custom theorem environment. It states four
interfaces explicitly: exact startup, positive whole-tape source-step
simulation, correct source command enumeration, and an effective PA-proof
compiler. The proposed arithmetic translation and proof-producing finite
binary-comprehension argument use full PA induction. The reverse invariant
carries actual PA proof codes, avoiding a new identification with an
auxiliary native certificate encoding. It treats the zero-code alias,
coincident-variable gate case, stack underflow, transposed quantifier code,
role permutations, global equality orientation, changed head ranks, and
both reverse-stuttering bounds.

The arithmetic argument is conditional on those interfaces for whichever
literal table is claimed. It must not be presented as a freshly kernel-
checked endpoint merely because imported files contain related theorems.
The supplied selected table has exact executable source/runtime receipts;
the unchanged source and imported arithmetic theorem interfaces remain
identified in the fragment. No proof of Con(PA) is asserted.

Provenance and citations
-----------------------
All repository comparisons were pinned to ProveIt commit:
 906367250a7f96c923147b10df392294bced7be5

Repository:
 https://github.com/VladimirReshetnikov/ProveIt/tree/906367250a7f96c923147b10df392294bced7be5

Imported PA196 source:
 https://github.com/VladimirReshetnikov/ProveIt/tree/906367250a7f96c923147b10df392294bced7be5/Computability/BusyBeaver/Research/PA/jamesyc-upstream/pa196

The imported James Chang BusyBeaver upstream commit is:
 407cdc356f6b586635e71ac92be394255f4bfea4

The principal supplied archive is:
 docs/incoming/pa_consistency_comparison_and_new196_2026-11-13.zip
Within it, pa_consistency_research/axioms/ provides compiler.py,
symbolic_runtime.py, verify.py, verify_emitter.py, search/support.py,
search/ties/, the separate196 grammar, and the reference excerpts.
Copies in code/ are unchanged except that source_checks.py extracts the
source_binding function, unchanged, from verify.py. The selected tied
grammar is axioms/search/ties/alltie_10.grammar.json after replacing the
already available two- and four-increment readers by their macro names.

The four known-zero CD3/CD4/CD5/CD6 closing variants are prior work in:
 docs/incoming/pa_tm_extended_research_2026-11-13.zip
 pa_tm_extended_research_2026-11-13/auxiliary196/closing_variants.md

Direct arithmetic translations, proof-producing comprehension, and the
native logical calibration are prior work in:
 docs/incoming/pa_tm_research_2026-11-13.zip
   report/pa_reverse_translation.tex
 docs/incoming/pa_consistency_reduction.zip
   math_reduction/internal_converse.tex
 docs/incoming/pa_consistency_research.zip
   notes/internal_soundness.tex
and in the principal archive's axioms/proof/diagonal_prior.tex and
axioms/proof/changes.tex. Paths within these archives have their own
package-root prefix; consult the archive inventory in the main report.

The cleanup invariant used for the conditional closing alternatives is in
PA196/Source/AXGate.lean, local claim fifth; its field/register mapping is
in AXGateSteps.lean. Those files are included under code/reference/PA196/
Source/. The selected unconditional R113 variant does not require that
zero-register invariant.

Copies of the upstream and ProveIt licenses are included under licenses/.
