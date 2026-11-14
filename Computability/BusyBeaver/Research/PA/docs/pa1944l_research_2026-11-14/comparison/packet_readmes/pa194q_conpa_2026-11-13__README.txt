PA194Q and PA194CSZ: two new 194-state consistency machines
=========================================================

Principal result: PA194Q has 194 working states, a binary two-way infinite
tape, an all-zero start, and a separate halting label. No sub-194 machine
was established. This packet meets the requested alternative of a
materially different 194-state construction.

Read report/pa194q_report.pdf. The complete LaTeX sources are beside it.
The PDF prints both full transition tables and compares all 41 delivered
PA research packets present at the pinned repository commit.

The new preservation result is PA |- Halt(PA194Q) <-> Halt(PA194C).
Together with the supplied ordinary mathematical calibration of PA194C,
this gives PA |- (not Halt(PA194Q)) <-> Con(PA). The new source exchanges
the curried premises in one quantifier-distribution axiom; it changes 79
of 3,649 source instructions, with a newly verified 194-state realization.
The premise-exchange proposal itself is credited to earlier research.

The proof uses explicit proof translations, cached-command compilation,
literal source-step simulations and a complete blank initialization.
The PA calibration remains an explicitly inherited mathematical
dependency. The executable certificates are supporting checks, not a
new foundational proof kernel. No newly compiled end-to-end Lean/Rocq
theorem or completed iPRA consistency endpoint is claimed.

Machine convention and identity
-------------------------------
Principal table: machine/pa194q.tm
SHA-256: 48e98b5504dc5b3f20a2d040cb54ed1c96bee4c5e32ea27ae98ffada4dce7ea1

Optional second table: secondary/pa194csz/machine_csz/pa194CSZ.tm
SHA-256: 62e93098caf7c09ff2938d07064f0dbbb47c71ec369892968258fff708592269

Both tables have working labels 0,...,193, start 0 and halt 194.
The head starts on cell 0 of an all-zero two-way infinite tape. Each of
the 388 rows is: current_state read_bit write_bit L_or_R next_state.
The halt label is excluded from the working-state count. Every move is
one cell left or right. Native labels and their exact dense bijections
are included. Table novelty is checked under arbitrary state renaming,
start choice, global reflection and symbol complementation.

Reproduce accepted constructions
--------------------------------
Python 3.10 or later, using only its standard library:

    python3 -B reproduce.py
    python3 -B reproduce.py --secondary

The first command rebuilds PA194Q, checks all 4,749 primitive outcomes
using the construction runtime, checks every simultaneous local fold,
replays the 61-line exchange certificate, verifies the exact 190-token
source-word change, checks novelty against the frozen corpus, and runs
the independent literal-tape audit. The second additionally rebuilds and
verifies PA194CSZ and its 263,180-pair inductive invariant.

Use assertions: do not run with -O or PYTHONOPTIMIZE. No external checkout,
network, solver or proof assistant is needed. Independent literal replays
can take several minutes. --quick skips those replays only; it does not
replace their certificates. Reproduction overwrites generated receipts.

For PA194Q, the independent checker rederives four generic list lemmas
from literal rows, resolves the source in two ways and checks exact
dense/native conjugacy. It covers nine arbitrary natural register values,
both decrement branches, address-plus-gap length 48+n for any n>=0, and
an arbitrary finite nonempty list of arbitrary natural spare values.
Its exact 57,922-step blank simulation compares the entire resulting
tape to the clean source frame. This finite startup is not long-run
evidence for nonhalting. The corresponding CSZ startup is 58,014 steps.

Proof and verification boundary
-------------------------------
- New formula: Q -> (P -> R), replacing P -> (Q -> R), where
  P=U(D,A), Q=U(D,I(A,H)), R=U(D,H).
- Exchange is derived using K, S and modus ponens. K and S are inherited
  derived rules of the unchanged restricted rho8 basis. The exact Lean
  implication-basis references are retained for this dependency.
- Complete numerical calculi and explicit bidirectional proof
  transformations are supplied in the report. The zero-code alias
  I(0,0)=0 is handled without assuming injective formula syntax.
- Positive physical source-step durations support both directions of
  halting equivalence. Universal symbolic contracts go beyond finite
  numerical samples. They remain trusted executable/mathematical
  certificates rather than proof-assistant kernel output.
- PA194CSZ is a second new composition of supplied symmetric Shift and a
  zero-register jump. Its new common invariant proves their compatibility.

Corpus and negative search
--------------------------
Repository: https://github.com/VladimirReshetnikov/ProveIt
Commit: 17f92105e2bc4317feae6c219cb2143437b482ff

The fresh comparison catalogs 41 deliveries and recognizes 4,417 literal
table occurrences, 620 byte forms, and 446 action-graph classes. Fifteen
194-state byte forms reduce to eight old graph classes, including a
rejected scanner. Counts include unsuccessful candidates and reference
copies, not only consistency machines. The scanner recognizes complete
numeric five-column binary tables in .tm and .txt files, including
recursively nested ZIPs; it does not parse every possible encoding in
program source or prose. All frontier designs discussed have literal
tables in scope. The two new tables are absent from this frozen corpus.

The bounded source/grammar searches and local-state exclusions did not
produce a verified 193-state machine. They are not a minimality proof.
See search/README.txt and the report for exact scope and counters.

Files
-----
report/          PDF, main .tex and every included .tex fragment
machine/         Principal dense/native/raw tables and exact source maps
construction/    Frozen grammar, folds, deterministic builder and inputs
verification/    Independent literal checker and formula/exchange checks
evidence/        Accepted construction, source, fold and physical receipts
comparison/      Full corpus census, delivery ledger, frontier and checker
secondary/       Complete PA194CSZ construction, proofs and verifiers
references/      Inherited mathematical calibration and Lean interfaces
search/          Discovery sources, inputs, logs and negative-result scope
licenses/        Preserved supplied licenses
PROVENANCE.json  Repository and source identities
RESULTS.json     Compact machine-readable result and proof boundary
SHA256SUMS       Hashes of the delivered files, excluding this manifest

To check integrity before regeneration, use sha256sum -c SHA256SUMS.
See NOTICE.txt for attribution. No repository changes were published.
