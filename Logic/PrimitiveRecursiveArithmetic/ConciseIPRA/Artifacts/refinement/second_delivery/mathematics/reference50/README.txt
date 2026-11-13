A 50-NODE SCALAR PREDECESSOR FOR iPRA
Prepared for Vladimir Reshetnikov, 12 November 2026
================================================

RESULT AND LIMIT

The requested new axiomatization below the current complete-checker
complexity frontier has NOT been established. This package contains a
new mathematical partial result: an internally correct scalar predecessor
with 50 fully expanded constructor nodes, versus the incoming 57-node term.
It preserves the existing whole-domain bi-interpretation with full
first-order intuitionistic primitive recursive arithmetic.

The new idea uses an absorbing factor orbit and a seven-node parity
control that is interchangeable with ordinary parity in selector tests.
The predecessor equations are proved using only computation, equality,
and induction on literal equations. No primitive axiom or rule is removed.

The mathematical reduction is 7/57 = about 12.28 percent, or one third
against the original 75-node term. A restricted seven-node lower bound
for a separate selector control is proved. No claim that the entire
50-node predecessor or the proof checker is minimal is made.

The direct compact checker envelope remains (244 tokens, 267 AST nodes,
479 normalized bytes), attained by THREE DIFFERENT unchanged upstream
programs. Compressed-source execution wrappers belong to a different
accounting class. The compact, native-goal-validated, and whole-input-
validated interfaces have different contracts and are not combined.

START HERE

ipra_absorbing_predecessor.pdf
    Complete paper: explicit native theory, new equational proof,
    selector-control lower bound, bi-interpretation preservation,
    measurements, and further research questions.

ipra_absorbing_predecessor.tex
    Flattened, standalone LaTeX source, requiring no input fragments.

src/
    Modular authoring sources, used to reconstruct the flattened TeX.

code/predecessor50.py
    New self-contained raw-tree constructors, evaluator, node counter,
    and finite arithmetic/formula-size checks. This is a research utility,
    not a proof checker or a formalization of the universal theorem.

code/predecessor50_results.json
    Counts, finite examples, actual prefix-formula sizes, and the expanded
    50-node AST. Binder names are annotations; there is no subtree sharing.

baseline/
    Five UNCHANGED upstream standalone proof checkers, their exact
    contracts, fixtures, source identities, and reproduction utility.
    266 process checks were rerun under normal and optimized Python.
    These checkers do not certify the new predecessor theorem directly.

reference/
    Exact inherited base-theory and checker-protocol chapter excerpts,
    pinned README, and the earlier 57-node predecessor proof. These
    chapter fragments are reference material, not standalone documents.

evidence/
    Pinned source identities, reproduction and review records.

REPRODUCE

    python3 verify_manifest.py
    python3 reproduce.py
    python3 reproduce.py --pdf

The metric reference runtime is CPython 3.12.14. The PDF build requires
pdfLaTeX and ordinary packages listed in the TeX preamble. No network is
used by reproduction. If the system pdfLaTeX format is missing, the bundled
helper constructs a private format from the installed TeX sources without
changing the system configuration. To rebuild only the paper from the modular
sources:

    python3 reproduce.py --source-only --pdf

The manifest describes delivered bytes. Reproduction can rewrite receipts,
including environment-specific metadata, so check it first when exact
identity is required.

MATHEMATICAL STATUS

The proof is an internal equational derivation, not a standard-model
numerical argument. It therefore applies to nonstandard models too.
Both interpretation domains remain whole, equality remains actual,
and the numerical composite comparison graphs remain x=y.

Finite computations corroborate the source definitions and counts; they
are not universal proofs. No new Lean/Rocq verification, external peer
review, globally optimal axiom basis, or smaller checker is claimed.

PROVENANCE

Repository: https://github.com/VladimirReshetnikov/ProveIt
Snapshot: e85c5e24dba535a296c46cd18fa66a146ce36b8e
Path: Logic/PrimitiveRecursiveArithmetic/ConciseIPRA
The unified article, README and all ten then-current incoming archives
were inspected. Archive URLs and SHA-256 values are retained in baseline/.
The novelty statement is limited to that inspected corpus.

Inherited mathematics, code and fixtures are attributed in the paper.
The included MIT No Attribution license applies to the new material too.
No GitHub commit, pull request, or external publication was created.
