A SMALLER VALIDATED PROOF PRESENTATION OF iPRA
============================================

12 November 2026
Baseline: VladimirReshetnikov/ProveIt
commit 62396b06020f794fa6dc01b4025a6a5db9d4d28a
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA

RESULT AND LIMIT

This archive contains a proved implementation reduction of the existing
native scalar iPRA calculus, and a separate mathematical independence result.
The theory remains equiconsistent and bi-interpretable with full first-order
intuitionistic primitive recursive arithmetic. Both numerical interpretation
domains are whole, equality is actual, and both domain composites are x=y.

The new immutable-context checker uses the empty context to mark public-goal
validation. After that pass it adds the existing neutral assumption, so the
context itself records the phase. A separate flag disappears. Exact accepted
certificates and input consumption are preserved; no proof translator is needed.

The primary complete checker measures 327 significant tokens, 375 AST nodes,
643 normalized UTF-8 bytes, versus 333 / 379 / 656 for its frozen native control.
An explicit-type-test variant measures 327 / 375 / 646.

THIS DOES NOT BEAT THE ENTIRE COMPACT ENVELOPE.
The corpus also contains compact protocols whose canonical guarded public-goal
grammar is an input contract, rather than enforced by their complete module.
Their coordinate minima found in the audit are 256 tokens, 276 AST nodes,
506 bytes, attained by different programs. No claim is made to have beaten
that envelope, deleted a mathematical axiom, or proved absolute minimality.
The user's strongest global reduction target remains unmet.

The separate theorem proves that equation progress cannot simply be deleted
from the native eight-rule kernel. The separating formula is

  Q_y (I(y,0;u.u)=0).

A separator in the public Eq/D language is D_{x,y}(I(y,0;u.u)=0),
where x is unused. The full native kernel proves both formulas.

A coherent saturated-model expansion validates all the other rules and
refutes this formula. The construction adapts Friedman's 1975 method while
handling substitution in raw iterator binders explicitly. This closes the
specific independence question in the pinned README; it is not a universal
checker-size lower bound. The new proofs have not been checked in Lean/Rocq.

CONTENTS

ipra_context_phase.tex / .pdf: complete report and inherited proof appendices.
paper/progress_independence.tex: new independent mathematical result.
paper/checker_equivalence.txt: detailed audit of the implementation change.
code/checker.py: complete primary acceptance module.
code/checker_portable.py: explicit type-test variant.
code/readable_checker.py: readable expansion of the same algorithm.
code/checker_list.py: optional one-shot mutable-list profile; not recommended
  as a repeatedly callable function with its default argument.
validation/fixtures/: positive and negative source certificates.
evidence/: measurements, validation results and baseline source census.
baseline/: frozen compact and native comparison programs.
reference/: inherited mathematical proofs, selected Lean endpoints, README
  snapshot and upstream license.
PROVENANCE.json / IMPLEMENTATION_PROVENANCE.json: source identities and hashes.
CLAIMS.json: precise achievements and limits.
MANIFEST.json: SHA-256 and size of every other archive member.

REPRODUCTION

  python3 reproduce.py
  python3 code/checker.py < validation/fixtures/computation_zero_local.json
  python3 build.py

The checker and validation require only Python's standard library. Measurements
use CPython 3.12.14. Rebuilding the report requires pdfLaTeX and the packages
named in its preamble. The included PDF is already compiled.

The code checks finite proofs within ordinary machine resource limits.
Assertions in the reproduction script are test assertions, not acceptance
conditions in the measured standalone proof checker. The real checkers are
tested under both ordinary Python and python -O.

LICENSE AND ATTRIBUTION

Frozen ProveIt material and derived code retain its MIT No Attribution license,
included at reference/LICENSE-ProveIt.txt. Newly written report material is
also provided under that license. The mathematical literature citation is:

Harvey Friedman, Provable equality in primitive recursive arithmetic with and
without induction, Pacific Journal of Mathematics 57(2) (1975), 379-392.
DOI: 10.2140/pjm.1975.57.379.
