FOUR RULES FOR iPRA: SUBSTITUTION AT WITNESS DISCHARGE
Prepared for Vladimir Reshetnikov, November 12, 2026

START HERE
report.pdf is the complete report. report.tex is standalone editable LaTeX;
research/constancy.tex is an additional editable appendix-source copy. The selected standalone verifier is
code/canonical_checker.py. The ZIP includes all source, code, examples,
matched controls, reproduction scripts, and attributed prerequisites.

RESULT
The new calculus has four inference families: one successor calculation,
Use of a unary clause, paired Introduction, and substitutive witness
discharge. Terms use the existing canonical successor-seeded recursor R.
Successor is R(0,a;u.0); canonicalization only erases the body when the
counter is literally zero. It never unfolds a successor iteration.

Substitutive discharge opens D at fresh b, proves s=t and F(s) in the
opened context, and exports F(t) when the exported formula has no b.
The formula template's variable is separate from the witness b.
Sources, targets, and templates may mention b if the result does not.

Reflexivity is derived rather than a fixed axiom. Calculation proves
W_t=t for W_t=R(1,0;u.t). A closed dummy D theorem derives full transport
from the discharge rule; transporting W_t=t along itself gives t=t.
A constant template recovers ordinary D-elimination. This bootstrap uses
no hidden reflexivity premise and no selector normalization.

The written proof establishes exact consequence equivalence with a
matched separate-rule calculus. Composing with the pinned canonical-R
and scalar bridges gives whole-domain bi-interpretability with full
first-order intuitionistic PRA, actual equality, identity numerical
composite graphs x=y, both formula round trips, and equiconsistency.

SIMPLICITY CLAIM AND LIMIT
The matched complete standalone checker decreases from 2318 to 2267
normalized bytes, 726 to 713 significant tokens, and 809 to 798 AST nodes.
Only the split/fused equality-and-elimination rules differ in that pair.
The improvement is modest. No global minimum or repository-wide record
is claimed: the historical compact 516-byte and validated-public-goal
788-byte profiles are not beaten. Incoming witness_discharge already has
three families plus a fixed reflexivity clause and full normalization.
The new four-family construction removes full normalization and the fixed
reflexivity clause; rule count alone is not its claimed advantage.

The certificate relation is primitive recursive on finite trees. There
is no uniform numerical evaluator, normalization-totality assumption,
or fuel field. Runtime memory/recursion limits still apply.

ADDITIONAL MATHEMATICS
The report gives a three-point obstruction to replacing binary equality
transport by unary congruence, covering raw and zero-normal scalar terms.
A separate appendix replaces quantifier-free induction by the constancy
rule f(Sz)=f(z) => f(t)=f(0), with an explicit Boolean equality-split axiom
and counter-aware recursion. Those extra costs are stated; this appendix
does not establish a smaller complete checker.

REPRODUCE
  python3 reproduce.py
  python3 build_pdf.py
  python3 code/canonical_checker.py < examples/canonical/accepted/reflexivity_zero.json
  python3 code/canonical_checker.py < examples/canonical/rejected/false_equation.json

Acceptance is exactly ACCEPT on standard output with exit status zero.
The negative example prints REJECT and has nonzero exit status.
Checker scripts use Python standard-library modules only. The PDF build
requires pdfLaTeX with standard TeX Live packages and disables shell escape.
Measurements use CPython 3.12.14, remove the module docstring, run ast.unparse,
and append one LF. Gzip-9 with timestamp zero is informational.

VERIFICATION
Canonical examples: 14 positives, 18 adversarial negatives, 14 exact-goal
round trips through the matched control, and 64 standalone CLI checks
across normal and optimized Python. The raw companion separately has
14 positives, 16 negatives, 2 open sequents, 60 CLI checks, 14 control
round trips, and 5 translations from the frozen raw CE5 checker.
The evidence files record the actual results. Finite checks do not
replace the general written proof. No new Lean/Rocq verification is claimed.
The canonical-R bridge is a written prerequisite; the downstream scalar
bridge is the part formalized in the repository. Upstream Lean was not rebuilt.

PROVENANCE
VladimirReshetnikov/ProveIt, commit
17898ea7e6a1300dfdcad71040d5daeed67916d4,
Logic/PrimitiveRecursiveArithmetic/ConciseIPRA.
All 67 filed-package summaries and all six incoming archive claims were
inspected; key definitions and bridge proofs were checked. Novelty is scoped to
that inspected material, not asserted over all literature. Source snapshots
and the upstream MIT No Attribution license are in reference/.
The checker traversal architecture is adapted from incoming witness_discharge;
the canonical R syntax and its bridge are inherited from canonical_recursors.
New work is the stated generalized-discharge composition, its equality
bootstrap, exact translations, validation, and the additional mathematical notes.
