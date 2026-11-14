Guard-padding obstruction
========================

For the separate-diagonal PA194 numerical calculus, replace guarded gates
G(a,b,r), r != a,b, by only the unguarded padded gates
G(a,b,F(a,b,c)), F=I(I(M(a,b),M(a,b)),c).
Retain all six logical/equality heads, the dominated propositional head,
truth, unrestricted diagonal B -> U(B,B), modus ponens, and generalization.

THEOREM. This modified calculus cannot derive the legitimate old gate
G(1,0,4), or its membership-vacuity conjunct V(1,0,4).

Interpret numerical variable 4 as the same object variable as numerical
variable 1; leave all other variables distinct. Use ordinary equality and
finite binary-set membership over the natural numbers. The unchanged
heads remain valid. Codes 1 and 4 both have support {0}, so all diagonal
axioms remain valid despite this variable alias. Every padded gate has
fresh index at least 544, exceeding its a,b parameters and every label
in its predicate; its finite separation interpretation remains valid.
The written proof explicitly handles f(a)=f(b), even when a != b.

The old vacuity V(1,0,4) becomes
Bit(x1,x0) -> forall x1 Bit(x1,x0), false at x1=1,x0=0.
Its original guard 4 != 1,0 passes. Hence old-gate recovery is impossible
for this exact modified calculus. One cannot justify it by silently
assuming arbitrary variable renaming.

This is NOT a proof that every guardless redesign fails or that the
modified theory cannot be equiconsistent with PA by some other route.
It rules out this claimed relative derivability argument.

Files:
  guard_padding_obstruction.tex -- complete theorem and proof, report fragment
  check_codes.py               -- exact code arithmetic/support checks
  code_checks.json             -- output of check_codes.py

Prior corpus proposal:
Computability/BusyBeaver/Research/PA/docs/pa_consistency_cross_archive/
research/theory_study/theory_results.tex, fresh-code padding section.
It uses another tautological wrapper and leaves instance recovery open.

Possible further route, explicitly OPEN:
A PA-to-restricted-public-image proof translation might avoid the raw gate
G(1,0,4), much as ConciseIPRA obtains completeness only on a translated
public language. No such translation for this padded numerical calculus
has been constructed here. The analogy is a research direction, not a
positive theorem about its arithmetic strength or its achievable state count.
