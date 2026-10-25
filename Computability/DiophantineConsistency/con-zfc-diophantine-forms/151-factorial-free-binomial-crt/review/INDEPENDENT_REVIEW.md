# Independent review of the factorial-free mathematical construction

**Reviewer:** `alternative_foundations`, an independent AI research agent in
this task.  
**Date:** 25 October 2026.  
**Reviewed draft:** `report/main.tex` in the
`ConZFC_Factorial_Free_Binomial_CRT_2026-10-25` delivery packet.  
**Companion derivation:** `FACTORIAL_FREE_BINOMIAL_CRT.md`.

## Conclusion and scope

I independently checked the changed mathematical source and its soundness
and completeness arguments. I found no unresolved mathematical obstruction
to the selected construction

\[
t=16+h^2,\qquad F=[2(t+1)]^t,\qquad
y=F(2v+1)^2,\qquad q=(2z+1)^2,
\]

with the retained eighteen power certificates and
\(H=2+\sum_{j=1}^{9}a_j\).
This review concerns the ordinary mathematical proof and its interfaces
with the inherited arithmetic compiler. Literal polynomial counts, hashes,
and complete source-to-output reconstruction are separate compiler audit
obligations; they are not independently certified by this note. Nor is this
a claim of proof-assistant verification of the complete construction.

The retained dependencies are the literal local \(C_{222}\) rule
polynomial and its majorant ledger, its logical calibration to syntactic
ZFC refutation, the signed Pell frame and semantic anchor, and the common
normalized-remainder compiler. I checked the new construction against the
stated hypotheses at these interfaces; this note does not reprove every
inherited source theorem or independently reconstruct every generated
quadratic register.

## Checks performed

1. **Binomial CRT replacement.** The threshold
   \(R\ge\operatorname{lcm}(1,\ldots,t)^2\) gives every row a prime-power
   selector \(p^e>t\) that survives in \(\binom{R+t}{t}\). Independently,
   every prime power in that binomial coefficient divides at least one
   consecutive factor \(R+i\). The latter fact is essential to
   completeness. Precision \(p^{2Ke}\) before division by the range
   factorials leaves the required precision \(p^{Ke}\). I checked both
   directions, including the finite counterexample showing why the radius
   hypothesis cannot simply be omitted.

2. **Label balance.** The unequal factor-count argument first makes both
   nonunit factor counts at most \(t\), even though the premise side starts
   with up to \(2t+1\) factors. The coefficient bound
   \((t+1)^t<F\) then turns equality at \(F\) into an identity of integer
   polynomials. Unique factorization gives exact label multiplicities;
   single-conclusion Horn closure yields a finite derivation, including
   when the submitted rule multiset contains cycles or repeated premises.

3. **Acyclic recovery.** The signed-power argument explicitly excludes
   zero bases. The initial odd-square radix supplies \(q\ge1\); positivity
   of the representatives and the shifted \(H\) precede use of
   \(q=(BH)^x\). The raw index congruence excludes \(B=0\). The last beta
   endpoint excludes \(x=0\), after which the first endpoint and then the
   last endpoint give the strict exponent budget. Positivity of \(B\) is
   recovered later from its exact binomial digit, so it is not assumed
   circularly.

4. **Remainder and evaluation budgets.** The binomial coefficient bound,
   the common normalized remainder bound, the derived-label budget, and
   the inherited local polynomial majorant all fit the exponent \(K=x\).
   The changed growth law is ample for these inequalities.

5. **The boundary \(y=F\).** This permitted algebraic branch must be
   considered only after local rows have been decoded. Its first beta
   remainder is zero; positive label weights propagate zero to the last
   accumulator, whose endpoint remainder is one. This contradiction
   correctly establishes \(y>F\) before positive accumulator cancellation.

6. **Constructive parity and cofinality.** The even growth factor supplies
   enough powers of two to choose \(y\) as an even multiple of \(t!\).
   The beta CRT moduli are odd, allowing an even code \(x\). The new
   binomial modulus is odd, allowing the dominant actual representative
   to be odd and the remaining eight to be even. Thus \(H\) is odd,
   the semantic anchor is even, and \((BH)^x\) is an odd square. The
   required witness sizes can be reached by adding full CRT moduli.

## Editorial clarifications communicated during review

The report should explicitly call the range-lemma parameter \(p\) prime.
For a derived label \(J(\boldsymbol A)\), the range proof also uses
\(J(\boldsymbol A)\equiv J(\boldsymbol w)\pmod {p^{Ke}}\) and the inherited
bound \(0\le J(\boldsymbol w)<2^K\), so its small residue is its actual
local label. In completeness the eight nondominant representatives can
be taken at most \(2N^2\), while the dominant one is in
\([2N^2,4N^2)\); this makes anchor domination explicit. A malformed TeX
copy of the three-square remainder norm was also reported for correction.
These are clarification and transcription issues rather than changes to
the selected construction.

**Signed:** `alternative_foundations` research agent.
