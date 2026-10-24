# Independent mathematical review

Reviewed by the parallel positive-equation research agent, October 23, 2026
(America/Los_Angeles). This is an independent AI-assisted review, not external
human peer review or a machine-checked formal proof.

## Scope and outcome

Read the new `PROOF.md`, `build.py`, the incoming joint-positivity source,
the signed `ORIENTATION_PROOF.md`, and the retained rational Pell descent.
The new quotient compression and the sixteen-variable root compression
pass the mathematical review. No blocking defect was found.

1. **Quotient recovery is not circular.** The hypothesis
   `c | (f^2-1)` is explicitly established before using the two missing
   congruences. The cited source70 proof separates its pre-auxiliary
   bootstrap (Sections 3--4.2) from auxiliary congruence use (Section 4.3).
   The signed guards, first and main norms, affine scale restrictions,
   and index identity used by the former remain in P17. The common-sign
   determinant and `eta*zeta>0` supply exactly its required sign premises.
   The displayed formulas for restoring `o` and `j` are then integral and
   satisfy both original equations directly.

2. **The P16 norm has its hypotheses before either omitted norm is
   recovered.** The guard and affine scales give `|c|>1`, hence
   `Q=I^2>1`, and also `|m|>1`, `|k|>=2`. Consequently `A0>0` and
   `S^2-4*A0=k^2-4>=0`. This excludes equal radicands without assuming
   the missing first Pell equation, auxiliary Pell equation, or rank
   conclusions.

3. **The rational-root recovery is valid over all integers.** If `V=0`,
   the cleared norm is a square plus a strictly positive term. Otherwise
   the second rational radicand is at least `S^2>A0`. Thus the rational
   sum cannot vanish, and
   `u=(n_total^2+A0-B)/(2*n_total)` recovers a rational square root of
   the integer A0. It is an integer. The other root divided by the
   nonzero integer S is rational; the adjacent-coefficient Pell descent
   makes it an integer. The two original roots are restored by integer
   translations, and the inverse witness `n=tau+S*nu` imposes no sign
   restriction.

4. **The centered-norm identity is correct.** With
   `n_total=n+B0+S*V`, `A0=B0^2+m*k^2+1`, and `delta=I^2-1`, expansion
   gives precisely the displayed L. In particular, the two large V^2
   terms cancel, leaving `S^2*(1-V^2)` in L. This is a polynomial
   identity, rather than a substitution that assumes either target norm.

5. **Degree certificates were checked by hand.** For P17, the joint
   guard is the unique degree-44 residual, with top part `-eta_top^4`;
   its squared coefficient is `2^32*3^64*beta^56`. For P16, L has the
   unique degree-48 top part `-S_top^2*V_top^2`; its norm correction has
   degree 94, below 96. Squaring the norm gives degree 192 and the
   displayed coefficient `2^64*3^136*beta^120`. For P23, the only
   occurrence of r in a degree-five residual is
   `-2*r*(a-E)^2*(eta+zeta)^2`, giving coefficient 4 on
   `r^2*a^4*eta^4` after squaring.

The native compiler, signed source calibration, and strong-rank theorem
remain the explicitly identified inherited mathematical dependencies.
This review does not independently rederive those whole upstream
theorems or turn a standard-model proof into an internal ZFC certificate.
