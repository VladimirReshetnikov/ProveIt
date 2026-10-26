# The already-live A+1 center:87 operations,degree228

**Retained scaled-chart method control.** The bounded late source17287/214
strictly dominates this earlier operation/degree point. Principal new
89/210 and90/206 compositions are in `late172/PROOF.md`; do not treat
this earlier circuit as a current Pareto claim.

This is a second exact positive-domain tradeoff from the same centering
argument: change only g0=AUE to gplus=(A+1)UE in PROOF.md. The register
A+1=Y(X+1)+2 was already needed to compute Delta=(A−1)(A+1), so its
reuse saves the private A=(A−1)+1 gate. Both complete tuple variants are
materialized as equation_plus1_bV.json, with87 live integer-leaf operations
(52 multiplications,19 additions,16 subtractions) and exact degree228.
The ten independent positive variables and all ordinary native interfaces
remain exactly as specified in PROOF.md. No rational leaf is used.

The whole polynomial is the equation in PROOF.md §1, with g0 replaced
by gplus everywhere, and no other change. In particular its carrier is
z=n+kappa+sigma−Wt−rho−gplus V.

## Full proof of the change

All root extraction, index exclusions, inverse authentication, projection,
and native reconstruction arguments of PROOF.md §§2–3 apply unchanged.
For the only new signed estimate, at a zero

    gplus²/G < (A+1)²/(A²−1) = (A+1)/(A−1) < 2,

since A>4. Thus gplus<2g, so the same bound

    gy+gplus|V| < (7/2)g|V| < 7L/16 < L/2

proves B>=0 before any sign assumption on R or V. The difference from
the parent numerator is again an integral multiple of M; every numerator
reduction modulo D and H is unchanged, and the final integer gplus V
preserves all remaining integrality conclusions.

For completeness take a parent positive zero with V>0 and set
n_new=n_old+gplus V. Since gplus>0 and is independent of n, this is a
strictly positive integer. The exact identity

    n_new−V(bB+gplus)=n_old−bVB

makes the new numerator equal to the old numerator and preserves the
vanishing final polynomial. No negative-root choice or extra seed bound
is required. Soundness is proved separately and does not assume that
the inverse shift preserves positivity. The historical and
Start-marker4177 native/Pcs calibrations are those of the main proof.

## Exact degree and checks

The exact residual and cancellation identities are

    gplus²−G=2(A+1)U²E²−E,
    Z²−M²GV²=Z0²−2Mgplus VZ0+M²[2(A+1)U²E²−E]V².

The three summands have degrees114,133,148 respectively. Therefore Q
raises the unique dominant branch to228; M²G−Z² has degree152. With the
same q0,k0,B0 as PROOF.md, the complete leading form is

    [Pplus]_228=9*2^11*q0^98*w^25*s^57*i^10*k0^32*B0².

This nonzero202-term polynomial is independently checked in both tuple
specializations, along with38 exact cuts and175 rejected actual gate
mutations. Normal and optimized receipts agree. build_variants.py --check
reproduces the literal JSON files. The original85/232 point, this87/228
point, and the main88/224 point are explicitly different operation/degree
tradeoffs; no global optimality or literature priority is claimed.
