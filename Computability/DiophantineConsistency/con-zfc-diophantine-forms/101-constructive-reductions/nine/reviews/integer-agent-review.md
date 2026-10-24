# Independent review: radix-origin translation and nine-variable equations

Reviewed the complete `report_section.tex`, `inherited/NineRatio.lean`,
`inherited/ratio59_PROOF.md`, `inherited/SATURATED_POSITIVE_PELL_AUDIT.md`,
`EXACT_AUDIT.json`, `NORMALIZATION_CHECKS.json`, the fifth-row all-one check in
`exact_audit.py`, and the source layout/formula declarations. `PROOF.md` was
not present at the time of this review; the complete LaTeX argument was.
This is an independent AI-assisted mathematical review, not external human
peer review or a new proof-assistant build.

## Conclusion

No mathematical error or implicit residue assumption invalidating the new
ordinary existence equivalence was found in the reviewed transformation.
The source-zero, digit, population, and finalizer interfaces have compatible
hypotheses. The full semantic theorem continues to depend on the specifically
retained ordinary native/compiler and refutation calibration; finite circuits
and their audits alone do not establish that theorem.

## Focused checks

1. **Exact translation.** The Laurent identity
   K'_d(U')^d=T^(-s) K_d U^d is correct for every d, and the explicit support
   hypotheses make every delivered exponent nonnegative. For r=1,s=2,
   the new height is H-2 and maximum coordinate weight W-1. The restricted
   maximality argument r<=1 and s<=2r correctly uses the occupied constant
   term of K2; it is not a claim about all layouts.
2. **Weight zero.** The mask proof applies to position zero: its digit B-b
   permits exactly the low log2(b) bits. No low sentinel digit is needed.
   In the actual application B=4096*M*b^2 is strictly larger than b, so
   adding the all-one word to digits z_i<b produces source digits
   p_i=z_i+1<=b<B without carry. The possible units digit does not create
   a missing numerical-ratio premise.
3. **Actual ratio interface.** The retained theorem declarations
   `Jones1982.Nine.ratio_sound` and `ratio_complete` assume R,N>=8,
   0<b<=R,N, positive auxiliary witnesses, margin, and the stated square,
   divisibility, and power-of-two conditions. Neither declaration requires
   b to divide g or R+1. Completeness uses 32g<Gcap, which is exactly
   g<t when Gcap=32t; the canonical packed source has this bound for all
   sufficiently large binary b. The soundness range is the weaker g<4t
   and is the range used in the new carry estimates.
4. **Positive g and b=1.** The independently expanded fifth residual is 1
   at the all-one source tuple for every fixed-port assignment. Therefore
   a genuine source zero yields g>0, including after the weight translation.
   For b=1, the low mask is N0-1 and the recovered 0<g<N0 prevents binary
   disjointness, excluding the endpoint without an artificial b>=2 premise.
5. **Dominance and soundness bounds.** Original31's kernel degrees give
   the claimed linear and constant gaps 25 and 460 relative to the
   positive quadratic head. These establish unconditional G_*>0 before
   knowing that b is binary. On g<4t, the estimate U_*<6bB^115 is valid
   even with a zero weight. The geometric bound
   86*M*b^2/(B-1)<1/32 holds because B=4096*M*b^2. The unchanged target
   headroom H-Q=32 keeps the high-mask estimates valid. Thus the source
   prefix does not import a stronger range than the ratio soundness gives.
6. **Population calibration.** With 116 low radix digits, 31 selected
   low positions, and 22 high target digits, pop(Tc)=138v-31k-22. The
   original31 exponent gives
   u+pop(Tc)=2121*kappa+4212*k-21=2*log2(N), since
   15*2134939-21=32024064. Compact54 similarly gives
   2335*kappa+4640*k-22=2*log2(N), since
   15*864026-22=12960368. Legendre's central-binomial valuation then
   exactly detects zero carry defect after the ratio has recovered binary b.
7. **No premature square extraction.** The strict unconditional root
   majorants and positive E0 force m>0 first. That margin restores the
   old carrier range and gives the strict separation needed for a nonzero
   rational radical sum. Only then is integrality extracted and J|Q
   recovered. The positive saturated ProductPell result applies after its
   C>=2R+1 hypothesis has been recovered. The old numerical ratio theorem
   and calibrated sparse source are composed afterward.
8. **Exact degree.** Original31 has r=7931, nu=2106, a=16357, W=115.
   Substitution into 88a+4r+8W+108 gives 1472168. Compact54's values give
   1626248. The cancellation-resolved norm identity is algebraically
   correct. For the full majorant, the four reported contribution degrees
   948768,997810,989850,752426 have a unique maximum 997810; the relevant
   leading coefficients are positive, so no top cancellation remains.
   The fixed coefficient slice has a nonzero quadratic-kernel head and
   the displayed attained R degree, rather than merely a syntactic bound.

## Remaining scope boundaries

The exact circuit counts and exhaustive finite source interactions are
recorded in the component's independent checkers and receipts; this review
checks their mathematical interpretation rather than claiming to reproduce
all of those computations. The two original native coefficient tuples must
remain separate. The original31 point's lower gate count does not dominate
compact54 in coefficient storage, and the report correctly discloses that
tradeoff. No global minimum or fewer-than-nine-variable claim is justified
or made.
