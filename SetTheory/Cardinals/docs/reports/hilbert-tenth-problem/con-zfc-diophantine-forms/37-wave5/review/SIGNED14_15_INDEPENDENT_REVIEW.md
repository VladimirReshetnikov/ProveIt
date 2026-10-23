# Independent review of the cofinal-base and square-scale reductions

Status: the mathematical reductions to fifteen and fourteen unrestricted integer variables pass independent source-level review. This report audits ordinary proofs and dependencies, not a new proof-assistant theorem or the final generated circuit. The sixteen-integer baseline is audited separately.

## Exact sources

All links below use ProveIt commit `8c6eec9d19ef80538c8e61ff6e0180040583446a`.

- [Master3.lean, USys_of_mem, lines 303–510](https://github.com/VladimirReshetnikov/ProveIt/blob/8c6eec9d19ef80538c8e61ff6e0180040583446a/Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master3.lean#L303-L510).
- [NineReduce.lean, reduced_of_mem, lines 271–326](https://github.com/VladimirReshetnikov/ProveIt/blob/8c6eec9d19ef80538c8e61ff6e0180040583446a/Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineReduce.lean#L271-L326).
- [Ratio.lean, exists_B25core, lines 429–560](https://github.com/VladimirReshetnikov/ProveIt/blob/8c6eec9d19ef80538c8e61ff6e0180040583446a/Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Ratio.lean#L429-L560).
- [NineRatio.lean, ratio_complete, lines 265 onward](https://github.com/VladimirReshetnikov/ProveIt/blob/8c6eec9d19ef80538c8e61ff6e0180040583446a/Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineRatio.lean#L265).
- [NineMain.lean, wset_iff_nine, lines 46 onward](https://github.com/VladimirReshetnikov/ProveIt/blob/8c6eec9d19ef80538c8e61ff6e0180040583446a/Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/NineMain.lean#L46).
- [Source 30 compact index, Sections 1–3](https://github.com/VladimirReshetnikov/ProveIt/blob/8c6eec9d19ef80538c8e61ff6e0180040583446a/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/30-quartic31/nine/COMPACT_NINE_PROOF.md).
- [Source 29 signed-domain algebra, Sections 2–5](https://github.com/VladimirReshetnikov/ProveIt/blob/8c6eec9d19ef80538c8e61ff6e0180040583446a/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms/29-simpler-forms/signed17/SIGNED17_PROOF.md).

## 1. The fixed base bound

For source 30's actual compact943 index, let s_index=45933757, z=2^s_index, nu=31, and L=5^32. Its index polynomial has distinct base-(2z) exponent positions in [0,L], and every digit z+c_alpha is an integer strictly between 1 and 2z. Therefore

    0<y<(2z)^(L+1)=2^kappa0,
    kappa0=(45933757+1)(5^32+1).

This uses the entire source-30 tuple and index, not source 29's old T4 index. The bound must be changed if that index is changed. kappa0 is even. For the fourteen-variable construction use the odd exponent kappa=kappa0+1. This still gives 2^kappa>y.

Replace the old expression b=y+1+epsilon by b=2^kappa r^2, with r an unrestricted integer required to be nonzero. Soundness is immediate: b>=2^kappa>y, so epsilon_old=b−y−1 is a nonnegative integer. Every source expression downstream of b agrees after that substitution.

It is NOT sufficient for completeness to say that squares are unbounded: the source representation might in principle impose additional base restrictions. The next two sections inspect its actual proof.

## 2. The master proof permits cofinally many power-of-two bases

USys_of_mem starts with a fixed quartic zero zs, then sets the exponent k=x*y+sum(zs)+1 and b=2^k. Inspection of the entire proof shows that the defining equality for k is used only in the initial derivation of

    k>=1, k<b, x*y<b, and zs_i<b for every i.

Every subsequent invocation uses b=2^k and these inequalities, not the equality defining k. Consequently the same ordinary construction is valid for every k>=x*y+sum(zs)+1. In particular, it is valid for arbitrarily large k in either parity class.

This is a strengthening established by inspection and reproduction of the mathematical proof. It is not the literal quantified conclusion of USys_of_mem, and no new compiled Lean theorem is claimed.

Choose k>=max(kappa,x*y+sum(zs)+1), with k=kappa modulo 2. Then r=2^((k−kappa)/2) is a positive integer and b=2^k=2^kappa r^2. This proves the needed completeness of the new base form without introducing an additional polynomial unknown for k or its half-difference.

## 3. Later reductions preserve that exact chosen base

NineReduce.reduced_of_mem begins with the chosen master-system witness. It then derives the original epsilon=b−x*y−1, identifies the explicit digit-polynomial expressions, and returns the SAME b and the SAME power-of-two exponent. It does not replace b with a new existential choice.

NineMain passes this fixed b, its resulting R and N, and its binomial-divisibility property into NineRatio.ratio_complete. That theorem treats R,N,b as fixed inputs. Its hypotheses require size inequalities, positivity, the binomial divisibility, the ceiling for g, and the fact that b is a power of two. There is no further parity or congruence restriction on its exponent.

Thus the cofinal-base restriction propagates through every later stage of completeness. Soundness uses the old nonnegative epsilon reconstructed from b, then the source ratio soundness and reduced-system soundness. One does not need to prove that arbitrary nonzero r itself is a power of two.

## 4. An odd exponent also makes the canonical w a square

The actual ratio-completeness construction is stronger than needed for fifteen variables. In Ratio.exists_B25core, lines 434–442, write b=2^k. The source explicitly defines

    w=2^(2R+1−k), U=N^2 w,
    b w=2^(2R+1).

The exponent is positive, because k<2R+1 follows from k<2^k=b<=R. Hence if k is odd, 2R+1−k is a nonnegative even integer, and w is a positive square.

This is the exact source formula. The alternate claim U=2^R is false for this Jones ratio construction and must not appear in the report. No parity property of R is required.

Because kappa=kappa0+1 is odd, the cofinal bases above all have odd k. Replace w by u^2, with u an unrestricted nonzero integer. The same canonical completeness witness admits u=2^((2R+1−k)/2). In NineRatio.ratio_complete, the subsequent product-Pell step chooses i and j but does not alter h,s,w or the already fixed base. Therefore square-w completeness persists to the final ratio predicate.

For soundness, any nonzero u gives w=u^2>=1, so the old coordinate w0=w−1 is nonnegative. Nothing else in the signed-domain restoration requires a stronger condition on w.

## 5. Integration with the signed finalizer and variable count

Retain all eight base coordinates, but use r in place of the old epsilon coordinate and u in place of the old w0 coordinate. The only remaining coordinate inequalities are g0>=0, s0>=0, and phi>=0, along with m>0. Encode those four inequalities with four Pell-stack variables.

Enforce the joint nonzero condition through

    Z=r u (i0+1) z1 z2 z3 z4.

The intersective merger then excludes every zero r,u,i or stack coordinate. The global denominator proof still holds for every integer assignment before those facts are recovered. After recovery, b>y and w>0 allow the source h proof; its reasoning uses these numerical facts, not the syntactic form b=y+1+epsilon or w=w0+1. The audited j-restoration argument then supplies a nonnegative j0 witness. Signed-i symmetry is unchanged.

There are 8 base coordinates + 4 stack variables + v and finalizer-u = 14 unrestricted integer unknowns. Names must be disambiguated in the final artifact: the square-scale coordinate u and the finalizer coordinate should not share a printed symbol.

The fifteen-integer variant drops only the epsilon guard; it can use either kappa0 or kappa. The fourteen-integer variant requires the odd choice kappa=kappa0+1. Keep the sixteen-variable baseline as a comparison and fallback, not as evidence for cofinal completeness.

## 6. Final-artifact obligations

- Preserve all fixed source-30 coefficients and index recipes as one bound tuple; no T4/Wang943 coefficient splicing.
- Include the cofinal-base proof and the exact source formula for square w; existence of the old nine-variable polynomial alone does not imply these stronger completeness properties.
- Add r and the square-scale coordinate to the nonzero multiplier, and remove only their inequality stack factors.
- Keep h and j as unrestricted input coordinates; their restoration proves existence, not positivity of the initially supplied values.
- Recompute circuit fidelity, operation count and exact degree after both quadratic substitutions; do not reuse the sixteen-variable metrics.
- A nonzero leading-form proof is needed for an exact degree, and a fixed power-of-two leaf has positive but enormous height. Do not confuse it with the smaller native coefficient radix.
- The end-to-end consistency claim still imports ordinary compiler/calibration theorems. This review does not establish consistency, a global variable minimum, or a new kernel certificate.
