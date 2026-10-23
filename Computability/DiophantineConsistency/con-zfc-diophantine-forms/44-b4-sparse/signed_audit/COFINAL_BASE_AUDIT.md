# Independent cofinal-base and square-w audit

Reviewed repository: VladimirReshetnikov/ProveIt, commit 22e75dd6b87b1b199bb08c778d7cf075ae5aae08. The source files quoted below are copied under upstream/. This is source-level mathematical review, not a Lean rebuild.

## Verdict

The square-base and square-w reductions in packages 34 and 37 are sound. Package 33's caution is correct for the different proposal of merely replacing the old slack epsilon by an arbitrary square. It is not an objection to the scaled-square BASE b=2^kappa epsilon^2, with a sufficiently large odd fixed kappa. Distinguishing base from slack resolves the apparent conflict.

## Exact source evidence and argument

1. In Master3.lean, USys_of_mem, lines 303–510, the source initially chooses k=xy+sum_i n_i+1 and b=2^k. Lines 312–320 establish k>=1, xy<b and n_i<b. Replacing that initial choice by ANY k>=xy+sum_i n_i+1 proves the same three inequalities. All subsequent construction uses b=2^k and those bounds. Digit definitions, transfer identities, coefficient bounds, normalization of g, and the carry tests remain valid. Thus the actual construction is cofinal in the exponent k, not merely in arbitrary integer bases.

2. In NineReduce.lean, reduced_of_mem, lines 271–321, the SAME b and exponent are transported. In particular lines 311–316 set epsilon_old=b-xy-1 and return the existing exponent. No new base is selected or imposed by that step.

3. In Ratio.lean, exists_B25core, lines 434–442, the source takes b=2^k and explicitly sets omega=2^(2R+1-k). It proves k<2R+1 using k<2^k=b<=R. Consequently the natural subtraction has its ordinary positive-integer meaning. For odd k the exponent 2R+1-k is positive and even, so omega is a positive square. The statement is not U=2^R; U=N^2 omega.

4. In NineRatio.lean, ratio_complete, lines 270–280, the construction retains omega from exists_B25core. Product-Pell completeness changes auxiliary i,j and adjusts phi to C-B1-W, but does not alter b or omega.

At input x=1, choose any odd fixed kappa with a=2^kappa>y. Starting from a quartic witness choose r>=0 large enough that k=kappa+2r meets the initial lower bound. Then epsilon=2^r gives b=a epsilon^2, and the canonical omega has a square root w. Conversely epsilon,w nonzero imply b>=a>y and omega=w^2>=1; the old ceiling epsilon_old=b-y-1 is a valid nonnegative integer. This proves both directions.

The failure mode warned about in package 33 is real: replacing epsilon_old by a square would demand b=y+1+u^2 be a power of two, and the cofinality of squares does not guarantee that arithmetic intersection. Packages 34 and 37 do not make that substitution.

## Other signed-domain checks

- The j-guard deletion in package 37 is valid and simpler than the signed-index reflection proof in package 34. Given the already-positive A,C,D,F,G1, the divisibility implies F|H-C; pairwise coprimality makes D,F,I individually square. A positive power of the Pell unit G1+sqrt(G1^2-1) is the identity modulo CF. Multiplying the existing positive real unit sqrt(I)+H sqrt(G1^2-1) by sufficiently large such powers produces positive H' congruent to H modulo CF. Then j'=(H'-B1)/C>0, while the old ratio conditions persist.
- A negative H causes no obstruction: sqrt(I)>|H|sqrt(G1^2-1), so the initial real unit is positive.
- There is no verified square restriction on the canonical s. Its floor/quotient construction is not a square parametrization. No s guard was removed in this audit.
- Package 34's linear-prefix Pell stack is valid and can be combined with package 37's faster coefficient circuit. It improves degree and slightly improves the finalizer circuit. The product-square proof first establishes each factor positive, then each prefix positive; it does not assume those signs prematurely.
- The final three-root separation proof must use absolute weights, allow complex roots, and omit zero roots from sign-pattern uniqueness. Both reviewed formulations meet these requirements.
- The five-degree intersective merger has a nonzero divisor for every integer assignment: J=4A-5!=0, and F=0 would force A=0,E=+/-1, contradicting 5|E. Its numerator never vanishes because the underlying polynomial has no rational root. Thus zeros cannot escape through a zero merger denominator.

## New construction avoids the cofinality gap entirely

The companion fixed-polynomial B4 front end constructs the digit code directly for every sufficiently large power-of-two base. It therefore does not need a generalization of Master3.USys_of_mem at all. It uses the same explicit canonical omega from exists_B25core, whose parity argument remains unchanged. This reduces the source dependency to elementary carries, the generic central-binomial coding lemma, and the literal Jones ratio interface.

## Limitations

The audit of packages 33–37 did not show another sign guard redundant. The new interval-weighted guard in THIRTEEN_GUARD_PROOF.md subsequently combines two guards, with a separate strengthened canonical-witness proof. The new fixed-polynomial front end also permits b=2 epsilon^2 and B=a b^4: only the odd exponent of b controls the square omega, so the coefficient scale a need not enter b. No new compiled formal theorem or end-to-end consistency certificate is claimed. The improved B4 arithmetic-circuit theorem depends on its separately stated universal carry proof and independently checked finite weight/coefficient certificates, plus the unchanged native compiler and K215 endpoint.
