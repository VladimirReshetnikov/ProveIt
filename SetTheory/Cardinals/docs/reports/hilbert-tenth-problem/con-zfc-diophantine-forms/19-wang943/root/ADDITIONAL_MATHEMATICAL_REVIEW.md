# Additional mathematical review

## Root reconstruction

The norm is evaluated in a free rank-four algebra. Its specialization to any real square roots of A1,A2 is the product over all four sign choices, even when the two quadratic fields coincide or a radicand is a square. Thus a zero supplies a genuine factor-zero branch without a genericity assumption.

All recovered quantities lie in Q(sqrt(A1),sqrt(A2)). Every automorphism fixes the integer linear combination Z. The two strict weight inequalities first fix sqrt(A1) and then sqrt(A2); rationality follows also in the degenerate field cases. In the scaled-auxiliary version, rational rho has integral square after f is recovered and hence is integral. The congruence K=1 mod H then recovers integral gamma. The rational auxiliary Pell saturation lemma supplies integral y without imposing extra divisibility on the original strong multiplier i.

The restricted-i variant needs a finite Pell-unit period modulo H*c^2 for completeness. Multiplication of the original index by H alone is not generally sufficient. The finalized proof makes this distinction.

## Uniform degree of the 26-integer polynomial

Write Q0=beta*J and k0=eta+zeta. The scaled-y twelve-variable resultant's highest term comes from the fourth powers of the four leading linear conjugates, whose multipliers are -6,-4,6,8. Their product is 1152. In the full positive-variable product, a nonzero monomial is

    J^1013 h i^64 eta^144 w^129 s^273 z

with coefficient 2^76 * 3^8 * beta^1013. Its total degree is 1625.

Under the seven disjoint ternary positivity parametrizations, the square substitution for w, and the odd substitution i=2r+1, all contributing variables except h and i have weight two. The degree is therefore

    2*1625 - 64 - 1 = 3185.

The selected monomial has coefficient 2^140 * 3^8 * beta^1013, nonzero for the actual positive beta. The sign-safe bound changes only lower-degree terms. The other fixed compiler ports occur below these leading terms, so the calculation is uniform for the complete selected tuple, not merely for sampled coefficient values.

## Compiler and domains

The directed-signal tile recipe retains every actual working transition, including the write and move entering halt. Start implements the authentic first action. The absence of directed colors on seams prevents a head from escaping, and the HB color propagates every reset row across its entire finite strip. Independent left/right seam colors are needed for the helical time offset. Occupancy bits in the binary edge labels propagate the selected cell through the spatial shift-one cycle.

Positive, nonnegative and unrestricted-integer domains must remain distinct. The twelve-variable equations are positive-domain constructions; the 26-integer version uses its own signed-bound and zero-branch argument. The zero-square-w branch is ruled out before invoking the positive-X dominance bound, and the zero-T branch is ruled out before division by its associated coefficient.

This is a mathematical review of the stated reductions. It is not a proof-assistant certificate, an accepting K215 computation, or a proof of Con(ZFC).

## Final unscaled saturation simplification

Saturation can be applied before recovering gamma. Once tau,g,f are integral, V=v*f-b is integral, so the rational auxiliary Pell equation already forces y integral. Then K*gamma=t-M*tau-y is integral and K=1 modulo H forces gamma integral. Thus neither the restriction i=H*j nor the replacement rho=d*y is needed. If Baux=0 in the signed construction, V=-b is integral independently of f, and the same saturation argument is available before the zero-scale contradiction.

For the final unrestricted-i, unscaled-y polynomial, the nonzero leading monomial is

    J^789 h i^48 eta^112 w^97 s^209 z

with coefficient 2^76 * 3^8 * beta^789 and total degree1257. The seven positivity blocks and square-w/odd-i substitutions therefore give degree

    2*1257 - 48 - 1 = 2465,

and coefficient 2^124 * 3^8 * beta^789. This supersedes the degree1625/3185 scaled-y forms as the recommended route. The earlier analysis remains valid for those precursor forms.

The final integer circuit reuses the already computed v^2 and takes W=2*((S*i)*v^2+b). For integral v, v^2>=|v|; for nonzero integral i, S*i>=|S|. This is the same strict conjugate bound, including v=0, without computing v*T. Its weighted-degree contribution68 is below the degree74 contribution of b, so the degree and leading coefficient are unchanged. The final ledger is192 operations (117 multiplications,75 additions/subtractions), replacing the193-operation draft.
