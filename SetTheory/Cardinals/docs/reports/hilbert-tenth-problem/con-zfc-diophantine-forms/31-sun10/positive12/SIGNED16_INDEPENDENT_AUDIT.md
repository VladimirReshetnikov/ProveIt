# Independent audit of the proposed sixteen-integer reduction

Audit date: 22 October 2026 (user timezone).
Repository pin: `8c6eec9d19ef80538c8e61ff6e0180040583446a`.

This is an ordinary mathematical source audit, not an independent proof-assistant
certificate. It checks the two new conceptual steps against the signed17 proof
and the Jones source construction available in this workspace.

## 1. Cofinal parity restriction on the binary base

`Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/Master3.lean`,
the theorem `USys_of_mem`, chooses

    w = x*y + sum_i zs_i + 1,   b = 2^w.

Reading the full construction shows that the exact equality for w is used only
to obtain `1 <= w`, `x*y < b`, and `zs_i < b`, after invoking `w < 2^w`.
The downstream construction of q, lambda, theta, e, ell, g, the bitwise
conditions, and the master system uses these consequences and `b=2^w`.
Therefore the same proof constructs witnesses for **every** integer exponent

    w >= x*y + sum_i zs_i + 1.

Let kappa=2^c be any fixed power of two exceeding the fixed index y. Restrict
to exponents w=c+2r, with r chosen sufficiently large. Then t=2^r is a positive
integer and b=kappa*t^2. Every source quartic witness still has a Jones witness
at such a base. The chain in `NineReduce.reduced_of_mem` and
`NineRatio.ratio_complete` does not introduce an incompatible upper bound on b.

In the soundness direction, nonzero arbitrary integer t gives
b=kappa*t^2 >= kappa > y. Thus epsilon=b-y-1 is a nonnegative integer, and the
original Jones signed-coordinate soundness theorem applies to the unchanged
expressions evaluated at that b. One does not assume t is a power of two in
soundness; that is only an explicit family of completeness witnesses.

For kappa=(2z)^(L+1), the bound kappa>y follows from the index digit polynomial:
its coefficients lie in [0,2z-1] and its degree is at most L. Consequently its
value at 2z is strictly below (2z)^(L+1). Because z is a power of two, kappa is
also a power of two. This proof should be stated explicitly in the report.

## 2. Removing the epsilon guard

The signed17 construction guards epsilon,g0,s0,w0,phi,j0 and the positive margin.
After b=kappa*t^2 and a nonzero requirement on t, epsilon's sign is automatic.
The remaining guard list is g0,s0,w0,phi,j0 followed by the margin, so it has
six Pell witnesses instead of seven. The eight base coordinates become
t,g0,h0,s0,w0,phi,i0,j0. Adding the six Pell witnesses and the two relation-
combining witnesses gives sixteen unrestricted integer variables.

The final optimized version takes Z=(i0+1)*product_j z_j, without a factor t.
The homogeneous intersective lemma makes S=Z*D0^5 nonzero at every final zero,
forcing the guarded Pell witnesses and i to be nonzero. After square recovery
and the guard inequalities, t!=0 follows automatically: t=0 would imply b=0
and Gcap=0, hence margin=-8*g*K^2<=0, contradicting margin>0 and g>=1.
Thus nonvanishing of t need not be separately encoded. The existing argument
T!=0 excludes S=0 before any inequality is recovered.

## 3. Smaller root-separation weights

For each Pell-stack factor

    B_j = 1 + 4*d_j*C_(j-1)^2*z_j^2,

d_j is 2 modulo 3, so it is nonzero for every integer input. After S!=0 has
forced every z_j!=0, induction gives C_(j-1)!=0. Hence B_j!=1. Also B_j is 1
modulo 4, so it is neither zero nor -1. Thus |B_j|>1 and |Cstar|>1.

The proposed w1=Cstar therefore satisfies

    |w1|=|Cstar|>sqrt(|Cstar|).

The established elementary bound

    sqrt(|(P^2-1)K^2+1|) <= P^2+K^2+1

and w2=Cstar*(P^2+K^2+2) give

    |w2| > sqrt(|Cstar|) + |w1|*sqrt(|a0|).

The three-root separation argument only uses magnitudes of these weights,
so their possible negative signs do not affect the Galois-conjugation proof.
This order matters: establish S!=0 first, then these inequalities, then recover
the three integer square roots. It would be circular to invoke the guard
inequalities to establish the weights before root recovery.

## Conclusion and boundary

No obstruction was found in the removal of the base guard or in the smaller
weights. They are supported by the exact source construction and elementary
arguments above. The final deliverable must still bind the chosen quartic31
and its fixed index as a single coherent instance, transcribe the literal
sixteen-variable circuit correctly, and preserve the source compiler and K215
semantic dependencies. This audit does not check those bytes or certify a
new kernel-checked end-to-end theorem.
