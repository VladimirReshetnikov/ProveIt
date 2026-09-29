# Rejected bound simplification: a symbolic counterfamily

This is an exploration note, not part of the final article or a new
certificate. It explains why replacing

    e + l*C^4 + alpha = q

by the one-operation-cheaper condition

    e + (b-1)*l + alpha = q

cannot be justified merely from the remaining coding equations and `r>0`.
The product `(b-1)*l` is already available in the T computation, but the
replacement loses necessary pre-Pell size information.

Fix any admissible coefficient data Z,V, with Z=2z=2^s and z>=4. Put
F=Z-1, so F>z. Choose an arbitrarily large positive integer k satisfying
k=-2 modulo F, and define

    B=Z^k, H=B/16, b=2, x=1, beta=1.

For k large enough, H is a power of two satisfying every lower bound in
the admissibility conditions. The binomial theorem gives

    B=(1+F)^k = 1-2F modulo F^2.

Therefore the following are positive integers:

    q=(B+F-1)/F,
    lambda=(B+2F-1)/F^2,
    theta=B-Z,
    t=V,
    l=F*V-1,
    e=q-V*(2Z-3),
    alpha=V*(Z-2)+1.

The positivity of e holds for all sufficiently large k. These definitions
satisfy the weaker bound, geometric equation, and packed congruence exactly:

    q^2-1=lambda*(B-1),
    theta+Z=B,
    e+l+alpha=q,
    e+l*q=V+t*theta.

Nevertheless q<B. Moreover

    D0=z*lambda-e
      = ((z-F)*B+z*(2F-1)-F*(F-1))/F^2 + V*(2Z-3)

is negative for all sufficiently large k, since z-F<0. Consequently,
for every positive integer g, with C=1+xB+g, the shortened third block

    S3=(2e-Z*lambda)*C^4+B*lambda*(1+q^2)

is positive: its first term is -2*D0*C^4>0. Also q>l follows from the
weaker bound, so

    Tplus=q-l+theta*lambda*q+(B-2)*q^4

is positive. Hence S=g+q*(e+l*q+q^2*S3)>0; setting n=q^8 and

    r=S*(n^2-n)+Tplus*(n^2-1)

gives r>0 and satisfies the defining r equation. The choice of g is
unbounded, so neither g<q nor C^4<q follows. S3 can exceed its intended
packing width by arbitrarily much.

This is a counterfamily to the proposed preliminary implication only.
It does not assert that all the subsequent Pell equations can be solved
for these values, nor that the fully weakened system is universal or
non-universal. Any successful use of the weaker bound would require a
new argument that uses those additional equations; r>0 alone is insufficient.
