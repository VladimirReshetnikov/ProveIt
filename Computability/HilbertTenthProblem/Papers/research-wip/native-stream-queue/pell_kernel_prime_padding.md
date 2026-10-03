# Elementary prime padding for simultaneous Boolean residue control

This lemma constructs Boolean subsets of distinct unit-cell positions
covering a growing modulus with an arbitrary fixed odd factor. It addresses
the simultaneous transport and main-index congruences in the proposed
interleaving analysis. It is a mathematical witness construction, not a
free arithmetic instruction, and establishes no universal operation bound.

The argument uses elementary cyclotomic polynomials and a binomial valuation
calculation. It requires no primitive-prime-divisor theorem, Dirichlet's
theorem or unproved prime-distribution assumption. The elementary prime
construction was supplied independently by the input-bridge research lane.

## 1. A suitable fixed prime always exists

Fix integers `Q>=2` and odd `S>=1` with `gcd(Q,S)=1`. Let

    t=ord_S(Q), with t=1 when S=1,
    m=lcm(2,t), A0=m*S*Q*(Q-1).

Let `ell` be any prime divisor of the positive integer `Phi_m(A0)`, where
`Phi_m` is the m-th cyclotomic polynomial. Such a divisor exists:
`m>=2`, `A0>=4`, and the complex-root product for `Phi_m(A0)` has absolute
value at least `(A0-1)^phi(m)>1`. Its value is a positive integer.

The constant term of `Phi_m` is1, so

    gcd(ell, m*S*Q*(Q-1))=1.                             (1)

In particular ell is odd. We also have `ord_ell(A0)=m`. Indeed
`X^m-1` is squarefree modulo ell, since ell does not divide m and its
derivative is `mX^(m-1)`. Its cyclotomic factors therefore have no common
root. If the order of A0 were a proper divisor v of m, then A0 would
be a root of both `Phi_m` and
`X^v-1=product_(j|v) Phi_j`, a contradiction.
Consequently `m` divides `ell-1`, and in particular `t` divides `ell-1`.

Set

    k=lcm(t,ord_ell(Q)), e=v_ell(Q^k-1).

Both orders divide `ell-1`, and (1) excludes `Q=1 modulo ell`. Hence

    2<=k<ell, k divides ell-1, e>=1,
    Q^k=1 modulo S, gcd(ell,S)=1.                        (2)

Everything in this section depends only on fixed Q,S. A finite search or
factorization constructs the data effectively; no complexity bound on
that compiler-time computation is needed.

## 2. An entire additive progression in a short physical interval

Choose a sufficiently large integer n and put

    N=ell^n, T=N/ell^e,
    C0=S*ell^e, M=S*N=C0*T.

Require `n>e`, `T>C0`, and, for a fixed integer shift `s>=2`,

    s+k*(T-1)<N-1, s+1<N-1.                             (3)

All requirements hold for every sufficiently large n, because
`k<ell<=ell^e`.

The binomial expansion gives
`v_ell((Q^k)^(ell^j)-1)=e+j` for all j>=0. More generally a multiplier
coprime to ell does not change this valuation. Thus the order of `Q^k`
modulo N is exactly T. Its order modulo S is1. By the Chinese remainder
theorem its order modulo M is T.

Since `Q^k=1 modulo C0`, its first T powers enumerate exactly

    {Q^(k*j): 0<=j<T} modulo M
      = {1+C0*z: z modulo T}.                           (4)

This is an equality of sets with unique representatives on each side.
It does not assert that z=j. Let `j(z)` be the unique orbit index
corresponding to the additive coordinate z.

All shifted unit-cell positions

    s+k*j, 0<=j<T,

are distinct and lie strictly between cell0 and cellN-1. The extra position
`s+1` is distinct from them because k>=2. Thus their use leaves the first
and last unit cells available for independently fixed marker bits.

## 3. Every residue has a Boolean subset with no position reuse

For any target z modulo M, normalize it by the unit `Q^s`:

    y=z*(Q^s)^(-1) modulo M.

Choose epsilon in{0,1} so that `y-epsilon*Q` is nonzero modulo ell;
epsilon0 works unless y is zero modulo ell, in which case epsilon1 works.
Let kappa be its least residue modulo C0. Then

    1<=kappa<C0<T, gcd(kappa,T)=1,
    y-epsilon*Q=kappa+C0*w modulo M

for a uniquely determined w modulo T. Solve

    kappa*z0+kappa*(kappa-1)/2=w modulo T.                (5)

The inverse of kappa exists. The kappa distinct residues
`z0,z0+1,...,z0+kappa-1` modulo T correspond through (4) to kappa
distinct physical positions `s+k*j(z0+i)`. Their weights sum to

    Q^s*[kappa+C0*(kappa*z0+kappa*(kappa-1)/2)]
      =Q^s*(y-epsilon*Q) modulo M.

Include the extra weight `Q^(s+1)` exactly when epsilon is1. The complete
sum is z modulo M. Every position is used zero or one times. By (3) no
position is0 or N-1. If Q is a power of two, these are literally distinct
binary unit bits in Q-cells, so the constructed integer has no carries
and obeys any periodic mask that permits those unit bits.

This proves full residue coverage modulo `S*N`, using at most `C0` chosen
bits, even though the modulus has an arbitrarily large fixed factor S.
The available unit orbit has T elements and remains inside N cells.
Those two facts avoid incorrectly applying the elementary L-1-weight
lemma to a modulus larger than the number of available bits.

## 4. Useful consequences for transport and main-index residues

The chosen prime also gives

    Q^N=Q modulo S, Q^N=Q modulo ell,
    gcd(Q^N-1,ell)=1.                                   (6)

For the first congruence, t divides ell-1, so `ell^n=1 modulo t`.
For the second use `ord_ell(Q) | ell-1`. The final conclusion follows
from (1).

For example let `S=L*d`, with L,d odd and coprime, and assume
`gcd(Q-1,d)=1`. Then for `q=Q^N`, equation (6) gives

    gcd(q-1,d*N)=1, gcd(L,d*N)=1.

Thus a transport target modulo L and a main-index target modulo dN can
be combined into one target modulo S*N. Reserve the low and top unit
bits, subtract their known residues, and apply Section3 to all remaining
needed residue control. The compiler-specific proof must still establish
its target formulas, mask hypotheses, strict bounds and exact power
transport; this lemma does not assume or supply those conclusions.

## 5. Exact checks and interface

[The checker](explore_pell_kernel_prime_padding.py) exports:

* `choose_prime(Q,S)`: the elementary fixed prime construction;
* `prepare_orbit(Q,S,ell,k,padding_exponent,shift=2)`: the independently
  enumerated modular orbit and its inverse additive-coordinate table;
* `select_subset(orbit,target)`: distinct physical cell positions whose
  Q-powers sum to the target modulo S*N.

The checker verifies the cyclotomic prime conditions, both orders, the
full orbit progression, every selected residue and all reserved-position
bounds. Three small moduli are exhausted; a larger modulus is sampled.
The receipt records13,474 targets, including13,371 exhaustive targets.
The prime and orbit fixtures include S=1 and nontrivial fixed factors.
No enormous positional integer or compiled universal witness is claimed
to have been materialized. Default execution compares the
[saved receipt](explore_pell_kernel_prime_padding.json); `--write` regenerates
it. The proof establishes the general lemma independently of those tests.

Two independent complete proof/source reviews pass, including the elementary
prime choice, progression cardinality, reserved positions and CRT application.
Fresh default receipt replay matches.
