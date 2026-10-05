# A repunit-divisor boundary for fixed polynomial index families

The literal packed index of direct-X83 is divisible by its supplied repunit
coordinate J. Consequently a fixed rational polynomial ansatz for R can
support infinitely many such q only if its numerator vanishes at q=1.
For the canonical family q=B*3^k, R=2*3^(3k+c)-3, every fixed integer c
fails this necessary condition. There are only finitely many candidate q
for that c, before imposing any native, input, positivity or kernel tests.
This is a necessary-condition theorem, not a decision procedure for the
full direct-X83 source and not a reduction of the universal84 bound.

## 1. The exact divisor and a general polynomial obstruction

Fix an integer B>=2. The authentic repunit and literal packed index are

    q=(B-1)J+1,
    R=(q*U-Z)(q^2-1)+(MC+q*MF_source)*J.                 (1)

All coordinates in this paragraph are integers and J>0. No assumptions
on the signs of U,Z or the masks are needed. Since J divides q-1, it
divides q^2-1; both summands in R are therefore multiples of J. Thus

    J divides R.                                        (2)

Suppose, in addition, that a fixed nonzero integer D and a fixed polynomial
P(T) with integer coefficients obey

    D*R=P(q).                                           (3)

Reducing modulo J gives P(q)=P(1) modulo J because q=1 modulo J.
Together with (2), this proves

    J divides P(1).                                     (4)

No cancellation by D modulo J, and no coprimality assumption on D and J,
is used. If P(1) is nonzero, J<=abs(P(1)) and hence

    q <= (B-1)*abs(P(1))+1.                              (5)

This is a finite explicit bound depending only on the fixed ansatz and
radix. It applies even if a different integer tuple U,Z and masks is
permitted at each q. Such freedom cannot remove the factor J in (1).
It also does not matter whether these tuples satisfy any other equations.

## 2. Every fixed three-adic offset has only finitely many candidates

Fix B=2^d with integer d>=1 and any fixed integer c. For positive integers
k with e=3k+c>=1, consider

    q=B*3^k, R=2*3^e-3.                                 (6)

Only k for which J=(q-1)/(B-1) is an integer are candidates. Set

    a=max(c,0), h=max(-c,0),
    D=3^h*B^3,
    P(T)=2*3^a*T^3-3^(h+1)*B^3,
    N=P(1)=2*3^a-3^(h+1)*B^3.                           (7)

These are fixed integers; D>0 and (6) gives D*R=P(q) exactly.
Moreover N is nonzero. If a=0, its first term2 is not divisible by3,
whereas the second term is. If a>0 then h=0; equality N=0 would give
3^(a-1)=2^(3d-1), which is impossible since 3d-1>=2 and the two sides
have incompatible prime factors. Therefore (5) gives

    B*3^k <= (B-1)*abs(2*3^a-3^(h+1)*B^3)+1.             (8)

Every fixed integer offset c has only finitely many possible exponents k
satisfying the literal index. In particular no fixed-c infinite canonical
family of this form can be completed to direct-X83 zeros. This conclusion
does not use the valuation of Y, the population of R, C>=0, the numerical
window for R, or any special congruence choice for k.

The exponent c is a parameter of this proposed family, not one of the
unchanged source's paid ports. The theorem does not give a uniform finite
bound when c varies with k: its right side explicitly depends on c.

## 3. Direct exclusion of the authentic radix-compatible progression

Root proposed, and Pascal separately proved the scalar properties of,
the progression

    d an authentic odd exponent with25|d, B=2^d,
    c=2^(3d+1), o=ord_(B-1)(3), L=lcm(o,c),
    k=n*L for n>=1, e=3k+c.                             (9)

The authentic exponents are odd powers of5, so the unit order exists.
Pascal's separate packet proves canonical q^3 divisibility, the literal
repunit, and the numerical outer bounds, and excludes the family by its
forced marker together with C>=0. Here (2) gives another exclusion that
requires neither a marker bound nor C>=0.

Since 5 divides d, 31 divides B-1. The order of3 modulo31 is30:

    3^30=1, 3^15=30, 3^10=25, 3^6=16 modulo31.

The three proper tests exclude division of30 by any of its prime divisors;
the order is exactly30. Reduction modulo31 shows 30 divides o. Since c is
a power of2, L is a multiple of15c, so k>=15c>c. Also

    J=(B*3^k-1)/(B-1) > 3^k > 2*3^c.                    (10)

In (7), a=c and h=0. Its N=2*3^c-3B^3 is positive: c>3d implies
c>=3d+1, whence 2*3^c>=6*3^(3d)>3*2^(3d)=3B^3.
Consequently 0<N<2*3^c<J, contradicting J dividing N.
Every positive member of (9) fails the exact packed index itself.

## 4. Boundaries, retained failures and attribution

**Remark 1 (the fixed-offset infinite-completion proposal fails).** The
preliminary proposal that a sufficiently large fixed-offset progression
(6) might supply infinitely many literal packed completions is false.
Equations (4)--(8) give its explicit finite obstruction, even if the
repunit, canonical cubic divisibility and outer numerical bounds have
already been proved. Section3 excludes every member of the particular
authentic progression (9). The corresponding scalar kernel theorems
remain valid and do not assert a compiler zero.

**Remark 2 (the nonzero remainder hypothesis cannot be dropped).** The
stronger assertion that every fixed polynomial ansatz has finitely many
repunit-compatible packed indices would be false. Take P(T)=T^2-1,D=1.
For each J>0 and q=(B-1)J+1, choose U=1,Z=q-1,MC=MF_source=0 in (1).
Then R=q^2-1=P(q) for every J. These are integer examples for the divisor
statement, not valid compiler masks or full source zeros. Here P(1)=0,
so (4) is vacuous, exactly as the theorem requires.

**Open question 1.** The original direct-X83 proposal still requires
q dividing X on every complete positive zero. This report excludes a
family of proposed counterexamples; it does not prove that obligation.
Varying offsets c(k), or a different canonical relation between q and R,
would need to satisfy J dividing R and all the other authentic conditions.
No construction or impossibility theorem for those remaining cases is
claimed here. The source of this direction is the existing direct-X83
review and Pascal's canonical valuation families.

Root derived the divisor and fixed-polynomial obstruction while reviewing
Pascal's radix-compatible construction. The literal equations are read
from the committed `direct_X_authentic_outer_root.md` lines1--49, whole
SHA256 `35d5d5080a615583779f31b1985768045455ab6cbbfc394dac4b93cc2713a617`.
The actual radix hypothesis and modulo31 order are in the committed
`direct_X_canonical_three_adic_family_pascal.md` and its root review.
The modified recipe is `complete75_half_binomial_compiler.md` lines1--70,
SHA256 `68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117`.
The separate radix-compatible note is a dependency for its quoted scalar
claims only; this report supplies its own proof of the exclusion.

No saved program, scientific helper or source array is evaluated. Any
accompanying receipt authenticates bytes and read spans only. The proof
is by integer divisibility and explicit inequalities and involves no
numerical materialization of authentic compiler parameters or witnesses.
