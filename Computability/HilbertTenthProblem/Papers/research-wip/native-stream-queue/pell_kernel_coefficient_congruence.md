# Using the whole weakened norm coefficient as index modulus does not repair it

Replace the weakened kernel's `U=jc-J` by `U=jK-J`, where its existing
register is `K=ic^2=Delta(f^2-1)`. This is a same-cost source change: the
kernel remains42=24M+18A and the full candidate remains75=40M+35A,
with30 positive coordinates and19 equations. It retains the canonical
complete76 completeness map, but the exact wrong-index auxiliary family
survives the stronger modulus.

This is a refutation of the proposed kernel repair. No actual compiler
packing or false ordinary input is supplied. The soundness of the
original complete75 candidate remains open; the established complete
universal bound remains76.

## 1. Literal source and canonical completeness

Keep the other source equations of the
[single-product candidate](../../1980/EXPLORATION_SINGLE_PRODUCT_AUXILIARY_SCALE.md).
The three auxiliary equations are now

    K=ic^2=Delta(f^2-1),
    K(U^2-y^2)=1-y^2,
    U=jK-J=of-c,  J=2r+1.                            (1)

In the DAG replace only `jc=j*c` by `jc=j*ic2`. The `ic2` register is
already available before this instruction, so this introduces neither
an extra operation nor a dependency cycle. The changed source polynomials
are precisely the last auxiliary norm and last congruence. The checker
independently expands all19 comparisons and their norm correction.

For canonical complete76 witnesses, let

    m=2cJ, f=chi_A(m), R=Delta*psi_A(m),
    i_new=(R/c)^2, K=R^2,
    U=chi_R(J)/R, y=psi_R(J).

The retained strong construction makes c divide R and all these
coordinates positive. Since J=3 modulo4, the normalized odd-index
polynomial has constant term -J, giving `U=-J modulo K`. Thus set
`j_new=(U+J)/K`, a positive integer. Retain `o=(U+c)/f` and every other
coordinate of the canonical map. All three equations(1) hold.

This completeness statement uses fresh canonical witnesses, not a claim
that an arbitrary old supplied value of j can be divided by K/c.

## 2. Exact even-modulus CRT criterion

For A>=2 and odd p>=3 put

    Delta=A^2-1, c=psi_A(p), d=chi_A(p),
    f=2d^2-1, R=2Delta*c*d,
    K=R^2, i=4Delta^2*d^2,
    sigma=(-1)^((p-1)/2), g=gcd(p,K).                 (2)

Then `K=ic^2=Delta(f^2-1)` and `R>f>2c`. Also c is odd. If A is
even, d is even and Delta is odd; if A is odd, Delta is divisible by8.
In either case K is divisible by16. Since p is odd,
`gcd(4p,K)=4g`, and g is odd.

For an odd integer 0<J<c seek t>=0 satisfying

    s=p+4pt=-sigma*J modulo K,
    (-1)^t=-sigma.                                   (3)

These conditions are soluble exactly when

    g divides J,  J=p+1+sigma modulo8.               (4)

To prove this, the congruence for t is
`4pt=-sigma J-p modulo K`. Its ordinary solvability requires
`4g | -sigma J-p`. The condition on odd g is g|J; the modulo4 part
requires J=3 modulo4. Divide by4g to obtain

    t0=[(-sigma J-p)/(4g)]*(p/g)^(-1)
                                      modulo K/(4g). (5)

The reduced modulus is divisible by4, so parity of t cannot be altered
by adding it. Modulo8, the first congruence forces the desired parity
exactly when `J=p+1+sigma modulo8`. This condition includes J=3 modulo4
and proves both directions of(4). Take the least nonnegative solution
of(5). Then s>=p>=3. There is no unpaid parity adjustment of an
even-modulus solution.

## 3. All auxiliary equations and strict positivity

For the s just constructed set

    U=chi_R(s)/R, y=psi_R(s),
    j=(U+J)/K, o=(U+c)/f.                            (6)

For odd s, `chi_R(s)/R=Q_(s-1)/2(R^2)` is an integer polynomial in K,
with constant term `(-1)^((s-1)/2)*s`. Since s=p modulo4, (3) gives

    U=sigma*s=-J modulo K.                           (7)

The same polynomial identity used by the existing wrong-index family
gives `U=sigma*psi_A(s) modulo f`, because
`K=1-A^2 modulo f`. Also
`psi_A(p+4pt)=(-1)^t*c modulo chi_A(2p)=f`. Therefore(3) yields

    U=sigma*(-1)^t*c=-c modulo f.                    (8)

Equations(7)–(8) make j,o integers. They are strictly positive: s>=3
and `U>=4R^2-3=4K-3>max(c,f,J)`. The Pell norm at R gives the middle
equation of(1), and the coefficient identity in(2) gives the first.
Thus all repaired auxiliary equations hold exactly.

For example A=4,p=3,J=27 and A=2,p=7,J=63 satisfy(4) with t=2 and s=J.
The checker materializes their entire auxiliary tuples. Their actual
main indices p differ from J despite the repaired modulus.

## 4. Attach the existing full wrong-index kernel

Use the [dyadic-balanced example](../../1980/EXPLORATION_DYADIC_BALANCED_WRONG_INDEX.md):

    q=16, r=269, J=539, p=329,
    X=2^329, Y=2^91, a=Y(X+1), A=a+2.

The old exact seven first/main equations and scale bounds are unchanged.
For its actual main coordinates,

    gcd(p,c)=gcd(p,Delta)=gcd(p,d)=1,
    gcd(4p,K)=4, K=16 modulo32.

Here sigma=1 and `J=3 modulo8=p+2 modulo8`, so(4) holds. Formula(5)
becomes

    t=-217*329^(-1) modulo K/4.

This t is odd. It gives `s=p+4pt=-J modulo K`, and(6) completes all
three repaired auxiliary equations. The checker computes these CRT
precursors exactly: K has554875 bits, its reduced modulus has554873
bits, and s has554882 bits. It does not materialize the final Pell
outputs at this enormous s; identities(7)–(8) supply their residues.

The main index is still329 instead of539, and
`popcount(269)=4<12`. Thus the required4096 divisibility of the central
binomial coefficient still fails. The same bounded numerical input
bridge at u=3,W=8 also attaches, using its unchanged main coordinates.
This numerical bridge is not identified with the actual compiled
`u=2d*x+b`, and no false compiled input is claimed.

## 5. Evidence

The [checker](pell_kernel_coefficient_congruence.py) audits the full75
DAG and19 independent source polynomials. It checks the exact CRT
criterion over bounded A,p,J, materializes two complete auxiliary tuples,
and attaches the new CRT to the actual q16 wrong-index tuple. The
[receipt](pell_kernel_coefficient_congruence.json) records sizes instead
of printing enormous integers. Canonical completeness and the final
large Pell extension are parametric mathematical proofs; finite checks
are supplementary. Independent full proof, source, and default-replay
review passed, including the even-modulus parity condition and the actual
wrong-index main tuple.
