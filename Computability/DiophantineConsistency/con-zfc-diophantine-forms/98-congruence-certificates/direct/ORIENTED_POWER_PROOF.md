# An eleven-coordinate positive-power certificate

All coordinates in this note range over the nonnegative integers. The inputs
`n,k` must be strictly positive. The output is `m`. This is a specialization
of the Pell--Matiyasevich criterion, not a new proof of that criterion.

## The intermediate fourteen-coordinate certificate

There are fourteen additional coordinates

    A, X, U, S, R, z, y, q, d, g, b, s, r, h.

Define the following polynomial abbreviations; none is another quantified
coordinate:

    W = n+k,
    Z = z+1,
    Y = k+y,
    T = m+g+1,
    V = Y^2(d+1),
    B = 1+4Y(q+1).

Write `N(a,x,y)=x^2+y^2-1-a^2 y^2`. The nine equations are

    N(A,X,Y) = N(A,U,V) = N(B,S,R) = 0,
    B = A+Ub,
    S = X+Us,
    R = k+4Yr,
    X+Yn = YA+m+Th,
    2An = T+n^2+1,
    N(W+1,A,WZ) = 0.

**Theorem.** For every positive `n,k` and natural `m`, the nine equations
have a natural solution in the fourteen additional coordinates if and only
if `m=n^k`.

## The original criterion being used

The pinned Mathlib theorem `Pell.eq_pow_of_pell`, together with the
Matiyasevich Pell-index certificate, gives the following positive-input
criterion. Existentially choose natural `W,A,T,Z,X,Y,U,V,S,R,B` such that

* `A>=2`, `Y>=k`, `B>=2`;
* the first three norms above vanish;
* `B=1 mod 4Y`, and `V` is a positive multiple of `Y^2`;
* `B=A mod U`, `S=X mod U`, `R=k mod 4Y`;
* `X+Yn=YA+m mod T`, `2An=T+n^2+1`, and `T>m`;
* `W>=n,k` and `N(W+1,A,WZ)=0`.

These conditions are equivalent to `m=n^k`. The positivity of `n,k` is
part of the criterion. The repository wrappers `PellRepresentation.lean`
and `PowerRepresentation.lean` and the primary Mathlib source are included.
The Mathlib source is pinned at
`81a5d257c8e410db227a6665ed08f64fea08e997` (the repository's v4.32 pin).

## Soundness of the new graph

Here `W=n+k>=2` and `Z>=1`. The last norm is

    A^2 = 1+W^3(W+2)Z^2.

Thus `A>W>=n` and in particular `A>=2`. The definitions give `Y>=k>=1`,
`B>=5`, `V>=Y^2`, and `T>m`. Each of the four oriented equations implies
the corresponding original congruence. Every remaining original condition
holds literally. The original criterion therefore proves `m=n^k`.

## Why all four quotients are natural

This part applies to any solution of the original positive-input graph,
not just to a canonical completeness witness.

Since `V>=Y^2>=Y>=1`, the first two norms imply `U>=X` and `U>=A`.
Both `B` and `S` are positive: `B>=2` is explicit and the third norm
implies `S>=1`. If `0<a<=u`, every positive natural number congruent to
`a mod u` is `a+u q` for a natural `q`. This remains true at `a=u`,
because the residue-zero representative must be positive. Apply this with
`(a,u)=(A,U)` and `(X,U)` to get the first two oriented quotients.

Next `0<k<=Y<4Y`, so a natural number congruent to `k mod 4Y` is
`k+4Y r` with `r>=0`.

For the last quotient, the first norm gives

    X^2-(A-1)^2Y^2 = 1+2(A-1)Y^2 > 0,

and hence `X>(A-1)Y`. Since `n>=1`,

    X+Yn-YA > (n-1)Y >= 0.

Consequently `D=X+Yn-YA-m > -m > -T`. The original power congruence
makes `D` an integer multiple of the positive `T`. It follows that
`D>=0`, giving `D=Th` with natural `h`. This proof is the reason the
sign of the last quotient is safe; positivity of its individual summands
alone would not suffice.

## Fixing W without losing completeness

The standard Mathlib completeness proof sets `W=max(n,k)`, then uses only
`W>=n,k` and `W>0`. The same explicit construction works with `W=n+k`.
For parameter `a>=2`, let `x_j(a),y_j(a)` be the nonnegative Pell sequence

    x_j(a)+y_j(a)sqrt(a^2-1) = (a+sqrt(a^2-1))^j.

Set

    A=x_W(W+1),    Z=y_W(W+1)/W.

The congruence `y_j(a)=j mod(a-1)` makes `Z` an integer. It is positive,
and the last norm holds. The elementary Pell growth estimate gives

    n^k <= n^W < (W+1)^W <= A.

The first strict inequality needed here is the comparison of the bases
`n<W+1` at positive exponent `W`; no strict comparison of `n^k` and
`n^W` is claimed. In particular `A>m=n^k>=n`.

Now set `X=x_k(A)`, `Y=y_k(A)`, and `T=2An-n^2-1`. Then `Y>=k`.
Because `A>=n+1`,

    T-A = (2n-1)A-n^2-1 >= n^2+n-2 >= 0,

so `T>=A>m`. Reducing in the quadratic ring modulo `T` and substituting
`sqrt(A^2-1)=n-A` gives `X+Yn=YA+n^k mod T`.
The standard Pell-index certificate supplies `U,V,S,R,B` for this fixed
`A,X,Y,k`. Thus the original positive graph has a solution with the
specified `W=n+k`.

Apply the quotient argument above. Define `y=Y-k`, `d=V/Y^2-1`,
`g=T-m-1`, and `z=Z-1`. Since `B>=2`, `Y>=1`, and `B=1 mod4Y`,
its quotient `(B-1)/(4Y)` is at least one; therefore
`q=(B-1)/(4Y)-1` is natural. These substitutions and the four oriented
quotients give exactly the fourteen-coordinate certificate.

## Exact elimination to eleven coordinates

The preceding graph is a convenient proof interface. Its last norm gives
`A>W>=n`, so replace `A` by `n+a+1` with a new natural coordinate `a`.
This is a bijective reparameterization. The three directed equalities
can now be solved by polynomial substitution:

    X = Y(a+1)+m+Th,
    S = X+Us,
    R = k+4Yr.

All coefficients in these defining expressions are nonnegative. They
therefore eliminate three primitive coordinates and their three equations
without imposing any additional condition. The eleven remaining coordinates
are

    U, a, z, y, q, d, g, b, s, r, h.

The defined expressions are `W=n+k`, `Z=z+1`, `Y=k+y`, `T=m+g+1`,
`A=n+a+1`, `V=Y^2(d+1)`, `B=1+4Y(q+1)`, and the displayed `X,S,R`.
The final six equations are

    N(A,X,Y) = N(A,U,V) = N(B,S,R) = 0,
    B = A+Ub,
    2An = T+n^2+1,
    N(W+1,A,WZ) = 0.

Existence in these eleven coordinates is therefore exactly `m=n^k` for
positive `n,k`. This is the actual graph materialized by the builder.
The exact symbolic audit verifies all six equations after eliminating
every arithmetic gate, and verifies all three restoration identities.

## The global CRT evaluation quotient

The direct construction represents its local row as `P=E-F`, where `P`
is a product of sums of squares plus further squares. Consequently
`E>=F` on every natural assignment, without assuming that any rule is
valid. The final congruence `B divides E-F`, with `B>0`, can therefore
be written `E=F+Bq` using one natural quotient. This saves the two-natural
representation of a signed quotient at that final call site as well.

## Completed direct polynomial and exact counts

The upstream shared-CRT compiler is applied to the literal C222 numerical
calculus. The only mathematical changes are the positive-power graph just
proved and the final quotient orientation. The compiler, all fixed source
formulas, all final residuals, and the expanded polynomial are supplied.
No K215 run or Jones universal polynomial is used.

The affine-eliminated equation has 2473 natural unknowns, 2089 quadratic
residuals, exact degree four, 20580 expanded monomials, and coefficient
height 127808289. The retained-affine variant has 4860 unknowns, 4476
quadratic residuals, 14719 monomials, and coefficient height1837.

The main equation is the sum of squares of the 2089 explicitly listed
rows in `eq/equation.json`. The completely expanded same polynomial is
`eq/expanded_polynomial.json`. All coefficients are literal integers.

The inherited C222-to-ZF and constructible-choice calibrations give, in
ordinary mathematics formalizable in ZFC,

    P has a natural zero  iff  ZFC has a finite syntactic refutation.

Negating this yields the required no-zero iff Con(ZFC) theorem. The new
arithmetic reductions have ordinary proofs and exact finite audits. No new
end-to-end Lean certificate or object-language ZFC proof term is claimed.
The full transitive semantic calibration was not rebuilt here. No global
minimality or literature-wide priority is claimed.
