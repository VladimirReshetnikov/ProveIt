# The same 51-operation mask module with a base-four Pell power

The [one-field half-mask module](one_field_half_mask.md) has an alternative
with exactly the same **51=30M+21A** operations and the same bounded-mask
predicate, but its retained power is

    X=4^(2r+1).

Its binary exponent is even. This removes the parity obstruction to using
the retained power as a shift between cells of even binary width, without
computing `2X`. It does not establish the required alignment, a universal
controller or a complete certificate below76.

The [checker](explore_pell_kernel_base_four_half_mask.py) and
[receipt](explore_pell_kernel_base_four_half_mask.json) supply the exact
source and finite corroboration. The proof below gives soundness and
positive completeness for this mask module.

## 1. Source and exact predicate

Fix an even integer `d>=8`, `B=2^d`, and an odd fixed `m` with

    0<m<B-1, popcount(m)=d/2.

For positive parameters `n,F`, there are positive witnesses for the module
if and only if, for some integer `N>=1`,

    n^2=B^N, 0<F<n^2,
    F AND [m*(B^N-1)/(B-1)] = 0.                         (1)

The powers and AND describe the predicate; they are not certificate
instructions. Keep the half-mask source

    q=n*n, D0=q*n,
    (B-1)Jrep=q-1,
    r=(q-F)(q-1)+m*Jrep.                                 (2)

Keep all ten kernel equations with `X=w*D0`, `Y=s*D0`, `E=XY`, and
`a=E+Y`, but now use

    A=a+4, Delta=A^2-1=a^2+8a+15, H=8a+15.

In particular the main exponent and norm are

    dmain=X+a*c+gamma*H,
    dmain^2=1+Delta*c^2.

The auxiliary coefficient remains `(i*c^2)^2=Delta*(f^2-1)`, with the
unchanged fixed-minus congruences and auxiliary norm. The complete twelve
source polynomials are constructed independently in the checker.

The source changes just two literal operands of the base-two module:

    4*a becomes 8*a;
    (4*a)+3 becomes (8*a)+15.

The existing addition of this shared register to `a*a` computes `Delta`.
Every instruction remains paid, so the kernel is still43 operations and
the outer source is still8. There are eighteen positive existential
coordinates in addition to the two positive parameters `n,F`, and twelve
equations. A containing certificate which also quantifies `n,F` has twenty
positive coordinates in this module.

## 2. Exact indices before power recovery

Put `M=m*Jrep`. Positivity in (2) gives

    q>=B>=256, 0<M<q-1,
    F<=q, 15<=m<=M<=r<q^2,
    D0>=4096, D0^2=q^3.

The endpoint `F=q`, `r=M` is retained here. As in the base-two module it
will be excluded only after power recovery and binomial divisibility.

For any positive kernel solution,

    X,Y>=D0, XY>=q^3>r+1,
    a=Y(X+1)>q^3>2r+1,
    8r/a<8/q<=1/32<1/2.                                 (3)

The first norm has Pell parameter `P=2XY^2+1>A=a+4`. Its congruence
`k=r+1+hXY` gives first index `t>=r+1`, since `P=1 modulo XY` and
`0<r+1<XY`. The positive interval gives `c>Yk>k`. Comparing Pell growth
at `A<P` therefore makes the main index satisfy

    p>=t+1>=r+2>=17,
    c>=(2A-1)^16>A*(A^2-1)^2,
    c>Yk>2r+1.

These are the unchanged relaxed auxiliary rank lemma's hypotheses. Its
generic parameter is `A`; it never requires `A=a+2`. The strong coefficient
`i*c^2`, its square, and both fixed-minus congruences are retained. The
rank and half-parameter arguments therefore recover

    p=2r+1, c=psi_A(2r+1), dmain=chi_A(2r+1).

The first index is then exactly `t=r+1`. To verify the changed growth
comparison explicitly,

    (2P-1)-4A = 4Y[X(Y-1)-1]-15 > 0.

If `t>=r+1+XY`, the main/first Pell ratio is less than one, contradicting
`c/k>Y`. No exponent or mask interpretation has entered these steps.

## 3. Shift-four ratio, exponent and rounding

Put `Q=XY^2` and `xi=(X+1)^(2r)/X^r`. At the exact indices, elementary
Pell growth gives

    c/k >= xi*(1+7/(2a))^(2r)*(1+1/(2Q))^(-r) > xi,
    c/k < xi*(1+4/a)^(2r) < xi*(1+16r/a).                (4)

The first strict inequality uses `14Q>a`. The last uses (3) and the
geometric bound `(1+t)^s<1+2st` when `st<1/2`.
The supplied interval `Y<c/k<Y+1` and the lower bound imply

    Y>=X^r, a>X^(r+1).

Before interpreting the exponent congruence, its required bounds hold:

    4^(3(2r+1))=64*4096^r < X^(r+1)<A,
    X^3<=X^r<a<A.

Here `X>=4096` and `r>=15`. The base-four chi congruence criterion now
applies because `A-4=a` and `2*A*4-4^2-1=8a+15=H`. It proves

    X=4^(2r+1).                                         (5)

Equivalently, the Pell recurrence directly gives
`chi_A(j)-a*psi_A(j)=4^j modulo H`; the same size estimates distinguish
the representatives. The checker verifies the changed congruence in its
materialized examples.

Since `xi<Y+1<2Y`, (4) yields

    0<c/k-xi<32r/(X+1)<1/2.

The last inequality follows from (5). The binomial expansion `xi=L+T`
has positive fractional tail `T<1/4`, integral part `L`, and
`L=binom(2r,r) modulo X`. Consequently

    L<xi<c/k<Y+1, Y<c/k<xi+1/2<L+3/4,

so integrality forces `Y=L`. The common scale divides both `X` and `Y`,
and therefore `D0` divides `binom(2r,r)`.

Since `n^3` divides the power of two in (5), `n` is a power of two.
The repunit equation recovers `q=B^N` exactly as in the base-two module.
Thus `D0=2^(3dN/2)` and `popcount(M)=dN/2`.

## 4. Mask soundness and positive completeness

The endpoint `F=q` would give `r=M`, whose central-binomial valuation is
only `dN/2`. This contradicts the required divisibility by
`D0=2^(3dN/2)`. Hence `F<q`, and now `q<=r<q^2`.
The unchanged inverse-packing identity gives

    popcount(r)<=dN+popcount(M)=3dN/2,

with equality exactly when `F AND M=0`. The scale divisibility forces
equality, proving (1).

Conversely suppose (1). Define `Jrep` and `r` by (2). The mask has its
unit bit set, so `F` is even and `r` is odd. Also

    q<=r<q^2, D0<r^2, popcount(r)=3dN/2.

Choose `X=4^(2r+1)` and let `Y` be the integer part of `xi`. The scale
divides both integers: `D0<r^2<X` supplies the power quotient, and the
central-binomial valuation and `Y=binom(2r,r) modulo X` supply the other
quotient. Thus `w=X/D0` and `s=Y/D0` are positive integers.

Set `a=Y(X+1)`, `A=a+4`, and use the canonical main and first Pell
coordinates at indices `2r+1` and `r+1`. Bounds (3)--(4) and the tail
estimate make both interval slacks positive. The first index quotient
`h=(k-r-1)/(XY)` and the triangular norm quotient are positive integers,
as in the retained construction.

The base-four recurrence makes `gamma=(dmain-X-a*c)/H` integral. Its
positivity follows from

    dmain-a*c=4c-psi_A(2r)>3c>X.

Finally the unchanged generic fixed-minus converse applies at this new
`A`: choose auxiliary index `2c(2r+1)`, then its relaxed Pell coefficient
and normalized auxiliary Pell root at index `2r+1`. Odd `r` gives the two
required negative residues and positive `i,j,o,y_aux,f`. This constructs
every supplied coordinate strictly positively. The witness maps recompute
all affected Pell values; they do not identify base-two and base-four
witnesses numerically.

## 5. Consequence for a possible compiler and evidence boundary

The recovered binary exponent is `4r+2`. For a fixed even width `d=2e`,
its whole-cell alignment condition becomes `e | (2r+1)`. When `e` is odd
there is no parity obstruction. For example an eventual compiler can
choose `e` to be an odd prime power. This observation removes one obstacle;
the module does not enforce that divisibility, select a temporal stride,
or construct compatible compiler masks.

The exact checker verifies all twelve source residuals, the auxiliary
norm correction, the two changed literal operands, and the unchanged
51-operation ledger. It checks4,690 pre-power tuples, including938
positive `F=q` endpoints and2,968 positive nonpower-square cases.
It also checks465,498 bounded fields and166 boundary valuation deficits.

Three small first/main prototypes at `r=3,7,15` materialize all seven
changed first/main equations, strict positive quotients, ratio and
rounding inequalities. They are not claimed to meet the module's outer
equations; their purpose is to check the modified constants and norm
identities directly. Large actual module witnesses, including auxiliary
Pell values, are supplied by the parametric proof and are not expanded.
The established complete universal bound remains76.

Independent complete proof/source/receipt review passed, including the
changed exponent congruence, smaller ratio estimates and positive converse.
Fresh default receipt replay matches. No Lean formalization is claimed.

## Appendix: even masks at the same cost

The source also permits any fixed `0<m<B-1` with `popcount(m)=d/2`,
without an oddness requirement. The exact predicate is then

    n^2=B^N for some N>=1, 0<F<n^2,
    F AND [m*(B^N-1)/(B-1)] = 0,
    F+m is odd.                                          (6)

No source equation or instruction changes. The preliminary bounds, rank,
base-four exponent, valuation and boundary exclusion above never used
oddness of `m`, so they still establish all claims through mask soundness.
The [necessary fixed-minus parity theorem](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md)
additionally forces `r` odd. That theorem is generic in the main Pell
parameter `A>=2`; its proof depends on the recovered indices, the strong
auxiliary rank divisibility and the two negative congruences, all retained
here. It applies in particular to `A=a+4`.

After power recovery `q` is even and `Jrep` is odd. Hence

    r=(q-F)(q-1)+m*Jrep = F+m modulo2.

This proves necessity of the last condition in (6). Conversely (6) makes
the packed index odd and provides exactly the mask valuation. The same
positive fixed-minus converse in Section4 then constructs every witness.
For odd `m`, the mask already forces `F` even, so the last condition is
automatic. For even `m`, the condition requires `F` odd.

This extension is useful for a proposed interleaved mask `MC+B0*MF`,
which is even in the current native compiler. It addresses only parity;
it does not prove the arithmetic typing or separation of interleaved data
and verification fields. The checker exhausts both mask parities at
`d=8,10` and compares the specification with packed valuation plus the
necessary odd-index condition.
