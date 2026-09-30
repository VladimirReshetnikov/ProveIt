# A 99-operation polynomial with19 positive witnesses

The fixed complete75 compiler has a single-polynomial representation with
**19 strictly positive existential witnesses**, exact degree **84**, and
evaluation cost **99=49M+50A**. The underlying comparison certificate has
**76=41M+35A operations and eight equations**. This improves the polynomial
cost and witness count of the
[101-operation representation](complete75_signed_projection_elimination101.md).
The complete comparison-certificate bound remains75, attained by the
101 representation's underlying comparison system.

The change strengthens the canonical raw bound, eliminates the packed-index
witness, and shares a linear expression between the new bound and the
packing. Soundness restores a positive solution of the101 source.
Completeness uses a pointwise margin of the actual fixed compiler, including
every permitted low-dummy adjustment. The fixed program numerals are
unchanged. This preserves the accepted ordinary input set, rather than
every old witness tuple. No optimality or formalization claim is made.

## 1. Definitions, domain and eight equations

Use the same fixed compiler constants and notation as101. The ordinary
input x and these19 existential coordinates are strictly positive:

    J,F,alpha,z,f,h,i,j,o,s,w,tau,eta,zeta,y,Z,delta,rho,sigma.

The old supplied R coordinate is absent. Keep the definitions

    q=(B-1)J+1, X=w*q^3, Y=s*q^3, E=XY,
    k=eta+zeta, a=E+Y, c=kY+eta,
    H=4a+3, Delta=a^2+H,
    gamma=rho+sigma, D=X+ac+gamma*H,
    u=2d*x+b, kappa=u+delta*Delta,
    mu=W+a*kappa+rho*H.

Replace the C definition by the stronger bound

    C=q-F-Z-alpha-2d*x, W=C-Z.                         (1)

For the literal source define the shared intermediate registers

    T=q-F, V=T-Z,
    C=V-alpha-2d*x,
    G=(q-1)*T+V.                                      (2)

Since q-1 is the already computed repunit `(B-1)J`, no subtraction
computes it a second time. The polynomial identity

    G=(q-1)(q-F)+(q-F-Z)=q^2-Z-qF                     (3)

holds on every integer assignment. Define the packed index by

    R=G*(q^2-1)+(MC+q*(MF+B-1))*J.                     (4)

All appearances of R now use this same computed expression. There is no
packing comparison and no extra witness for T,V,G or R.

The eight residuals are exactly the101 residuals with their packing
residual omitted and definitions(1)–(4) substituted:

    (DC+B*DR+X)C - (F+z(q-1)),
    (E^2+X)(kY)^2 - (tau^2-1),
    k - (R+1+hE),
    D^2 - (1+Delta*c^2),
    (ic^2)^2 - Delta*(f^2-1),
    (ic^2)^2*((jc-R)^2-y^2) - (1-y^2),
    (jc-R) - (of-c),
    mu^2 - (1+Delta*kappa^2).                          (5)

Their sum of squares is the final polynomial. Signed intermediate values
are permitted. In particular C,W and R need not be positive away from
its zero set. Every binary addition, subtraction and multiplication in
the source, including multiplication by a fixed numeral, is charged.

## 2. Soundness: the new bound restores positive R

Suppose positive retained coordinates make the polynomial vanish. Every
residual(5) vanishes. The repunit gives q>=B>=16, and the transport
residual gives

    C=(F+z(q-1))/(DC+B*DR+X)>0.

This division is used only in the proof; C is computed by subtraction in
the actual circuit. Equation(1) now implies

    0<F,Z<q, V=C+alpha+2d*x>0, T=V+Z>0.

Thus `G=(q-1)T+V>0`. Formula(4), the fixed positive masks and J>0
give **R>0**. The packed-index witness has therefore been restored with
its required domain before any kernel theorem is applied.

Set the101 slack to

    alpha_101=alpha+F+Z>0.                             (6)

Then its C definition is exactly `C=q-alpha_101-2d*x`, and its W
definition remains W=C-Z. The packing equation is an identity by(3)–(4),
and the remaining eight101 equations are precisely(5). This is a positive
assignment of all20 supplied101 coordinates, including the restored R;
101 does not require the computed W to be positive in advance.

The101 soundness theorem now applies in its stated order: transport and
shifted packing bound Z and R, establish positivity of the input root,
permit the strong half-binomial kernel, restore the input index gap, and
finally force W=2^u>0. It gives a positive solution of every original
complete75 equation and therefore the correct ordinary input membership.
This argument neither assumes an input power nor weakens an auxiliary
Pell norm.

## 3. Canonical completeness with the actual compiler

Take an accepted ordinary input and the canonical complete75 witnesses.
Write `r0=2^b` for the compiler's inner radix; its outer base is
`B=r0^L`, and `q=B^N=r0^(LN)`. This radix r0 is distinct from the
packed index R. Use the original genuine word, whole-cell temporal
rotation and all the required ordinary Boolean low-dummy adjustments.
The extra upper dummy bits are zero, as in the canonical construction.

The [modified compiler](complete75_half_binomial_compiler.md) and the
[earlier margin proof](complete75_bounded_packing_elimination105.md)
establish the following pointwise bounds on these actual words:

* Every inner-radix digit of C and its whole-cell temporal rotation is0
  or1, for every subset of the allowed low dummy bits.
* Every coefficient of `DC*C+DR*Rword` is at most `r0/4-2`.
* Adding the temporal word gives the actual F coefficients at most
  `r0/4-1`, with support inside the same LN digits.

Consequently every coefficient of **2C+F** is at most `r0/4+1`.
This is below r0, so there are no radix carries. Since r0>=16,

    2C+F <= (r0/4+1)*(q-1)/(r0-1) < q/3.               (7)

Indeed `3*(r0/4+1)<=r0-1` for r0>=16, and q-1<q gives the strict
final inequality, including r0=16. This pointwise domination includes
every ordinary low-dummy subset; it therefore survives the five-adic
adjustment of the actual packed R to the required temporal congruence.
No new margin or enlargement of the program constants is required.

Canonical Z=C-W satisfies 0<Z<C. Original padding gives N>2x. With
t=dN>=4 and q=2^t,

    2d*x<t<2^(t-1)=q/2.

Combining this with(7) yields

    C+Z+F < 2C+F < q/3,
    alpha=q-C-Z-F-2d*x > q/6 > 0.                     (8)

Choose this new positive alpha. Retain the genuine F,Z and all kernel
and input witnesses. The gamma-dominance proof gives sigma=gamma-rho>0.
The new C and W definitions recover their original values, and(3)–(4)
compute the original actual packed index, including its dummy alignment.
Erase that supplied R coordinate. Every residual(5) vanishes, proving
completeness for the same fixed compiler and ordinary input.

The new source is not asserted to preserve all old positive tuples: an
arbitrary old raw slack may be smaller than F+Z. Soundness maps every new
tuple to an old one; completeness is supplied by the canonical subfamily
proved to satisfy(8).

## 4. Source transformation and exact count

The101 source has75 certificate gates and nine comparisons. Without
sharing, strengthening C by subtracting F and Z adds two subtractions.
Eliminating the R witness then removes its comparison and would give a
100-operation polynomial from a77-operation certificate.

Identity(3) saves one addition/subtraction. The old pair of blocks was

    C=q-F-Z-alpha-2d*x,             # four subtractions
    qF=q*F; packed=Z+qF;
    G=q^2-packed.                  # one product, two sums/differences

The shared blocks in(2) use four subtractions to obtain T,V,C and only
one product and one sum to obtain G. The square q^2 remains available
for the other packing and common-scale operations. The actual new source
therefore has **76=41M+35A operations**,19 witnesses and eight comparisons.

For a direct gate audit against101, five gates are replaced by six:
`C_partial,marked_rhs,qF,packed,gap` are replaced by
`q_minus_F,q_minus_FZ,C_after_alpha,marked_rhs,gap_product,gap`.
The other70 gates are identical under the single alias R to its packing
output. Topological reordering introduces no computation or comparison.
The packing expression is evaluated once.

Eight residual subtractions, eight squares and seven sums yield

    76+8+8+7=99=49M+50A.

The [checker](complete75_bounded_projection_elimination99.py) and
[receipt](complete75_bounded_projection_elimination99.json) include the
complete99-gate polynomial DAG and its output register. The retained
comparison indices in the original nineteen-equation source are
`2,5,8,11,12,13,14,17`. There are no hidden residual constraints.

## 5. Degree, verification and scope

All program numerals are fixed; x and the19 existential coordinates have
degree one. The computed R has degree four, below the degree-six jc
expression and the degree-nine hE expression in its remaining uses.
C,W,T,V still have degree one. The norm identity

    (az+v)^2-(a^2+H)z^2-1 = 2azv+v^2-Hz^2-1

gives residual degree bounds, in the order(5),

    5,26,9,22,22,34,6,42.

The unique degree42 term of the input norm is unchanged, so the highest
homogeneous part of the final polynomial is

    16*(B-1)^60*delta^4*w^10*s^10*J^60.

This is nonzero for every fixed admissible B>1, proving exact degree84.

The checker verifies local gate identities, topological availability,
operation histograms and the exact gap factorization. It independently
replays the original nineteen-equation source on256 arbitrary assignments,
restoring the old slack by(6), R by(4), W, gamma and the gap. These identity
tests deliberately include negative computed R and W values off the zero
set. Another128 of those cases satisfy C>0 and directly exercise the
positive packing restoration. These are partial-interface checks, not full
huge Pell tuples.

Five actual compiler layouts, including both high-correction cases, check
the sparse coefficient domination of2C+F with all low Boolean lanes on.
The proof of(7) is parametric; the finite layouts corroborate the compiler
implementation. A separate polynomial specialization verifies degree84
and its leading coefficient. Default execution recomputes the full
deterministic receipt and compares it to the checked-in result.

Two independent proof and source reviews passed. Separate replays against
the original nineteen residuals checked1,024 assignments across four bases,
including468 negative C and340 negative computed R cases; all556 cases
with C>0 satisfied the packing-positivity implications. A second manual
eight-residual implementation agreed on512 assignments, and four unequal
weighted polynomial specializations confirmed the residual degree bounds
and the predicted top coefficient. The full original75 checker also
passed. These finite audits supplement the parametric proofs above.

| Construction | Certificate operations | Positive witnesses | Equations | Polynomial operations | Degree |
|---|---:|---:|---:|---:|---:|
| Signed projection101 |75|20|9|101|84|
| Bounded projection99 |76|19|8|99|84|

From the repository root with verification dependencies installed:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_bounded_projection_elimination99.py
