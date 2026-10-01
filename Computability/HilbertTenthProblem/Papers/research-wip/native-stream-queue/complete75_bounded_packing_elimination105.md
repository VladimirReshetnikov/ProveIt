# A 105-operation polynomial from a stronger packing bound

The fixed compiler of the
[complete75 theorem](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md)
gives one polynomial of exact degree84, evaluable in
**105=51M+54A operations**, with **21 strictly positive existential
witnesses** and ordinary positive input x. Strengthening one bound costs
one addition, but permits elimination of the packed-index witness and its
comparison. The resulting arithmetic certificate costs **76=41M+35A**
with ten equations. Its single-polynomial evaluation improves the
[107-operation construction](complete75_positive_elimination.md).

This does not lower the best arithmetic certificate below75. The bound
is for positive witnesses and fixed compiler numerals; no optimality,
publication record, signed-integer convention, or formal proof is claimed.

## 1. The changed bound and the conditional positive definition

Use all eight positive definitions in the107 construction. In particular

    q=(B-1)J+1, C=Z+W,
    X=w*q^3, Y=s*q^3, E=XY,
    k=eta+zeta, a=E+Y, c=kY+eta,
    H=4a+3, Delta=a^2+H,
    D=X+ac+gamma*H,
    u=2d*x+b, kappa=u+delta*Delta,
    mu=W+a*kappa+rho*H.

Replace its raw bound by

    C+F+alpha+2d*x=q.                                    (1)

Every coordinate supplied here is strictly positive. On any assignment
satisfying(1), we have `0<Z<C<q` and `0<F<q`. Thus

    q^2-Z-qF >= 1.

Define the packed index by its already computed expression

    R=(q^2-Z-qF)(q^2-1)+(MC+q*(MF+B-1))*J.               (2)

Equation(1), q>1, and the positive fixed masks prove R>0. This definition
is positive on the zero set of the retained raw-bound residual. It need
not be positive on an arbitrary assignment of the remaining coordinates.
That distinction is accounted for in soundness below; R is a computed
intermediate in the final polynomial, not an unchecked positive witness.

The21 retained positive coordinates are exactly

    J,F,alpha,z,f,h,i,j,o,s,w,tau,eta,zeta,gamma,y,Z,W,delta,phi,rho.

The main root D is separate from the fixed compiler cell width d.
All program numerals, including the original MC and MF, remain unchanged.

## 2. Ten equations and soundness

Put K=DC+B*DR. After the displayed definitions, retain these residuals:

    P0 = C+F+alpha+2d*x-q,
    P1 = (K+X)C-F-z(q-1),
    P2 = (E^2+X)(kY)^2-tau^2+1,
    P3 = k-R-1-hE,
    P4 = D^2-1-Delta*c^2,
    P5 = (ic^2)^2-Delta*(f^2-1),
    P6 = (ic^2)^2*((jc-R)^2-y^2)-1+y^2,
    P7 = jc-R-of+c,
    P8 = c-kappa-phi,
    P9 = mu^2-1-Delta*kappa^2.

All abbreviations, including R from(2), are substituted polynomial
expressions. The final single polynomial is

    P=P0^2+P1^2+...+P9^2.                                (3)

Let a positive retained assignment satisfy P=0. Each residual is an
integer, so every square vanishes, in particular P0. Section1 therefore
makes R strictly positive. The other eight eliminated coordinates are
unconditionally positive by the earlier elimination theorem. Restore the
old raw-bound witness as

    alpha_old=alpha+F>0.

Then(1) becomes exactly `C+alpha_old+2d*x=q`. The packed-index equation
holds by definition, all eight earlier deleted equations hold by their
positive definitions, and the other ten source equations are precisely
the displayed vanishing residuals. Hence all nineteen original complete75
equations have positive witnesses. Its fixed compiler soundness proves
that x belongs to the represented recursively enumerable set.

This proof uses no positivity of R before P0 vanishes, and no digit or
power hypothesis on an arbitrary retained assignment. Merely deleting R
without the strengthened bound would not justify this argument.

## 3. Canonical compiler completeness satisfies the stronger bound

Write `r0=2^b` for the compiler's **inner radix**, to distinguish it from
the packed index R. Its outer base is `B=r0^L`, and
`q=B^N=r0^(LN)=2^(dN)`. Use exactly the canonical accepting words,
whole-cell temporal rotation, and ordinary Boolean dummy adjustment of
the complete75 proof. The new upper dummy bits remain zero.

Every inner-radix digit of C and of its whole-cell rotation is0 or1,
including after any subset of the ordinary low dummy bits has been
turned on. The proved compiler mass bound in
[the modified compiler, Section4](complete75_half_binomial_compiler.md)
is

    every coefficient of DC*C+DR*Rword <= r0/4-2.

Adding the whole-cell rotated word therefore gives every coefficient of
the actual verification word F at most `r0/4-1`. All supports remain
inside the same LN digits. Consequently C+F has no radix carries and
has every digit at most r0/4. Since r0>=16,

    C+F <= (r0/4)*(q-1)/(r0-1) < q/3.                  (4)

The pointwise bound covers every Boolean low-dummy subset. Thus it
survives the five-adic adjustment of the actual packed R to the required
temporal congruence; it is not a bound only for the initial all-zero
dummy choice. The compiler's fixed numerals require no enlargement.

The original padding gives N>2x. Put t=dN; then t>=4 and

    2d*x<t<2^(t-1)=q/2.                               (5)

The elementary inequality `2t<2^t` holds for every integer t>=4.
Equations(4)–(5) give

    alpha=q-C-F-2d*x>q/6>0.

Choose this new bound slack. Every other outer and kernel witness in
the canonical complete75 construction is unchanged, including its
actual packed R, masks, dummy congruence, transport quotient, and input
Pell values. Erase R and the other eight defined coordinates. This gives
a positive solution of(3) at every accepted input.

Not every old complete75 witness must satisfy the stronger bound. The
two sources represent the same accepted input set because soundness maps
every new witness to an old one, while completeness uses the canonical
old witnesses just proved to satisfy(4)–(5).

## 4. Exact cost and degree

Start from the audited75-operation positive-elimination DAG. Add the
one gate `strengthened_raw_bound=raw_bound+F`. Replace every use of the
supplied R by the existing packing-output register, and delete its
comparison. The packing expression is computed before all uses of R,
so this substitution is acyclic. No new witness or instruction evaluates
that expression a second time.

This leaves76 instructions:41 multiplications and35 additions or
subtractions. The ten comparisons require ten subtraction gates, ten
squares, and nine sum gates to evaluate(3):

    76+10+10+9=105=51M+54A.

There are no internal comparisons in that evaluation DAG. The only
final relation is P=0. The prior107 source remains the smaller75-operation
certificate; the new105 source is the cheaper single-polynomial circuit.

The residual degree bounds are respectively

    1,5,26,9,22,22,34,6,17,42.

The substituted R has degree4, while jc has degree6 and hE degree9,
so the changed R definition does not increase those degrees. The input
norm is unchanged. As in the107 proof, its unique highest-degree part is

    -4*(B-1)^30*delta^2*w^5*s^5*J^30.

All other residuals have degree at most34. Therefore the highest-degree
part of P is the nonzero monomial

    16*(B-1)^60*delta^4*w^10*s^10*J^60,

and P has exact degree84 for every fixed admissible B>1. The ordinary
input and all21 witnesses have degree one in this statement; compiler
numerals have degree zero.

## 5. Checks and limits

The [checker](complete75_bounded_packing_elimination105.py) and its
adjacent receipt record every105 gate. Local source rewiring is checked
exactly, together with register availability and uniqueness. Its independent
old-source replay verifies all residual identities after the essential
slack change `alpha_old=alpha+F`; positive restoration of R is separately
checked on assignments satisfying the new bound. These assignments are
algebraic fixtures, not full accepting computations.

Five actual sparse compiler layouts, including both high-monomial branches,
are checked with every old native position turned on independently in
each lane. Their nonnegative coefficient domination proves the asserted
margin for every canonical Boolean subset in those fixtures, including
all low-dummy choices. The parametric margin in Section3 applies to the
arbitrary fixed compiler from the universal theorem; it is not inferred
solely from those examples. Full compiler words and enormous Pell values
remain parametric. The degree fixture independently checks degree84 and
its stated leading coefficient. Independent proof and source review passed,
including the actual compiler mass margin after dummy alignment, conditional
positivity of R, restoration of the old slack, the gate counts, and degree.

From the repository root, with the pinned verification dependencies installed:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_bounded_packing_elimination105.py
