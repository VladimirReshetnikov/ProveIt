# A 101-operation polynomial from a signed projection

> The [factored first-norm descendant](complete74_factored_first_norm.md)
> saves one multiplication, giving **74=40M+34A** with the same supplied
> witnesses, comparisons and complete SOS polynomial as this source.
> The three raw/positive/signed forms cost130/106/100 as fully paid SOS
> polynomials, with exact degrees52/84/84. This historical proof is retained.

The fixed complete75 compiler admits a single polynomial with **20 strictly
positive existential witnesses**, exact degree **84**, and evaluation cost
**101=50M+51A**. Its comparison certificate costs **75=41M+34A** and has
**nine equations**. This improves both the104 polynomial with a75-operation
certificate and the102 polynomial with a76-operation certificate in the
[gamma-dominance packet](complete75_gamma_dominance_elimination102.md).

The transformation preserves the complete positive solution set of the
[original universal75 source](../../1980/FIXED_RAW_UNIVERSAL_75_PROOF.md),
after the explicitly given coordinate changes. It does not restrict
completeness to canonical compiler witnesses or require the strengthened
raw bound used for102. The new difference expressions can be negative
away from the zero set. Proving their positivity on the zero set is the
substantive step; signed intermediate registers are allowed by the
arithmetic model. No universality claim is made over unrestricted integer
witnesses, and no optimality or formalization claim is made.

## 1. Exact definitions and residuals

Fix the same program numerals `B,DC,DR,MC,MF,d,b` as complete75. In
particular, `B=2^d>=16`, b is positive and odd with b<B, and

    0<MC,MF<B-1, MC=2 mod4, MF=4 mod8.

The ordinary input x and the following20 existential coordinates are
strictly positive integers:

    J,F,alpha,z,f,h,i,j,o,R,s,w,tau,eta,zeta,y,Z,delta,rho,sigma.

Write `K0=DC+B*DR`; this and `2d` and `MF+B-1` are fixed compiler
numerals. Retain the paid definitions and common subexpressions

    q=(B-1)J+1, X=w*q^3, Y=s*q^3, E=XY,
    k=eta+zeta, a=E+Y, c=kY+eta,
    H=4a+3, Delta=a^2+H, A=a+2,
    gamma=rho+sigma, D=X+ac+gamma*H,
    u=2d*x+b, kappa=u+delta*Delta.

Here A and u are mathematical abbreviations; the checker uses `odd_index`
for u and `A` for Delta. No additional A computation is required.
Change the C and W definitions to

    C=q-alpha-2d*x, W=C-Z, mu=W+a*kappa+rho*H.          (1)

There is no supplied W coordinate. Remove the raw-bound comparison and
the input gap comparison, and use precisely these nine residuals:

    (K0+X)C - (F+z(q-1)),
    R - ((q^2-Z-qF)(q^2-1)+(MC+q*(MF+B-1))J),
    (E^2+X)(kY)^2 - (tau^2-1),
    k - (R+1+hE),
    D^2 - (1+Delta*c^2),
    (ic^2)^2 - Delta*(f^2-1),
    (ic^2)^2*((jc-R)^2-y^2) - (1-y^2),
    (jc-R) - (of-c),
    mu^2 - (1+Delta*kappa^2).                          (2)

The output polynomial is the sum of their squares. The actual auxiliary
square `(ic^2)^2` is retained in both equations, just as in complete75.
All nine residuals vanish if and only if this polynomial vanishes.

## 2. Bounds before the kernel, without W positivity

Take any positive retained assignment where all residuals(2) vanish.
The definition of q gives q>=B>=16. The transport equation gives

    C=(F+z(q-1))/(K0+X)>0.

The quotient is only a proof expression: the circuit defines C by(1).
Thus `0<C<q` and `0<2d*x<q`. At this point W may still be negative.

Put

    S'=Z+qF-1,
    TC=MC*J+1, TF=MF*J-1, T'=TC+q*TF.

The fixed bounds and `q=(B-1)J+1` imply, before any power decoding,

    0<TC<q, 3<=TF<q-2, 3q+1<=T'<q^2-1.

The retained packing equation is identically

    R=(q^2-S')(q^2-1)+T'.                             (3)

Since R is a supplied positive coordinate, `S'>q^2` would make
`R<=T'-(q^2-1)<0`, a contradiction. Positivity of F,Z also gives S'>=q.
Consequently

    q<=S'<=q^2, 1<=Z<=q^2-q+1<q^2,
    3q+1<=R<q^4, -q^2<W=C-Z<q.                      (4)

Neither Z<q nor W>0 was needed for these conclusions. In particular the
potential boundary S'=q^2 is left in place until the existing kernel and
compiler proof have the information needed to reject it.

All kernel coordinates are already positive: in particular gamma=rho+sigma
is positive and `D=X+ac+gamma*H>0`. The input coordinate kappa is positive,
and the signed definition of its root causes no extra branch, because

    a=Y(X+1)>q^6>q^2,
    mu=W+a*kappa+rho*H > -q^2+a > 0.                 (5)

The ten equations of the strong
[half-binomial kernel](pell_kernel_half_binomial42.md) now hold, including
those supplied by definitions. Bounds(4), q>=16 and the actual common
scale q^3 meet every external hypothesis of that theorem. It gives

    q=2^t, X=2^R, c=psi_A(R), D=chi_A(R), R=3 mod4.  (6)

The other kernel conclusions and all its auxiliary positivity statements
are unchanged. No typed-word or input conclusion was used to apply it.

## 3. Recovering the omitted gap and the sign of W

The positive input norm, kappa>0, and(5) give an index v>=1 with

    kappa=psi_A(v), mu=chi_A(v).

Define `E_A(j)=chi_A(j)-a*psi_A(j)`, where A=a+2. Its initial
values are E_A(0)=1 and E_A(1)=2. It obeys the Pell recurrence

    E_A(j+1)=2A*E_A(j)-E_A(j-1),

so it is strictly increasing: successive positive differences follow
inductively from

    E_A(j+1)-E_A(j)
      =(2A-2)E_A(j)+(E_A(j)-E_A(j-1))>0.

The two projection definitions imply

    E_A(v)=W+rho*H
          <X+(rho+sigma)*H=E_A(R),                   (7)

since W<q<X and sigma>0. Thus v<R and the missing input gap is restored
by the strictly positive integer `phi=c-kappa`.

To recover W itself, use `u=2d*x+b`. It is odd, and

    0<u<2q<R<a+1=A-1.

For every `0<j<R<A-1`, the Pell discriminant congruence gives

    psi_A(j)=j mod Delta, if j is odd,
    psi_A(j)=j*A mod Delta, if j is even.

These are the actual least positive representatives: j and jA both lie
strictly between0 and Delta. The congruence follows directly by reducing
the Pell recurrence modulo Delta, using A^2=1 there. Because
`kappa=u+delta*Delta`, an even v would force `u=vA>=2A>2q`, impossible.
An odd v instead forces **v=u**.

Reducing the recurrence for E_A modulo H gives `E_A(j)=2^j mod H`:
the initial values agree, and `4A-1=H+4`. Consequently

    W=2^u mod H.

Now `0<2^u<2^R=X<a`, whereas(4) gives `-q^2<W<q`.
Since a>q^2 and H=4a+3, their difference satisfies

    -H < -q^2-a < W-2^u < q < H.

The only multiple of H in this interval is zero. Hence

    W=2^u>0.                                         (8)

All omitted coordinates have now been restored with the original positive
domains: C,W,mu by(1),(5),(8), phi by(7), gamma=rho+sigma, and the earlier
positive triangular definitions. The original raw bound and marker
equations are identities under(1). Every original complete75 equation
therefore has positive witnesses, and its universal soundness theorem
applies to this same ordinary input x.

## 4. Completeness preserves every old solution

Conversely, take any positive solution of the original complete75 source.
The positive triangular definitions hold, and the original raw bound and
marker equation force exactly(1), with the existing positive C and W.
The only new witness requiring justification is sigma=gamma-rho.

The original theorem gives odd indices u,R with u<R, hence R>=u+2,
and X=2^R, W=2^u. For every j>=1,

    psi_A(j)<E_A(j)=2psi_A(j)-psi_A(j-1)<=2psi_A(j).

The psi recurrence and strict growth give

    psi_A(u+2)-2psi_A(u)
      >(4A^2-2A-3)*psi_A(u)>A.

It follows that `E_A(R)-E_A(u)>A>X`. Subtracting the two original
projection identities yields

    H*(gamma-rho)=E_A(R)-E_A(u)-X+W>0.

Thus sigma is a strictly positive integer. Delete W and phi, replace
gamma by sigma, and perform the earlier triangular eliminations. All
nine residuals(2) vanish. This is inverse to the restoration in Sections2–3,
so it gives a bijection of the original and new positive solution sets
at each x. In particular the full fixed compiler and all its positive
completeness witnesses remain available without a stronger raw bound.

## 5. Literal cost and exact degree

Start from the75-operation gamma-only certificate, whose polynomial cost
was104. Its three additions

    marked_rhs=Z+W,
    bounded=marked_rhs+alpha,
    raw_bound=bounded+scaled_t

are replaced by three subtractions

    C_partial=q-alpha,
    marked_rhs=C_partial-scaled_t,
    W=marked_rhs-Z.

Here `scaled_t=2d*x` was already paid. Reorder the DAG topologically;
all other72 gates are identical. One witness and one comparison disappear,
so the certificate still costs75=41M+34A with20 witnesses and nine equations.
Nine residual subtractions, nine squares and eight sums give

    75+9+9+8=101=50M+51A.

The [checker](complete75_signed_projection_elimination101.py) and
[receipt](complete75_signed_projection_elimination101.json) expose the
entire101-gate acyclic polynomial schedule, including the output register.
No residual comparisons or witness computations are hidden in this count.

All fixed program numerals have degree zero; x and the20 witnesses have
degree one. The new C and W still have degree one. After the ordinary
polynomial cancellation

    (az+v)^2-(a^2+H)z^2-1 = 2azv+v^2-Hz^2-1,

the residual degree bounds in the order(2) are

    5,4,26,9,22,22,34,6,42.

The unique degree42 part of the input norm residual is
`-4*(B-1)^30*delta^2*w^5*s^5*J^30`. Its square is the unique
degree84 part of the final polynomial:

    16*(B-1)^60*delta^4*w^10*s^10*J^60.

It is nonzero for every fixed admissible B>1. Therefore the degree is
exactly84, not just bounded by84.

## 6. Evidence and limits

The checker verifies the exact gate replacement and both deleted
polynomial identities. It then independently evaluates the old
nineteen-equation source on256 arbitrary retained assignments after
restoring the deleted coordinates. This includes negative C and W
values; algebraic equivalence off the zero set does not assert their
positivity. On each assignment the new polynomial equals the old sum
of squared residuals after substitution.

Separate exact checks exercise the shifted packing bounds with nonpositive
W, the resulting positive input root, the discriminant residues and the
signed exponent representative window. The gamma-dominance packet's
exact Pell fixtures are also replayed. These are scoped partial-interface
checks, not full accepting compiler tuples. The parametric arguments above
prove the conditional positivity and equivalence; finite checks corroborate
their implementation. A univariate specialization independently confirms
degree84 and its leading coefficient. Default replay compares the entire
fresh deterministic result to the checked-in receipt.

Independent proof/source review and default replay passed. That review
checked the pre-power shifted-packing bounds, conditional positivity of C
and mu before W is decoded, exact index recovery, the signed representative
window, the solution-set bijection, all gate changes, and the degree claim.
A second independent proof/source review also passed and checked512
additional old/new residual identities at B=16,32,64,128, including412
assignments with negative restored W. These identity checks do not replace
the proof of positivity on the zero set.

From the repository root with the verification dependencies installed:

    python3 Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/complete75_signed_projection_elimination101.py
