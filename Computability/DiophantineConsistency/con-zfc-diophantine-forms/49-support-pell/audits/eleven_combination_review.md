# Independent review: an eleven-variable norm with no inner separator

Reviewed against ProveIt commit `124c07c0b77a9e20e84676514d8b1ff78536ea3f`.
The source interfaces are package 38's `eleven/ELEVEN_POSITIVE_PROOF.md`
and package 44's `positive/PROOF.md`. This review proves the new combination
at their stated ordinary-mathematical compiler interface. It is not a Lean
build, an object-language ZFC derivation, or an independent re-proof of the
entire native-window compiler.

## 1. Exact assumptions and definitions

All eleven unknowns

    J,F,alpha,z,i,T,s,w,eta,zeta,t

are strictly positive integers. The four coefficient ports must be one
whole authentic normalized blank-K215 tuple, with the high mask already
shifted. In particular, the inherited outer interface applies once the
transport factor `Nt` is +1.

Use the following abbreviations, which are not additional unknowns:

    q=beta J+1, s0=s+3q, Cw=q-F-alpha,
    X=wq, Y=s0 q^3, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y,
    H=4a+3, Delta=a^2+H=(a+2)^2-1,
    ell=E kY, A=1+ell(ell+k), G=1+Delta c^2,
    b0=X+ac,
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J,
    Nt=(K0+w)Cw+(q-F)-z(q-1),
    I=ic^2, D=1+Delta I^2, Q=Delta(D-1)=(Delta I)^2,
    d=Q-1, v=cT, b=c+RD,
    e=Q(Dv^2+b^2)-1, Baux=2Qvb,
    delta=(a+2)c-ell, K=IT+1,
    S=EH, L=E(1+HK),
    W=E b0+H[E(t+b+delta)+k-R-1].

The proposed norm is the formal eight-factor product

    N = product_{g^2=G, tau^2=A, f^2=D}
          [d(W-Lg-S tau)^2-S^2 e+S^2 Baux f].

Each of the three root symbols takes both formal signs. This is an
integer polynomial by sign invariance. No algebraic-independence or
independent-Galois-automorphism assertion is used. The equation is

    Nt(1+N)-1=0.

The intended statement is existence equivalence with the normalized
compiler, hence with a finite syntactic ZFC refutation, on the stated
positive domain. The source compiler theorem is inherited.

## 2. Outer bounds without the deleted quotient

The scalar norm has the same trace/remainder evaluator as package 44,
with every occurrence of the scaling factor H in that evaluator replaced
by S. Writing the trace as `2x0` gives

    N = (ur-x0*vbar)^2 modulo 4.

Thus at a root of the product equation, `1+N=-1` is impossible, since it
would give `N=-2`. Both integer factors are units, so `N=0` and `Nt=1`.
The authentic outer interface then gives

    q>=16, Cw>0, 3q<R<q^4-2,
    X>=q, Y=(s+3q)q^3>3q^4>3R,
    E=XY>R+1, E>=65536,
    k>=2, kY<c<k(Y+1)<2kY,
    I>=c^2, c>=2, a+2<2E.

No inequality `k>E`, `c>EY`, or `R<k` is available at this stage or
used below. The last bound follows from `a+2=E+Y+2<2E`, since `X>=16`
and `Y>=4096`.

## 3. Sharper relative-error bound: K=IT+1 is sufficient

Let `g=sqrt(G)`, `f=sqrt(D)`, and `tau=sqrt(A)` be the positive real
roots for estimates only. We have

    g<(a+2)c<2Ec, f<(a+2)I<2EI,
    Delta c^2>A>1,
    1<A<Delta I=sqrt(Q), and g>tau.

To verify the nontrivial radicand comparison, use `c>kY` and
`Delta>(E+Y)^2` to bound `Delta c^2-A` from below by

    k^2[2EY^3+Y^4-EY]-1 > 0.

All these bounds are independent of the deleted index equation.

The exact coupled identity is

    (Ig)^2-(cf)^2=I^2-c^2.

Since `I>=c^2` and `c>=2`, its right side exceeds `I^2/2`.
Also `cf<Ig`. Therefore

    Ig-cf > I^2/(4Ig) > I/(8Ec)
           >= c/(8E) > Y/(4E).                  (1)

This need not exceed one. That stronger assertion was the point where
package 44 used `k>E`. It is unnecessary: the relative error in the
auxiliary root estimate is much smaller.

Indeed `c<I^2`, `D<4E^2I^2`, `R<E`, and `cf<2EI^2` give

    b<5RE^2I^2<5E^3I^2,
    b+cf<6E^3I^2,
    d=Delta^2I^2-1>(1/2)E^4I^2.

Consequently

    (b+cf)/d < 12/E < Y/(4E) < Ig-cf,           (2)

where the middle strict inequality uses `Y>48`.

For any coherent auxiliary branch, with `f'=+f` or `-f` and possibly
complex y,

    d y^2 = Q(vf'-b)^2-1 = e-Baux*f'.

Set `Z=b+Tcf>1`. Then

    |y|^2 <= (QZ^2+1)/d < [Z(1+1/d)]^2.

The last strict difference is `(QZ^2-d)/d^2>0`, because `Q=d+1`.
As `T>=1`, (2) gives

    Z/d <= T(b+cf)/d < T(Ig-cf).

It follows that

    |y| < Z+Z/d < b+ITg,
    |tau'+y| <= tau+|y| < b+(IT+1)g=b+Kg.       (3)

This is precisely the outer separation inequality needed by the
no-inner-separator construction, with its original lower-degree weight.
No additional T term in K is required.

## 4. Main radical and inner rational recovery

At `N=0`, some coherent branch gives

    x=(W-Lg')/S=tau'+y.

If `g'=-g`, then

    x=b+[t+(k-R-1)/E]+delta+b0/H+(K+1/H)g
      > b+Kg,

contradicting (3). Here `t+(k-R-1)/E>0`, since `t>=1`, `k>=2`,
and `E>R+1`; also `delta>0`. If G were nonsquare, the actual
quadratic conjugation of the rational-coefficient inner polynomial would
give this excluded negative branch. Thus g is a positive integer and x
is rational.

The inner polynomial is exactly package 44's

    C(x)=d(x^2+A)-e,
    F(x)=[C(x)^2+D Baux^2-4d^2x^2 A]^2
         -4C(x)^2D Baux^2.

Its exceptional branches remain excluded by the same integer-modulus
argument. If `C(x)=0` at a root, substitution yields

    d^2 A^2-d e A+Q^2 v^2 b^2 D=0.

Reducing modulo Q forces `Q|A(A-1)`, impossible because
`0<A(A-1)<Q`. Similarly `F(0)=0` forces `Q|(A-1)^2`, impossible.
The bounds follow from `1<A<sqrt(Q)` above.

Thus the rational reconstruction formulas have nonzero denominators:

    U=C(x)^2+D Baux^2-4d^2x^2 A,
    f'=-U/(2C(x)Baux),
    tau'=(C(x)+Baux*f')/(2dx), y=x-tau'.

They give `(f')^2=D` and `(tau')^2=A`, so both rational roots are
integers. Rational Pell saturation, with `m=Delta I` and
`V=vf'-b`, makes y integral from `m^2V^2-(m^2-1)y^2=1`.
Hence x is integral. Reducing `W=Lg+Sx` modulo E gives

    E | H(k-R-1).                                (4)

This uses the inherited Pell saturation lemma; the combined argument
does not claim it as a newly checked formal theorem.

## 5. Restore the deleted quotient and the compiler

The remainder of package 38's reconstruction applies verbatim because
it needs exactly the integral main, first, strong and auxiliary roots
just recovered, together with (4) and `Y>3R`.

For clarity, the order of recovery is essential. The normalized strong
equation and Pell divisibility give `c|m` and `m>=pc>2p`. The auxiliary
signed congruences give `R=+p` or `-p` modulo c. Since
`c>2Y>6R` and `c>2p`, this forces the main Pell index `p=R` before
using any index quotient.

Write `k=2 psi_(2EY+1)(n)` for the first Pell equation. Monotonicity
gives `n<p=R`. Put `mu=E/gcd(E,H)`. The identity

    gcd(Y,H)=gcd(Y,3)<=3

implies `mu>=Y/3>R`. Equation (4) and the first Pell recurrence give
`2n=R+1 modulo mu`. Its absolute discrepancy is less than R, hence
`2n=R+1` exactly. Thus `E|(k-R-1)` and

    h=(k-R-1)/E >0.

Dividing the carrier identity by E and reducing modulo H gives
`g=b0 modulo H`. Set `gamma=(g-b0)/H`. It is positive: by this stage
`n>=25`, whence `k>=4(2EY+1)>X` and `c>X`; also `g>(a+1)c`.
All normalized compiler equations are restored. The signed auxiliary
interface permits the recovered sign of f and extracts a genuine blank
K215 halting run. The calibrated endpoint identifies such a run with a
finite syntactic ZFC refutation.

## 6. Completeness and positivity of the new carrier

Take a canonical positive normalized compiler witness for a blank halt.
Its inherited estimates give `Y>2^R`, `R>3q`, and `q>=16`; hence
`s_old=Y/q^3>3q` and `s=s_old-3q` is positive.

The full carrier correction satisfies `0<delta<g` independently of
`k>E`: since `c<2kY`, one has `ell/c>E/2>2`, so
`delta=(a+2)c-ell<ac<g`.

Set

    t=gamma+Kg+tau+y-b-delta-h.

It is an integer. The auxiliary Pell equation gives
`y>=|Tcf-b|>=b-Tcf`. Consequently, with `K=IT+1`,

    t > gamma+tau-h+T(Ig-cf) >0.

The last inequality uses `Ig>cf` and `tau>ell>k/E>h`.
Its defining equality gives `W=Lg+S(tau+y)`, so one norm factor
vanishes and the transport factor is +1. The equation has a positive
solution. This proves both directions of the new reduction under the
explicitly inherited semantic interface.

## 7. Degree and count boundaries

Let `N44(s_old,t_old)` be package 44's full-carrier norm, of proven
exact degree 892. In the localization at E, the new norm satisfies

    Nnew = E^16 * N44(s+3q, t+(k-R-1)/E).

Every factor is scaled by `E^2`; there are eight factors. Since the
old norm has t-degree at most 16, this identity clears to an ordinary
polynomial identity. `deg(E)=6` and the rational correction has degree
`4-6=-2`, lower than t's degree 1. It therefore cannot change the top
homogeneous part. The highest linear substitution `s_old=s+3 beta J`
is invertible, so it preserves nonvanishing of the old leading form.
Thus the combined norm has exact degree `892+16*6=988`, and multiplying
by the nonzero degree-two transport factor gives exact degree 990.

An operation count is intentionally not asserted by this review: it must
be obtained from the actual emitted, fully live division-free DAG, with
each binary arithmetic operation charged. The derivation alone does not
establish that count. Likewise, symbolic and finite arithmetic audits
supplement the proof and cannot decide consistency.

## 8. Review conclusion

No circular use of the missing h coordinate was found. The new ingredient
needed to combine packages 38 and 44 is inequality (2), which compares
the coupled-root gap with the actual relative error rather than with the
coarser constant one. It permits `K=IT+1` before restoring the index
quotient, preserving package 44's degree cancellation. The remaining
compiler, Pell saturation, endpoint and object-language formalization
boundaries must remain explicit in the containing report.
