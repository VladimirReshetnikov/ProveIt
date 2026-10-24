# Independent review of the eleven-positive root-transfer extension

Review date: 23 October 2026. Source snapshot:
`9cca523d9f27ad39d52993f4065cbd7e58f8bdd4` of
`VladimirReshetnikov/ProveIt`.

This review was prepared by an agent separate from the construction author.
It is an internal AI-assisted mathematical and algebraic review, not external
peer review, a Lean/Rocq certificate, or an exported derivation in the
repository's object-language ZFC calculus. No consistency assumption is used.

## Conclusion and exact scope

The final polynomial `p11_positive_degree325.json` has eleven strictly
positive integer unknowns, exact degree 325, and 113 live binary arithmetic
operations: 67 multiplications, 29 additions, and 17 subtractions. Its
two-residual presentation has degrees 312 and 13 and costs 110 operations.
The ordinary existence-equivalence proof is sound relative to the identified
inherited normalized positive compiler, Pell, and K215 calibration theorems.
The parent weighted/adaptive-carrier theorem was separately reviewed in the
twelve- and thirteen-positive component before this extension was considered.

The inherited coefficient inputs are the complete compact44 tuple with
`beta = 2^590069 - 1`; `MF` is already shifted. This extension uses the same
four integer inputs and introduces no new coefficient calibration. The
literal independent checker verifies the exact four fixed-port names and
their use. Payload authentication and the binding manifest are separately
covered by the component verifier and the retained parent coefficient audit;
the algebraic audit does not claim to rebuild that native compiler tuple.

The inspected eleven-positive predecessor is package 52's
`positive/positive11_Y_lean_product.json`: degree 954 and 113 operations.
Its literal JSON, README, and `positive/Y_ABSORPTION_PROOF.md` were inspected.
Package 50's degree-954/115-operation and package 53's degree-958/117-operation
or degree-962/115-operation variants do not improve that point; the inspected
later packages do not supply a better eleven-positive point. The new result
therefore lowers the degree at the same variable count and operation count
in this explicitly bounded comparison. No global minimum is inferred.

## 1. The radical bounds hold before the carrier equations

Let the eleven supplied coordinates be positive and use the registers in
`PROOF.md`. Then `q>3`, `k>=2`, `c>=3`, `a>=2`, `Delta>=15`, and
`I=i*q*(q-1)*c^2 >= c^2`. These do not use `C>0`, scale divisibility, or
an index equality. The elementary inequalities

    ell < a*c,   k<c,
    ell(ell+k) < a(a+1)c^2 < Delta*I^2

give `1<Dtau<Df<Q`, where `Q=Delta*(Df-1)=Delta^2*I^2`. The strict
inequality `Q>Df` also follows directly from
`Q-Df=Delta*(Delta-1)*I^2-1>0`.

For positive real roots `t=sqrt(Dtau)` and `f=sqrt(Df)`,

    t < ell+k < (a+1)c,
    f > (a+1)I >= (a+1)c^2 >= 3c^2.

Writing the integer `b=cT-R`, the formula `V=Df*b-c` yields `V=-c`
if `b=0`, `V>=Df-c>1` if `b>=1`, and `V<=-Df-c<-1` if `b<=-1`.
Thus `|V|>1` on every positive input. Consequently the rational auxiliary
radicand satisfies

    Dy=(Q*V^2-1)/(Q-1)=V^2+(V^2-1)/(Q-1)>V^2>1.

No complex-root or zero-root case remains hidden in the norm argument.

## 2. Every rational-sum degeneracy is excluded

The three radicands `Dtau,Df,Dy` are pairwise distinct. The first two were
ordered above. If `Dy` equals either integer `D` among them, then

    Q*(D-V^2)=D-1,

which is impossible because the right side is strictly between 0 and Q.

There is a strict dominant root in both cases for `b=cT-R`. If `b=0`,
then `Dy<c^2+1`, so `y=sqrt(Dy)<c+1`, whereas

    f-t > (a+1)c(c-1) > c+1.

Thus `f>t+y`. If `b!=0`, then `|V|>=Df-c>2f>f+t`, so
`y>|V|>f+t`. Therefore **every** signed sum of the three roots is nonzero.
Both cases are necessary; one cannot assume `cT-R` has a particular sign.

The elementary root-extraction lemma in the final proof is valid. For
signed roots `x1,x2,x3` with nonzero rational sum `t` and rational squares
`a,b,c`, define

    u=(t^2-a-b-c)/2,
    v=(u^2-ab-ac-bc)/(2t).

Then `u=x1*x2+x1*x3+x2*x3` and `v=x1*x2*x3`. Moreover

    x1*(a*t+v)=a*(a+u),
    a*t+v=x1*(x1+x2)*(x1+x3).

The denominator is nonzero because the radicands are positive and pairwise
distinct. Thus `x1` is rational; cyclic repetition gives all three roots.
The independent audit proves these polynomial identities exactly. The
alternative square-class argument is also correct, but is unnecessary for
the elementary proof and is not being used to assume independent sign
automorphisms after specialization.

## 3. The final majorant remains unconditional

The final circuit uses

    Rhat=q^3*(q+F+alpha),
    Vbar=Df*(cT+Rhat),   L=3*Vbar.

The authentic compact tuple has `0<MC<beta` and `0<MF<2*beta`.
Since `J=(q-1)/beta`, its positive mask term is less than `2q^2`.
The triangle inequality therefore gives

    |R| < q^4+F*q^3+alpha*q^2+2*q^2 < Rhat,

the last step using `alpha>=1` and `q>3`. This argument does not presume
that `F<q`, `alpha<q`, or `C>0`.

Because `Rhat` and `R` are integers, `Rhat-|R|>=1`. Hence

    Vbar-|V| >= Df*(Rhat-|R|)-c >= Df-c > 0.

This explains why the final optimized `Vbar` needs no added `+c`.
Also `Vbar>Df>sqrt(Df)` and
`sqrt(Dy)<2|V|<2Vbar`. Thus `L>sqrt(Df)+sqrt(Dy)` and `L>c>k`.
These bounds supply a positive recovered transport gap for every norm
sign choice and a positive inverse coordinate for completeness.

## 4. The cleared norm has exactly the intended roots

The universal octic identity is

    F8(x;a,b,c)
      = ((x^2-a-b-c)^2-4(ab+ac+bc))^2-64abc*x^2
      = product over epsilon in {+1,-1}^3
          (x-epsilon1*sqrt(a)-epsilon2*sqrt(b)-epsilon3*sqrt(c)).

It is a polynomial identity, valid also when the formal sign factors cease
to be distinct after specialization. The independent checker multiplies all
eight factors in an ordinary polynomial ring after replacing `a,b,c` by
three independent squares, and obtains this exact identity.

Put `A=M^2*Dtau`, `Bf=M^2*Df`, `Cnum=M^2*(Q*V^2-1)`, and
`delta=Q-1>0`. The final compressed registers

    Tn=delta^2*A*Bf,
    Rn=delta*Cnum,
    Jn=delta*(Zbar^2-A-Bf)-Cnum,
    Ncenter=Jn^2-4*(Tn+Rn*(A+Bf)),
    N8=Ncenter^2-64*Tn*Rn*Zbar^2

are exactly `delta^4*F8(Zbar;A,Bf,Cnum/delta)`. The independent checker
verifies the compressed center and tail against the uncompressed formula.
Since `M,delta>0` and all three radicands are positive, `N8=0` gives
signed roots with

    Zbar/M=tau_*+f_*+y_*.

The preceding separation and extraction argument forces all three roots
to be rational; it is not sufficient merely to invoke a resultant.

## 5. Integrality and all signed restoration branches

The squares of `tau_*` and `f_*` are integers, so these rational roots are
integers. The displayed sum shows that the reduced denominator d of
`y_*` divides M. Its square relation gives `d^2 | delta`.
Every prime dividing `M=q^3(q-1)` divides I and hence Q, so
`gcd(M,Q-1)=1`. Therefore `d=1`. This is a prime-support argument;
the stronger and generally false assertion `M|Q` is not needed.

Set

    i_old=i*q*(q-1),  f_old=|f_*|,  y_old=|y_*|,
    u=y_old-V,
    r=n+L-f_*-y_*.

The first three coordinates are positive. Since `y_old>|V|`, also `u>0`.
Since `L>|f_*|+|y_*|`, also `r>0` for all four sign combinations of
the eliminated strong and auxiliary roots. It is essential that their
signed values occur in r; using absolute values there would not preserve
the first carrier.

The actual carrier then satisfies

    Z=Zbar-M*(f_*+y_*)=M*tau_*.

The strong equation follows from `f_old^2=Df`; the auxiliary equation
follows from `Q*V^2-(Q-1)*y_old^2=1` with `y_old=V+u`. Thus the four
weighted-carrier equations are restored, with positive weight `hstar=L`.
The already reviewed weighted/adaptive-carrier theorem recovers the
normalized source and the inherited finite syntactic ZFC refutation.

## 6. Completeness and freedom to impose stronger divisibility

Fix the outer coordinates of a canonical source witness. With
`m0=q(q-1)c^2` and `Aparam=a+2`, the matrix

    [[Aparam,Delta],[1,Aparam]]

has determinant one. Its reduction modulo m0 lies in a finite group, so
some positive power is the identity. The integer entries of that power
give `f=chi_Aparam(v)>0` and `I=psi_Aparam(v)>0` with `m0|I`.
This supplies the required positive coordinate `i=I/m0` without assuming
an extra divisibility promise from the original compiler.

I checked package 61's `lem:auxcomplete` directly. It requires only the
canonical `R>=3`, `R=3 mod4`, `c=psi_Aparam(R)`, and a positive strong
Pell pair with `c|I`. The stronger divisor m0 therefore preserves all its
hypotheses. It supplies fresh positive T,u and y. The construction order
is: outer witness, strong pair, auxiliary pair, then L,W, then transport
gap. There is no circular choice of a strong root depending on its own
majorant.

The canonical first transport construction gives `r>qW-2k>L`, because
`W=1+(q-1)L`, `q>=16`, and `L>k`. Thus

    n=r-L+f+y>0.

It gives `Zbar=M*(tau+f+y)`, so a coherent octic factor vanishes. The
unchanged adaptive main carrier supplies positive gamma and vanishes as
well. Every supplied coordinate is positive.

## 7. Unit-product finalization is valid without residual positivity

The final literal output is `P11=N8+A1+N8*A1`, identically
`(1+N8)(1+A1)-1`. The equation therefore forces the two integer factors
to be both 1 or both -1. But N8 is a square minus 64 times an integer,
and A1 is a square minus `U^2` times an integer, with `4|U`. Each residual
is 0 or 1 modulo 4, so neither can equal -2. Thus

    P11=0  if and only if  N8=A1=0.

No claim that either residual is everywhere nonnegative is made or needed.

## 8. Independent finite algebra and exact degree

`independent_audit.py` uses the separately authored sparse ring in
`independent_ring.py`; it imports neither the construction builder nor its
verifier. It checks all 59 named local polynomial contracts in the literal
DAG, the finalizer, gate ordering, complete input/gate liveness, and exact
counts. The result is 113 live gates, comprising 67 multiplications,
29 additions, and 17 subtractions. Restricting to the two residual outputs
leaves 110 gates.

The audit verifies the universal norm, elementary root extraction,
compressed norm identities, and adaptive-main cancellation by exact
integer polynomial arithmetic. It then propagates leading homogeneous
forms through the actual literal DAG. The single apparent degree-14
cancellation in A1 is handled by the separately checked identity

    A1=2Uac*(UX+H*shift)+(UX+H*shift)^2-U^2*H*c^2-U^2.

Its unique degree-13 term is `2UacH*shift`. Every other residual/gate
leader is propagated exactly, rather than inferred from generic maxima
that might cancel. In leading coordinates `q0=3*beta*j` and
`k0=eta+zeta`, the final leading polynomial has 9,917 symbolic monomials.
The audit obtains exact degrees

    I:7, Df:18, Q:22, V:22, Rhat:4, L:22, W:23, Zbar:28,
    A:16, Bf:26, Cnum:74, Ncenter:156, N8:312, A1:13, P11:325.

It independently recovers the exact coefficient

    [j^108 i^24 eta^49 X^42 Y^85 alpha^16 gamma] P11
      = 2^7 * 3^8 * (3*beta)^108 > 0.

There are no remaining uncompressed j,eta,zeta terms in the leading
form before this substitution, so the selected coefficient transfers
without ambiguity from the q0,k0 coordinates. It is independent of K0,
MC,MF and remains nonzero for the authentic positive beta. This proves
the stated degree on the actual fixed tuple, not merely a generic slice.

Both normal and `python3 -O` executions of the audit pass. Its
machine-readable receipt is `INDEPENDENT_AUDIT.json`. Finite verification
does not establish consistency, produce a refutation, or prove the
unbounded compiler theorem; those remain the written mathematical proof
and its explicitly inherited source interfaces.

## 9. Attribution and the actual architectural difference

Package 52 already uses multiroot norms, conditional radical separation,
positive majorants, and a modulo-four unit-product finalizer. These generic
tools are not new in this extension. Package 61 supplies the positive
transport carrier and normalized squared-root auxiliary
interface; package 65 supplies the adaptive modulus idea used in A1.

The new composition differs from package 52 in specific ways. Its norm
keeps the main Pell root, first Pell root, strong Pell root, and an
auxiliary ordinate inside eight quadratic factors; the resulting norm
has degree sixteen in its carrier. Its auxiliary radicand depends on the
signed strong root. In the present construction, `V=Df(cT-R)-c` uses the
strong square only, so the auxiliary radicand is independent of the sign
of that root. The first root, strong root, and auxiliary root can therefore
be transferred together into the first positive transport gap with a
direct octic sum norm. The adaptive main carrier is retained separately,
and X,Y are direct supplied coordinates. Finally, the factor q(q-1) in I
forces denominator coprimality and replaces the older rational-Pell
saturation step by elementary integrality.

The defensible novelty claim is this composition, its explicit positive
inverse map, and the checked degree-325/113-operation endpoint in the
inspected family. Neither a new generic three-root norm nor a new generic
product finalizer is claimed.
