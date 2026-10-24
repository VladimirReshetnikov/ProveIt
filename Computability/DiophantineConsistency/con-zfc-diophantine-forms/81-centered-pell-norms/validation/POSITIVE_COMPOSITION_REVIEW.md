# Independent mathematical review of the positive-domain compositions

Reviewed against ProveIt commit
`2605669a532342f153b13eb6b4a0af4b54f5fa37`, 23 October 2026.

## Scope and verdict

The two proposed compositions are mathematically valid with the exact
strictly positive domains and inherited whole compact44 coefficient tuple
specified below.  The review concerns the new mathematical reductions and
degree claims.  It does not constitute independent reconstruction of the
native tile compiler, its K215 calibration, or an end-to-end Lean/Rocq
certificate.

1. In source 70's eleven-positive-variable equation, replacing
   `I=i*q*(q-1)*c^2` by `I=i*c^2` is valid.  The adjacent-coefficient Pell
   descent in source 69 replaces source 70's prime-support denominator
   argument.  The result has exact degree **277**.
2. In source 69's twelve-positive-variable equation, replacing its main
   carrier `U=q^5, S=q^4` by source 70's `U=4*q^2*Y, S=4*q*Y` is valid,
   while retaining `J=6j+1`.  The result has exact degree **78**.

The anticipated arithmetic counts are not certified by this proof memo.
They should be read from the separately rebuilt literal live circuits.

## Sources actually checked

All paths are relative to `Computability/DiophantineConsistency/con-zfc-diophantine-forms/`:

* `70-residue-orientation/eleven/PROOF.md` and `build.py`.
* `70-residue-orientation/positive/section.tex`, including the complete
  weighted/adaptive carrier proof.
* `69-cones-pell/positive/PROOF.md` and `build.py`.
* `61-congruence-carriers/positive/PROOF13.md`.
* `61-congruence-carriers/report/congruence_carriers.tex`, specifically
  `lem:auxcomplete` (the positive auxiliary reconstruction lemma).

## A. Eleven positive variables: removing q(q-1) from I

### A.1 Domain, root separation and the majorant

Retain exactly the eleven positive inputs of source 70.  Put `I=i*c^2`;
every other source-70 register is unchanged.  In particular `J=3j+1`,
`Df=1+Delta*I^2`, `Q=Delta^2*I^2`, `delta=Q-1`,
`V=Df*(c*T-R)-c`, and `Dy=(Q*V^2-1)/(Q-1)` in the proof only.

The source-70 unconditional separation proof uses the lower bound
`I>=c^2`, not the extra factor `q(q-1)`.  Here are its relevant checks:

* On all positive inputs, `c>=3`, `a>=2`, `Delta>=15`,
  `ell<ac`, `k<c`, and `Delta>a(a+1)`.  Consequently
  `1<Dtau<Df<Q`, with `Dtau=ell(ell+k)+1`.
* With positive roots `t=sqrt(Dtau)`, `f=sqrt(Df)`,
  `t<(a+1)c` and `f>(a+1)c^2>=3c^2`.
* Write `b=cT-R`.  If `b=0`, then `V=-c`, `Dy<c^2+1`, and
  `f>t+sqrt(Dy)`.  If `b!=0`, then `|V|>=Df-c`, hence
  `sqrt(Dy)>|V|>2f>f+t`.  Thus no signed sum of the three positive
  roots is zero.
* The radicands are pairwise distinct.  If `Dy=D` for either
  `D=Dtau` or `D=Df`, then `Q(D-V^2)=D-1`, contradicting
  `0<D-1<Q`.
* The bound `|R|<Rhat=q^3(q+F+alpha)` uses only positive inputs,
  the genuine mask bounds and `q>=16`.  Since `Df>c`, it gives
  `|V|<Vbar=Df(cT+Rhat)`.  Also `f<Vbar` and `sqrt(Dy)<2Vbar`.
  Thus `L=3Vbar>f+sqrt(Dy)` and `L>k` hold without any carrier
  equation, index equality, or `C>0` assumption.

These facts are sufficient for the rational three-radical extraction lemma
used in source 70.  No unproved independence of three square classes is
being assumed.  Its algebraic extraction formulas have nonzero denominators
because the radicands are distinct and the signed sum is nonzero.

### A.2 Integrality without any prime-support condition

At `N8=0`, the conjugate norm gives signed rational roots
`tau_*,f_*,y_*` whose squares are `Dtau,Df,Dy` and whose sum is
`Zbar/M`.  The first two are integers because they are rational roots
of integer squares.  For the third root, the defining identity is

    Q V^2 - (Q-1)y_*^2 = 1.

Here `Q>1` and `V` are integers before any carrier equation is used.
Source 69's Pell descent therefore makes `y_*` an integer directly.
The argument does not require `gcd(M,Q-1)=1`, `q(q-1)|I`, or any
divisibility of `Zbar` already known independently.

For clarity, the descent itself is sound.  If `y=a/m` is reduced,
`m^2|Q-1`.  For positive `V>1`, the transform

    V'=(2Q-1)V-2(Q-1)y,
    y'=(2Q-1)y-2QV

has integral `V'`, the same norm equation, the same reduced denominator
`m`, and `0<|V'|<V`.  The inequalities follow from `y>V` and
`QV>(Q-1)y`.  The terminal case `V=1` has `y=1`.  Sign changes do
not affect the proof.  This checks the one new semantic step required
for removing the strong-Pell multiplier.

### A.3 Soundness and positivity

Use

    i_old=i, f_old=|f_*|, y_old=|y_*|,
    u=y_old-V, r=n+L-f_*-y_*.

The unconditional bounds give `u>0` and `r>0`; the signs of `f_*`
and `y_*` must be retained in the definition of `r`.  Then
`Z=Zbar-M(f_*+y_*)=M*tau_*`, and the first, strong and auxiliary
residuals of the weighted carrier vanish.  Its main residual is the
unchanged `A1=0`.  Apply the source-70 weighted carrier theorem with
`h_*=L>0` to recover a positive source solution.

The product finalizer is unchanged.  `N8` is a square modulo 4,
and `A1` is a square modulo 4 because `4|U`.  Thus neither residual
can equal -2.  The identity `(1+N8)(1+A1)=1` is equivalent to both
residuals being zero.  No positivity of the residuals is required.

### A.4 Completeness and order of choices

The ordinary canonical source already provides a positive normalized
strong Pell pair `f,I` with `I=i*c^2`; no additional congruence is now
required.  Alternatively, powering the determinant-one Pell matrix
modulo `c^2` constructs such a pair by the elementary finite-group
argument in source 70.

The actual source-61 `lem:auxcomplete` applies to every positive pair
`f^2-Delta I^2=1` with `c|I`, assuming only the inherited canonical
`R>=3`, `R=3 mod4` and `c=psi_(a+2)(R)`.  It imposes no extra
strong-index congruence.  Hence it supplies positive `T,u,y` for the
chosen pair.  Compute `L,W` only after this step.  Then choose the
transport gap `r=Wt+tau-ell-k-s` as in source 70.  The source inequalities
give `r>qW-2k>L`, so `n=r-L+f+y>0`.  This makes
`Zbar=M(tau+f+y)` and the norm zero.  The independent adaptive-main
carrier reconstruction supplies positive gamma.

The choices are ordered: outer source, strong pair, auxiliary pair,
majorant and weight, transport gap.  There is no dependence loop.

### A.5 Exact degree after specialization

Put `q0=3*beta*j`, `k0=eta+zeta` and

    Bt0=(K0*q0+X)*(q0-F-alpha)-q0*F.

The new degrees are

    I 5, Df 14, Q 18, V 18, L 18, W 19, Zbar 24,
    A 16, Bf 22, Cnum 62, Ncenter 132, N8 264, A1 13.

The leading forms needed are

    Q0=i^2*k0^4*X^4*Y^8,
    Zbar0=-3*i^2*q0^7*k0^4*X^2*Y^6*(q0+F+alpha)*Bt0,
    in264(N8)=Q0^4*Zbar0^8,
    in13(A1)=32*q0^2*k0*X^2*Y^4
                   *(4*q0^2*Y*gamma+q0^3*(q0-F)).

Only the product `N8*A1` reaches degree 277.  The coefficient of

    j^60 i^24 eta^49 X^42 Y^85 alpha^16 gamma

is exactly `2^7*3^8*(3*beta)^60>0`.  Choosing gamma forces its branch
of the last factor; choosing the minimum j exponent forces the q0-free
parts of `(q0+F+alpha)^8*Bt0^8`, which give
`X^8*(F+alpha)^16`.  Thus the coefficient cannot be cancelled by the
other fixed ports.  This proves exact degree 277 on the authentic slice.

## B. Twelve positive variables: inserting the adaptive main carrier

### B.1 What changes

Retain all twelve source-69 inputs and every source-69 register except
the two main-carrier scales.  Use

    J=6j+1, S=4qY, U=qS=4q^2Y,
    Dstar=U(X+ac)+H(U*gamma+S*X-r0),
    A1=Dstar^2-U^2(1+Delta*c^2).

Keep `W=1+(q-1)k` in the first carrier, and keep the source-69 merger
norm `N` with `f=t+1`, `rho=f^2-1`, `d=Delta*c^4`,
`Q=Delta*rho`, and `V=f^2(cT-R)-c`.

### B.2 No circular use of positivity or rank recovery

From `A0=0` alone, the first carrier yields `q^3|Y`, `q-1|Bt`,
and `Bt>0`, hence `C>0`.  Only then invoke the authentic-source
inequalities `3q<R<q^4-2`.

The adaptive numerator is positive before `q|X` or any auxiliary-rank
conclusion.  Indeed `r0<k`, `c>kY`, and
`UaY-H=4a(q^2Y^2-1)-3>0`, so `Dstar>Uac-Hk>0`.
Therefore `A1=0` supplies a positive integral main Pell root.
The main and first Pell classifications, using just `A0,A1`, give

    c>kY>=4(2XY^2+1)Y>8XY^3>=8q^9>2R.

As in the parent, the first index cannot be one: that would give
`k=2, eta=zeta=1, c=2Y+1`, contrary to the second main Pell value
`c>=2(a+2)>=4Y+4`.

Since `f=t+1>=2` and `T>=1`, it follows that

    V=f^2(cT-R)-c>f^2*c/2-c>=c>1.

This conclusion is available before the merger norm is decoded.  Thus
its denominator `2(1-Q)(n+V)` is nonzero.  Source 69's rational recovery
and Pell descent make its recovered `i,u` integral, and replacing them
by `|i|` and `|y|-V` makes both positive.  The four weighted-carrier
residuals then vanish with `h_*=k`, and source 70's theorem reconstructs
the original normalized source.  For the theorem's `J=3j_old+1`
parameter use `j_old=2j>0`.

### B.3 Finalizer and completeness

The stronger `J=6j+1` condition is retained.  Since beta is odd, q is
even.  Hence `A0` is a square modulo4.  The adaptive `U` is divisible
by4, so `A1` is a square modulo4.  The merger's `bN` is even, so N
is a square modulo4 as well.  Consequently the three-factor finalizer
`(1+A0)(1+A1)(1+N)=1` forces all three residuals to vanish.

Canonical source witnesses have `J=1 mod6`, so the new positive j exists.
Source 70's weighted/adaptive completeness gives positive r and gamma
with `h_*=k`.  Source 69's canonical strong and auxiliary pair then
gives `t=f-1>0`, `n=i+u>0`, and the exact merger identity gives N=0.
The adaptive gamma choice depends only on the outer source and satisfies
`gamma=gamma_old-w+r0/U>0`; the last positivity is source 70's
`r0/U>=XY/q^2=wY/q>w`.

### B.4 Exact degree and leading coefficient

Put `q0=6*beta*j`, `k0=eta+zeta`, with Bt0 as above.  The unchanged
first carrier and merger have exact leading forms

    in15(A0)=-2*q0^8*k0^2*X*Y^2*Bt0,
    in50(N)=4*q0^6*(q0-F)^2*k0^8*X^8*Y^16*t^8*n^2.

The adaptive main residual has the degree-13 leading form from A.5.
Only the product of the three residuals reaches degree 78.  Its
homogeneous form is

    -256*q0^16*(q0-F)^2*k0^11*X^11*Y^22*t^8*n^2*Bt0
           *(4*q0^2*Y*gamma+q0^3*(q0-F)).

The coefficient of

    j^18 F^2 eta^11 X^12 Y^23 t^8 n^2 gamma alpha

is exactly `1024*(6*beta)^18>0`.  The gamma branch supplies the factor4;
the smallest j exponent forces F^2 from `(q0-F)^2` and `-X*alpha`
from Bt0.  This proves exact degree 78 after every authentic fixed port
has been specialized.

## Limitations and integration requirements

The reduction depends on the exact whole compact44 coefficients and the
source-61/source-70 normalized compiler interface.  The ordinary proofs
are formalizable in ZFC, but this memo does not claim a proof-assistant
certificate.  The final deliverable should include literal circuit
rebuilds, independently measured operation counts, exact degree
certificates and the unchanged source coefficient provenance.  The
eleven-variable result retains the source-70 K215 route; the new CRT
homogenization theorem belongs in a separate exploratory section.
