# Ten positive variables by four radical roots and small rational residues

## Status and inherited boundary

This note proves a new reduction from the normalized compact44 positive
Pell/source interface already used in packages 61, 69, 70 and the incoming
`ZFC_Diophantine_Joint_Guards/pell` component. It does not independently
reprove the native tableau compiler, K215 calibration, or the internal ZFC
formalization. The new reduction needs **no additional cofinal congruence
condition** on the canonical witnesses. In particular, it does **not**
impose `(q-1)|Y`.

The key new argument is that integrality of a sum of rational residues can
be separated by a small-absolute-value bound, after recovering the Pell
indices. Coprimality of `H` and `q-1` is unnecessary. The main Pell root's
sign is also forced by the same argument, after rank recovery.

Repository snapshot: `c1a102936aca437e9999530a0111e6ddab56dc6d`.
Primary inherited proof sources:

* `con-zfc-diophantine-forms/61-congruence-carriers/report/congruence_carriers.tex`,
  normalized strong-index and signed auxiliary-index lemmas, canonical
  witnesses, and the `q^5` main carrier.
* `61-congruence-carriers/positive/PROOF13.md` and `PROOF14.md`.
* Incoming `ZFC_Diophantine_Joint_Guards/pell/PROOF.md`, Sections 1--6:
  coefficient bounds, strong normalization, adjacent-coefficient descent,
  three-root majorants and weighted transport completeness.
* Incoming `.../pell/FOUR_ROOT_LIMITS.md`: two counterexamples which the
  present proof explicitly avoids.
* `NATIVE_HALF_BINOMIAL.md` explains why arbitrary extra divisibility of
  `Y` cannot simply be imposed. No such divisibility is used here.

All displayed divisions in this note are proof-only rational expressions;
the equation is obtained by the ordinary four-root norm and denominator
clearing, as specified by the accompanying polynomial generator.

## 1. Variables, fixed coefficients and polynomial registers

Use exactly ten strictly positive integer variables

    j, F, alpha, i, T, X, s, n, eta, zeta.

The four fixed compact44 coefficients are `beta,K0,MC,MF`, with `MF`
already the shifted mask. They are the coherent tuple used by the incoming
eleven-variable proof. In particular `beta=2^590069-1`, `K0>=1`,
`0<MC<beta`, `0<MF<2 beta`, and `beta=1 (mod 3)`.

Define polynomial registers

    J=3j+1; q=beta J+1; C=q-F-alpha;
    Y=q^3 s; E=XY; k=eta+zeta; c=kY+eta;
    a=E+Y; H=4a+3; Delta=a^2+H=(a+2)^2-1;
    ell=EkY;
    R=((q-1)(q-F)+alpha)(q^2-1)+(MC+q MF)J;
    Rhat=q^3(q+F+alpha);
    Bt=(q K0+X)C-qF;
    I=i c^2; Df=1+Delta I^2;
    Q=Delta^2 I^2; delta=Q-1; V=Df(cT-R)-c;
    Dt=ell(ell+k)+1; Dd=1+Delta c^2;
    Vbar=Df(cT+Rhat);
    Gbar=2c+2X+k+Rhat+1;
    L=3 Vbar+Gbar; W=1+(q-1)L;
    v=k-R-1; U=q^5; S=q^4; b0=X+ac.

For proof only put

    Dy=(Q V^2-1)/(Q-1),
    z_rat=ell+k+n+L+s-W Bt/(q-1)+b0/H+(S X-v)/U.

The equation asserts that `z_rat` is a signed sum of the four roots

    sqrt(Dt), sqrt(Df), sqrt(Dy), sqrt(Dd)/H.

More precisely, take the product of the sixteen conjugate linear factors
and clear all positive denominators. This gives one ordinary polynomial
in the stated ten variables. A norm zero is equivalent to an equality

    z_rat=tau_*+f_*+y_*+d_*/H,

where the starred roots have the indicated squares and arbitrary signs.
The next section proves that all four starred roots are rational, and
subsequently integral. This implication is not assumed merely from the
definition of a norm.

For exact agreement with the circuit, put `M=(q-1)U`. Its register named
`Z` is the integer polynomial `M H z_rat`; the scaled squared roots are
`M^2 H^2 Dt`, `M^2 H^2 Df`, `M^2 H^2 Dy`, and `M^2 Dd`.
The circuit multiplies the corresponding sixteen linear factors and
clears the sole remaining rational radicand denominator by `delta^8`.
All scaling factors are strictly positive on the stated domain.

## 2. Unconditional separation of every signed subset

This section assumes only positivity of the ten inputs. We have `q>=16`,
`Y>=q^3>=4096`, `k>=2`, `c>=2Y+1`, `a>=2Y`, `I>=c^2`, and `Q>Df>1`.
Let the positive real roots be

    t=sqrt(Dt), d=sqrt(Dd), f=sqrt(Df), y=sqrt(Dy).

The elementary inequalities inherited from the three-root construction are

    ell<t<ell+k<(a+1)c,
    f>(a+1)I>=(a+1)c^2,
    0<d/H<(a+2)c/H<c.

Moreover `c<k(Y+1)` and `ell=XY^2 k>=Y^2 k`. Since `Y>=4`,

    t>ell>2c+1.

Write `b=cT-R`, an integer. If `b=0`, then `V=-c` and

    c<y<c+1,

because `Q>c^2` and `Dy=c^2+(c^2-1)/(Q-1)<c^2+1`.
Thus

    0<d/H<y,    t>y+d/H,    f>t+y+d/H.

The last inequality follows from
`f-t>(a+1)c(c-1)>2c+1`.

If `b!=0`, then `|V|>=Df-c=f^2-c`, and `y>|V|`. We have
`f>t+d/H` from the displayed bounds. Also `f>3c^2>c+2`, so
`f^2-c>2f`. Consequently

    0<d/H<t,    f>t+d/H,    y>f+t+d/H.

In either case the four positive roots admit an ordering in which each
root after the first is strictly greater than the sum of all predecessors.
Every nonempty signed subset sum is therefore nonzero. This is stronger
than a single dominant root; the latter condition alone would not suffice
for four-root extraction.

### Rational extraction lemma

Let `r_1,...,r_m` be positive real square roots of positive rationals.
Suppose no nonempty signed subset sum is zero. If a signed sum of all
`r_i` is rational, each `r_i` is rational.

Proof: in the multiquadratic field generated by the roots, partition them
by their classes in `Q*/Q*^2`. Distinct square classes are linearly
independent over `Q`, by averaging against the quadratic characters of
the finite Galois group. In a rational signed sum, each nontrivial
square-class contribution must therefore vanish. Any nonempty such class
would give a forbidden signed subset sum. Hence every class is trivial.

Apply this lemma to `t,f,y,d/H`. At a polynomial zero all starred roots are
rational. Since `Dt,Df,Dd` are integers, `tau_*,f_*,d_*` are integers.
The adjacent-coefficient Pell descent (reproduced in the incoming proof)
applies to

    Q V^2-(Q-1)y_*^2=1

and gives `y_*` integral as well. The descent requires only `Q>1` and
integer `V`; it does not require main-root orientation, source rank,
transport divisibility, or `C>0`.

## 3. Uniform majorants and the positivity bootstrap

The coherent mask bounds imply, for every positive input,

    |R|<Rhat,    |V|<Vbar,    f+y<3 Vbar.

These are exactly the inequalities proved in Section 3 of the incoming
three-root proof; replacing its free `Y` by the positive polynomial
`q^3 s` preserves them.

Define proof-only rational coordinates

    r=tau_*-ell-k-s+W Bt/(q-1),
    gamma=(d_*-b0)/H-(S X-v)/U.

For either sign of `d_*`,

    |gamma|
      <=d/H+b0/H+X/q+|v|/q^5
      <c+(X+c)+X+(k+Rhat+1)
      =Gbar.

The four-root equality is precisely

    r+gamma+f_*+y_*=n+L.

Therefore

    r=n+L-f_*-y_*-gamma
      >=n+L-f-y-|gamma|>n>0.

At this point `r` and `gamma` may still be rational. Their integrality is
not used. The identity defining `r` gives

    W Bt/(q-1)=ell+k+s+r-tau_*>s+r>0,

since `|tau_*|<ell+k`. Thus `Bt>0`; if `C<=0`, its defining expression
would be negative. Hence `C>0` and the authenticated coefficient bounds
now give

    3q<R<q^4-2.

This establishes the bootstrap without assuming either main-root
orientation or exact transport divisibility.

## 4. The unsigned Pell indices and the q-power residue

Classify the positive roots `|d_*|` and `|tau_*|`:

    |d_*|=chi_A(p), c=psi_A(p), A=a+2,
    |tau_*|=chi_P(m), k=2 psi_P(m), P=2XY^2+1.

These are the inherited main and doubled-first Pell classification
lemmas. Since `c>1`, `p>=2`. If `m=1`, then `k=2`, `eta=zeta=1`,
and `c=2Y+1<2A=psi_A(2)`, impossible. Hence `m>=2`. The usual
growth estimates yield

    k>8XY^2, c>8XY^3>8q^9>2R, m<p, c>2p.

The strong equation uses `I=i c^2` exactly as in the normalized source.
It yields a strong Pell index divisible by `c` and greater than `2p`.
Put `S_aux=Delta I`; then `c|S_aux`, `S_aux>=2`, and
`S_aux^2=Delta(f^2-1)=Q`. The signed auxiliary-index lemma applies
to the integer norm `S_aux^2 V^2-(S_aux^2-1)y^2=1`. Its two residue
hypotheses are `V=-c (mod f)` and `V=-R (mod c)`, the latter following
from `f^2=1 (mod c)`. With `0<p,R<c/2`, it gives

    p=R.

It does not require the sign of `d_*`, a positive `gamma`, or transport
divisibility. It uses the positive main ordinate `c` and the absolute main
root. Also `c>2R` makes `V>1`, and `u=|y_*|-V>0` follows from `Dy>V^2`.

The root equality says that `r+gamma` is an integer. Since `tau_*`,
`ell,k,s` are integers, clearing its denominators gives

    U | H(q-1)(S X-v).

Now `q=2 (mod 3)` and `q^3|Y`; hence `H=3 (mod q)` and `gcd(H,q)=1`.
Also `gcd(q,q-1)=1`. Thus

    q^5 | q^4 X-v.

In particular `q^4|v`. The first Pell recurrence gives
`k=2m (mod 4XY^2)`, and `q^4|4XY^2`, so

    2m-R-1=0 (mod q^4).

Because `1<=m<p=R<q^4`, its absolute value is less than `q^4`.
Therefore it is zero:

    R=2m-1.

Now `v=k-2m` is a positive multiple of `4XY^2`, which itself is a
multiple of `q^5`. The previous congruence then yields `q|X`.
Consequently `(S X-v)/U` is an integer, and integrality of the merged
equality also gives

    (q-1)(d_*-b0)/H is an integer.                 (1)

No coprimality between `H` and `q-1` has been invoked.

## 5. A lower bound for Y which separates the remaining residue

Put `r0=(R-1)/2=m-1`. This temporary proof index is unrelated to the
transport coordinate `r`. From `R>3q` and `q>=16`, `r0>=24`.
Standard recurrence induction gives, for `B>=2`,

    psi_B(t)>(2B-1)^(t-1) for t>=2,
    psi_B(t)<=(2B)^(t-1) for t>=1.

Moreover

    (2A-1)^2-2PX
      =4Y^2(2X+1)+12Y(X+1)+9-2X>0.

It follows that

    c/k=psi_A(2r0+1)/(2 psi_P(r0+1))>X^r0/2.

On the other hand `c/k=Y+eta/k<Y+1`, so

    Y>X^r0/2-1>=q^r0/2-1>q 2^(2r0+1)=q 2^R.     (2)

The final elementary inequality already holds for `q>=16,r0>=4`:
`q^r0/2 >=4q 2^(2r0+1)`, and subtracting one leaves a strict excess.

## 6. Sign recovery and exact main/transport residues

Write `T0=2^R`. The Pell polynomials satisfy, modulo `H`,

    chi_A(R)-a psi_A(R)=2^R,
    chi_A(R)+a psi_A(R)=(2a+2)^R.

Indeed substitute `Delta=a^2` into the binomial expression for
`(A+sqrt(Delta))^R`; `A-a=2` and `A+a=2a+2`.
Since `2(2a+2)=H+1`, the second identity also gives

    T0(chi_A(R)+ac)=1 (mod H).                    (3)

Suppose first that `d_*=-chi_A(R)`. Multiplying (1) by `T0` and using
(3) shows that

    (q-1)(1+T0 X)/H

is an integer. It is positive. But (2) gives

    H>4Y(X+1)>4q T0(X+1)>(q-1)(1+T0 X),

so that integer is strictly smaller than one, a contradiction. Therefore
`d_*>0`.

The first Pell congruence and (1) now show that

    (q-1)(T0-X)/H

is an integer. Its absolute value is less than one: (2) yields
`H>4q T0(X+1)>q(T0+X)>(q-1)|T0-X|`.
It is consequently zero, and

    X=2^R,    H|(d_*-b0).

The recovered `gamma` is now integral. The merged equality makes `r`
integral as well. Since `r=tau_*-ell-k-s+W Bt/(q-1)`, we obtain
`(q-1)|W Bt`. Finally `W=1 (mod q-1)` gives

    (q-1)|Bt.

This is the promised replacement for the invalid cancellation of `H` in
the old four-root attempt. It is an Archimedean small-residue argument,
not a coprime-denominator assertion.

## 7. Reconstruction of the normalized source

Put

    w=X/q>0; s=Y/q^3=s>0;
    h=v/(XY)>0;
    gamma_old=(d_*-ac-X)/H;
    f_old=|f_*|, tau_old=|tau_*|, y_old=|y_*|;
    T_old=f_old T.

All are integers. The positivity of `gamma_old` follows from
`d_*>(a+1)c` and `c>X`, since
`H gamma_old=d_*-ac-X>c-X>0`.
The main, first, strong and auxiliary Pell equations hold, as does
`k-hXY-R=1`.

Because `Bt=q((K0+w)C-F)>0` and `(q-1)|Bt`, coprimality of `q,q-1`
gives the positive integer

    z_new=((K0+w)C-F)/(q-1).

Set `z=z_new+1`. Then
`(K0+w)C+(q-F)-z(q-1)=1`, the authentic old-z transport equation.
The normalized auxiliary coordinate agrees because

    c(T_old f_old-1)-R f_old^2=Df(cT-R)-c=V.

This reconstructs a positive source solution and hence, using exactly the
inherited source calibration, a finite syntactic ZFC refutation.

## 8. Canonical completeness; no extra restriction on Y

Start with a finite refutation and its canonical normalized source tuple.
The source already has `Y=q^3 s` with positive integer `s`; retain that `s`.
Its canonical repunit gives positive `j=(J-1)/3`. Retain `X,F,alpha,
eta,zeta` and the normalized strong pair `f,I=i c^2`.
The inherited auxiliary reconstruction supplies positive `T,u`, with
`y=V+u>0`.

The canonical first index is `(R+1)/2`. Thus `v=k-R-1` is a positive
multiple of `4XY^2`, and therefore of `q^5`. Since `q|X`, the number

    gamma=gamma_old-X/q+v/q^5

is an integer. Its sign is not needed; the unconditional bound
`|gamma|<Gbar<L` applies. Compute `Vbar,Gbar,L,W` after choosing the
strong and auxiliary witnesses.

The source gives `t0=Bt/(q-1)>=q`, and its positive first root satisfies
`ell<tau<ell+k`, while `s<k`. Define

    r=W t0+tau-ell-k-s.

Then

    r>qW-2k>2L,

because `L>k`, `q>=16`, and `W=1+(q-1)L`.
Set

    n=r+gamma+f+y-L.

It is an integer and is positive:
`n>r-|gamma|-L>r-2L>0`.
The four-root equality holds with the positive roots `tau,f,y,d`, so the
ordinary four-root norm vanishes. Every new variable is positive.

Thus the new polynomial has a positive zero if and only if the inherited
normalized source has one. No new parity, residue, divisibility, finite
group, or cofinality promise is required of canonical `Y` or `s`.

## 9. Logical conclusion and proof scope

Composing this new equivalence with the retained native/source theorem
gives, by ordinary mathematics formalizable in ZFC,

    exists a positive zero of the ten-variable polynomial
      iff a finite ZFC refutation exists.

Negation gives the requested equivalence of unsolvability and syntactic
`Con(ZFC)`. This note proves the new arithmetic reduction; it does not
claim that the inherited compiler or this new endpoint has been checked
as an object-language ZFC derivation in Lean. Coefficient identity,
ordinary mathematical correctness, finite algebraic replay, and the
unfinished formalization are distinct evidence levels.
