# Independent review: recovering an omitted index quotient from a Pell residue

This note reviews the thirteen-positive-variable descendants of
the package-142 fourteen-variable raw and reduced coprime products. It
reviews the mathematical construction, not a new end-to-end proof-assistant
certificate. The two emitted JSON circuits were inspected against their
complete frozen parent sources. Independent literal parent-delta, topology,
full-liveness and domain checks passed; hashes and operation counts are in
`FIXED13_SOURCE_REVIEW.json`. Full coefficient materialization and the
construction's own finite algebra checker remain separate responsibilities.

## Reviewed construction

Use the complete fixed coefficient tuple and the outer definitions of the
retained package-142 proof. Write

```
E = X Y,        k = eta+zeta,       ell = E k Y,
A1 = 1+ell(ell+k),                 c = kY+eta,
a = E+Y,       A0 = a+2,           Delta = A0^2-1,
N1 = D^2-Delta c^2,
Nt = (K0+w)(q-F-alpha)+(q-F)-z(q-1).
```

Replace the former input `i` throughout the strong construction by `E*i`,
replace the former independent combined root `t` by the integer polynomial

```
t = E*n-k+R,
```

and delete the input `h` and factor `Nk=k-hE-R`. Keep `n` positive; the
displayed `t` is not assumed positive. The new product equation is

```
N1 * Nt * (3 Eprod+1) * Ns = 1.
```

The old raw or reduced definitions of `Eprod,Ns` are otherwise retained.
The proposed operation counts are respectively 70 and 71. Their exact
degrees independently recompute to 206 and 162.

## Soundness audit

### 1. Recover the roots before using the missing congruence

All product factors are integral units. The factor `3 Eprod+1` is `1 mod 3`,
so it equals +1. The main norm cannot be -1 modulo 4, because
`Delta=A0^2-1` is 0 or 3 modulo 4. Hence `N1=1` and `Eprod=0`.

In the raw construction, set `Baux=Q-1`, `Caux=Q V^2-1`. Its folded
identity is

```
Baux*t^2 = A1*Caux.
```

The definitions give `A1|Q`, so both `Baux` and `Caux` are -1 modulo
`A1`. Also `Q>1` rules out `t=0`, since that would force `Q V^2=1`.
Every prime valuation in `A1` is therefore even. Consequently
`A1=tau^2`, with `tau>0`, and `tau|t`. Now the normalized strong factor
is a genuine Pell norm and cannot be -1 modulo 4. Thus `Ns=1`.
The reduced construction obtains `Ns=1` first and then applies the same
coprime extraction. Both routes give a positive integer `j` with

```
f^2 = 1+Delta*j^2*c^4,   S = Delta*j*c^2,   Q = S^2,
j = tau*E*i             (raw),
j = A1*E*i              (reduced).
```

Therefore `y=|t|/tau` is a positive integer and

```
Q V^2-(Q-1)y^2 = 1.
```

The remaining product factor is `Nt=1`. No unresolved transport sign and
no premise about the omitted `Nk` are used in these deductions.

### 2. Authenticate the main index independently of `Nk`

Put `C=q-F-alpha`. If `C<=-1`, then `Nt<=-(K0+w)<=-2`, using
`F,z>=1`. If `C=0`, then `q-F=alpha<=q-1` and `Nt<=0`. Thus `C>0`.
The literal fixed coefficient bounds give `3q<R<q^4-2<E`.

The first Pell norm has discriminant `EY(EY+1)`, whose fundamental
positive solution is `(2EY+1,2)`. Hence, for some `n0>=1`,

```
tau = chi_P(n0),     k = 2 psi_P(n0),     P = 2EY+1.
```

The main norm gives `c=psi_A0(p)` with `p>=1`. If `n0=1`, then `k=2`,
`eta=zeta=1`, and `c=2Y+1` lies strictly between `psi_A0(1)=1` and
`psi_A0(2)=2A0`, a contradiction. Therefore `n0>=2`, and

```
k >= 8EY+4,       c > kY > 8XY^3 > 2R.
```

Also `c>2`, so `p>=2` and `c=psi_A0(p)>2p`.

The retained normalized-rank lemma applies to
`I=j*c^2=psi_A0(m)`: strong divisibility gives `p|m`; writing `m=pv`
and `D0=chi_A0(p)`, composition gives `I=c*psi_D0(v)`. Since
`D0^2=1 mod c`, the recurrence gives
`psi_D0(v)=v*D0^(v-1) mod c`. Hence `c|v`, so `pc|m` and `m>2p`.

The signed auxiliary-index lemma now has all its hypotheses:

```
c=psi_A0(p), f=chi_A0(m), c|m, m>2p,
c|S, S^2=Delta*(f^2-1),
V=-c mod f, V=-R mod c, 0<p,R<c/2.
```

For clarity, the second congruence follows from `f^2=1 mod c`; the
first is immediate from `V=f^2(cT-R)-c`.

Here is the signed lemma's essential proof. Classify the auxiliary Pell
equation at base `S` to obtain an odd index `nu=2v+1` with
`S|V|=chi_S(nu)`, `y=psi_S(nu)`. The odd quotient identity
`chi_S(2v+1)/S=Q_v(S^2)` and `Q_v(1-A0^2)=(-1)^v psi_A0(2v+1)` give
`psi_A0(nu)=±c mod f`. Squaring converts this into
`chi_A0(2nu)=chi_A0(2p) mod chi_A0(m)`. The signed abscissa stepdown
with `2p<m` gives `nu=±p mod m`, hence modulo `c`. On the other hand,
`Q_v(0)=(-1)^v nu` and `c|S` give `nu=±R mod c`. Thus `p=±R mod c`.
The strict bounds below `c/2` force `p=R`.

The detailed coefficient-independent proofs of the normalized-rank and
signed-index lemmas are retained in the Nearest-Factorial source closure,
`compact/upstream/upstream/certificate_sources/universal_pell.tex`,
Lemmas “Direct normalized rank” and “Signed auxiliary-index recovery”.
They explicitly do not assume a deleted index quotient. I independently
checked their stepdown and rank arguments.

### 3. The auxiliary ordinate replaces the missing quotient constraint

As `P=1 mod E`, its abscissa recurrence gives `tau=1 mod E`. The strong
construction gives `E|S`. Since `nu` is odd, the ordinate recurrence gives

```
y = psi_S(nu) = ±1 mod S^2,
```

and consequently `t=±tau*y=±1 mod E`. The defining polynomial
`t=E*n-k+R` therefore yields `k-R=epsilon mod E`, for some
`epsilon` in `{+1,-1}`. Independently the first Pell recurrence gives
`k=2n0 mod E`.

Since `P>A0`, an index `n0>=R` would imply
`k=2psi_P(n0)>psi_A0(R)=c`, contrary to `c>kY`. Thus `n0<R`.
Both `R<E` and the strict bounds on `n0` show
`|2n0-R-epsilon|<E`. The congruence is therefore the exact equality

```
2n0 = R+epsilon.
```

The branch `epsilon=-1` is impossible. Put `B0=2A0^2-1`. The duplication
identity gives

```
psi_A0(2n0+1) = psi_B0(n0+1)+psi_B0(n0).
```

Here `B0>P` and `2B0-1>2(Y+1)`. The Pell recurrence and monotonicity
give
`psi_B0(n0+1)>(2B0-1)psi_B0(n0)>2(Y+1)psi_P(n0)`.
Thus `R=2n0+1` would imply `c>k(Y+1)`, contradicting
`c=kY+eta<k(Y+1)`.

Hence `2n0=R+1` and `E|(k-R-1)`. Restore

```
h = (k-R-1)/E.
```

It is positive because `k>=8EY+4` and `R<E`. Thus `Nk=1` is restored,
and all positive parent coordinates exist. This proves soundness by an
exact bridge to the retained positive P66/native calibration.

## Completeness audit

A finite refutation supplies the canonical parent outer coordinates with
`R=3 mod 4`, `A1=tau^2`, and `k-R-1=hE`. Keep these outer coordinates.
The finite matrix-period construction lets the strong multiplier `j`
be chosen divisible by `tau*E` in the raw case, or by `A1*E` in the
reduced case. Set the new positive `i` to the resulting quotient and
choose fresh canonical auxiliary witnesses for this new strong pair.

For `S=Delta*j*c^2`, these are

```
y_star=psi_S(R),
V_star=chi_S(R)/S,
T_star=(V_star+c+R*f^2)/(c*f^2)>0.
```

The retained polynomial congruences make `T_star` integral. Because
`R=3 mod 4`, `y_star=-1 mod S^2`, so
`t_star=tau*y_star=-1 mod E`. Also `k-R=1 mod E`. Therefore

```
n = (t_star+k-R)/E
```

is a positive integer and realizes `E*n-k+R=t_star`. All factors of the
new product equal +1. This is a new canonical completion, rather than a
claim that an arbitrary old strong multiplier already has the requested
divisibility.

## Degree check and qualification

In the raw variant the respective degrees of `W,Q,Eprod,Ns` become
`68,80,118,68`. With `deg(N1)=18`, `deg(Nt)=2`, the output degree is
206. An attained coefficient is `-24 beta^124` at

```
J^124 w^18 s^35 eta^17 i^4 f^4 T^2 gamma z.
```

In the reduced variant the corresponding degrees are `90,14,52,90`,
giving exact degree 162. An attained coefficient is `-24 beta^96` at

```
J^96 w^14 s^27 eta^13 i^2 f^6 T^2 gamma z.
```

These are nonzero for the actual fixed `beta>0`. The new computed `t`
has degree 7 and cannot cancel either top homogeneous term.

The same argument does not automatically extend to the parent with the
strong root itself omitted: there the combined root is `tau*f*y`, and
`f^2=1 mod E` does not imply the single global sign `f=±1 mod E` for a
composite `E`. No twelve-variable conclusion is asserted here.

The emitted circuits agree literally with the construction specified above.
The thirteen-variable mathematical improvement is valid relative to the
explicit retained logical calibration.

## Later q-squared multiplier and q-fourth-power carrier

The additional 13-positive, 72-operation, degree-154 reduced variant has
also passed conceptual review. Replace the multiplier scale `E` by `q^2`
and use `t=q^4*n-k+R`. Now the proof needs only `q^4|Q=S^2`, rather than
`E|S`: the odd auxiliary ordinate is `±1 mod Q`, and hence `±1 mod q^4`.
The first abscissa still has `tau=1 mod q^4`, because `q^4|E` and
`P=1 mod E`. The strict bound `R<q^4` again turns the missing congruence
into `2n0=R±1`; the same ratio argument excludes the minus sign.

After `2n0=R+1` has been recovered, the full first-Pell recurrence gives
`k=2n0 mod 4EY`. Thus `E|(k-R-1)` is restored even though the new
carrier used the smaller modulus `q^4`. There is no invalid cancellation
of a factor of a composite modulus. Canonical completeness chooses the
strong multiplier divisible by `A1*q^2`; `y_star=-1 mod Q` then gives the
required `q^4` congruence and a positive carrier input.

The degree is independently `18+2+52+82=154`. The attained coefficient is
`-24*beta^92` at `J^92*w^12*s^25*eta^13*i^2*f^6*T^2*gamma*z`.
The complete literal graph has one extra `q^4=q^2*q^2` multiplication
relative to the 71-operation variant. Its source hash is recorded in the
updated finite-source receipt.

## Rational twelve-variable companion

Section 7 of the final `FIXED_CARRIER_PROOF.md` was also independently
reviewed and accepted. Its rational intermediate is positive from
`n>=1`, `R<E-2` and `k>=2`. Prime valuations over the rational numbers
recover the two coprime integer squares. The adjacent-Pell descent is
valid: `d^2|(Q-1)` makes the transformed first coordinate integral;
the displayed difference of squares proves it positive, and `y>v` makes
it strictly smaller than `v`. The transformed ordinate preserves its
reduced denominator since `2Q-1=1 mod d`. Therefore the rational ordinate
is integral, giving `E|(k-R-1)` and the restored positive `h`.
The zero case of this difference is excluded by the first-Pell gap.
For completeness, cofinal strong powers let the positive restored combined
root exceed the fixed outer `h`, so `n=t-h` is positive. No global sign
for a square root of one modulo composite `E` is used. This validates the
separate 12-positive, 74-operation, degree-438 construction.
