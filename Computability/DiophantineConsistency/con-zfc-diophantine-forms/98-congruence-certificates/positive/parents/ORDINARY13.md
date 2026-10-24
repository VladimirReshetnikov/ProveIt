# Thirteen positive variables, 90 operations, degree 51

The ordinary strong norm also improves the earlier 13-positive 90/55
unit-product tradeoff to **90 live operations and exact degree 51**.
It remains a degree/cost tradeoff with source73's 92/30 sum of squares.
This is an ordinary mathematical reduction with the same whole compact44
tuple. No Lean work or new native calibration is claimed.

The literal circuit is [p13_ordinary_degree51.json](p13_ordinary_degree51.json).
Its only unknowns are

```text
j,F,alpha,f,i,T,X,Y,r,eta,zeta,u,gamma > 0.
```

Use the shared adaptive carrier from the
[normalized-norm note](../short-unit-products/README.md#binding-and-shared-carrier)
with `m=3`, hence `J=3j+1`. Use exactly its authentic compact44 four
ports; MF is already shifted. Define

```text
rho=f²-1, Q=Delta rho, I=ic²,
V=f²(cT-R)-c, y=V+u,
F0=1+A0, F1=1+A1,
Fa=Q V²+(1-Q)y²,
Fs=1+I²-Q.

P13=F0 F1 Fa Fs-1=0.
```

The change is the strong factor: the normalized version used
`f²-Delta I²`, of degree14. Here `Fs=1+I²-Q` has degree10.
The literal circuit replaces one multiplication by one addition:
49 multiplications, 24 additions, and 17 subtractions still total90.

**Unit-product lemma.** For every integer assignment to all input symbols
and ports, P13 vanishes if and only if

```text
A0=A1=0,   Q V²+(1-Q)y²=1,   I²=Q.
```

This is an exact local statement about the ordinary residuals. It is not
a claim that ordinary and normalized strong equations have the same zero
sets on every tuple. As in the normalized 13-factor proof, M is even,
Delta is zero or three modulo four, and Q is zero or one modulo four.
Thus F0 and F1 cannot equal -1, while Fa is V² or y² modulo four.
Also `Fs=1+I²-Q` is zero, one, or two modulo four, so it cannot be -1.
An integer product equal to one therefore has all four factors equal to
one. This argument does not require q or U to be even; no parity
restriction on the new j coordinate is needed.

**Soundness.** The two carrier equations, the authentic mask bounds,
`J=1 (mod 3)` and `beta=1 (mod 3)` yield all the early conclusions in
the [ordinary twelve-variable proof](README.md#early-recovery-no-strong-or-auxiliary-equation-is-assumed):

```text
C>0, q³|Y, q-1|Bt, 3q<R<q⁴-2,
gcd(q,H)=1, Dstar>0, q⁴|(k-R-1),
c=psi_(a+2)(p), k=2 psi_(2XY²+1)(m1),
m1>=(R+1)/2>=24, p>m1,
c>(a+2)Delta², c>2p, c>2R.
```

None uses the strong or auxiliary equation. They do not require q to be
even: the early q-adic divisibility uses `q³|Y` and `gcd(q,H)=1`.
The local strong equation gives `Q=I²>0`, so `f>=2`. Consequently V>1
and the supplied y=V+u is positive. The ordinary strong-rank theorem and
signed auxiliary-index theorem apply exactly as in the twelve-variable
proof, yielding p=R, `q|X`, and the deleted source gaps and quotients.
No rational elimination is necessary here because f,i,y are already
integral supplied/reconstructed coordinates.

In particular `c²|f²-1`, so the two extra coordinates in compact44's
literal seven-equation source kernel are

```text
o=f(cT-R)>0, j_source=(V+R)/c>0.
```

They are integral and satisfy `of-c=V=j_source c-R`. Its shifted
transport coordinate is `z=[(K0+X/q)C-F]/(q-1)>0`; the old convention
is z_old=z+1. Thus the same ordinary whole-tuple compiler/calibration
theorem yields a finite syntactic ZFC refutation.

**Completeness.** Use canonical normalized compact44 source witnesses,
with `J=1 (mod 3)`, `J>1`. Take `j=(J-1)/3>0`, retain f and the
positive auxiliary pair, and put `i_ordinary=Delta i_normalized`.
Then I²=Delta(f²-1)=Q, and the auxiliary equation is unchanged.
Use source73's positive adaptive main lift
`gamma=gamma_old-w+(k-R-1)/U`; the two carrier residuals vanish.
All four factors equal one, giving P13=0. This is an existence
equivalence through canonical witnesses, not a pointwise reverse division
of arbitrary i by Delta.

These two directions retain the ordinary inherited native/compiler
interpretation. They neither certify it anew nor supply an encoded
internal-ZFC biconditional.

**Exact degree.** With `q0=3 beta j`, `k0=eta+zeta`,
`R0=q0³(q0-F)` and `Bt0=(K0q0+X)(q0-F-alpha)-q0F`, the four factor
leaders have degrees15,13,13,10:

```text
L0=-2q0⁸k0²XY²Bt0,
L1=8q0²k0X²Y⁴(q0²Y gamma+R0),
La=2X²Y²f⁴uR0,
Ls=i²k0⁴Y⁴.
```

The degree51 leader is their product. Its monomial
`j¹⁵ F eta⁷ X⁶ Y¹³ f⁴ i² u gamma alpha` has coefficient
`-32(3beta)^15`, which is nonzero independently of K0,MC,MF. Hence
the degree remains51 at the actual fixed tuple.

Run `python3 build13.py`, `python3 check13.py`, and
`python3 -O check13.py` with SymPy available. The independent checker
imports no builder, compares the complete adaptive carrier prefix with
the earlier checked literal, verifies all640 unit-residue cases,
topology/liveness/counts, the selected homogeneous coefficient, a complete
univariate degree specialization and160 independent new-factor evaluations.
Normal and optimized receipts are [CHECKS13.json](CHECKS13.json) and
[CHECKS13_OPTIMIZED.json](CHECKS13_OPTIMIZED.json).
