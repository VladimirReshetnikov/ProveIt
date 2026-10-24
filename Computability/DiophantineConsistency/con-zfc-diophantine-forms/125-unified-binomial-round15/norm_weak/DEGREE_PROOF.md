# Weak-Y split-carrier norm: exact degree and cost

This is a separately audited degree/cost tradeoff, not a replacement of the frozen cheaper norm pair. The two graphs use eleven unrestricted integer variables and the same six fully bound authentic ports. The centered graph has exact degree416 and125 live binary operations (79 multiplications,24 additions,22 subtractions); its direct sibling has degree456 and124 operations (79,23,22).

## Definitions and identity boundary

Retain the complete ordinary prefix and weighted guard of the frozen construction, but use Y=qv. Put M=2q^2, Dc=HM, M2=M^2, M4=M2^2 and

S=sr Dc M4=srH M^5,
zc=Dc T+MK+H(v−q^2),
Ac=(zc^2+3Dc^2)(zc^3−19Dc^3).

All quantities are polynomial abbreviations, not extra variables. The polynomial remains the full eight-conjugate norm

[(Z^2+A−B−G)^2−4(AZ^2+BG)]^2−64(AZ^2)(BG),

where A=9S^2Df, B=S^2delta Cy, G=81S^2P, and Z=S(n+QV)−Ac (centered) or Sn−Ac (direct). Its literal guard schedule is D81=243Budget−324, Dg81=81+D81Dt s^2, P81=DtDg81, G=S^2P81. The full polynomial identity Dg81=81Dg is checked.

The separate semantic proof must recover M|(v−q^2) from the carrier BEFORE assuming the old cubic-Y size bounds, c≠0 or adjacent-Pell descent. This norm note does not silently inherit those assertions before that step. See the accompanying weak-Y semantic proof for the exact quantifier order.

## Highest homogeneous parts

All degrees count only the eleven variables; every authentic coefficient is fixed. Write

q0=6beta j, X0=12wq0, Y0=q0v, a0=X0Y0,
F0=12wC−q0z, R0=−q0^3F0, k0=R0+h a0,
I0=rc^2, S0=128sr a0 q0^10.

The two terms of k0 both have degree5; neither may be discarded in the complete top homogeneous form. The exact degrees are

I3, S16, Df14, Q22, V19, Cy60, delta Cy82,
Dt22, Dg40, P62, Ac35, A46, B114, G94.

The leading forms relevant to the norm are

V0=−a0^2 I0^2 R0,
B0=2^14 s^2r^10c^16 a0^14 q0^26 F0^2,
G0=−2^16 3^5 s^4r^2 a0^6 q0^22 Y0^6 k0^6,
Ac0=(8a0 q0^2T)^5.

All are nonzero over the authentic coefficient tuple.

## Exact degree416 after centering

Set W=Sn−Ac. The universal polynomial identity is

Z^2−B=W^2+2SQVW+S^2[Q(V^2+1)−1].

The displayed degrees are70,92,92. Thus the expression has degree at most92. In fact its degree-92 part is −2S0Q0V0Ac0+S0^2Q0V0^2. The two summands have different C degrees,1 and2, so this part is nonzero.

Since G has degree94 and A degree46, the paired norm's v=Z^2+A−B−G has unique top form −G0. In the inner bracket v^2−4(AZ^2+BG), the degrees are188,160 and208, respectively. Hence its top form is −4B0G0. The final correction64(AZ^2)(BG) has degree368, strictly below416. The complete highest homogeneous form of the final polynomial therefore is

16B0^2G0^2
=2^64 3^10 s^12r^24c^32 a0^40 q0^96 Y0^12 k0^12 F0^4.

Taking the maximal-C term in k0^12 and F0^4 gives an attained monomial

j^224 w^56 v^52 C^16 s^12 r^24 c^32

with exact coefficient2^400 3^290 beta^224>0. Its total degree is416. Another endpoint, choosing the h^12 branch, is

j^212 w^56 v^64 h^12 s^12 r^24 c^32 C^4

with coefficient2^388 3^278 beta^212>0.

Thus the claimed degree is a universal upper bound with an explicit nonzero authentic integer coefficient, not a sampled-ray claim.

## Direct sibling: degree456

Without the integral shear, deg Z=35. In Z^2+A−B−G the unique top form is −B0 (degree114). Its square dominates BG (degree208) and AZ^2 (degree116), so the final output has whole top form B0^4 and degree456. The final correction has degree324.

The monomial j^216 w^64 v^56 C^8 s^8 r^40 c^64 has coefficient2^400 3^280 beta^216>0.

## Checks and arithmetic cost

`check_norm.py` checks all35 coefficients of the free triquadratic product, the paired/symmetric identity, the center identity, the weighted-guard identity, full six-payload byte bindings, graph topology, and exact leading degrees at every actual DAG node with the proved center cancellation substituted at its identified node. Both normal and python-O runs pass. The independent skeptic checks the complete prefix against a separate transcription and exercises corrupted-graph controls.

The generator uses only owned local arithmetic-DAG code. Every binary scalar multiplication and square is charged; reuse and leaves are free. The two candidate files and full payloads are identified by the accompanying release manifest. Frozen lower-cost graphs in `../norm/` are unchanged.
