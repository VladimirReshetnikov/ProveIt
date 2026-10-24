# Nonzero square scaling of sign guards: twenty integers at degree eighteen

## Result and precise scope

The packet `equation.json` defines one polynomial in twenty unrestricted
integer unknowns, of exact degree 18. Its literal shared circuit has 115
live binary operations (57 multiplications, 30 additions, 28 subtractions).
It has an integer zero exactly when the retained `joint22-centered` parent
has an integer zero. Consequently, composition with that parent's stated
ordinary native/Pell/K215 calibration proves, in ordinary mathematics
formalizable in ZFC, that the absence of zeros is equivalent to Con(ZFC).

This is a degree/circuit-size tradeoff against the incoming 20-integer,
degree-20, 111-operation transport projection: degree decreases by 10%,
at the cost of four operations. It does not improve the fewer-variable
frontiers, and it is not a global simplicity or external-priority claim.

The exact comparison source is ProveIt `43ac596e36c105a0e8b07c2d1f5ae200cae9c056`,
including its incoming archives. The immediate parent was already present
at `bf2f392d73eb2ed74bd51cfdb509ecb704d04eb3` and is retained verbatim under
`parent/`. Its equation SHA256 is
`53a82b6b385f254f7e8f2a04ed800fa33c7a9ac92bc0940a63742e8a199a1a7c`.

The distinctive step is to replace a sign quantity by its product with an
already provably nonzero square **before eliminating arithmetic coordinates**.
This preserves the positivity predicate while allowing the c equation to
lower the polynomial degree. It is an existence equivalence; the four
private guard coordinates need to be regenerated, so it is not a claimed
polynomial isomorphism of all zero sets.

## The complete equation

The unknowns, all in Z, are

```
J3,C,z,f,h,r,v_scale,w3,tau,eta,y,gamma,o,j,c,b,
pair_root,pair_pos1,pair_pos2,pair_pos3.
```

The fixed coefficient tuple is exactly the parent's source34 six-port tuple:

```
beta=2^1064921-1, K0,MC,MF, cone_A=2^1113, cone_B=2^666104.
```

MF is already shifted. The actual six integers are supplied as the parent's
minimal unsigned little-endian byte strings compressed with gzip. Their
binding records 615883 uncompressed bytes. No port is an unknown, and no
port is selected by a search for a refutation.

Define polynomial abbreviations only:

```
J=3J3+1, q=beta J+1, W=12w3+4, X=qW,
Ytarget=(2v_scale+1)q^3,
F=(K0+W)C-z(q-1), alpha=q-F-C,
E=Xb, a=E+b, V=fo-c, k=1-V+jc+hE,
H=4a+3, Delta=a^2+H, I=(2r+1)c^2,
R=(q(q-F)-C)(q^2-1)+(MC+qMF)J,
d=(cone_A F)(cone_B C)-(q-cone_A F-cone_B C)^2,
tnew=b eta(c-eta-b eta),
Pos=1+pair_pos1^2+pair_pos2^2+pair_pos3(pair_pos3+1),
ell=E(c-eta), p=fo, Q=Delta(f^2-1).
```

Let the eight residuals be

```
B1=b-Ytarget,
B2=c-eta-kb,
B3=tau^2-ell(k+ell)-1,
B4=(X+ac+gamma H)^2-Delta c^2-1,
B5=cj-V-R,
B6=I^2-Q,
B7=I^2[V^2-(p+y)^2]+(p+y)^2-1,
B8=d tnew-(pair_root^2-d-tnew+1)^2-Pos.
```

The ordinary Diophantine equation is

```
P20=B1^2+B2^2+B3^2+B4^2+B5^2+B6^2+B7^2+B8^2=0.
```

All abbreviations are finite polynomial substitutions. There are no hidden
quantifiers, variable exponents, inequalities, or divisions in P20.

## The universal simultaneous-positivity guard

Write

```
Guard(x,y;s,u,v,w)=xy-(s^2-x-y+1)^2-[1+u^2+v^2+w(w+1)].
```

For arbitrary integers x,y,

```
x>0 and y>0  iff  there exist integers s,u,v,w with Guard=0.
```

This is the inherited joint-guard lemma; the following proof makes its use
here self-contained. Pos is always positive. Thus Guard=0 forces xy>0.
If both x,y were negative, then
`s^2-x-y+1>|x|+|y|`, whose square exceeds xy, a contradiction. Therefore
both are positive. Conversely, put N=x+y-1>0. Choose an integer s whose
square is closest to N. Elementary comparison of consecutive squares gives
`(s^2-N)^2<N`. Also `N<=xy`, since `(x-1)(y-1)>=0`. Therefore
`xy-(s^2-N)^2` is a positive integer.

Every positive integer n is a Pos value. Indeed 4n-3 is positive and is 1
modulo 4, so it is not of the forbidden three-square form 4^a(8b+7).
Legendre's theorem supplies a representation by three squares, one odd and
two even. Writing them as `(2w+1)^2,(2u)^2,(2v)^2` and dividing by four
gives the asserted Pos representation. This establishes the converse.

## Why the sign rescaling is sound

On B1=0, b is nonzero. The factor 2v_scale+1 is an odd integer and cannot
be zero. Also q=beta J+1 cannot vanish for any integer J because beta>1:
otherwise beta would divide 1. Hence b=(2v_scale+1)q^3 is nonzero on every
integer zero, without any previously recovered positive sign.

Let `told=eta(k-eta)`. The following exact identity holds for all integer
assignments, even away from the zero set:

```
tnew-b^2 told = b eta(c-eta-kb) = b eta B2.
```

Consequently, on B2=0, `tnew=b^2 told`. Since b is nonzero, tnew>0 is
equivalent to told>0. The new guard is therefore equivalent, after
existentially quantifying its private four coordinates, to the parent's
guard on d,told. No sign assumption on b is needed. In particular, this
argument does not rely on the later signed Pell recovery to justify an
earlier sign constraint.

The coefficient support is reduced because tnew is a degree-four
polynomial in the retained coordinates. Directly inserting
`k=1-fo+c(j+1)+hXb` into told would give degree five; its square inside the
guard would raise that residual to degree ten. The scaled expression
avoids that growth while imposing exactly the same strict sign condition.

## Complete connection to the retained parent

The parent has 22 coordinates and ten residuals, explicitly printed in
`parent/PROOF.md` and literally specified in `parent/equation.json`.
Its coordinates include a,E,F,alpha, and its centered auxiliary y is the
same coordinate used here.

First change the pair (a,E) to (b,E), where b=a-E. The first parent row
becomes b-Ytarget; the second becomes E-Xb. Eliminate the monic second
row by E=Xb and restore a=E+b. This removes one coordinate and one row.

Second, change (F,alpha) to (F,C), with C=q-F-alpha. The transport row is
monic in F, so restore F=(K0+W)C-z(q-1), then alpha=q-F-C. This removes
another coordinate and another row. The rank expression is exactly

```
((q-1)(q-F)+alpha)(q^2-1)+(MC+qMF)J
 = (q(q-F)-C)(q^2-1)+(MC+qMF)J.
```

The eight surviving arithmetic rows are unchanged except for the auxiliary
row and sign guard. To make the auxiliary row's low degree visible, put

```
D=V^2-(p+y)^2.
```

The old centered auxiliary residual is `Q D+(p+y)^2-1`; the new one is
`I^2 D+(p+y)^2-1`. Their difference is exactly B6*D. Retaining B6
makes this an invertible polynomial row operation.

Number the parent's ten rows from zero. After the polynomial coordinate
restorations, rows 0 through 8 are exactly

```
B1, 0, B2, B3, B4, B5, 0, B6, B7-B6*D.
```

The final parent row is its universal guard on d,told. The final new row
is that same guard on d,tnew, with its four private witnesses regenerated
using the preceding positivity lemma.

**New zero to old zero.** Restore E,a,F,alpha by the displayed integral
polynomials. B1 proves b nonzero and B2 proves tnew=b^2 told. B8 gives
d,tnew>0, hence d,told>0. The positivity lemma supplies four parent guard
coordinates. All nine arithmetic parent rows vanish by the exact list
above. Thus the restored tuple is a parent zero.

**Old zero to new zero.** Set b=a-E and C=q-F-alpha, keep every other
arithmetic coordinate, and discard E,a,F,alpha. The parent first, second,
and transport rows force exactly the required restorations. Their
remaining arithmetic rows make B1,...,B7 zero. The parent's guard gives
d,told>0; b is nonzero by its first row, so tnew=b^2 told>0. The same
positivity lemma supplies four new guard coordinates, making B8 zero.

Both directions preserve all six fixed numerals. This proves existence
equivalence over the full integer domain. The native/Pell/refutation
interpretation is inherited from the retained parent, not established by
the finite algebra checker. Negating the existence equivalence and
composing the parent's calibration yields the claimed Con(ZFC)
biconditional without assuming consistency. No new complete Lean/Rocq or
encoded object-language ZFC derivation is claimed.

## Degree and circuit certificates

The residual degrees are exactly

```
4,5,8,8,5,8,9,8.
```

Only B7 reaches degree nine. Since `V=fo-c`,

```
V^2-(fo+y)^2=-(c+y)(2fo+y-c).
```

The degree-six part of I^2 is `4r^2 c^4`, so the complete degree-nine
part of B7 is `-8r^2 c^4 fo(c+y)`. Therefore the full degree-eighteen
homogeneous component of P20 is exactly

```
64r^4 c^8 f^2 o^2(c+y)^2.
```

For example the coefficient of `r^4 c^8 f^2 o^2 y^2` is 64. It is
independent of every fixed port; actual numerical specialization cannot
cancel it. The exact sparse algebra verifier checks the complete leading
form, not only a syntactic degree propagation or modular sample.

The circuit evaluates the centered auxiliary expression before expanding
the cancellation; this keeps the operation count at 115. A naive gate
degree propagation therefore overestimates the actual degree. The graph
and exact polynomial checks deliberately treat those as distinct claims.
Operations include squaring and multiplication by fixed numerals; fixed
leaves and previously computed registers are free. All 20 variables, all
six fixed ports, and every listed gate are live.

## Reproduction

Run `python3 build.py`, `python3 check.py`, and `python3 -O check.py` from
this directory. Only Python's standard library is needed. The checker
does not import the builder; it interprets the delivered definitions and
circuit, verifies complete literal parent-row identities, the rescaled
sign identity, exact degrees, the homogeneous component, all coefficient
payload hashes, and the sum-of-squares finalizer. The exact sparse ring
engine in `parent_ring.py` is retained verbatim from the parent; its
provenance is explicit and this shared engine is not an independent
algebra implementation. These finite checks support transcription and
algebraic identities. They are not a substitute for the universal sign
proof above or the inherited compiler calibration.
