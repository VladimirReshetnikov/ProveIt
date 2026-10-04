# Native masks on the dyadic W=0 branch of shared-projection83

Fix the actual modified universal-compiler numerals and a positive zero of the unchanged shared-projection83 candidate. If q is dyadic and W=0, then

```
popcount(R)=3 log2(q)+2,
(Z−1) AND (MC*J+1)=0,
F AND (MF0*J−1)=0.
```

Here MF0 is the native field mask; the actual source's fixed `MF` port is MF0+B−1. Thus Z is native typed and contains the origin Start bit, while C=Z has no End bit. This result does **not** identify the supplied field with the old one-rotation field, recover a genuine computation, or prove ordinary-input soundness. The unchanged source remains a candidate of83=46M+37A operations and18 positive witnesses; no new universal bound follows.

The proof first confines any binomial cancellation escape to a maximally filled periodic word, then uses the actual transport constants to exclude that escape. The final periodic-word transport argument was jointly developed in this research turn. All predecessor code is read only as bytes/JSON.

## 1. Exact premises and the population ceiling

Use the accepted offset theorem and even-radix boundary. The literal source retains

```
q=(B−1)J+1, X=wq, Y=sq^3,
C=q−F−Z−alpha−2dx, W=C−Z,
u=2dx+b,
R=(q^2−Z−qF)(q^2−1)+(MC+q(MF0+B−1))J,
(K+w)C+q−F−transport_quotient*(q−1)=1,
K=DC+B*DR.
```

The four variable outer quantities J,F,Z,alpha, the ordinary input x, and every witness keep their strict-positive domain. The accepted pretyping and offset facts are

```
C>0, F+Z<q, |W|<q, q>=16,
R=3 mod4, R>3q+1, R+2<q^4,
0<u<2q<R,
X−W=2^R−2^u,
r=(R−1)/2 odd, Y=M_r(X)/2,
M_r(X)=sum_(j=0)^r binom(2r,r+j)X^j.
```

For the exact half-binomial identity, the even-radix proof establishes X>2^(R−1), a lower binomial tail less than1/2, and a strict Pell error less than1/2 before any mask typing. No equality X=2^R is used here.

Assume q=2^t. The repunit equation and B=2^d imply d|t, so q=B^N and t=dN for a positive integer N. Since W=0, divisibility of X=2^R−2^u by q and R>t imply u>=t. The actual layout has

```
V0=2^b>=32, B=V0^L, d=bL, 0<b<d,
b>=5, u−t=d(2x−N)+b>=b.                              (1)
```

Indeed 2x−N is integral, and a negative value would make u−t<0. The bound b>=5 follows from the compiler's power-of-five choice of b and V0>=16.

Write

```
S'=(Z−1)+qF,
T_C=MC*J+1, T_F=MF0*J−1, T'=T_C+qT_F.
```

The positive raw bound gives 1<=S'<q^2. The fixed modified masks, before any claim that Z or F is typed, give 0<T'<q^2−1 and popcount(T')=t+2. The actual index is

```
R=(q^2−S')(q^2−1)+T'.
```

The inverse-population lemma of modified75 §2 therefore yields

```
popcount(R)<=3t+2,                                    (2)
```

with equality exactly when S' AND T'=0. Put p=popcount(r). Since R=2r+1, (2) says p<=3t+1. It remains to exclude p<3t+1.

## 2. Every low-population escape has v2(r+1)=u

Let h=3t+1 and C_j=binom(2r,r+j). The even-radix theorem gives the exact cubed-scale congruence. Since X=2^R−2^u and R>h,

```
C_0−2^u C_1+2^(2u) C_2−2^(3u) C_3 =0 mod2^h.         (3)
```

Every j>=4 term vanishes modulo2^h because u>=t+b. Define

```
k2=v2(r+1), l2=v2(r+3), h2=v2(r−1).
```

The central-binomial identity and adjacent coefficient ratios give

```
v2(C_0)=p,
v2(C_1)=p−k2,
v2(C_2)=p+h2−k2,
v2(C_3)=p+h2−k2−l2.                                  (4)
```

Suppose p<h, hence p<=3t. If k2=1, then h2>=2 and l2>=2. The last l2 binary digits of r are those of 2^l2−3, which have l2−1 set bits, so l2<=p+1. The weighted third term consequently has valuation

```
p+h2−1−l2+3u >=3u>p.
```

The weighted first and second terms also have valuation greater than p. The central term is uniquely least, and (3) is impossible.

If k2>=2, then h2=l2=1. The four weighted valuations become

```
p,  p+u−k2,  p+2u+1−k2,  p+3u−k2.                   (5)
```

When k2<u the central term is uniquely least and has valuation p<h. When k2>u the first weighted term is uniquely least, with valuation p+u−k2<p<h. In either case (3) again fails. Therefore any hypothetical low-population zero must satisfy

```
k2=u.                                                (6)
```

This argument permits arbitrary cancellation in the tied case (6); it does not silently assume a central valuation there.

## 3. The exception forces a repeated maximal word

Set Dmask=B−1−MC. The actual fixed layout gives

```
Dmask=sum_(e in E,e!=1) V0^e+2 V0^e_*.
```

Its permitted digits are1 at the ordinary allowed native positions,3 at the ignored dummy e_*,0 at End position1, and0 elsewhere. In particular 0<Dmask<B−1. This is a fixed numeral, not an assumed bound on an untyped variable.

Reducing the literal packed index modulo q gives

```
R=Z+MC*J=Z−Dmask*J−1 modq.                            (7)
```

Under (6), R+1=2(r+1) is divisible by2^(u+1), hence by q. Since both Z and Dmask*J lie strictly between0 and q, (7) forces

```
Z=C=Dmask*J.                                         (8)
```

The unchanged transport equation now implies J|F. Write F=fcell*J. The raw source slack gives

```
(B−1−fcell−2Dmask)J+1=alpha+2dx>1,
```

so

```
1<=fcell,  fcell+2Dmask<B−1,  fcell<B−1.               (9)
```

Cancelling J from the integer transport congruence yields

```
fcell=(K+w)Dmask mod(B−1).
```

Since q=B^N=1 mod(B−1), wq=X implies w=X mod(B−1). Also u=2dx+b, so 2^u=V0 mod(B−1), and the actual K=DC+B*DR reduces to DC+DR. Consequently

```
fcell=(DC+DR+2^R−V0)Dmask mod(B−1).                   (10)
```

This deduction uses no native assumption on F and no temporal alignment.

One more exact expansion will be useful. Substituting (8), MC*J=q−1−Z and F=fcell*J into the packed index gives

```
R+1=q*[q^3−q^2F−qZ+(fcell+MF0)J].                   (11)
```

Equations (1) and (6) imply that the bracket is divisible by2^(u+1−t), in particular by V0. The first three terms inside it are divisible by V0, and J is odd. Thus

```
fcell+MF0=0 modV0.                                   (12)
```

Every term of the baseline complete78 field mask has strictly positive V0-exponent. Complete76 leaves those tested positions unchanged, and modified75 adds precisely4. Therefore the actual native mask satisfies MF0=4 modV0, not merely4 mod8. Equation (12) forces

```
fcell=V0−4 modV0.                                    (13)
```

## 4. The actual positive field has a different low digit

Let Yrot be the least nonnegative residue of 2^R Dmask modulo B−1. It is an ordinary cyclic binary rotation of the fixed d-bit word Dmask. No supplied field or variable selector is being typed in this definition.

Apply the actual modified compiler's coefficient bound to the repeated native cell Dmask. The one-cell spatial rotation of a repeated cell is itself, so the unshifted coefficient string is

```
G=(DC+DR)Dmask.
```

Modified75 §4 applies to arbitrary permitted native digits before selector consistency or synchronization. It bounds each raw V0-coefficient of G by V0/4−2. Its degree is below L, including the optional high monomial in DC: complete76 chose L beyond that monomial plus every native exponent. Thus G is its actual nonnegative digit expansion with no hidden reduction modulo B−1.

Write the bit-rotation exponent modulo d as bs+ell, 0<=ell<b. For ell<=b−2 every digit of Yrot is at most3*2^ell<=3V0/4. For ell=b−1 a low native bit contributes V0/2, and the sole additional dummy bit can contribute one unit from the preceding position, so every digit is at most V0/2+1. These are the same elementary rotation bounds used in modified75 §4; they need no consistency of the native selectors.

Consequently

```
Tplus=G+Yrot
```

has all V0-digits at most V0−2, no carries, and degree below L. Hence 0<Tplus<B−1. Define

```
Tactual=Tplus−V0*Dmask.
```

The actual numeral DR=V0^Hlayout has Hlayout>1, so DR>V0 and

```
Tactual=(DC+DR−V0)Dmask+Yrot>0.
```

Also Tactual<Tplus<B−1. Its residue is exactly the right-hand side of (10). Together with (9), uniqueness of the representative between0 and B−1 gives

```
fcell=Tactual.                                       (14)
```

This step does not assert that subtraction creates no inner-radix borrows; it only uses the exact integer bounds and congruence. The possible borrows do not affect reduction modulo V0.

Both DC and DR are divisible by V0, since their minimum exponents are positive. Reducing (14) modulo V0 therefore shows that the unit digit of fcell equals the unit digit of Yrot. But every rotated digit is at most

```
max(3V0/4,V0/2+1)=3V0/4<V0−4,                         (15)
```

where strictness uses V0>=32. This contradicts (13). The tied binomial case (6) is impossible on the actual compiler slice.

## 5. Recovered masks and the remaining arithmetic boundary

All possibilities with p<3t+1 have now been excluded. From (2), p=3t+1 and popcount(R)=3t+2. Equality in the inverse-population lemma gives both claimed AND conditions.

The low mask makes Z−1 a subword of the complement of MC*J+1; adding back1 inserts exactly the origin Start bit. Thus Z is native typed in the modified sense, with the ignored dummy digit allowed to range from0 through3. Its End bit is absent in every cell. Since W=0, C=Z also has no End bit.

This numerical typing is not yet a contradiction. On this branch the transport multiplier obeys

```
w=2^R−2^u mod(q−1),
```

which is a difference of two rotations. The old soundness proof identifies a positive one-rotation field, proves its alignment with clean bands and anchor parity, and only then invokes the marker-bijection argument. Those steps have not been proved for the two-rotation difference. In particular one cannot simply combine “Start present” and “End absent” with that old conclusion. Ordinary-input soundness in this remaining typed sector stays open.

## 6. Evidence and dependency scope

The fresh companion authenticates the eight explicit predecessor pins in its source, reads the full83-row receipt as inert data, checks its source ordering/ledger and21 literal interface rows, and evaluates no inherited DAG. It tests the unique-minimum valuation dichotomy against exact small binomial coefficients and wider exponent families. Its generic finite rotation examples check digit bounds, exact positive transport representatives and the low-digit contradiction under the stated scalar hypotheses. The receipt records17,497 exact nonexception binomial cases, three tied shapes,21,317 wider exponent cases and8,652 synthetic rotation/transport cases. Those synthetic coefficient strings are explicitly not asserted to be outputs of the universal compiler. No new compiler, complete zero tuple or huge Pell coordinate is generated.

The proof dependencies actually read are the accepted shared-projection offset note; the whole even-radix and dyadic negative-offset notes; modified75 §§1–4 for masks, scalar coefficients and rotation bounds; complete76 §1 for the optional high monomial and the enlarged degree bound; complete78 §§2–3 for the explicit DC,DR,MF strings and native coefficient estimates; and complete86 transport-shear §1 for the exact fixed K/source convention. The old compiler's machine semantics are not re-audited here. All code associated with these dependencies is inert.

No source change, new witness, free evaluation, operation reduction or claimed universal83 theorem is part of this packet.

Fresh normal and optimized Python (`-O`) exact receipt replays from `/` both pass. Frozen companion hashes:

* PY `4ea248a62a3866c2b30a51ba282fda198e2663b323eae0eb384bd77714eaeaeb`.
* JSON `f094621d6314b1297c5317398c5dbac2de3980a57b039f0db1aa8f6187860469`.

The new helper accepts `--root` pointing to native-stream-queue and exactly one of `--output` or `--expect`; output creation is exclusive. Neither mode runs any predecessor program.
