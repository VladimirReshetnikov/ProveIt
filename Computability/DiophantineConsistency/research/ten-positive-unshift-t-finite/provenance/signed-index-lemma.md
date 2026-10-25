# Signed auxiliary-index recovery and canonical completeness

This note records the exact coefficient-independent Pell lemmas used by the
new thirteen-positive-variable construction. The statements are extracted
from, and proved by the arguments in, the pinned ProveIt sources listed
below. They require no machine/compiler theorem and no assumption about
ZFC consistency. All source paths refer to repository revision
`beb0192cb8dc36f78c369c080f2adfbc1887a486`.

## 1. Pell notation

For an integer `A>=2`, put `Delta=A^2-1` and define integer sequences by

```
chi_A(0)=1, chi_A(1)=A,
psi_A(0)=0, psi_A(1)=1,
z(n+2)=2A*z(n+1)-z(n).
```

Equivalently,
`chi_A(n)+psi_A(n)*sqrt(Delta)=(A+sqrt(Delta))^n`.
We use positive-solution classification for `x^2-Delta*y^2=1`, the
addition formulas, and strong divisibility
`gcd(psi_A(r),psi_A(s))=psi_A(gcd(r,s))`.
The fundamental positive integer-coordinate solution is `(A,1)`:
every positive ordinate has abscissa at least `A`, and `(A,1)` occurs.
These facts are the ordinary Pell dependencies, explicitly collected in
the [inherited Pell audit][audit].

## 2. Signed abscissa step-down

**Lemma.** Let `A>=2`, `m>=1`, and `0<r<m`. If `t>=0` and

```
chi_A(t) = chi_A(r) (mod chi_A(m)),
```

then `t=+r` or `-r (mod 2m)`.

**Proof.** Write `F=chi_A(m)`. The addition formulas and
`chi_A(2m)=2F^2-1`, `psi_A(2m)=2F*psi_A(m)` give

```
chi_A(j+2m) = -chi_A(j) (mod F),
chi_A(2m-j) = -chi_A(j) (mod F).
```

Reducing `t` modulo `2m` and reflecting an index above `m` gives a signed
representative `epsilon*chi_A(s)`, where `0<=s<=m` and `epsilon=+/-1`.
The case `s=m` has residue zero, whereas `0<chi_A(r)<F`. If `s<m` and
`epsilon=-1`, congruence would require
`F | chi_A(s)+chi_A(r)`, although

```
0 < chi_A(s)+chi_A(r) <= 2chi_A(m-1) < F.
```

The last inequality follows directly from the recurrence for `A>=2`.
Thus `epsilon=+1`. Both `chi_A(s)` and `chi_A(r)` lie strictly between
zero and `F`; equality of residues is equality of integers, so strict
growth gives `s=r`. The reduction and reflection change the index only by
multiples of `2m` and by sign, proving the claim. This is the explicit
signed step-down proof in [the ordinary kernel, Section 5][ordinary];
[package 38, Section 5][eleven] repeats it in the normalized setting.

## 3. The exact signed auxiliary-index interface

**Lemma.** Let `A>=2`, `Delta=A^2-1`, and let `p,m,R,c,f,M` be positive
integers satisfying

```
c=psi_A(p), f=chi_A(m),
c|m, m>2p,
M>=2, c|M, M^2=Delta*(f^2-1),
0<p<c/2, 0<R<c/2.
```

If integers `V,y` satisfy

```
M^2 V^2-(M^2-1)y^2=1,
V=-c (mod f),
V=-R (mod c),
```

then `p=R`. The signs of `V` and `y` are unrestricted.
If a norm construction recovers a signed strong root `f_signed`, use
`f=|f_signed|`: its square is unchanged and congruence modulo `f_signed`
is the same congruence modulo `f`. Thus the lemma also covers that
signed-root branch without changing the supplied witnesses.

**Proof.** The equation excludes `V=0` and `y=0`. Positive Pell
classification at parameter `M` supplies `ell>=1` with

```
M*|V|=chi_M(ell), |y|=psi_M(ell).
```

For even indices, `chi_M(2v)=(-1)^v (mod M)`, so `ell` is odd. Write
`ell=2v+1`. The integer polynomial `Q_v` defined by
`chi_Z(2v+1)=Z*Q_v(Z^2)` satisfies

```
Q_v(1-A^2)=(-1)^v psi_A(2v+1),
Q_v(0)=(-1)^v(2v+1).
```

For verification, `Q_0(x)=1`, `Q_1(x)=4x-3`, and
`Q_(v+1)(x)=(4x-2)Q_v(x)-Q_(v-1)(x)`. Substituting `x=0` or
`x=1-A^2` proves the two evaluations by induction.

Now `|V|=Q_v(M^2)`. Since `M^2=1-A^2 (mod f)` and `V=-c (mod f)`,
we obtain `psi_A(ell)=+c` or `-c (mod f)`. Squaring and using
`chi_A(2j)=1+2Delta*psi_A(j)^2` gives

```
chi_A(2ell)=chi_A(2p) (mod chi_A(m)).
```

The preceding lemma applies because `0<2p<m`. Hence
`ell=+p` or `-p (mod m)`, and therefore modulo `c`.
On the other hand, `c|M` gives `M^2=0 (mod c)`; the second polynomial
evaluation and `V=-R (mod c)` give `ell=+R` or `-R (mod c)`.
Combining yields `p=+R` or `-R (mod c)`. The strict bounds
`0<p,R<c/2` exclude a negative identification and every nonzero multiple
of `c`, so `p=R`.

This is precisely the signed implication proved in [the ordinary kernel,
Section 5][ordinary], with `M` in place of that source's ordinary strong
coordinate `I`. The proof uses only the displayed hypotheses. In
particular, it needs no positivity restoration for `V`, no lower bound
`c>A*Delta^2`, no deleted index quotient, and no information about `q`,
`X`, `h`, or the main-root congruence. Excluding `V=+/-1` separately in
the new thirteen-variable proof is valid but is unnecessary for this
lemma: the argument above already covers every integer branch.

## 4. Why the new normalized strong equation supplies its hypotheses

Suppose `c=psi_A(p)>2`, `f,I>0`,

```
f^2-Delta I^2=1, c^2|I.
```

Pell classification yields `f=chi_A(m)` and `I=psi_A(m)` for an integer
`m>=1`. Strong divisibility and `c|I` give `p|m`; write `m=pv`.
If `D=chi_A(p)`, the composition identity is

```
I=c psi_D(v).
```

Since `D^2=1 (mod c)`, its recurrence gives
`psi_D(v)=v D^(v-1) (mod c)`. As `D` is invertible modulo `c` and
`c^2|I`, this implies `c|v`. Therefore

```
p*c|m, c|m, m>=pc>2p.
```

Putting `M=Delta I` gives `M^2=Delta(f^2-1)` and `c|M`. This is the
direct normalized argument in [package 57, Section 5][lowdegree],
[package 38, Section 5][eleven], and [the inherited audit, Section 3.1][audit].
It is distinct from the older ordinary-strong rank lemma, whose extra
large-`c` hypothesis must not be imported into the new proof prematurely.

For the proposed thirteen-variable polynomial, `I=ic^2` and its strong
residual is exactly this normalized equation. The carrier and first-Pell
arguments already establish `c>2R`, while Pell growth establishes `c>2p`.
The auxiliary register is `V=f^2(cT-R)-c`; thus `V=-c (mod f)` and
`V=-R (mod c)`, the latter using `f^2=1 (mod c)`. Its auxiliary residual
supplies the lemma's equation with `y=|V+u|`. Consequently every hypothesis
is present before concluding `p=R`. There is no additional unproved
auxiliary-index implication at this boundary.

## 5. Explicit positive auxiliary reconstruction for completeness

**Lemma.** Let `A>=2`, `Delta=A^2-1`, `R>=3` with `R=3 (mod 4)`, and
`c=psi_A(R)`. Suppose positive integers `f,I` satisfy

```
f^2-Delta I^2=1, c|I.
```

Put `M=Delta I`. Then there exist positive integers `T,u` such that, with
`V=f^2(cT-R)-c`,

```
M^2 V^2-(M^2-1)(V+u)^2=1.
```

**Proof and explicit construction.** Write `R=2v+1`; now `v` is odd.
Define

```
V*=chi_M(R)/M=Q_v(M^2),
y*=psi_M(R).
```

These are positive integers. The Pell identity gives
`M^2 V*^2-(M^2-1)y*^2=1`. Since
`M^2=Delta(f^2-1)=1-A^2 (mod f^2)` and `c|M`, the same polynomial
identities give

```
V*=-c (mod f^2), V*=-R (mod c).
```

The normalized strong equation gives `f^2=1 (mod c)`, so
`gcd(c,f^2)=1`. Hence

```
T=(V*+c+Rf^2)/(cf^2)
```

is a positive integer and `f^2(cT-R)-c=V*`. Also `R>=3` and `M>=2`
give `V*>=4M^2-3>1`. Rearranging the Pell identity yields

```
y*^2-V*^2=(V*^2-1)/(M^2-1)>0.
```

Thus `u=y*-V*` is a positive integer, completing the construction.
This is [source 58, Section 6.4][integral], or the more general
[squared-modulus reconstruction, source 51][squared], with `M=Delta I`
in place of the ordinary strong square root. It requires no assumption
that an arbitrary old quotient is divisible by `f`, and no auxiliary
cofinality hypothesis.

## 6. Remaining source boundary and completeness audit

The three elementary arguments above make the new rank and auxiliary
reconstruction steps explicit. They do not themselves prove the native
compiler or the K215 calibration. The overall equivalence still composes
with the complete authentic compact tuple and its native-window theorem
from [source 44][native], together with the ordinary source kernel and
the finite-refutation calibration named there.

For completeness of the new thirteen-variable equation, the source
provides **canonical**, rather than arbitrary, positive witnesses. The
specific additional promises needed are:

* `B=2^590069`, `q=B^N`, and `J=1+B+...+B^(N-1)` with
  `N=581197^n>1` odd. Source 44, Section 6 establishes the actual-rank
  controller and odd canonical dimensions. Therefore `J=1 (mod 3)` and
  `j=(J-1)/3>0`.
* `R=3 (mod 4)` and `c=psi_(a+2)(R)`. These concern the whole compact
  tuple and its canonical masks; they are not assumptions on independent
  arbitrary coefficient ports. Source 44, Section 6 and source 58,
  Section 4 record them.
* `X=2^R`, the first index `n0=(R+1)/2>=3`, and
  `k=2psi_(2XY^2+1)(n0)`. The inherited kernel provides these canonical
  conclusions. They imply `w=X/q>q` from `R>3q`, and source 58,
  Section 6.3 proves the stronger root margin `gamma_old>X>=w`.

The new proof uses these promises correctly. Its old transport identity
gives `z_old>=2`, so `t=q(z_old-1)>=q`. With `tau>ell` and `k>s`,
the new gap obeys

```
r=Wt+tau-ell-k-s > qW-k-s >0,
W=(q-1)k+1.
```

The first-Pell congruence makes `r0=k-R-1` a positive multiple of
`4XY^2`, hence of `q^5`. Thus
`gamma=gamma_old-w+r0/q^5` is a positive integer. The preceding explicit
auxiliary construction gives positive `T,u` while leaving both carriers
untouched. All retained supplied coordinates are already positive.

**Audit conclusion:** the inherited results already supply every needed
implication at the signed-index and canonical-completeness boundaries;
the new reduction does not require an additional conjectural Pell theorem.
The mathematical composition is an ordinary proof formalizable in ZFC.
The collected sources and this review do not claim a newly compiled
end-to-end Lean/Rocq proof or an object-language derivation file.

## Pinned references

[ordinary]: https://github.com/VladimirReshetnikov/ProveIt/blob/beb0192cb8dc36f78c369c080f2adfbc1887a486/Computability/DiophantineConsistency/con-zfc-diophantine-forms/35-cancel12/sources/catalogue/25-hybrid12/upstream/ORDINARY_BLANK_PROOF.md
[eleven]: https://github.com/VladimirReshetnikov/ProveIt/blob/beb0192cb8dc36f78c369c080f2adfbc1887a486/Computability/DiophantineConsistency/con-zfc-diophantine-forms/38-batching11/eleven/ELEVEN_POSITIVE_PROOF.md
[lowdegree]: https://github.com/VladimirReshetnikov/ProveIt/blob/beb0192cb8dc36f78c369c080f2adfbc1887a486/Computability/DiophantineConsistency/con-zfc-diophantine-forms/57-separated-degrees/low_degree/PROOF.md
[audit]: https://github.com/VladimirReshetnikov/ProveIt/blob/beb0192cb8dc36f78c369c080f2adfbc1887a486/Computability/DiophantineConsistency/con-zfc-diophantine-forms/36-small-tuple/proofs/INHERITED_PELL_AUDIT.md
[integral]: https://github.com/VladimirReshetnikov/ProveIt/blob/beb0192cb8dc36f78c369c080f2adfbc1887a486/Computability/DiophantineConsistency/con-zfc-diophantine-forms/58-integral-root/report/report.tex
[squared]: https://github.com/VladimirReshetnikov/ProveIt/blob/beb0192cb8dc36f78c369c080f2adfbc1887a486/Computability/DiophantineConsistency/con-zfc-diophantine-forms/51-sparse-arith/short/SQUARED_MODULUS_PROOF.md
[native]: https://github.com/VladimirReshetnikov/ProveIt/blob/beb0192cb8dc36f78c369c080f2adfbc1887a486/Computability/DiophantineConsistency/con-zfc-diophantine-forms/44-b4-sparse/native/PROOF.md
