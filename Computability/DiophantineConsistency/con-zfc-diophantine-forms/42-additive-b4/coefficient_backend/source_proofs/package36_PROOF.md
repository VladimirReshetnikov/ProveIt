# Port-specific labels and a shared anchor: B = 2^1012115

## Result, dependencies, and scope

This construction combines package 25's mixed-radix clauses and short
native geometry with package 24's prime-padding controller. It also removes
two unnecessary horizontal label bits and one redundant source anchor.
The final dimensions and fixed base are

\[
 b=115,\quad L=8801,\quad d=bL=1,012,115,\quad
 \rho=2^{115},\quad B=\rho^{8801}=2^{1,012,115}.
\]

The four exact coefficient ports occupy 506,664 raw bytes in total, compared
with 977,220 for the previous smallest tuple. Their largest bit length is
1,016,946, compared with 1,958,376. The base exponent is 48.18% smaller;
the total raw payload is 48.15% smaller. The coefficients are materialized
integers with a finite recipe, independent of whether K215 halts.

The adapter below is an ordinary mathematical proof, formalizable in ZFC,
relative to the inherited blank-K215 native compiler, Pell arithmetic,
Wang-language theorem, and finite-refutation calibration. It includes the
canonical parity and square/odd-scale promises needed for signed-domain
adapters. No new Lean/Rocq end-to-end certificate is claimed. After
composition with a compatible arithmetic skeleton, the conclusion is the
equivalence of unsolvability with Con(ZFC), not a consistency proof.

The reviewed commit is
`8c6eec9d19ef80538c8e61ff6e0180040583446a`. The source collection is
`SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms`.
The principal inherited arguments are:

* Package 25, `proofs/COEFFICIENT_PROOF.md`: mixed-radix selector decoding,
  compact clause targets, short transport, and external zero-mask bits.
* Package 24, `sections/coefficients.tex`: arbitrary fixed odd dimensions
  and the Boolean coverage argument for actual rank control.
* Package 27, `coefficients/COEFFICIENT_PROOF.md`: full native-interface
  transfer and canonical parity, square-scale, and odd-scale promises.
* Package 27, `coefficients/upstream/compiler/WANG943_COEFFICIENTS.md` and
  `WANG943_COMPACT_LAYOUT.md`: unchanged language semantics and native
  decoding geometry.

Exact reference copies, attribution, and digests are retained in
`source_proofs/`, `licenses/`, and `SOURCES.json`.

## 1. Port-specific occupied label encoding

Use exactly the inherited ordered 943 Wang tiles, in slot order
west, north, east, south. The two horizontal slots have labels at most 249,
so their identifiers fit in eight bits. The vertical slots have labels at
most 438 and need nine identifier bits. Encode occupied labels by

| Slot s | Copy offset o_s | Width l_s | Occupancy addend a_s | First payload field p_s |
|---|---:|---:|---:|---:|
| West | 1023 | 9 | 256 | 0 |
| North | 1013 | 10 | 512 | 9 |
| East | 1003 | 9 | 256 | 19 |
| South | 983 | 10 | 512 | 28 |

An edge label x in slot s is represented by the l_s-bit word x+a_s.
This code is injective on that slot's label set and has highest bit one.
Comparisons occur only between west/east or north/south, so the two ends
always use the same code. Neither matching nor occupancy propagation
requires equal widths for horizontal and vertical edges. The tile language
itself is unchanged. The tile-list SHA-256 is
`66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f`.
The builder reconstructs it from the literal 430 K215 actions.

Let `e_s(j)=o_s+j` for `0<=j<l_s`. Use one shared source anchor u=1095,
and two separate tested anchors v1=2195, v2=3296. The support is

\[
 E=\{0,\ldots,942\}\cup\{e_s(j):s<4,j<l_s\}
      \cup\{1063,1064,1095,2195,3296\}.
\]

It has `943+38+2+3=986` elements. Relative to the old support, exactly
`1012,1032,1096` have been removed. Both dummy positions remain.

For `0<=j<41` set `w_j=2^(10+2j)`. For tile i with labels x_(i,s), define

\[
 c_i=1+\sum_{s<4}\sum_{j<l_s}
       \operatorname{bit}_j(x_{i,s}+a_s)w_{p_s+j}
       +w_{38}+w_{39}+w_{40}.
\]

Give the copy at e_s(j) coefficient w_(p_s+j), and assign the anchor
coefficients

\[
 c_{1095}=w_{38},\quad c_{2195}=w_{39},\quad c_{3296}=w_{40}.
\]

Both dummy coefficients vanish. The clause mask is

\[
 \mu=1022+\sum_{j=0}^{40}w_j.
\]

It has 91 bits and population 50. These are 38 independent label fields
and three anchor fields, all in radix four above a radix-1024 selector field.

## 2. Complete fixed coefficient recipe

Let

\[
 Z=(2^{113}-1)\sum_{e=8792}^{8798}\rho^e
                   +(2^{73}-1)\rho^{8799}.
\]

Define

\[
\begin{split}
 D_C={}&\rho^{30}+\rho^{62}+\rho^{1100}+\rho^{2201}
      +\sum_{e\in E}c_e(\rho^{4393-e}+\rho^{5495-e}),\\
 D_R={}&\rho^{42},\\
 M_C={}&B-1-\sum_{e\in E\setminus\{1\}}\rho^e-2\rho^{1063},\\
 M_{F,\mathrm{native}}={}&4+\mu(\rho^{4393}+\rho^{5495})
      +\sum_{j=0}^{9}\rho^{1013+j}+\sum_{j=0}^{8}\rho^{1065+j}
      +\rho^{2195}+\rho^{3296}+Z.
\end{split}
\]

The four actual ports are

\[
 \boxed{\beta=B-1,\quad K=D_C+BD_R,\quad M_C,\quad
 M_F=M_{F,\mathrm{native}}+B-1.}
\]

They must be rebound as a whole tuple. The fourth port is already shifted;
substituting the native high mask at a skeleton's `MF` port is incorrect.
All sums and powers in this recipe are fixed finite integer arithmetic.

## 3. Exact local decoding and the shared-anchor argument

Let n be the number of selected tiles in a native cell. Before any high
field is decoded, `0<=n<=943`. All nonconstant clause terms are divisible
by 1024, so the low ten bits of the sum are n. Disjointness with 1022 forces
n=0 or 1. Now each radix-four payload field is the sum of at most one
selected tile bit and one copy bit; each anchor field is n plus its anchor
bit. These sums belong to {0,1,2} and are carry-free. The field's tested low
bit vanishes precisely for 0 or 2. Thus n=0 forces all copies and anchors
zero, and n=1 forces all copies to encode its tile and all three anchors one.
The proof does not assume carry-free payloads before selector extraction.

The complete current/spatial/temporal native-basis identities are:

| Tested target | Current contribution through D_C | Spatial contribution through D_R | Temporal contribution |
|---|---|---|---|
| 1013+j, 0<=j<10 | 983+j | none | 1013+j |
| 1065+j, 0<=j<9 | 1003+j | 1023+j | none |
| 2195 | 1095 through shift 1100 | none | 2195 |
| 3296 | 1095 through shift 2201 | none | 3296 |

The only change in the anchor comparison is that both tests read the same
source anchor u=1095. In an occupied current cell that bit is one. The
two tested temporal positions remain distinct, and both must still be one.
The binary and whole-cell synchronization proof uses those two distinct
target positions; it does not require distinct current source positions.
In an empty cell the shared source anchor is zero as required.

Every row of the table is a full coefficient identity for every e in E;
there are no unlisted contributions from the other bare shifts or reflected
clause bands. At each T in {4393,5495}, the coefficient of rho^(T-e) in D_C
is exactly c_e, and e+42 is never T. The builder and independent auditor
check 66,062 exact scalar native-basis identities. By linearity, these cover
every native assignment including all allowed dummy digits.

For synchronization, the new E is a subset of the previous support, still
containing both v1 and v2. Its low part below the two tested anchors ends
at 1095. The difference 1102 is absent from E-E: it exceeds the low span,
`2195-1102=1093` is absent, and `3296-1102=2194` is absent. The difference
1101 occurs exactly once: `2195-1101=1094` is absent, while
`3296-1101=2195` is present. Since `L=8801>2*3296`, there is no additional
circular case. Therefore

\[
 ((4393-E)\bmod8801)\cap((5495-E)\bmod8801)=\varnothing,
\]

\[
 ((2195-E)\bmod8801)\cap((3296-E)\bmod8801)=\{0\}.
\]

The first equality supplies a clean clause band for every binary rotation.
Apply synchronization first in the distinguished Start cell. The inherited
origin condition already forces that cell's selector zero to be one.
Its clean clause therefore forces the shared source anchor at 1095 to be
one, without any prior assumption that other cells are occupied. Both
distinct tested temporal anchors must consequently be one. This is the
local starting point of the alignment argument; global occupancy propagation
is used only after alignment has been recovered.

For binary remainders 1 through b-2, all rotated native digits are even.
For remainder b-1, only the one upper-dummy spill can be odd. The two
distinct tested anchors require two odd digits, so neither case can pass.
The second equality then forces the remaining whole-radix alignment to
be a whole native cell. This is the source synchronization proof with the
same required two tested anchors. Once aligned, parity at each overlap
test enforces equality of the corresponding label bits. The occupied high
bit propagates occupation from the marked Start through the cyclic word;
the injective port-specific codes give exactly the same Wang matching
constraints as before.

## 4. Carry bounds, zero padding, and mask population

The source's conservative pre-decoding carry bound applies with the new
support and clause coefficients:

\[
 \mathcal M=(986+2)\left(2\sum_{e\in E}c_e+6\right).
\]

Finite arithmetic gives `bitlength(M)=112` and `bitlength(4M+8)=114`.
Both `4M+8` and `2mu+4` are strictly below rho=2^115. Even the
conservative padding bound `2(2^113-1)+4=2^114+2` is below rho.
Consequently the inherited uniform no-carry, nonaligned-rotation, and
strict positive raw-slack bounds remain valid.

The maximum unshifted current-product exponent is still
`5495+3296=8791`; the spatial product has maximum exponent 3338, and the
temporal native support ends at 3296. Thus every padded bit at positions
8792 through 8799 is identically zero on every intended aligned cell,
including after any safe dummy changes. There is no carry into those cells.
All positions lie below L. These extra constraints preserve completeness
and may be discarded in soundness.

The high mask's original tests have population
`2*50+10+9+2+1=122`. The added zero tests have population
`7*113+73=864`. Hence

\[
 \operatorname{pc}(M_{F,\mathrm{native}})=986,\qquad
 \operatorname{pc}(M_C)=d-986,
\]

and the exact balance remains their sum d. The low congruences also remain

\[
 M_C\equiv2\pmod4,\quad M_{F,\mathrm{native}}\equiv4\pmod8,
 \qquad 0<M_C,M_{F,\mathrm{native}}<B-1.
\]

These statements are verified on the materialized integers, as well as
from their defining supports. They do not assert that the two masks are
mutually disjoint; each mask constrains its corresponding packed object.

## 5. Explicit actual-rank controller

Changing b and L requires a new completeness controller. Set

\[
 d=5\cdot13\cdot23\cdot677,\qquad
 \lambda=3433,\quad k=3432=\lambda-1.
\]

Trial division proves lambda prime. Exact modular exponentiation certifies

| Modulus | 5 | 13 | 23 | 677 | 3433 |
|---|---:|---:|---:|---:|---:|
| Multiplicative order of B | 4 | 12 | 11 | 52 | 132 |

Thus `ord_d(B)=1716`, which divides k, and

\[
 B^k\bmod\lambda^2=1,973,976\ne1,\qquad
 v_\lambda(B^k-1)=1.
\]

With `H0=1+B D_C+B^2(D_R+1)`, the unit certificate is

| Prime p | B mod p | (B²-1) mod p | H0 mod p |
|---|---:|---:|---:|
| 5 | 3 | 3 | 2 |
| 13 | 7 | 9 | 12 |
| 23 | 9 | 11 | 20 |
| 677 | 665 | 143 | 602 |
| 3433 | 3241 | 2533 | 3121 |

Choose canonical spatial width w and temporal height h to be sufficiently
large powers of lambda, by the unchanged independent rectangular padding
theorem. Put `N=wh=lambda^n`, `q=B^N`, and require `N>d lambda^2` and
`h>lambda`. The orders above all divide lambda-1, so

\[
 q\equiv B^w\equiv B\pmod{d\lambda}.
\]

Switching the low dummy bit in cell j changes the actual packed rank by

\[
 \delta R=-\Gamma B^j,\qquad
 \Gamma=\rho^{1063}(q^2-1)[1+q(D_C+BD_R+B^w)].
\]

This is the unchanged source identity, which depends on the dummy
position and full coefficients, not on the number of copy or anchor bits.
The unit table proves `gcd(Gamma,dN)=1` for the new coefficients.

### Boolean coverage of the actual modulus

Put `T=N/lambda`, `C0=d lambda`. Every residue modulo `dN=C0 T` is a
Boolean subset sum of

\[
 \{B^{2+kj}:0\le j<T\}\cup\{B^3\}.
\]

The valuation and elementary binomial lifting identity show that B^k has
order T modulo lambda^n and is 1 modulo d. Its first T powers are therefore
exactly the T residues `1+C0 z` modulo `C0 T`. Normalize a desired residue
by B^-2. Choose epsilon in {0,1} so that subtracting epsilon B leaves a
nonzero residue modulo lambda. Let a be its least residue modulo C0.
Then `1<=a<C0<T` and `gcd(a,T)=1`. Write the remaining target as `a+C0 u`
and solve

\[
 a z_0+\frac{a(a-1)}2\equiv u\pmod T.
\]

The a distinct orbit entries with additive coordinates
`z0,z0+1,...,z0+a-1` modulo T sum to that target. Include the extra B^3
exactly when epsilon=1. No dummy cell is used twice.

The largest selected position is at most
`2+(lambda-1)(N/lambda-1)=N-N/lambda-lambda+3`. Because `h>lambda`,
`w<N/lambda`. All selected positions and their needed translates by one
and w remain below N and avoid the origin; the separate position 3 is
distinct because k>1. Therefore the source no-wrap dummy argument applies.

Starting with a canonical halting tableau with these dummy bits zero and
actual rank R0, choose the subset for
`(R0-dw)Gamma^-1 mod dN`. The changed actual rank satisfies

\[
 R\equiv dw\pmod{dN},
\]

exactly the temporal rotation required by X=2^R. All tile, overlap,
marker, mask, carry, and strict-slack conditions remain valid. The
inherited Pell converse supplies the remaining positive witnesses.

## 6. Canonical square scale and odd multipliers

Both d and N are odd; put `t=dN`, so q=2^t. Start occupies selector zero,
selector one is forbidden, and all other positions are above the first
two bits, so the canonical word C is 1 modulo 4. Let J be the source
cell-replication factor and define

\[
 S=(C-1)+qF,\qquad
 T_{\rm mask}=(M_CJ+1)+q(M_{F,\mathrm{native}}J-1),\quad M=q^2.
\]

The native constraints give `S AND Tmask=0` and `0<=S,Tmask<M`.
Exact population balance and the low congruences imply
`pc(Tmask)=t+2`. The source identity

\[
 R=(M-S)(M-1)+T_{\rm mask}
   =(M-1-S)M+(S+T_{\rm mask})
\]

has two disjoint blocks. Therefore `pc(R)=3t+2` and `R=3 mod4`,
unchanged by all safe dummy choices. The inherited strict rank-size bounds
still hold. Hence the canonical scale `X/q=2^(R-t)` is a positive integer
square. The canonical Pell parameter A is even and `c=psi_A(R)` is odd.
Taking auxiliary rank `m=cR` supplies the same odd positive normalized
multiplier i; the ordinary Delta-scaled multiplier is odd as well since
Delta=A²-1 is odd. Finally the source half-binomial identity gives
`v2(Y)=pc(R)-2=3t`. Since `Y=s q^3`, the scale s is odd. These are the
same completeness promises used by the inherited signed-domain adapters.

Soundness decodes any solution by the finite interface proved above;
it does not assume that a recovered tableau has prime-power dimensions.
Completeness chooses the prime-power rectangles only to construct a
witness from a finite halting run. The unchanged marked Wang-language
theorem and K215 calibration complete both directions.

## 7. Use and verification limits

The entire new tuple can replace the corresponding four ports of a
compatible positive, ordinary, quartic, or signed arithmetic skeleton
without changing its number of unknowns, equations, degree, or arithmetic
operations. Jones compression must recompute its index constants from the
newly bound source quartic; fixed indices from a different tuple cannot be
silently reused.

`build_coefficients.py` checks the language, label capacities, support
identities, carries, populations, prime controller, and exact payloads.
`audit_coefficients.py` does not import that builder: it independently
reconstructs the four complete integers from a separately pinned tile list,
checks the decoded digits, and checks controller units using the actual
materialized integers. The audit includes 66,062 exact native-basis checks.

These finite certificates do not replace the universal compiler, Pell,
tile-language, or foundational endpoint proofs. Their ordinary proofs and
provenance remain explicit. No global minimum over coefficient encodings,
arithmetic circuits, or Diophantine presentations is asserted.

