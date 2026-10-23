# Bounded-checksum clauses for the K215 native compiler

## Result and proof boundary

The fixed native tuple below uses

\[
\rho=2^{67},\qquad L=8807,\qquad
B=\rho^L=2^{590069}.
\]

It preserves the compiler interface proved for package 36-small-tuple at
ProveIt commit `22e75dd6b87b1b199bb08c778d7cf075ae5aae08`.
The four actual coefficient ports occupy **295,388 raw bytes**, compared
with 506,664 for that package, a reduction of **41.6994%**. Their largest
bit length is **592,884**, compared with 1,016,946. Their gzip payloads
occupy 9,445 bytes. These are sizes of the native ports, not heights of
every coefficient in a fully expanded downstream polynomial.

The new idea is to replace separate radix-four bit comparisons by one
bounded binary checksum. The local constraint is proved exactly below;
it is not a probabilistic hash. Both the support geometry and its decoded
943-tile language remain the same. The smaller radix requires new padding
and a new actual-rank controller; their finite certificates and unbounded
argument are included.

The imported results are the K215 finite-refutation calibration, its marked
Wang-language theorem, the native-window/Pell compiler, independent
rectangular padding, and the native compiler's canonical slack and parity
lemmas. This is an ordinary mathematical adapter to those results, with
finite exact audits. It is not a new end-to-end Lean or Rocq certificate.

## 1. One bounded checksum replaces 41 separate tests

Use the literal ordered 943 tiles `(west,north,east,south)` of package 36.
The SHA-256 of `wang943_tiles.json` is
`66b55f1d11fca9fefc93b12fcfc8b4cabb75b08e9fd03311f9e894a1c5e5e81f`.
The builder independently reconstructs them from the 430 actions of K215.

As before, the physical horizontal copies use the occupied nine-bit code
`256+x`; vertical copies use the occupied ten-bit code `512+x`.
In the checksum word, place the 34 identifier bits first and all seven
mandatory ones (four occupancy bits and three anchors) last. Define

\[
\ell_i=x_{i,0}+2^8x_{i,1}+2^{17}x_{i,2}+2^{25}x_{i,3},
\quad U_i=\ell_i+127\,2^{34}.
\]

Thus `0<U_i<2^41`. Its highest seven bits are all one. This permutation
does not alter physical native positions or the copy bits represented;
it lowers the selector coefficients because the mandatory ones become
the most significant checksum bits. Let the 41 independent copy/anchor
bits form `W`, with `0<=W<2^41`, in that order.

Give selector `i` the scalar clause coefficient

\[
c_i=1+2^{10}(2^{41}-U_i)
   =1+2^{10}(2^{34}-\ell_i),
\]

and give the copy for binary position `j` coefficient `2^(10+j)`.
The clause mask is

\[
\boxed{\mu=1022+2^{10}(2^{41}-1).}
\]

Let `n` be the number of selected tiles. At a clean clause target, the
quantity tested against `mu` is

\[
S=n+2^{10}\left[\sum_{i\text{ selected}}(2^{41}-U_i)+W\right].
\]

Initially `0<=n<=943<1024`, without any assumption on higher carries.
Therefore `S AND mu=0` implies `n AND 1022=0`, hence `n=0` or `n=1`.
Only now decode the upper field:

* If `n=0`, its value is `W`, lies in `[0,2^41)`, and is zero modulo
  `2^41`. Therefore `W=0`.
* If `n=1`, with selected tile `i`, its value is `2^41-U_i+W` and lies
  strictly between zero and `2^42`. It is a multiple of `2^41`, so it
  equals `2^41`. Consequently `W=U_i`.

The converses are immediate. Thus the allowed local encodings are exactly
the all-zero cell and one selected tile with its correct occupied labels
and all three anchors set to one. This is precisely the old local
semantics. The proof works uniformly for every Boolean copy assignment;
it does not rely on enumerating the `2^41` possible words.

More generally, for any finite list of `m`-bit words `U_i` with
`0<U_i<2^m`, and fewer than `2^s` selector bits, use

\[
c_i=1+2^s(2^m-U_i),\qquad
\mu=(2^s-2)+2^s(2^m-1).
\]

The same proof enforces either no selector and word zero, or exactly one
selector and its prescribed word. The selector bound is essential.

## 2. Complete fixed integer recipe

Use the same 986-element native support as package 36:

\[
E=\{0,\ldots,942\}\cup
\bigcup_{s=0}^3\{o_s,\ldots,o_s+l_s-1\}
\cup\{1063,1064,1095,2195,3296\},
\]

where

| Slot | Offset `o_s` | Width `l_s` | Identifier start `p_s` | Occupancy bit |
|---|---:|---:|---:|---:|
| West | 1023 | 9 | 0 | 34 |
| North | 1013 | 10 | 8 | 35 |
| East | 1003 | 9 | 17 | 36 |
| South | 983 | 10 | 25 | 37 |

For `0<=j<l_s-1` set `c_(o_s+j)=2^(10+p_s+j)`; for the occupied high bit
set `c_(o_s+l_s-1)=2^(44+s)`.
Set `c_1095=2^48`, `c_2195=2^49`, `c_3296=2^50`, and
`c_1063=c_1064=0`. The selector coefficients are those in Section 1.
Define

\[
Z=(2^{65}-1)\sum_{e=8792}^{8804}\rho^e
 +(2^{19}-1)\rho^{8805},
\]

\[
\begin{aligned}
D_C={}&\rho^{30}+\rho^{62}+\rho^{1100}+\rho^{2201}
 +\sum_{e\in E}c_e(\rho^{4393-e}+\rho^{5495-e}),\\
D_R={}&\rho^{42},\\
M_C={}&B-1-\sum_{e\in E\setminus\{1\}}\rho^e-2\rho^{1063},\\
M_{F,\rm native}={}&4+\mu(\rho^{4393}+\rho^{5495})
 +\sum_{j=0}^9\rho^{1013+j}+\sum_{j=0}^8\rho^{1065+j}
 +\rho^{2195}+\rho^{3296}+Z.
\end{aligned}
\]

The four ports are the entire tuple

\[
\boxed{\beta=B-1,\quad K=D_C+BD_R,\quad M_C,\quad
M_F=M_{F,\rm native}+B-1.}
\]

In particular `MF_source` in the artifact is already shifted. All sums and
powers in these definitions are fixed finite arithmetic. No coefficient
depends on whether the blank machine halts.

## 3. Exact interface and synchronization

For every `e` in `E`, the native coefficient identities are unchanged:

| Tested target | Current source | Spatial source | Temporal source |
|---|---|---|---|
| `1013+j`, `0<=j<10` | `983+j` | none | `1013+j` |
| `1065+j`, `0<=j<9` | `1003+j` | `1023+j` | none |
| 2195 | 1095 | none | 2195 |
| 3296 | 1095 | none | 3296 |

At each clause target `T` in `{4393,5495}`, the coefficient of
`rho^(T-e)` in `D_C` is exactly `c_e`, and `e+42` is never `T`.
The finite audits check all **66,062** scalar identities independently;
linearity gives them for every native assignment, including dummy digits.

The binary alignment proof needs only the local semantics proved in
Section 1, the two distinct tested anchors, and the following support
conditions:

\[
\{(4393-e)\bmod8807:e\in E\}\cap
\{(5495-e)\bmod8807:e\in E\}=\varnothing,
\]

\[
\{(2195-e)\bmod8807:e\in E\}\cap
\{(3296-e)\bmod8807:e\in E\}=\{0\}.
\]

The gap 1102 is absent from `E-E`, while the anchor gap 1101 occurs only
between 2195 and 3296; `8807>2*3296` excludes additional circular cases.
Consequently one clause band is clean for any rotation. In the distinguished
Start cell, selector zero is already one. Its clean clause forces the source
anchor one and hence requires both distinct temporal anchor tests to receive
odd digits. A binary rotation with remainder 1 through 65 has no such odd
digits; remainder 66 has at most the single upper-dummy spill. Both cases
are excluded by the two tests. The unique anchor intersection then forces
whole-cell alignment. This uses the inherited native rotation lemma with
the new radix; the copy/anchor semantics needed by it are exactly preserved.
Once aligned, label overlaps and their occupied high bits give the same
Wang matching and occupation propagation as before.

The conservative inherited mass bound is

\[
\mathcal M=988\left(2\sum_{e\in E}c_e+6\right).
\]

Its bit length is 65 and that of `4M+8` is 67. Exact checks give

\[
\max\{4\mathcal M+8,\ 2\mu+4,\ 2(2^{65}-1)+4,\ 16\}<2^{67}.
\]

Thus all old no-carry, rotated-digit and positive raw-slack bounds apply.
The largest unshifted current-product exponent is still `5495+3296=8791`;
spatial and temporal exponents are at most 3338 and 3296. Hence every added
padding test, at exponents 8792 through 8805, tests a canonical zero, even
after safe dummy changes. All tests lie strictly below 8807. They preserve
completeness and can be discarded during soundness extraction.

The clause mask has 50 set bits. The nonpadding high-mask population is
`2*50+10+9+2+1=122`. Padding adds `13*65+19=864` bits. Therefore

\[
\operatorname{pc}(M_{F,\rm native})=986,\quad
\operatorname{pc}(M_C)=d-986,\quad
M_C\equiv2\pmod4,\quad M_{F,\rm native}\equiv4\pmod8,
\]

and both masks are strictly between zero and `B-1`.

## 4. Actual-rank control and completeness

The new dimensions have

\[
d=590069=67\cdot8807,\qquad
\lambda=581197,\quad k=\lambda-1=581196.
\]

All three displayed factors/primes are prime, as certified by trial
division. The exact orders of `B` and unit residues are:

| Prime `p` | `ord_p(B)` | `B mod p` | `(B^2-1) mod p` | `H0 mod p` |
|---|---:|---:|---:|---:|
| 67 | 66 | 46 | 38 | 41 |
| 8807 | 4403 | 456 | 5374 | 5193 |
| 581197 | 581196 | 348469 | 573553 | 76889 |

Here `H0=1+B D_C+B^2(D_R+1)`. The least common multiple of the first two
orders is 290598, which divides `k`; the third order divides `k` as well.
Also

\[
B^k\bmod\lambda^2=182964883980\ne1,\qquad
B^k\equiv1\pmod\lambda,
\]

so `v_lambda(B^k-1)=1`.

Choose the canonical spatial width `w` and temporal height `h` to be
sufficiently large powers of `lambda`, using the inherited independent
rectangular padding theorem. Put `N=wh=lambda^n`, `q=B^N`, and require
`N>d lambda^2` and `h>lambda`. All relevant multiplicative orders divide
`lambda-1`, whence

\[
q\equiv B^w\equiv B\pmod{d\lambda}.
\]

Changing a safe low dummy bit in cell `j` changes the actual rank by

\[
\delta R=-\Gamma B^j,\quad
\Gamma=\rho^{1063}(q^2-1)
 [1+q(D_C+BD_R+B^w)].
\]

The unit table proves `gcd(Gamma,dN)=1`. The following explicit subset
argument then supplies every needed residue modulo the actual modulus.
Set `T=N/lambda` and `C0=d lambda`. The powers `(B^k)^j`, `0<=j<T`,
are exactly the `T` residues `1+C0 z` modulo `C0 T`: they lie there by
the period congruences, and the valuation-one lifting theorem gives exact
order `T`. To hit a desired residue using

\[
\{B^{2+kj}:0\le j<T\}\cup\{B^3\},
\]

normalize by `B^-2`. Choose `epsilon` in `{0,1}` so that subtracting
`epsilon B` leaves a residue nonzero modulo `lambda`. Its least residue
`a` modulo `C0` satisfies `1<=a<C0<T` and `gcd(a,T)=1`. Write the remaining
target as `a+C0 u`. Solve

\[
az_0+a(a-1)/2\equiv u\pmod T.
\]

The `a` distinct orbit entries with additive coordinates
`z_0,...,z_0+a-1` modulo `T` sum to that target. Include `B^3` exactly
when `epsilon=1`. Thus all changes are Boolean and no dummy is repeated.

The largest selected cell index is at most
`2+(lambda-1)(T-1)=N-T-lambda+3`. Since `w<T`, all selected cells and
their required translates by one and `w` avoid wraparound and the origin.
The separate cell 3 is distinct and also safe. Starting from a canonical
halting tableau with these dummy bits zero and rank `R0`, target
`(R0-dw) Gamma^-1` modulo `dN`. The modified actual rank satisfies
`R=dw mod dN`, exactly the required temporal alignment. Every language,
carry, overlap, marker, population and strict-slack condition is retained.
The inherited Pell converse supplies the remaining positive witnesses.

Soundness does not suppose the dimensions of an arbitrary solution to be
prime powers. Prime-power padding is only the explicit completeness
construction.

## 5. Canonical square-scale and odd-multiplier promises

Both `d` and `N` are odd. Set `t=dN`, so `q=2^t`. In a canonical cell
word `C`, selector zero is one, selector one is forbidden and all other
positions exceed one; hence `C=1 mod4`. Let `J` be the cell replication
factor and put

\[
S=(C-1)+qF,\quad
T_{\rm mask}=(M_CJ+1)+q(M_{F,\rm native}J-1),\quad M=q^2.
\]

Exactly as in the inherited interface, `S AND Tmask=0`, both are below
`M`, and `pc(Tmask)=t+2`. The identity

\[
R=(M-S)(M-1)+T_{\rm mask}
 =(M-1-S)M+(S+T_{\rm mask})
\]

has two disjoint blocks, proving `pc(R)=3t+2` and `R=3 mod4`. Safe dummy
changes preserve these conclusions. The canonical scale `X/q=2^(R-t)`
is therefore a positive integer square. The canonical Pell parameter is
even and its relevant `psi` value `c` is odd. Taking auxiliary rank `cR`
gives the same odd positive normalized multiplier; the ordinary multiplier
is odd since its extra factor `Delta` is odd. Finally the inherited
half-binomial identity gives `v2(Y)=pc(R)-2=3t`; writing `Y=s q^3`
shows that `s` is odd. Thus the strengthened signed-domain interfaces are
preserved, as well as the positive one.

## 6. Use in a fixed Diophantine equation

The complete new tuple may replace all four ports of a compatible native
positive, ordinary, quartic or signed skeleton. It changes no witness
count, degree or arithmetic-operation count at that interface. It must
not be spliced with ports from a different tuple. Any later Jones/Sun
coefficient index must be recomputed from the newly specialized parent;
an index tied to old coefficients cannot be reused.

Composing this adapter, a proved compatible skeleton, the unchanged
marked-language theorem, and K215 calibration yields, inside ZFC,

\[
\text{the fixed system has a solution}
\quad\Longleftrightarrow\quad
\text{there exists a finite ZFC refutation}.
\]

Negating gives the requested consistency equivalence. This argument proves
neither side of that equivalence.

## 7. Reproduction

Run `python3 build_coefficients.py` and then
`python3 audit_coefficients.py` from any working directory. Both use the
Python standard library and explicit exception checks, including under
`python3 -O`. The independent audit does not import the builder. It reads
all four payloads, reconstructs all four complete integers, rechecks the
66,062 native identities, verifies every one of the 943 canonical clauses,
rejects all 38,663 single-copy-bit mutations, and certifies the actual
coefficient unit residues and exact multiplicative orders. These finite
checks complement the universal decoding and padding proofs; they do not
replace the imported compiler or foundational formalization.
