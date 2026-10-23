# A 1,064,921-bit native base by combining mixed clauses and fixed-factor padding

## Result and dependency boundary

The complete new coefficient tuple has

\[
b=121,\qquad L=8801,\qquad d=bL=1064921=11^2\cdot13\cdot677,
\qquad \rho=2^{121},\qquad B=2^{1064921}.
\]

It combines package 25's mixed-radix clauses and short geometric layout
with package 24's Boolean padding controller for an arbitrary fixed odd
factor. Neither source package combines these two improvements. The base
exponent is 45.4760448% smaller than the wave-4 record, 5^9 = 1,953,125.
The actual four-port payload is 533,099 bytes, 45.44739158% below the
977,220-byte wave-4 tuple. All four integers are explicitly materialized.

The change preserves the complete blank-K215 native compiler interface,
including the canonical odd s, odd i, and square scale required by the
signed-domain reductions. Its proof uses the inherited marked-Wang-language,
native/Pell compiler and literal K215 calibration. These are ordinary
mathematical dependencies, not numerical hypotheses. The present delivery
does not rebuild an end-to-end Lean or Rocq certificate. In particular,
checking the bytes is not checking an unbounded nonhalting claim.

All comparisons refer to ProveIt commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`. The source-specific proof files
are identified in `SOURCE_LEDGER.json`; no historical coefficient ports
are mixed with the new tuple. The source proof `mixed125_full_interface.md`
contains the full ordinary-interface and parity transfer at the previous
radix, and `fixed_factor_padding.tex` contains the controller argument.

## 1. Literal finite coefficient recipe

Use exactly the 943 ordered directed-signal tiles from package 19, as
retained by packages 25 and 27. The included list is independently regenerated
from the literal 430-action K215 table. Selector 0 is Start, selector 1
is the globally impossible forbidden tile, and the others are lexicographically
ordered. The tile language is unchanged. The included proof
`wang943_language.md` proves that a marked periodic tiling exists exactly
when blank K215 halts; it also proves arbitrary sufficiently large independent
width and height padding, which is crucial below.

The native support is

\[
E=[0,942]\cup[983,992]\cup[1003,1032]
 \cup\{1063,1064,1095,1096,2195,3296\}.
\]

It has 989 elements and maximum 3296. The two dummy positions are 1063
and 1064. Position 1064 already includes the one possible spill of the
upper bit of dummy 1063. For edge slots west, north, east, south, set

\[
e_0(j)=1023+j,\quad e_1(j)=1013+j,\quad
e_2(j)=1003+j,\quad e_3(j)=983+j\quad(0\le j<10).
\]

The four anchors in order are 1095, 1096, 2195, 3296. Let

\[
W_j=2^{10+2j}\quad(0\le j<44),\qquad
\mu=1022+\sum_{j=0}^{43}W_j.
\]

For tile i with labels t_{i,s}, define

\[
c_i=1+\sum_{s=0}^3\sum_{j=0}^9
\operatorname{bit}_j(t_{i,s}+512)W_{10s+j}
+\sum_{j=40}^{43}W_j.
\]

The copy coefficient is c_{e_s(j)}=W_{10s+j}; the four anchors receive
W_40,...,W_43 respectively; both dummy coefficients vanish. This defines
c_e on every e in E. Every label plus 512 is less than 1024 and has its
occupation bit set.

Set T_1=4393, T_2=5495 and H=42. The external zero mask is

\[
Z=(2^{119}-1)\sum_{e=8792}^{8798}\rho^e
 +(2^{27}-1)\rho^{8799}.
\]

It contains exactly 7·119+27=860 bits. Define

\[
\begin{aligned}
D_C={}&\rho^{30}+\rho^{62}+\rho^{1100}+\rho^{2200}
 +\sum_{e\in E}c_e(\rho^{4393-e}+\rho^{5495-e}),\\
D_R={}&\rho^{42},\\
M_C={}&B-1-\sum_{\substack{e\in E\\e\ne1}}\rho^e-2\rho^{1063},\\
M_{F,\mathrm{native}}={}&4+\mu(\rho^{4393}+\rho^{5495})
 +\sum_{j=0}^9(\rho^{1013+j}+\rho^{1065+j})
 +\rho^{2195}+\rho^{3296}+Z.
\end{aligned}
\]

The four actual arithmetic ports, and no others, are

\[
\boxed{\beta=B-1,\qquad K=D_C+BD_R,\qquad
M_C,\qquad M_F=M_{F,\mathrm{native}}+B-1.}
\]

Thus downstream `MF` is already shifted. All sums are finite and have
fully specified integer coefficients. No part of the recipe waits for
K215 to halt. A polynomial evaluator's `Bm1` port aliases beta, `K0`
and `Kconstant` alias K, and `MF` aliases MF_source.

## 2. Exact local decoding and geometry

The mixed clause decoder is inherited unchanged from package 25. Here
is its essential ordering, which avoids a circular carry assumption.
Before selector extraction the low ten bits of a clean clause sum are
the selector count n, with 0 <= n <= 943. All other contributions are
divisible by 1024. Mask 1022 therefore forces n in {0,1} independently
of any higher-field carries. Conditional on that fact, each higher
radix-4 field is the sum of at most one selected tile bit and one copy
bit, or n and one anchor bit. It is 0, 1 or 2, so no radix-4 carry occurs.
Testing its low bit forces 0 or 2. Thus an empty cell has no copies or
anchors, and an occupied cell has exactly one selected tile, matching
copies, and all four anchors. The converse follows by direct substitution.

At the tested spatial and temporal fields, exact linear identities give:

| Target | D_C contribution | D_R contribution | Temporal contribution |
|---|---|---|---|
| 1013+j | native position 983+j | none | position 1013+j |
| 1065+j | native position 1003+j | position 1023+j | none |
| 2195 | position 1095 | none | position 2195 |
| 3296 | position 1096 | none | position 3296 |

At either clause target T, the coefficient on basis position e is
exactly c_e; the D_R contribution is zero. The generator and an independent
checker each verify all 69,230 identities on the full native support.
These are basis identities, hence imply the assertions for every native
assignment, including all permitted dummy values.

The smaller circumference is safe because L=8801>2·3296. The two circular
geometric identities are

\[
(4393-E)\bmod L\;\cap\;(5495-E)\bmod L=\varnothing,
\]

\[
(2195-E)\bmod L\;\cap\;(3296-E)\bmod L=\{0\}.
\]

The first follows because the clause gap 1102 does not occur in E-E;
the second because the only support pair separated by 1101 is (2195,3296).
The exact checks include circular residues, not just interval reasoning.
These identities supply a clean band for every temporal rotation and
unique whole-cell anchor synchronization after binary alignment.

For binary remainder 1,...,b-2, all low digits of the rotated native
word are even. For remainder b-1 there is only the one possible odd
upper-dummy spill. The two distinct occupied anchor tests require two
odd digits and exclude both cases. The spill position is already in E,
so the finite geometry has not omitted this boundary case. This is
the inherited binary-alignment proof with b=121.

## 3. Carry bounds, filler, and native populations

Put

\[
M=(989+2)\left(2\sum_{e\in E}c_e+6\right).
\]

The exact finite values satisfy

\[
\operatorname{bitlength}(M)=118,\qquad
\operatorname{bitlength}(4M+8)=120,
\qquad 4M+8<2^{121},\qquad 2\mu+4<2^{121}.
\]

The six non-clause contributions in this bound include the four bare
D_C terms, the D_R term and the temporal term. Thus the same uniform
no-carry and strict-slack estimates used in the native compiler hold
before selector extraction. The largest filler digit satisfies

\[
2(2^{119}-1)+4<2^{121}.
\]

The maximum unshifted computational exponent is
T_2+max(E)=5495+3296=8791. The other contributions have smaller maxima.
Every filler position 8792,...,8799 is therefore identically zero in a
canonical aligned computational cell, including every permitted dummy
adjustment. All such positions lie below L=8801. Since the carry bound
has already been proved, these are actual zero binary digits, not merely
zero formal coefficients before carrying. Dense filler consequently
preserves completeness. In soundness the decoder can discard these
extra tests; adding them cannot introduce a spurious solution.

The 53 bits in each clause mask, 20 edge bits, two anchor bits, one
low-origin bit and 860 filler bits give

\[
\operatorname{pc}(M_{F,\mathrm{native}})=106+20+2+1+860=989.
\]

The low mask removes 988 native low bits and the upper dummy bit, all
distinct. Hence

\[
\operatorname{pc}(M_C)+\operatorname{pc}(M_{F,\mathrm{native}})=d,
\quad M_C\equiv2\pmod4,
\quad M_{F,\mathrm{native}}\equiv4\pmod8,
\]

and both masks lie strictly between 0 and B-1. The shifted inverse-population
identity and its exact two-bit surplus therefore remain valid. The two
native masks are not claimed to be mutually disjoint: each constrains
its own data word.

## 4. Fixed-factor completeness controller

Unlike a power-of-five construction, the new d is not a power of the
padding prime. We use the package-24 fixed-factor Boolean controller,
with the following newly checked certificate:

\[
\lambda=2341,\qquad k=\lambda-1=2340,\qquad
\operatorname{ord}_{d}(B)=780\mid k,
\]

\[
B^k\bmod\lambda^2=2556373\ne1,
\qquad 2556373\equiv1\pmod\lambda.
\]

Thus v_lambda(B^k-1)=1. Trial division proves lambda prime. The orders of
B modulo 121,13,677,lambda are 10,12,52,60 respectively. Order 780 is
certified by B^780=1 modulo d and B^(780/p) != 1 for p=2,3,5,13.

Let H_0=1+BD_C+B^2(D_R+1). The complete unit certificate is:

| Prime p | B mod p | D_C mod p | D_R mod p | B^2-1 mod p | H_0 mod p |
|---|---:|---:|---:|---:|---:|
| 11 | 2 | 5 | 4 | 3 | 9 |
| 13 | 6 | 1 | 12 | 9 | 7 |
| 677 | 611 | 38 | 643 | 293 | 654 |
| 2341 | 2100 | 2051 | 586 | 1896 | 1225 |

Choose spatial width w and temporal height h as sufficiently large
powers of lambda. Independent rectangular padding permits this. Put
N=wh=lambda^n, q=B^N, and require h>lambda and N>d lambda^2. Since all
the relevant multiplicative orders divide lambda-1,

\[
q\equiv B^w\equiv B\pmod{d\lambda}.
\]

A safe low dummy switch at cell j changes the *actual* packed Pell
index by -Gamma B^j, where the inherited exact identity is

\[
\Gamma=\rho^{1063}(q^2-1)
 \left[1+q(D_C+BD_R+B^w)\right].
\]

The displayed unit table proves gcd(Gamma,dN)=1: every prime factor of
dN belongs to {11,13,677,lambda}, and modulo each prime the two nontrivial
factors are B^2-1 and H_0. The remaining factor is a power of 2.

### Boolean coverage lemma

Every residue modulo dN is a sum of a subset of

\[
\{B^{2+kj}:0\le j<T\}\cup\{B^3\},\qquad T=N/\lambda.
\]

*Proof.* Let C_0=d lambda, so dN=C_0T and T>C_0. The valuation-one
identity implies that B^k has order T modulo lambda^n. It is 1 modulo d.
By the Chinese remainder theorem its first T powers are therefore exactly
the T residues of the form 1+C_0 z modulo C_0T.

Normalize a desired residue by multiplying by B^-2. Choose epsilon in
{0,1} so that this residue minus epsilon B is nonzero modulo lambda.
This is possible because B is a unit modulo lambda. Let a be the least
residue of that difference modulo C_0. Then 1<=a<C_0<T and gcd(a,T)=1.
Write the remaining target as a+C_0u. Choose z_0 satisfying

\[
az_0+\frac{a(a-1)}2\equiv u\pmod T.
\]

Select the a distinct orbit entries with additive coordinates
z_0,z_0+1,...,z_0+a-1 modulo T, and select the extra B^3 exactly when
epsilon=1. Their sum gives the target. Every cell is selected at most
once. The largest orbit position is

\[
2+(\lambda-1)(N/\lambda-1)=N-N/\lambda-\lambda+3.
\]

Because h>lambda implies w<N/lambda, its translates by 1 and by w stay
below N. The extra position 3 is distinct from the orbit since k>1 and
has the same no-wrap property. This proves Boolean coverage on safe
dummy positions. QED.

Starting from a canonical halting tableau with these dummy bits zero,
let its actual packed index be R_0. Apply the lemma to
(R_0-dw)Gamma^-1 modulo dN. The adjusted index satisfies

\[
R\equiv dw\pmod{dN},
\]

which is precisely the temporal rotation needed by X=2^R. Dummy switches
change no tile, copy, anchor, low-origin or filler condition. The uniform
carry bound retains the strict positive raw slack required by the ordinary
arithmetic interface. Thus the inherited Pell converse constructs all
remaining positive witnesses. No independent choice of R was assumed.

## 5. Full ordinary and canonical parity interface

The soundness proof uses only the local decoding, tested fields, circular
geometry, native populations and carry conditions already checked. It
places no prime-power assumption on arbitrary recovered solutions. The
controller supplies the new completeness argument. Consequently the full
ordinary blank-K215 arithmetic interface transfers to the new tuple,
including the ordinary quartic source; any algebraic zero-set reduction
of that source can substitute the four ports simultaneously.

For the canonical signed refinements, put t=dN, so q=2^t and t is odd.
The Start origin gives C=1 mod4. With F the native field and J=(q-1)/(B-1),
define

\[
S=(C-1)+qF,\qquad
T_{\rm mask}=(M_CJ+1)+q(M_{F,\mathrm{native}}J-1),\quad M=q^2.
\]

The native mask conditions give S AND T_mask=0 and 0<=S,T_mask<M.
The low congruences imply that the +1 and -1 corrections each add one
population bit. The exact balance therefore gives pc(T_mask)=t+2.
The shifted packing identity is

\[
R=(M-S)(M-1)+T_{\rm mask}
 =(M-1-S)M+(S+T_{\rm mask}).
\]

The two displayed blocks are disjoint, so

\[
\operatorname{pc}(R)=2t+\operatorname{pc}(T_{\rm mask})=3t+2.
\]

Also S=0 mod4 and T_mask=3 mod4, giving R=3 mod4. Thus the main
Pell scale 2^(R-t) is an integer square. The inherited auxiliary-rank
choice supplies an odd i. Finally the authentic half-binomial identity
gives v_2(Y)=pc(R)-2=3t; since Y=sq^3, s is odd. These arguments are
unchanged by the new filler placement or dummy tuning. This proves the
same additional completeness promises used by the compatible signed
reductions. It does not authorize rebinding an unrelated fixed Jones
polynomial without also recomputing its specialized index constants.

Composing the complete native interface with the literal K215 calibration
gives, in ordinary mathematics formalizable in ZFC,

\[
\exists\text{ positive source witnesses}
\iff \text{blank K215 halts}
\iff \text{ZFC has a finite refutation}.
\]

Negating yields the intended equivalence to Con(ZFC). No side of that
equivalence is assumed or proved true here.

## 6. Exact bytes, reproduction, and limitations

| Port | Bits | Raw bytes | Gzip bytes |
|---|---:|---:|---:|
| beta | 1,064,921 | 133,116 | 164 |
| K | 1,070,004 | 133,751 | 9,794 |
| MC | 1,064,921 | 133,116 | 264 |
| MF_source | 1,064,922 | 133,116 | 263 |
| Total | | 533,099 | 10,485 |

All files use minimal unsigned little-endian raw encoding, compressed with
gzip. Read them with `int.from_bytes(gzip.decompress(path.read_bytes()),
'little')`. Their raw and compressed SHA-256 hashes are in
`coefficients/COEFFICIENT_BINDING.json`.

Run `python3 build_coefficients.py` to regenerate the tuple and certificate.
Run `python3 audit_independent.py` for a separate read-only reconstruction
which does not import the generator. Both use only Python's standard
library and the included sources. The literal machine is checked against
SHA-256 fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090.

The finite checks certify the exact recipe, byte identity, native-basis
equalities, populations, modular-order and valuation conditions. The
unbounded conclusion rests on the proofs above and their explicitly
identified inherited theorems. There is no global coefficient minimum,
new machine-state record, consistency proof, or new proof-assistant
certificate. Compression is reported separately from integer height.
