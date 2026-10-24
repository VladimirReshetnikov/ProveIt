# A mixed-radix, parity-separated, unrounded coefficient tuple

## The theorem and its exact scope

This construction combines three independently supplied ideas from the seven
wave-4 reports pinned at ProveIt commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`: package25's mixed clause fields
and external zero tests, package26's parity-separated copy tracks, and
package24's Boolean controller for an arbitrary fixed odd factor. The
943-tile language and its blank-machine interpretation are unchanged.

The result is a complete four-port tuple with

\[
 b=121,\quad L=8801,\quad d=bL=1064921,\quad
 \rho=2^{121},\quad B=2^{1064921}.
\]

It satisfies the ordinary inputless native/Pell compiler interface, including
canonical square scale, odd strong multiplier and odd cubic scale. Therefore
it can instantiate the ordinary quartic31, the positive twelve-variable
reductions, the signed integer reductions, and then the quartic-dependent
Jones index construction. The last step must regenerate its coefficients
and index bound from the new tuple: its old numerical Jones constants must
not be retained.

This is a mathematical adapter to the inherited native/Pell and K215
calibration proofs, not a new Lean or Rocq certificate. No proof of Con(ZFC)
and no global minimum of coefficient height is asserted.

## Complete bounded recipe

Take exactly the ordered943 tiles in `wang943_tiles.json`. They have
ordered fields (west,north,east,south). Start is selector0, Forbidden is
selector1. `build_coefficients.py` reconstructs all943 tiles from all430
literal K215 actions and checks equality of the entire list, not just its
length. The source machine SHA-256 is
`fdbcef0825886035c3091c8537a69535bc96f9e265f0ae45863543d40ae70090`.

Let
\[
 e_t(j)=o_t+2j,\quad (o_0,o_1,o_2,o_3)=(1020,1000,980,960),
 \qquad W_j=2^{10+2j}.
\]
For0<=j<10 these are the copy exponents of the four edge labels. Define
\[
 E=\{0,\ldots,942\}\cup\{e_t(j):0\le t<4,0\le j<10\}
 \cup\{1063,1064,1095,1096,2195,3296\}.
\]
Thus |E|=989 and max E=3296. Each edge label x is encoded by its ten-bit
occupied word x+512. If tile i has labels x_it, let
\[
 c_i=1+\sum_{t=0}^3\sum_{j=0}^9\operatorname{bit}_j(x_{it}+512)W_{10t+j}
       +\sum_{j=40}^{43}W_j.
\]
The copy coefficient c_(e_t(j)) is W_(10t+j). The coefficients at anchors
1095,1096,2195,3296 are W40,W41,W42,W43 respectively; both dummy
coefficients c1063,c1064 are zero. Finally set
\[
 \mu=1022+\sum_{j=0}^{43}W_j,
 \quad Z=(2^{119}-1)\sum_{e=8792}^{8798}\rho^e
          +(2^{27}-1)\rho^{8799}.
\]
The complete native constants are
\[
\begin{split}
 D_C={}&\rho^{40}+\rho^{41}+\rho^{1100}+\rho^{2200}
       +\sum_{e\in E}c_e(\rho^{4393-e}+\rho^{5495-e}),\\
 D_R={}&\rho,\\
 M_C={}&B-1-\sum_{e\in E,\ e\ne1}\rho^e-2\rho^{1063},\\
 M_{F,n}={}&4+\mu(\rho^{4393}+\rho^{5495})
       +\sum_{j=0}^9(\rho^{1000+2j}+\rho^{1021+2j})
       +\rho^{2195}+\rho^{3296}+Z.
\end{split}
\]
The four polynomial ports, always replaced together, are
\[
 \boxed{\beta=B-1,\qquad K_0=D_C+BD_R,\qquad M_C,
              \qquad M_F=M_{F,n}+B-1.}
\]
MF is the shifted source high mask, not M_(F,n). These are fixed finite
integer definitions; no coefficient is chosen by waiting for a halt.

## Mixed clause decoding precedes payload carry analysis

Before decoding, n, the number of selected tile digits, lies in[0,943].
Every nonconstant clause contribution is divisible by1024. Consequently
the low ten bits of the clause sum are exactly n, even if there are
carries among higher fields. Disjointness with the low mask1022 forces
n=0 or n=1. Only after that conclusion do we analyze the44 payload
fields. Each radix4 field is the sum of a Boolean tile/occupancy bit and
one Boolean copy/anchor bit, hence is0,1,or2. No payload carry remains,
and masking its low bit permits0 or2. If n=0 all copies/anchors vanish;
if n=1 they equal the selected tile's occupied labels and its four1anchors.
This establishes exactly the same local decoder as the old uniform-radix
clause. It is not circularly assuming all payload carries absent before
extracting n.

## Exact geometry, arbitrary rotation and parity separation

For each j=0,...,9 the complete convolution identities are:

- At1000+2j, DC sees960+2j through shift40; the temporal native word
  sees1000+2j; DR sees nothing.
- At1021+2j, DC sees980+2j through shift41; DR sees1020+2j through
  shift1; the temporal word sees nothing.
- At2195, DC sees1095 through shift1100, while the temporal word sees2195.
- At3296, DC sees1096 through shift2200, while the temporal word sees3296.

In both anchor cases DR is absent. At each clause target4393,5495 the
coefficient on every basis digit e is exactly c_e and DR is absent. These
are identities of the full DC coefficient polynomial, including both
reflected clauses, not bare-shift approximations. All69,230 component
identities are checked exactly. Linearity makes them universal in the
native digits, including the harmless dummy values.

The parity tracks explain the short shifts: the temporal targets are even,
spatial targets odd, copy positions even, and other potential predecessors
are outside the native support. The reflected contributions at the short
clause locations are justified by the exact identities, not by the
inapplicable old inequality4393-max(E)>max(E).

The same exact finite support also gives
\[
 (4393-E)\bmod L\;\cap\;(5495-E)\bmod L=\varnothing,
\]
and
\[
 (2195-E)\bmod L\;\cap\;(3296-E)\bmod L=\{0\}.
\]
For the first, the band difference1102 is absent from E-E. For the second,
the only support pair of difference1101 is(2195,3296): the small part has
span1096, and the missing candidates1094 and2194 prevent other pairs.
There are no additional circular cases because L=8801>2max E.
The upper-dummy spill position1064 is already in E.

The inherited carry-free rotation argument supplies a clean clause for
any binary shift. Nonzero binary remainders1,...,119 give only even rotated
digits; remainder120 permits at most the one upper-dummy odd spill. Neither
can supply the two required odd anchors in the marked occupied cell.
The binary remainder is therefore zero, and the anchor intersection then
forces a whole-cell rotation. The edge-bit equations recover the exact
Wang matches. The one-cell spatial shift propagates occupancy from Start.
No divisibility or coprimality restriction is imposed on the temporal shift
of an arbitrary purported solution.

## Uniform carries, positive slack and external zero population

Let
\[
 \mathcal M=991\left(2\sum_{e\in E}c_e+6\right).
\]
Its bitlength is118, while4M+8 has bitlength120. The clause mask has
bitlength97. The added padding is a mask, not an extra convolution term.
The explicit stronger estimates hold:
\[
 \max(4\mathcal M+8,2\mu+4,2(2^{119}-1)+4,16)<2^{121},
\]
\[
 3\rho/4+\mathcal M\le\rho-2,\qquad
 \rho/2+1+\mathcal M\le\rho-2.
\]
These bounds apply before decoding, including all native selector choices
and dummy values, and retain the compiler's strict canonical slack.
The maximum unshifted DC-product exponent is5495+3296=8791; DR and
temporal products are lower. Hence every bit tested by Z, at8792,...,8799,
is identically zero for all aligned native assignments. All positions
are below L. Adding these tests cannot harm completeness, and discarding
them cannot harm soundness. No convolution carry enters the padding.

The clause mask has53bits. The two clauses, twenty edge tests, two anchor
tests and low test contribute129bits; Z contributes7*119+27=860bits.
Therefore
\[
 \operatorname{pc}(M_{F,n})=989,
 \quad\operatorname{pc}(M_C)=d-989,
 \quad M_C\equiv2\pmod4,
 \quad M_{F,n}\equiv4\pmod8.
\]
Both masks lie strictly between0and B-1. These statements are checked on
the actual materialized integers. The two masks are not claimed disjoint
from one another: they constrain different packed objects.

## Explicit rank controller without any power-of-five hypothesis

This is the new completeness issue: d is no longer a power of five.
Use
\[
 d=11^2\cdot13\cdot677,\quad \lambda=2341,\quad k=2340=\lambda-1.
\]
Trial division proves all displayed primes. Exact modular arithmetic gives
\[
 \operatorname{ord}_{121}(B)=10,\quad
 \operatorname{ord}_{13}(B)=12,\quad
 \operatorname{ord}_{677}(B)=52,
\]
so ord_d(B)=780 divides k, lambda=1 modulo780, and
\[
 B^k\bmod\lambda^2=2556373\ne1,
 \qquad v_\lambda(B^k-1)=1.
\]
The prime-unit rows (p,B mod p,(B^2-1) mod p,H0 mod p), with
H0=1+B DC+B^2(DR+1), are
\[
 (11,2,3,7),\ (13,6,9,1),\ (677,611,293,53),\
 (2341,2100,1896,594).
\]
Thus every needed factor is a unit at each prime of d lambda.

The unchanged tile language permits every sufficiently large spatial
width and temporal height independently: extra untouched blank margins
increase the width, and padded halting rows increase the height. This is
stronger than choosing powers of five in older convenient witnesses.
The precise pinned source is package30/compiler/WANG943_COEFFICIENTS.md,
Section2.4, copied here as sources/WANG943_LANGUAGE_AND_COMPILER.md;
it states arbitrary sufficiently large independent integer widths/heights,
not just powers of five.
Choose width w_c and height h_c to be sufficiently large powers of lambda,
with h_c>lambda, N=w_c h_c=lambda^n>d lambda^2, and q=B^N.
The recorded orders and Fermat's theorem give
\[
 q\equiv B^{w_c}\equiv B\pmod{d\lambda}.
\]
Changing the free lower dummy in cell j changes the actual packed rank by
\[
 -\Gamma B^j,\quad
 \Gamma=\rho^{1063}(q^2-1)
         [1+q(D_C+BD_R+B^{w_c})].
\]
The prime-unit table proves gcd(Gamma,dN)=1, since dN has no other primes.
Checking only a convenient five-adic residue would not suffice here.

### Boolean coverage lemma

Put T=N/lambda and C0=d lambda. Every residue modulo C0 T=dN is the sum
of a Boolean subset of
\[
 \{B^{2+kj}:0\le j<T\}\cup\{B^3\}.
\]
Indeed, the non-Wieferich certificate and binomial lifting give exact
order T for B^k modulo lambda^n and order1 modulo d. Its first T powers
are consequently exactly the T distinct residues1+C0 z modulo C0 T.
Given target r, normalize by B^-2. Choose epsilon in{0,1} such that
r B^-2-epsilon B is nonzero modulo lambda. Let a be its least residue
modulo C0. Then1<=a<C0<T and gcd(a,T)=1. Write the remaining target as
a+C0 u and solve
\[
 az_0+a(a-1)/2\equiv u\pmod T.
\]
Select the a distinct orbit entries with additive coordinates
z0,z0+1,...,z0+a-1 modulo T; include B^3 if epsilon=1. Their sum is the
required residue. The extra cell3 is outside the orbit cells2+k j because
k>1. No cell is selected twice.

Every selected position is safe: the maximum orbit index is
N-N/lambda-lambda+3; adding1or w_c stays below N because
w_c<N/lambda, and all positions are at least2. Thus none of the required
spatial/temporal translates wraps. Given the rank R0 with these dummies
zero, use the target(R0-d w_c)Gamma^-1. The new actual rank satisfies
R congruent d w_c modulo dN, precisely the temporal shift required by
X=2^R. Dummy changes preserve all decoded tiles and mask tests, including
the zero padding and the unique Start origin. The uniform slack inequalities
remain valid. This proves the new completeness controller, not just its
finite numerical prerequisites.

## Canonical parity promises and signed-family transfer

All d,w_c,h_c,N are odd. Write t=dN, so q=2^t. The canonical unique Start
makes C congruent1 modulo4. The native origin has no other zero-exponent
contribution; the temporal neighbor is not Start itself. With
\[
 S=(C-1)+qF,\quad M=q^2,\quad
 T_m=(M_CJ+1)+q(M_{F,n}J-1),
\]
the native acceptance masks give S AND T_m=0 and0<=S,T_m<M. Replicated
blocks do not overlap. Since M_C=2 mod4, adding1 to M_C J increases its
population by1; since M_(F,n)=4 mod8, subtracting1 from M_(F,n)J also
increases its population by1. Thus pc(T_m)=N pc(M_C)+N pc(M_(F,n))+2=t+2.
The exact source packing identity is
\[
 R=(M-S)(M-1)+T_m=(M-1-S)M+(S+T_m).
\]
Its high block is the2t-bit complement of S; the low disjoint sum adds
populations. Hence pc(R)=2t+pc(T_m)=3t+2. Also S=0 mod4 and T_m=3 mod4,
so R=3 mod4. These facts persist through rank tuning.

The inherited strict bound R>3q+1 in particular gives R>t. Canonical
X=2^R therefore has scale X/q=2^(R-t), a positive integer square because
R and t are odd. The canonical main Pell base a+2 is even. Its coordinate
c=psi_(a+2)(R) is odd, and the same strong rank m=cR gives the normalized
multiplier psi_(a+2)(m)/c^2 odd and positive. The ordinary Delta-scaled
multiplier is also odd since Delta=(a+2)^2-1 is odd. These statements are
the inherited Pell binomial/parity lemmas with new odd t, not new
five-power assumptions.

Finally the inherited authentic half-binomial kernel identity gives
v2(Y)=pc(R)-2=3t. Thus Y=s q^3 has positive odd s. This supplies the extra
completeness promise needed by the signed odd-scale families. Soundness
uses their unchanged weak transport bounds, Pell rank recovery and signed
root restoration; the four new ports satisfy the entire native interface
proved above. A coefficient transfer based only on these congruences,
without the rank controller and exact geometry, would be insufficient.

## From the compiler interface to the requested logical equivalence

The unchanged marked periodic tile language has a marked periodic tiling
if and only if the literal blank K215 computation halts. Soundness traces
its unique initialized head between reset rows; completeness pads a finite
halting computation with blank margins and halt rows. All these finite
arguments, the elementary Pell compiler, the controller above, and the
later polynomial eliminations are formalizable in ZFC. They yield
existence of a solution to any compatible fully instantiated skeleton if
and only if K215 halts, which the inherited finitary calibration identifies
with existence of a ZFC refutation. Taking negations gives in ZFC the
required equivalence between no solution and Con(ZFC). No appeal to the
soundness of Lean, Rocq, or ZFC itself is used to assert that equivalence.

The ordinary quartic31 is an exact positive-zero-set elimination from the
ordinary source interface. Therefore its transfer follows from this full
interface, not merely from a match between normalized polynomial ports.
Jones's parameter nu remains31 for that quartic, regardless of the much
smaller native radix exponent d. Changing d does not justify changing nu.

## Size and verification boundary

The exact raw minimal unsigned little-endian payload sizes are:

| Port | Bitlength | Bytes |
|---|---:|---:|
| beta |1064921|133116|
| K |1065043|133131|
| MC |1064921|133116|
| MF_source |1064922|133116|

The total is532479rawbytes, versus977220for packages25and27; d is45.476%
smaller than1953125. Deterministic gzip storage in the supplied build is
10466bytes. Compression is not a coefficient-height measure. The binding
manifest records every raw/gzip SHA-256. Both raw and compressed actual
coefficients are provided; none of these four ports remains a recipe only.

The builder and an independent checker verify all finite hypotheses,
including exact machine-to-tile equality, basis identities, native mask
populations, actual decoded constants, prime/order/lifting certificates,
and strict bounds. These finite audits supplement but do not replace the
universal mathematical proof or the inherited native/Pell calibration.
