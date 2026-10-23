---
title: Smaller Diophantine forms for ZFC consistency
author: OpenAI assisted research for Vladimir Reshetnikov and ProveIt
date: 23 October 2026
---

# Results and interpretation

This report combines the seven wave-4 submissions in ProveIt at commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`. It gives a small family of explicit
polynomials rather than claiming a single universal optimum. Number of
unknowns, permitted domain, total degree, arithmetic-circuit size, and
coefficient height measure different kinds of simplicity.

For every selected construction $P$ below, with the fixed coefficients and
quantifier domain stated for that construction, the conclusion is

$$\mathrm{ZFC}\vdash
 \bigl(\neg\exists\mathbf x\;P(\mathbf x)=0\bigr)
 \longleftrightarrow \mathrm{Con}(\mathrm{ZFC}).$$

This does not decide either side. The new arguments are ordinary mathematical
proofs formalizable in ZFC; they are not new Lean or Rocq certificates. The
finite audits check polynomial identities, arithmetic bounds, counts, fixed
coefficient bytes, and transcription. They do not replace the unbounded
Pell/compiler arguments or prove that the machine does not halt.

| Domain and form | Unknowns | Degree | Binary operations |
|:--|--:|:--|--:|
| Positive norm, cheapest evaluator | 12 | 1081 | **110** |
| Positive norm, recommended translation | 12 | **1041** | **111** |
| Positive norm, lowest degree here | 12 | **1022** | 124 |
| Positive Jones compression | 9 | $92324\cdot5^{32}+296$ | **1554** |
| Nonnegative Jones compression | 9 | $92324\cdot5^{32}+296$ | 1559 |
| Unrestricted integer compression | **14** | $813056\cdot5^{32}+2152$ | **1586** |
| Lower-degree integer compression | 15 | $406528\cdot5^{32}+2528$ | 1594 |
| Unrestricted integer quartic | **50** | **4** | See residual system |

The new four-port radix is $B=2^{1064921}$, compared with $2^{5^9}$
in the smallest wave-4 coefficient constructions. All four actual coefficients
occupy 532479 raw bytes. The new Jones index is $z=2^{4259933}$.
The fourteen-integer polynomial eliminates the enormous dense $y$ coefficient
altogether: its replacement is the single explicit power of two
$2^{99184317514300346374515978685}$.


The most useful concise presentation is the twelve-positive-variable form.
The nine-variable construction minimizes the natural-domain witness count
among the explicit forms considered here but pays for it with enormous
degree and some enormous coefficient recipes. The unrestricted-integer
construction serves a different purpose: its variables require no sign
restrictions. The quartic is a low-degree alternative, not a competitor on
variable count.

# Comparison with the new submissions

Packages 24--30 are mutually independent wave-4 submissions in the pinned
catalogue. Package 30 is our preceding construction. The following comparisons
use the packages' stated degree claims and independently recounted live
circuits where indicated in the accompanying review ledger.

| Package | Main contribution | Selected previous figures |
|:--|:--|:--|
| 24 | Tighter separating weights | 12 positive: degree 1069, 123 operations |
| 25 | Mixed-radix layout and external population padding | Coefficient radix $2^{5^9}$ |
| 26 | Ratio separation and parity copy tracks | 24 integers: degree 2432, 163 operations |
| 27 | Multivariate Horner evaluation and exact coefficient aliases | Nine positive: 1537 operations |
| 28 | Signed-divisor finalizer | Nine nonnegative: degree $93264\cdot5^{33}+288$ |
| 29 | Coprime Pell guards and intersective divisibility | 17 integers, 20607 operations |
| 30 | Quartic register elimination and scalar norm evaluation | 12 positive: 111 operations; positive quartic in 31 variables |

The new combinations are structural, not mere relabellings. They reuse
package 27's exact coefficient-expression aliases after reducing the Jones
parent to 31 variables; improve the signed majorants in package 28; replace
the positivity mechanism used by package 29; and translate the carrier in
package 30's inexpensive norm. The fixed compiler tuple is rebuilt coherently
from the smaller-layout ideas, not assembled by mixing ports from different
submissions.

No construction here is claimed to beat the inherited 67-operation single
polynomial or 59-operation system on operation count alone. Those remain
useful alternatives. A system whose equality comparisons are free is not
directly comparable to a single-polynomial residual circuit.

# Conventions and proof dependencies

We write $\mathbb N_0=\{0,1,2,\ldots\}$ and
$\mathbb Z_{>0}=\{1,2,\ldots\}$. All quantified variables are listed; every
other named expression is either an abbreviation or a fixed integer
coefficient. An arithmetic circuit uses only binary addition, subtraction,
and multiplication. Multiplication by a fixed numeral counts as a gate.
Shared subexpressions count once. Construction of fixed coefficients is not
included in the evaluation-gate count, and is documented separately.

The common proof chain is:

1. The fixed blank-tape run of K215 halts exactly when the specified syntactic
   ZFC proof system has a finite refutation.
2. The finite native tile language and its no-carry compiler describe exactly
   those halting runs.
3. The Pell arithmetic interface represents the compiler conditions.
4. The new polynomial transformations preserve existence of solutions in
   the explicitly stated domains.

The first three steps are inherited mathematical dependencies, with pinned
source proofs supplied or identified in the archive. The fourth step and the
new compiler-parameter adapter are proved here. The ZFC-provability claim is
obtained by formalizing the arithmetic arguments within ZFC, not by invoking
Lean's or Rocq's soundness inside ZFC.

Every arithmetic instance uses the same four ports
$\beta=B-1$, $K_0$, $M_C$, and $M_F$, where $M_F$ is the shifted source mask,
not the native high mask. Whole-tuple bindings are mandatory. A smaller
radix does not reduce the Jones parent-variable count $\nu$; that count is
31 because of the separate quartic reduction.

# How the smaller fixed coefficients are constructed


## The theorem and its exact scope

This construction combines three independently supplied ideas from the seven
wave-4 reports pinned at ProveIt commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`: package 25's mixed clause fields
and external zero tests, package 26's parity-separated copy tracks, and
package 24's Boolean controller for an arbitrary fixed odd factor. The
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
selector1. `build_coefficients.py` reconstructs all 943 tiles from all 430
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
Every nonconstant clause contribution is divisible by 1024. Consequently
the low ten bits of the clause sum are exactly n, even if there are
carries among higher fields. Disjointness with the low mask1022 forces
n=0 or n=1. Only after that conclusion do we analyze the 44 payload
fields. Each radix4 field is the sum of a Boolean tile/occupancy bit and
one Boolean copy/anchor bit, hence is 0,1,or2. No payload carry remains,
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
span1096, and the missing candidates1094 and 2194 prevent other pairs.
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
Its bitlength is 118, while4M+8 has bitlength120. The clause mask has
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
The maximum unshifted DC-product exponent is 5495+3296=8791; DR and
temporal products are lower. Hence every bit tested by Z, at 8792,...,8799,
is identically zero for all aligned native assignments. All positions
are below L. Adding these tests cannot harm completeness, and discarding
them cannot harm soundness. No convolution carry enters the padding.

The clause mask has 53 bits. The two clauses, twenty edge tests, two anchor
tests and low test contribute129 bits; Z `contributes7*119+27=860` bits.
Therefore
\[
 \operatorname{pc}(M_{F,n})=989,
 \quad\operatorname{pc}(M_C)=d-989,
 \quad M_C\equiv2\pmod4,
 \quad M_{F,n}\equiv4\pmod8.
\]
Both masks lie strictly between0 and B-1. These statements are checked on
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
so ord_d(B)=780 divides k, lambda=1 modulo 780, and
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
The precise pinned source is package 30/compiler/WANG943_COEFFICIENTS.md,
Section 2.4, copied here as sources/WANG943_LANGUAGE_AND_COMPILER.md;
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
The prime-unit table proves `gcd(Gamma,dN)=1,` since dN has no other primes.
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
N-N/lambda-lambda+3; adding1 or w_c stays below N because
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
makes C congruent1 modulo 4. The native origin has no other zero-exponent
contribution; the temporal neighbor is not Start itself. With
\[
 S=(C-1)+qF,\quad M=q^2,\quad
 T_m=(M_CJ+1)+q(M_{F,n}J-1),
\]
the native acceptance masks give S AND T_m=0 and 0<=S,T_m<M. Replicated
    blocks do not overlap. Since M_C=2 mod 4, adding1 to M_C J increases its
    population by 1; since M_(F,n)=4 mod 8, subtracting1 from M_(F,n)J also
increases its population by 1. Thus pc(T_m)=N pc(M_C)+N `pc(M_(F,n))+2=t+2.`
The exact source packing identity is
\[
 R=(M-S)(M-1)+T_m=(M-1-S)M+(S+T_m).
\]
Its high block is the 2t-bit complement of S; the low disjoint sum adds
populations. Hence `pc(R)=2t+pc(T_m)=3t+2.` Also S=0 mod 4 and T_m=3 mod 4,
so R=3 mod 4. These facts persist through rank tuning.

The inherited strict bound R>3q+1 in particular gives R>t. Canonical
    X=2^R therefore has scale X/q=2^(R-t), a positive integer square because
R and t are odd. The canonical main Pell base a+2 is even. Its coordinate
c=psi_(a+2)(R) is odd, and the same strong rank m=cR gives the normalized
multiplier `psi_(a+2)(m)/c^2` odd and positive. The ordinary Delta-scaled
multiplier is also odd since Delta=(a+2)^2-1 is odd. These statements are
the inherited Pell binomial/parity lemmas with new odd t, not new
five-power assumptions.

Finally the inherited authentic half-binomial kernel identity gives
`v2(Y)=pc(R)-2=3t.` Thus Y=s q^3 has positive odd s. This supplies the extra
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

The total is 532479 raw bytes, versus 977220 for packages 25and27; d is 45.476%
smaller than 1953125. Deterministic gzip storage in the supplied build is
10466 bytes. Compression is not a coefficient-height measure. The binding
manifest records every raw/gzip SHA-256. Both raw and compressed actual
coefficients are provided; none of these four ports remains a recipe only.

The builder and an independent checker verify all finite hypotheses,
including exact machine-to-tile equality, basis identities, native mask
populations, actual decoded constants, prime/order/lifting certificates,
and strict bounds. These finite audits supplement but do not replace the
universal mathematical proof or the inherited native/Pell calibration.


# A lower degree twelve variable norm


## Results

All six new circuits use twelve strictly positive integer unknowns and the same four **fixed**, coherently bound compiler coefficients. The single-equation degree/operation pairs are

| Carrier correction | Degree | Binary operations | System degree | System operations |
|---|---:|---:|---:|---:|
| no correction | 1081 | 110 | 1072 | 106 |
| b | **1041** | **111** | 1032 | 107 |
| `b+M(ac−ell)` | 1033 | 114 | 1024 | 110 |
| `b+M((a+2)c−ell)` | 1025 | 116 | 1016 | 112 |
| even-M, half-corrected | 1023 | 119 | 1014 | 115 |
| half-corrected plus auxiliary approximation | **1022** | **124** | 1013 | 120 |

All system entries have three equations. All operation counts charge every binary addition, subtraction and multiplication, including by a numeral, while sharing intermediate expressions. All degrees are exact, not merely syntactic bounds. The first row is the previous package 30 polynomial with a cheaper evaluator. The other rows are different polynomials whose zero sets are equisolvable, not claimed identical.

The principal recommendation is the 111-operation degree-1041 form: it preserves the operation count of package 30's degree-1081 form and improves package 24's degree-1069 form at 123 operations. The other rows describe genuine further degree/cost tradeoffs, not a global minimum. Twelve is not a minimum number of variables: the separate Jones nine-variable reductions have much larger degrees.

## Fixed compiler interface

Use one complete tuple (beta,K0,MC,MF) satisfying the normalized blank-K215 interface. In particular MF is the shifted high mask. No mixing of ports from different tuples is permitted. The release's binding supplies the selected four fixed integers and their finite recipe. The mathematical theorem below is uniform in any complete tuple satisfying that interface, including package 30's materialized Wang943 tuple.

The supplied variables are

    J,F,alpha,z,h,i,T,s,w,eta,zeta,t > 0.

Retain the following definitions from package 30:

    q=beta J+1, C=q−F−alpha, X=wq, Y=sq³, E=XY,
    k=eta+zeta, c=kY+eta, a=E+Y, H=4a+3,
    Delta=a²+H=(a+2)²−1,
    ell=EkY, A=1+ell(ell+k), G=1+Delta c², b0=X+ac,
    R=((q−1)(q−F)+alpha)(q²−1)+(MC+q MF)J,
    Nk=k−hE−R, Nt=(K0+w)C+q−F−z(q−1),
    I=ic², D=1+Delta I², Q=Delta(D−1)=(Delta I)²,
    d=Q−1, v=cT, b=c+RD,
    P=QDv², U=Qb², e=P+U−1, Baux=2Qvb,
    M0=k(I²+T²).

Every symbol other than the twelve supplied variables and four fixed ports is a polynomial abbreviation, not an additional quantified unknown.

For the first four rows put M=M0. For the last two put M=2M0. In every case let

    L=HM+1, W=b0+H(t+sigma).

The corrections are respectively

    sigma=0;
    sigma=b;
    sigma=b+M(ac−ell);
    sigma=b+M((a+2)c−ell);
    sigma=b+M0[2((a+2)c−ell)−k];
    sigma=b+M0[2((a+2)c−ell)−k]+v(a+2)I.

The fifth and sixth corrections can be written b+M delta, with

    delta=(a+2)c−ell−k/2,

but their displayed polynomial definitions contain no division: M=2M0 cancels the denominator. There are no variable exponents or rational coefficients.

## Complete scalar polynomial

Define computed expressions

    n=(HM)² A, dn=d n,
    HP=H²P, HU=H²U, He=HP+HU−H²,
    j=4 HP HU,
    Tr=2d(W²+L²G), Kr=d(W²−L²G), Kn=Kr²,
    AA=2(dn+He), cc=(dn−He)²−j,
    at=Tr−AA, bt=cc−Kn, co=16 dn j,
    vr=at(at Tr+2bt)−co,
    ur=bt²−at² Kn,
    N=ur²+Tr ur vr+Kn vr².

The promised polynomial and system are

    Nk Nt(1+N)−1=0,

or

    Nk=1, Nt=1, N=0.

This is a literal integer polynomial specified by a finite straight-line circuit. The JSON files enumerate all gates and all supplied variables. Squaring Kr rather than multiplying d² by (W²−L²G)² saves one binary multiplication in every variant. This is an exact ring identity.

## Why the scalar expression is the norm

For a formal argument x put

    Cx=d(x²+M²A)−e,
    F(x)=(Cx²+D Baux²−4d²x²M²A)²−4 Cx² D Baux².

Then

    N = H^16 F((W−L sqrt(G))/H) F((W+L sqrt(G))/H).

The right side is a polynomial. More explicitly N is the product of the eight factors

    d(W−HM tau−L g)² − H²e + H² Baux f,

where independently tau=±sqrt(A), g=±sqrt(G), f=±sqrt(D). Formal signs here are a polynomial device and do not assert independent Galois automorphisms.

To verify the scalar formula without field assumptions, use

    (C²+j−K)²−4jC²=(C²−K−j)²−4Kj.

After eliminating tau and f, the remaining polynomial in z has the shape

    [(d z²)²−AA(d z²)+cc]²−co(d z²).

For z=W±L sqrt(G), the two quantities x=d z² have sum Tr and product Kn. Reduction modulo x²−Tr x+Kn gives ur+vr x. Its norm is ur²+Tr ur vr+Kn vr². This proof works when any radicals specialize to zero, squares, or coincident quadratic fields.

## Uniform soundness under positive carrier corrections

The inherited package 30 proof, included as upstream/INHERITED_POSITIVE12_PROOF.md, establishes the following facts from Nk=Nt=epsilon, epsilon in {1,−1}, before recovering eliminated roots:

    q≥16, X≥q, Y≥q³, E=XY,
    3q<R<q⁴−2, k=R+epsilon+hE>E,
    kY<c<2kY,
    sqrt(G)−sqrt(A)>kY²,
    2(v sqrt(D)+b)<M0 kY²< M0 sqrt(A).

These are consequences of the entire authentic compiler tuple and transport interface, not assertions for arbitrary ports. They imply for any M≥M0 that every complex root x of F satisfies

    |x|<M sqrt(G),

and that F(0) is nonzero. The package 30 rational-recovery proof also needs

    d M² A>2Q(Dv²+b²),

which follows from these same inequalities and is preserved by replacing M0 with 2M0.

The new carrier leaves every one of these bounds unchanged. Its correction sigma is positive whenever nonzero. Indeed b>0. Also

    ac−ell = kY²+a eta >0,
    (a+2)c−ell >0,
    (a+2)c−ell−k/2 > k(Y²−1/2)>0.

Thus W>0 in every variant.

The identity Tr=2x0 and `Kn=x0²−4d²W²L²G,` with x0=d(W²+L²G), shows

    N ≡ (ur+x0 vr)² (mod 4).

At a solution of the product equation, 1+N cannot equal −1. The three integer factors are units, so N=0 and Nk=Nt=epsilon with a common unit sign. The three-equation system directly gives epsilon=1.

Choose a vanishing factor F((W−Lg)/H). If G is nonsquare, its two actual quadratic conjugates would provide two roots of F with distance 2L sqrt(G)/H, exceeding the common bound 2M sqrt(G) since L=HM+1. Thus g is integral and x=(W−Lg)/H is rational. Since W>0 and |x|<M sqrt(G), the selected g must be positive.

The inherited explicit rational-recovery formulas recover rational f and tau with f²=D and tau²=A; both are integers. The rational auxiliary root y=x−M tau obeys

    Q(vf−b)²−(Q−1)y²=1.

Because Q is an integer square, the rational Pell saturation lemma makes y integral. Hence x is integral. The congruence W≡b0 (mod H), unchanged by every new correction, gives g≡b0 (mod H), so gamma=(g−b0)/H is integral. It is positive because g>(a+1)c and c>X. The original normalized blank-machine interface, including its signed quotient extension, now recovers the accepting K215 computation and epsilon=1 exactly as before.

All denominators and zero cases in this recovery are covered by the inherited proof: Cx>0 for real x, Baux>0, d>0, M>0, and F(0)≠0. No new rationality assumption or sign change of an affine main-root expression is introduced.

## Constructive completeness and positivity of the translated variable

Take a canonical positive normalized blank-compiler witness, including positive g,tau,y,gamma. Package30 uses

    t_old=gamma+Mg+M tau+y.

Set t=t_old−sigma. This is an integer. Its defining identity gives W=Lg+H(M tau+y), so N=0 and Nk=Nt=1. It remains essential to prove t>0, rather than assuming a translation preserves the positive domain.

For sigma=b, M tau>b follows from the bound above, and t>0.

For sigma=b+M delta with delta=ac−ell or `delta=(a+2)c−ell` or its half-corrected counterpart, one has delta<g. Indeed ell/c>E/2>2, hence (a+2)c−ell<ac<g; the other deltas are smaller. Therefore

    t=gamma+M(g−delta)+M tau+y−b>0.

For the final auxiliary correction, use M=2M0 and

    (a+2)I<2 sqrt(D).

The latter follows from `D=1+((a+2)²−1)I²` and a+2≥2. Consequently

    M tau >4(v sqrt(D)+b)>v(a+2)I+b.

The same displayed formula for t, with the additional subtraction v(a+2)I, is still strictly positive. This proves completeness without enlarging a Pell index, imposing divisibility, or changing the canonical coefficient calibration.

Thus all six constructions are equisolvable with blank halting of K215. Composing with the inherited proof calibration and negating yields, in ZFC, that their absence of solutions in the stated positive domain is equivalent to Con(ZFC). This is a mathematical equivalence proof, not a consistency proof or a new Lean/Rocq certificate.

## Exact degrees by the eight factors

All four fixed coefficients have degree zero. Scale every supplied variable by a formal parameter Z and work in the Laurent-series field over the rational function field of those variables and fixed coefficients. The three positive-leading formal square roots exist because their leading forms are squares. This is only a device for reading the polynomial's homogeneous leading terms; no assumption about numerical square roots is made.

The common degrees are

    deg(E,H)=6, deg(Y)=4, deg(k)=1, deg(c)=5,
    deg(ell)=11, deg(A,G)=22, deg(I)=11, deg(D)=34,
    deg(Q,d)=46, deg(b)=38, deg(M0,M)=23.

Write a bar over a symbol for its leading homogeneous form. Then

    Hbar=4Ebar, cbar=kbar Ybar, ellbar=Ebar kbar Ybar,
    M0bar=kbar Ibar², bbar=Rbar Dbar,
    sqrt(D) has degree 17 and leading form Ebar Ibar.

The positive-leading expansions satisfy

    sqrt(G)−sqrt(A) = (ac−ell) + a term of degree 5,
    sqrt(G)−sqrt(A)−(ac−ell) has leading form 2cbar,
    sqrt(G)−sqrt(A)−((a+2)c−ell) has degree 1 and leading form −kbar/2,
    ((a+2)c−ell−k/2)−(sqrt(G)−sqrt(A))
        has degree−1 and leading form cbar/(2Ebar).

The first difference sqrt(G)−sqrt(A) has degree 9 and leading form kbar Ybar². These follow by expanding

    sqrt(G)=sqrt((a+2)² c²−c²+1),
    sqrt(A)=sqrt((ell+k/2)²+1−k²/4).

For example `sqrt(G)=(a+2)c−c/[2(a+2)]+lower-degree` terms, while `sqrt(A)=ell+k/2+terms` of degree at most−9. There is no vanishing leading coefficient for authentic beta>0.

For the b-based variants write

    Zsg,sa = W−Hb−HM sa sqrt(A)−L sg sqrt(G).

The corresponding factor becomes

    2dHb Zsg,sa + d Zsg,sa² − H²b² − H²QDv²
       + H² + sf H²Baux sqrt(D).

Here the last radical term has degree 119. The four (sa,sg) pairs give these degree lists, each repeated for the two f signs except in the last row:

| Correction | Degrees of Zsg,sa | Degrees of the eight factors | Sum |
|---|---|---|---:|
| b | 40, 40, 38, 38 | 130, 130, 130, 130, 128, 128, 128, 128 |1032|
| `b+M(ac−ell)` |40, 40, 38, 34|130, 130, 130, 130, 128, 128, 124, 124|1024|
| `b+M((a+2)c−ell)` |40, 40, 38, 30|130, 130, 130, 130, 128, 128, 120, 120|1016|
| half-corrected |40, 40, 38, 28|130, 130, 130, 130, 128, 128, 119, 119|1014|
| half-corrected plus auxiliary |40, 40, 38, 29|130, 130, 130, 130, 128, 128, 119, 118|1013|

In the first three rows each leading factor is 2 dbar Hbar bbar times its nonzero Z-leading form. In the half-corrected row the two special leading terms are the opposite nonzero f terms of degree 119.

For the last row the special branch is `(sa,sg)=(−1,+1).` Put f0=(a+2)I and `delta=(a+2)c−ell−k/2.` There

    Zsg,sa=H v f0 + H M(delta+sqrt(A)−sqrt(G)) + b0+Ht−sqrt(G).

Its degree 29 leading term is Hbar vbar fbar. At one f sign the two degree 119 contributions add; at the other they cancel. The next surviving degree 118 term is

    2 dbar Hbar² bbar Mbar cbar/(2Ebar),

which is nonzero. To check that no omitted term has degree 118 or greater: f0−sqrt(D) has degree 5, so the correction from replacing f0 by sqrt(D) contributes degree 107; b0+Ht−sqrt(G) has degree at most7; and all remaining square terms have degree at most104. Thus the final factor has exactly degree 118.

The product degree is the sum of the eight nonzero factor degrees in this Laurent field, and the product is the integer polynomial N. This proves all five exact norm degrees. For the unshifted baseline, the inherited proof gives N_top=Hbar^16 Ubar^8≠0 and degree 1072. Finally Nk and Nt have exact degrees 7 and 2 with nonzero leading forms, so the product polynomial has degree deg(N)+9. Every claim holds for the actual fixed tuple, not merely for generic coefficient values.

## Verification and scope

The new emitter contains no received executable imports. Its accompanying checker independently multiplies the eight radical factors using an eight-dimensional formal algebra; it checks positive, negative, zero, and degenerate inputs modulo several primes. Additional tests check the unit congruence, all gates and ports live, the factorization underlying the cheaper Kn evaluation, the exact degree claims by full finite-field univariate polynomial arithmetic, and synthetic radical-kernel witnesses. These finite diagnostics support the displayed identities but do not replace the mathematical proofs or verify the inherited compiler by finite testing.

Sources are pinned at commit `8c6eec9d19ef80538c8e61ff6e0180040583446a`. Package24 motivates deliberate leading-term cancellation; package 30 supplies the scalar trace norm and the separating bound. The new idea is translating the already quantified carrier by increasingly accurate polynomial approximations to the auxiliary and radical expressions while proving that the translated positive variable remains positive.


# A quartic in fifty unrestricted integers

The previous signed lift has 51 integer coordinates and 30 quadratic
residuals. Its only use of a packing register $G$ is

$$G=q(q-F)-C,\qquad
k-1-hE=LG+(M_C+qM_F)J,$$

where $q=\beta J+1$, $C=q-F-\alpha$, and the retained equations include
$L=q^2-1$ and $N=q(L+1)$. Delete $G$ and replace the packing equation by

$$k-1-hE=(q-F)(N-q)-CL+(M_C+qM_F)J.$$

It is still quadratic. The polynomial identity

$$L[q(q-F)-C]-[(q-F)(N-q)-CL]
  =(q-F)[q(L+1)-N]$$

proves an exact bijection of the integer zero sets: forget $G$ in one
direction, and restore $G=q(q-F)-C$ in the other. Unlike the positive-domain
version, no positivity proof for this restored register is needed.

The other 28 residuals, including all six positivity guards and the odd
scale, remain unchanged. Hence this reduction inherits exactly the source's
signed-domain soundness theorem. Taking the sum of the 29 squared residuals
gives a quartic in 50 unrestricted integers. Its coefficient of $\tau^4$ is
1, so its degree is exactly four for every admissible coefficient tuple.
The archive contains all residuals, a symbolic identity check, and a separate
independent reconstruction audit.

# Nine natural variables with a smaller signed finalizer

The local majorant MF below is unrelated to the fixed compiler mask port.


## Result, scope, and credits

Set L=5^32. There is an explicitly specified fixed polynomial with nine
nonnegative integer unknowns, exact total degree

    92324 L + 296 = 2149585634469985961914062796,

and a division-free circuit with 1,559 binary operations (692 additions,
22 subtractions, 845 multiplications). An equivalent polynomial over nine
strictly positive integer unknowns has 1,554 operations. Both have 80
nonliteral fixed leaves: the two index integers and 78 distinct nonliteral
coefficient recipes. The 402 original weighted coefficient records remain
the canonical coefficient specification.

These combine package 30's quartic31, package 27's multivariate Horner and
coefficient-recipe folding, and package 28's signed-divisor finalizer.
The new mathematical reductions are the signed quadratic majorants below,
which cause a provable leading cancellation and lower the degree, and
replacing u(2m−1) by um in the finalizer. Sources are pinned at
`8c6eec9d19ef80538c8e61ff6e0180040583446a`.

The claimed equivalence is a mathematical theorem formalizable in ZFC:
no solution in the stated domain if and only if Con(ZFC). It does not
prove consistency, decide existence, assert global minimality, or provide
a new proof-assistant certificate. It imports the explicit quartic/Pell
compiler interface, the coherent coefficient adapter, K215 calibration,
and the constructive parameterized Jones reduction. The new arithmetic
steps are proved below without assuming any radicand is a square.

## Fixed coefficient instance

The parent is the 31-positive-variable, 22-quadratic system in
quartic31.json. Its sum of squared residuals after replacing each positive
coordinate by n_i+1 is P31(x,n), with unused dummy input x. It has degree
four (coefficient of n_tau^4 is one) and P31(x, 0)≥1 (the residual EX+E−aX
is one at the all-ones tuple). The register-elimination proof from package
30 is retained as QUARTIC31_PROOF.md. All four coefficient ports are
replaced together by ../coefficients/payloads/COEFFICIENT_BINDING.json:

```text
beta=2^1064921−1, K=Kconstant, MC, and MF=MF_source.
```

The fourth is the shifted mask, never the native high mask. The complete coefficient adapter, not individual modular identities, establishes
that this tuple implements the ordinary positive compiler interface.

For each `alpha=(alpha_0,...,alpha_31)` of weight at most four, set
`c_alpha=(4−|alpha|)!` product_j alpha_j! times the coefficient of
x^alpha_0 n_1^alpha_1 ... n_31^alpha_31 in P31. Set
`expo(alpha)=sum_j` alpha_j 5^j. All 402 nonzero symbolic coefficients in the
four ports are listed in INDEX_CONSTANTS.json. The other coefficients
are zero. There are `binomial(36,4)=58,905` eligible alpha.

Let s=4,259,933 and z=2^s. INDEX_BOUND.json records a direct finite bound:
if c_alpha=sum_t a_t kappa^e_t and the four port bit lengths are b_j,
then |c_alpha| ≤ sum_t |a_t| 2^(sum_j b_j e_tj), and this last integer
plus one is strictly smaller than 2^s for every record. Here the bit
lengths are (1,064,921; 1,065,043; 1,064,921; 1,064,922). Thus

|c_alpha|+1 < z.

Define `e(T)=sum_{|alpha|≤4}` (z+c_alpha) `T^(L−expo(alpha)),`
y=e(2z), and the proof-interface constant `u_index=sum_{j=1}^31` (2z)^(5^j).
All exponents are positive integers, since `expo(alpha)≤4*5^31<L.`
Base-5 uniqueness gives distinct digit positions. Each digit z+c_alpha
lies strictly between one and 2z. Consequently

2(2z)^L ≤ y < (2z)^(L+1).

The left inequality uses c_0=24 P31(0)≥24. These facts are the explicit
Jones index hypotheses. The auxiliary u_index does not occur in the
polynomial. z is materialized as a 532,492-byte little-endian integer;
All 78 distinct nonliteral weighted coefficient leaves are also materialized
as signed-magnitude gzip files: 22,496,535 raw magnitude bytes compress to
2,427,559 bytes. Only y remains an explicit bounded recipe rather than a
materialized integer. The 402 canonical coefficient recipes remain available
for verification and aliases. No uncomputed recursively enumerable index
or unspecified integer is hidden in a coefficient.

## Complete polynomial description

The nine unknowns are epsilon,g0,h0,s0,w0,phi,i0,j0,n in N={0,1,...}.
Set `g=g0+1,h=h0+1,s=s0+1,w=w0+1,i=i0+1,j=j0+1,` and

```text
b=y+1+epsilon, B=b^5, q=B^L,
ell=sum_{k=1}^31 B^(5^k), lambda=sum_{k=0}^{4L−1}B^k,
N=q^16, Gcap=32 b B^(5^31).
```

Define the packed polynomial

```text
R=[g+e(B)q^3+ell q^5+
 (2(e(B)−z lambda)(1+B+g)^4+lambda B+lambda B q^4)q^7](N^2−N)
 +[q^3−b ell+ell+(B−2z)lambda q^3+(B−2)q^8](N^2−1).
```

Continue with

```text
U=N^2 w, Y=N^2 s, M=RY,
P=2M^2 U, K=R+1+h(P−1), A=M(U+1),
B1=2R+1, W1=bw, C=B1+W1+phi,
J=4A−5, Q=3W1 C−2(W1^2−1),
D=(A^2−1)C^2+1, E=i J D C^2,
F=(A^2−1)E^2+1, G=A+F(CD+1−A),
H=B1+jC, I=(G^2−1)H^2+1,
a0=(P^2−1)K^2+1, a1=DFI,
u=JF, v=QF+J(H−C),
m=K^2 Gcap−4(C−KY)^2 Gcap−8gK^2.
```

Every symbol is a polynomial abbreviation, not an additional unknown.
The letter u here is the signed divisor and is distinct from u_index.
Now put

```text
r=W1+phi, sigma=Y(U+1),
MD=sigma(RC+r^2), TC=CH+r^2,
MF=AE+1,
MI=F(D TC+2H^2+A^2)−A^2+1,
V0=PK+1, V1=MD MF MI+1,
Mdiv=Q^2+(H−C)^2+1,
Omega=u m,
Theta=u(n+Mdiv)+v−Omega(2Mdiv+V0 V1).
```

The requested polynomial is

```text
F9=(Theta^2−Omega^2(a0+V0^2 a1))^2
       −4 Omega^4 V0^2 a0 a1.
```

All powers have fixed nonnegative exponents. The JSON circuit expands each
power into binary multiplication gates. Its natural-domain filename is
nine31_signed_quadratic.json. For strictly positive unknowns substitute
each supplied variable by its value minus one; the optimized translated
circuit is nine31_signed_quadratic_positive.json.

## The packed integer cannot vanish

The index gives b≥2. Reduction modulo q gives

R ≡ (b−1)ell (mod q).

Indeed q divides N, and every term of the second bracket except
(1−b)ell is divisible by q. Moreover

0 < (b−1)ell ≤ (B−1)ell
     ≤ `(B−1)sum_{k=0}^{L−1}B^k` =q−1.

Hence R≠0 for every nonnegative assignment, before imposing F9=0.
Since U,Y≥1, sigma≥2 and A=R sigma imply |A|≥2.
Also P≥2R^2≥2 and
K≥R+P≥2R^2+R≥1. Thus J≠0, D≥1, AJ=A(4A−5)>0,
AE=iAJDC^2≥0, and F≥1. In particular u=JF≠0.

## Signed quadratic majorants

Here r=bw+phi≥2, C=2R+1+r, and H=(j+1)C−r.
The elementary identity

`2RC+r^2=4(R+(r+1)/4)^2+r^2−(r+1)^2/4`

is strictly positive when r≥2. It follows that RC+r^2>|RC|:
if RC≥0 its excess is r^2, and if RC<0 the excess is 2RC+r^2.
Since the quantities are integers, the excess is at least one. Therefore

```text
MD=sigma(RC+r^2) ≥ |AC|+sigma ≥ |AC|+2 ≥ sqrt(D).
```

In particular MD≥1. This statement permits either sign of R and C,
and C=0. No assumed sign of m or square condition was used.

Likewise

`2CH+r^2=2(j+1)C^2−2rC+r^2≥0`

by completing the square (j≥1). Thus TC=CH+r^2≥|CH|.
The coefficient j+1 is why this bound remains valid for negative C and
for H=0. Since AE≥0,

```text
MF=AE+1≥1,   F=(AE)^2−E^2+1≤MF^2.
```

Using G=FDC+F−A(F−1), integer inequalities |H|≤H^2 and
|AH|≤A^2+H^2 yield

|GH| ≤ FD TC+F `H^2+(F−1)(A^2+H^2).`

Adding |H|+1 and using |H|≤H^2 proves

```text
MI=FD TC+2F H^2+(F−1)A^2+1 ≥ |GH|+|H|+1.
```

Consequently MI≥1 and
`sqrt(|I|)≤sqrt(G^2H^2+H^2+1)≤|GH|+|H|+1≤MI.`
This includes negative I and both zero edge cases. Hence

V0,V1≥2,  sqrt(|a0|)≤V0−1,  sqrt(|a1|)≤V1−1.

For a0 use `1≤a0=(PK)^2−K^2+1≤(PK)^2.` For a1 multiply
D≤MD^2, F≤MF^2, |I|≤MI^2. These inequalities are unconditional
on the natural outer domain.

## A zero-margin-safe signed-divisor finalizer

Lemma. Suppose a0,a1,u,v,m,M,V0,V1 are integers with u≠0,
V0,V1≥2, sqrt(|at|)≤Vt−1, M≥1, and |v/u|≤M−1.
For n≥0 set Omega=um and
`Theta=u(n+M)+v−Omega(2M+V0V1).` Then the polynomial in Section 7.3
has a nonnegative integer n making it zero if and only if a0,a1
are integer squares, u divides v, and m>0.

Proof. If m=0, Omega=0 and `Theta/u=n+M+v/u≥n+1>0.`
Thus the polynomial is Theta^4≠0. Otherwise Omega≠0. Choose complex
square roots r0^2=a0, r1^2=a1. The polynomial factors exactly as
product_{epsilon,delta in {−1,1}}[Theta−Omega(epsilon r0+delta V0r1)].
A zero allows signs to be absorbed so that `s=r0+V0r1=Theta/Omega`
is rational. If s≠0 then 2s `r0=s^2+a0−V0^2a1` makes both roots
rational and hence integers (their squares are integers). If s=0,
`|r1|=|r0|/V0≤(V0−1)/V0<1` forces the integer a1 to have absolute
value below one, so a1=a0=0. This avoids any independence assumption
on quadratic fields and handles negative radicands.

Let `Z=2M+V0V1+r0+V0r1.` The root bounds give Z≥2M+1>0.
The vanishing factor becomes n+M+v/u=mZ. Its left side is positive,
so m>0. Its right side is integral, so v/u is integral and u divides v.
Conversely choose integer roots and let n=mZ−M−v/u. Then n is an
integer and n≥2M+1−M−|v/u|≥2. Its factor vanishes. QED.

For the Jones application, `|v/u|=|Q/J+(H−C)/F|`
`≤|Q|+|H−C|≤Q^2+(H−C)^2=Mdiv−1.` The lemma therefore applies.
The choice Omega=um saves one multiplication and one subtraction relative
to u(2m−1); the extra m=0 case above is essential.

## Equivalence to consistency

For each fixed eight-coordinate outer assignment, the last lemma identifies
existence of n with exactly the inherited four Jones ratio conditions:
a0 and a1 squares, JF dividing QF+J(H−C), and m>0.
The constructive parameterized Jones packing and ratio theorems then
identify existence of all nine coordinates with a zero of P31(1,·).
This uses nu=31, not the separate public existence theorem normalized
at nu=58. The explicit index in Section 7.2 satisfies the former theorem's
hypotheses. The quartic31 algebraic reduction and complete coefficient
adapter identify those zeros with a finite blank K215 halting computation;
the K215 calibration identifies this with a finite ZFC refutation.
All transformations concern finite arithmetic objects and are provable
in ZFC. Negating their existence equivalence gives precisely

    ZFC proves: [no N^9 solution to F9=0] iff Con(ZFC).

The positive-domain translated circuit has the same conclusion by the
bijection between N and positive integers. Neither statement is valid
merely by reading the same nine-variable formula over unrestricted Z.

## Exact degree despite a top cancellation

Degree counts the nine unknowns, with fixed coefficients of degree zero.
On the diagonal where every unknown is t, relevant degrees and leaders
are as follows (all leaders are independent of fixed coefficients):

R:235L, 1; A:555L+2,1; C:235L, 2;
D:1580L+4,4; E:2605L+7,2^6; `F:6320L+18,2^12;`
`G:8135L+22,2^15;` H:235L+1,2; `I:16740L+46,2^32;`
MD:790L+2,2; MF:3160L+9,2^6; `MI:8370L+23,2^16;`
V0:1900L+7,4; `V1:12320L+34,2^23;`
`Omega:9096L+31,−2^23;` `Theta:23316L+72,2^48.`

The naive top terms in Theta^2−Omega^2 V0^2 a1 cancel exactly.
To prove the true degree, use the following polynomial identities:

```text
DeltaD=MD^2−D=2AC sigma r^2+sigma^2 r^4+C^2−1;
DeltaF=MF^2−F=E^2+2AE;
DeltaIRoot=MI−GH=FD r^2+2FH^2+(F−1)A^2+1−FH+A(F−1)H;
DeltaI=MI^2−I=DeltaIRoot(MI+GH)+H^2−1;
Delta=V1^2−a1=DeltaD MF^2 MI^2+D DeltaF MI^2+DF DeltaI+2MD MF MI+1.
```

The leading term of DeltaD has degree 1110L+8 and coefficient4.
The first summand in Delta therefore strictly dominates, giving
Delta degree 24170L+72 and `coefficient2^46.` Let
`E0=u(n+Mdiv)+v−2Omega` Mdiv. Then the exact rewritten inner expression is

E0^2−2E0 Omega V0 V1+Omega^2 V0^2 Delta−Omega^2 a0.

Its unique leading summand has degree 46162L+148 and `coefficient2^96.`
After squaring, the final subtractand 4Omega^4 V0^2 a0 a1 has smaller
degree. Thus the exact degree is 92324L+296 and uniform leading coefficient
2^192≠0. This also proves exact total degree: these formulas give matching
multivariate upper bounds and nonzero diagonal leading terms.
The same degree and leader survive shifts to the strictly positive domain.

## Circuit identities and accounting

Set t_j=B^(5^j), `v_j=B^(5^31−5^j),` with v_31=1 and
    v_j=t_j^4 v_{j+1}. With weights `w=(t_31,v_0,...,v_31),`

```text
e(B)=t_31[z h4(w)+sum_alpha c_alpha t_31^(4−|alpha|) product_j v_j^alpha_j].
```

The complete homogeneous polynomial h4 is evaluated by the ascending
recurrence h_k←h_k+w h_{k−1}, k=1,...,4. The correction is evaluated
by recursive multivariate Horner, selecting a variable and splitting each
term into one divisible by that variable and one not. Every step is exact
distributivity. The deterministic heuristic chooses maximum incidence,
then exponent mass, then a fixed permuted tie-break. A finite search of
100 such heuristics selected8; no optimality is claimed.

Lambda is evaluated without division as
`product_{j=0}^31[1+t_j(1+t_j)(1+t_j^2)](1+q)(1+q^2).`
Identical coefficient recipes become one leaf and literal recipes become
literal integers. Each of the 402 alias identities is checked exactly as
an identity in the four ports, not numerically guessed. Shared gates and
literal constant folding are allowed; every binary addition, subtraction,
or multiplication, including scaling by a numeral, is charged. Registers,
references, and fixed integer leaves are free. Coefficient height is a
separate metric, and the bitlength of y is not hidden in a gate count.

## Reproducible checks and limitations

build_signed_nine.py regenerates the four supplied structured/new circuits.
check_degree.py checks cancellation-free exact leaders.
check_signed_nine.py compares inherited core named quantities and exact
rewrite identities modulo three primes, verifies all 402 coefficient alias
identities, checks three full 58,905-term digit sums, 6,144 bound assignments
including negative `R,C=0,H=0,86,016` bounded finalizer assignments, and 468
explicit finalizer completeness witnesses. These are implementation
regressions, not proofs that the final Diophantine equation has no solution.
check_actual_index.py reads the authentic four coefficient files, verifies
hashes/bitlengths, evaluates every coefficient bound on actual integers,
and checks all 78 stored signed-magnitude coefficient payloads against their
exact recipes, then records actual-instance modular outputs.
materialize_fixed_leaves.py constructs those payloads. bind_index.py constructs the
finite bound and materialized z. All programs are newly authored or carried
forward from our preceding independently authored audit, not executed
copies of received upstream programs.


# Fourteen unrestricted integers


These are the recommended signed constructions of this package. Earlier
sixteen/seventeen-variable intermediate constructions are superseded here.
Both equations below have unsolvability provably
equivalent in ZFC to Con(ZFC). The proofs are mathematical, not newly compiled
Lean or Rocq certificates. No global minimum is asserted.

## Shared definitions and coefficients

Use the exact Jones source registers and three-root finalizer in
the shared lemmas below. The source quartic has 31 positive variables; L=5^32.
Every weighted coefficient is fixed by INDEX_CONSTANTS.json, using the whole
coefficient tuple in ../coefficients/payloads/COEFFICIENT_BINDING.json.
The new index is z=2^4259933. Set

```text
 Bodd=2(2z)^(L+1)=2^[1+4259934(L+1)].
```

This is a fixed integer, not an unknown. Its exponent is odd, since L+1
is even. The index theorem gives `y=e_*(2z)<(2z)^(L+1)<Bodd.`
Bodd and y are specified by exact bounded recipes, not materialized as
full binary strings. All four native coefficient ports and z are materialized.

## The fourteen-variable polynomial

The unknowns are exactly

```text
 (epsilon,g0,h,s0,wroot,phi,i,j,z1,z2,z3,z4,residue,normroot) in Z^14.
```

In the Jones source definitions set

```text
 b=Bodd epsilon^2, w=wroot^2,
 g=g0+1, s=s0+1; h,i,j are unrestricted coordinates directly.
```

The other registers through a0,a1,m,Ddiv,Tdiv are unchanged. Guard only
`x1,x2,x3=(g0,s0,phi):`

```text
 d_r=3x_r+2 (r=1,2,3), d4=3m-1,
 C0=1, B_r=1+4d_r C_(r-1) z_r^2, C_r=C_(r-1)B_r,
 Cstar=C4, Z=epsilon wroot i z1 z2 z3 z4.
```

Define the complete finalizer by

```text
 S=Z Ddiv^5, r=Tdiv+Ddiv residue,
 T=(r^3-Ddiv^2 r-Ddiv^3)(r^2+23Ddiv^2),
 w1=Cstar, w2=Cstar(P^2+K^2+2), X=S normroot-T,
 A0=S^2 Cstar, A1=S^2 w1^2 a0, A2=S^2 w2^2 a1,
 V=X^2+A2-A0-A1, W=V^2+4X^2 A2-4A0A1.
```

The equation is

                    F14=W^2-16V^2 X^2 A2=0.

This is fully specified by signed14.json, with 1586 binary operations:
684 additions, 26 subtractions, 876 multiplications. Its exact degree is

                    813056*5^32+2152.

There are 80 nonliteral fixed leaves after aliases and integer constants
are folded. Polynomial register abbreviations do not increase the 14
quantified-variable count.

## Why the square w restriction is complete

The source Ratio.exists_B25core (pinned Ratio.lean.txt, necessity section)
chooses, for b=2^k,

                    w=2^(2R+1-k).

The exponent is strictly positive: b<=R implies `k<2^k=b<=R<2R+1.`
The cofinal packing proof permits arbitrarily large exponents k of either
parity. In Master3.USys_of_mem lines 312--320, the selected exponent is used
only to infer b>xy and that every quartic witness coordinate is below b;
the rest of the proof uses these inequalities and b=2^k, not the special
formula for that exponent. NineReduce propagates the same b unchanged. Our Bodd has odd exponent a, and choosing epsilon=2^t gives
k=a+2t odd. Therefore 2R+1-k is even and the canonical w is a positive
square. Choose

    wroot=2^((2R+1-k)/2).

All subsequent constructions in
exists_B25core and NineRatio.ratio_complete preserve that w.
This argument uses the exact canonical w formula; it does not assert that
arbitrary Pell witnesses may be required to be squares.

For soundness, the finalizer implies S!=0, hence epsilon,wroot,i and all
z_r are nonzero. Consequently b>Bodd-1>y and w>0. The guard stack gives
g,s positive, phi>=0 and m>0. The h-positivity proof in the shared lemmas below
uses only these statements, not any j condition, so h>0 as before.

## Why the j guard is unnecessary

The signed-H proof included below extends the product-Pell
soundness lemma to arbitrary signed H=B+jC. Its hypotheses hold here:
`R>0,A>1,B=2R+1>1` is `odd,C=B+bw+phi>=B,J=4A-5>0` and i!=0.
The quotient condition JF|QF+J(H-C), together with gcd(J,F)=1,
gives J|Q and F|H-C. The signed-H lemma recovers C=psi_A(B), even
when j is negative. Its key step reflects a negative Pell index modulo
    4t1, using `M_A^(4t1)=identity` modulo chi_A(t1).

The original positive product-Pell completeness theorem then supplies
fresh positive i',j' for the same A,B,C,J. Thus D F' I' is square and
F'|H'-C. Since J|Q is unchanged, JF'|QF'+J(H'-C) follows.
Neither a0 nor m depends on i,j. Therefore the recovered signed solution
can be replaced by an ordinary positive-i,positive-j Jones ratio solution.
All other coordinates, including the restricted square w, are unchanged.
The ordinary ratio soundness theorem applies.

Conversely, the cofinal odd-exponent packing construction gives a ratio
solution with square w and positive i,j. The linear-prefix stack supplies
four nonzero guard variables, the intersective lemma supplies residue,
and the three-root finalizer supplies normroot. These arguments prove both
directions of the refutation/solution equivalence. Negation gives

 ZFC proves (there is no integer zero of F14) iff Con(ZFC).

## A lower-degree equation in fifteen integers

Keep b=y+1+epsilon, with epsilon guarded rather than squared, but still
set w=wroot^2 and release j. Guard the four coordinates
(epsilon,g0,s0,phi) and m, using five z variables. Set
Z=wroot i z1 z2 z3 z4 z5. The remaining definitions are unchanged.
This gives signed15_linear.json, with 1594 operations
(688 additions, 26 subtractions, 880 multiplications) and degree

                    406528*5^32+2528.

Completeness chooses a sufficiently large odd k in the free-base packing
proof, then `epsilon=2^k-y-1>=0.` The canonical w is again a square.
Soundness needs only b>y and w>0; it does not require an independently
asserted parity of k. Using h,i,j directly rather than h0+1,i0+1,j0+1 is an affine bijection
on unrestricted integers and saves three gates without changing degree.
This form has roughly half the degree of F14,
at the cost of one additional integer variable and eight operations.

## Exact degree certificates

For F14 the named degrees are:

 m:4442L+14; Cstar:4442L+58; Ddiv:13750L+29;
 S:68750L+152; w2:8242L+68; A2:203264L+538.

A2 strictly dominates X^2,A0,A1, and the second term in the final
subtraction has smaller degree than A2^4. On the diagonal its leading
coefficient is `2^832*12^120*Bodd^(406528L+8),` which is nonzero.
For F15linear the corresponding output coefficient is 2^832\*12^248,
and `deg(A2)=101632L+632.` These give the stated exact degrees for the
actual coefficients, not merely generic degree bounds. The independent
modular checks supplement these exact mathematical leading-term arguments.

## Evidence and limitations

check_signed_forms.py regenerates each circuit from inert source data,
checks source-register equality on signed inputs, and independently computes
the finalizer as an8-by-8 multiplication-matrix determinant. Finite guard,
intersectivity and divisibility tests are included. The universal proofs,
not the finite tests, establish equivalence. No actual ZFC refutation or
halting witness is searched for, and no consistency claim is made.

Further reductions would require proving a further sign restriction is
redundant or a further canonical witness lies in a polynomially parameterized
subfamily. Neither arbitrary square substitution nor finite testing would
justify such a step.

## Complete shared Jones source registers

```text
B=b^5, q=B^L, ell=sum_{r=1}^{31}B^(5^r),
lambda=sum_{r=0}^{4L-1}B^r, e=e_*(B), theta=B-2z,
N=q^16, Gcap=32b B^(5^31),
```

```text
R=[g+e q^3+ell q^5+
   (2(e-z lambda)(1+B+g)^4+lambda B+lambda B q^4)q^7](N^2-N)
  +[q^3-b ell+ell+theta lambda q^3+(B-2)q^8](N^2-1).
```

```text
U=N^2w, Y=N^2s, M=RY, P=2M^2U,
K=R+1+h(P-1), A=M(U+1), B1=2R+1, W1=bw,
C=B1+W1+phi, J=4A-5, Q=3W1 C-2(W1^2-1),
D=(A^2-1)C^2+1, E=iJDC^2, F=(A^2-1)E^2+1,
Gp=A+F(CD+1-A), H=B1+jC, I=(Gp^2-1)H^2+1,
a0=(P^2-1)K^2+1, a1=DFI,
m=K^2 Gcap-4(C-KY)^2 Gcap-8gK^2,
Ddiv=JF, Tdiv=QF+J(H-C).
```


## Shared algebraic lemmas

## Linear-prefix square stack

For any integer assignment, every B_r and C_r is 1mod4, hence nonzero,
and `gcd(B_r,C_(r-1))=1.` Thus all factors B_r are pairwise coprime.
If all z_r!=0 and Cstar is an integer square, each |B_r| is a square.
As B_r=1mod4, a negative B_r cannot be a signed negative square, so every
B_r is a positive square. All prefix C_r are consequently positive.
If any d_r<0, its factor would be <=-3, a contradiction. No d_r vanishes
because d_r=2mod3. Hence d_r>0: all guarded x_j>=0 and m>0.

Conversely, suppose these inequalities hold. Inductively C_(r-1) is a
positive square. The positive integer d_r is 2mod3 and nonsquare, so
d_r C_(r-1) is nonsquare. Choose a nontrivial Pell solution
u^2-d_r C_(r-1) v^2=1 with v even (a suitable positive power of a Pell
unit has even second coordinate). Put z_r=v/2!=0. Then B_r=u^2 and
C_r is a positive square. This constructs the guard list.

When S!=0, all z_r!=0. Each d_r is nonzero and each prefix nonzero,
so B_r!=1; since B_r=1mod4, |B_r|>=3. Therefore |Cstar|>=3^r>1, where r is the number of guards.
This observation permits the smaller signed separation weight w1=Cstar.

## Divisibility and nonvanishing

For every integer base assignment Ddiv!=0. Indeed J=4A-5!=0. If F=0,
then (A^2-1)E^2=-1 forces A=0,E=+/-1, but E=iJDC^2 is then divisible
by 5, impossible.

The polynomial `Pi(t)=(t^3-t-1)(t^2+23)` has no rational root and has a
root modulo every positive integer. The cubic is monic and neither1
nor-1 is a root; the quadratic has no real root. For odd primes p!=23,
either the cubic has a simple root, or it is an irreducible cubic whose
Frobenius three-cycle fixes a square root of its discriminant -23;
then the quadratic has a simple root. Lift by Hensel. At23 the cubic's
root3 is simple. At2 the quadratic lifts because -23=1mod8. Apply CRT.

For nonzero D and arbitrary integer T0,Z,

 D|T0 and Z!=0  iff  exists v: ZD^5 | `(r^3-D^2r-D^3)(r^2+23D^2),`
     r=T0+Dv.

The right-hand polynomial never vanishes, since it equals D^5 Pi(T0/D+v).
If D|T0, intersectivity supplies v modulo |Z|. Conversely Z=0 would
force a zero. If p-adic valuations satisfy `v_p(T0)=beta<alpha=v_p(D),`
then v_p(r)=beta, the cubic and quadratic factors have valuations3beta
and 2beta respectively, so their product has valuation5beta<5alpha,
contradicting divisibility byD^5. Apply with D=Ddiv,T0=Tdiv.

## Three-root finalizer with signed small weights

The polynomial F is identically the product of the eight factors
X-S(e0 sqrt(Cstar)+e1 w1 sqrt(a0)+e2 w2 sqrt(a1)), e_r in{-1,1}.
Complex square roots are allowed in this formal identity. T is never zero.
If S=0, then F=T^8!=0. Hence every zero has S!=0.

On this locus, `|w1|=|Cstar|>sqrt(|Cstar|).` Also, for arbitrary real P,K,
`sqrt(|(P^2-1)K^2+1|)<=P^2+K^2+1.` Therefore
|w2|>sqrt(|Cstar|)+|w1|sqrt(|a0|).
Distinct sign patterns of the nonzero roots have distinct sums: the
largest differing root has magnitude at least1 (its square is a nonzero
integer), and its weighted contribution dominates all earlier ones.
If F=0, one sum equals normroot-T/S, a rational number. Every Galois
automorphism of the field generated by these roots changes their signs;
the separation forces it to fix each root. Each root is rational, and
then integer since its square is integer. Thus Cstar,a0,a1 are squares
and S|T. This argument does not assume independent square classes and
works for initially negative radicands. Conversely those square and
    divisibility conditions allow `normroot=T/S+r0+w1r1+w2r2.`

## Removing the h and i sign restrictions

The guards and square w give g,s,w positive, phi>=0,m>0, b>y and i!=0.
Replacing i by |i| changes none of a0,a1,Ddiv,Tdiv,m: i occurs through
E and thereafter only E^2. Hence i can be taken positive.

To show h>0, m>0 implies K!=0, g<Gcap/8=4b B^(5^31), and
4(C-KY)^2<K^2. Since b>y, B>2z and B>=32. With t=5^31,
1+B+g < B^(t+2)<=q and b ell<q. These bounds make both brackets
defining R positive (the positive lambda B q^4 absorbs
2z `lambda(1+B+g)^4).` Thus R>=N^2-N>=2. Consequently C>0,Y,U>=1,
P>=2R^2>R+2. The strict approximation forces K>0. If h<=0, then
    1<=K<=R+1<P. K=1 would imply P-1|R, impossible. For2<=K<P,
`(PK-1)^2<(P^2-1)K^2+1<(PK)^2,` contradicting a0 square. Hence h>=1.


## Removing the Jones j-positivity guard by signed index reflection

Let A,B,C,J be positive integers with A>1, B>1, B<=C, J>0,
and assume 2B<=C or B is odd. Let i be any nonzero integer and j any
integer. Define

```text
D=(A^2-1)C^2+1, E=i J D C^2, F=(A^2-1)E^2+1,
G=A+F(CD+1-A), H=B+jC, I=(G^2-1)H^2+1.
```

Suppose DFI is an integer square and F divides H-C. Then
C=psi_A(B), where psi_A is the Pell sine sequence with recurrence
    psi_A(n+2)=2A psi_A(n+1)-psi_A(n), psi_A(0)=0, psi_A(1)=1.

## Proof

Replacing i by |i| leaves D,F,G,H,I unchanged. Thus E may be assumed
positive. The standard product-Pell argument gives D,F,I positive,
G>1, and pairwise coprime D,F,I. Indeed F=1 modulo D, G=1 modulo D,
I=1 modulo D, G=A modulo F, and H=C modulo F imply I=D modulo F.
Hence all three factors are positive squares.

The Pell parametrization supplies nonnegative indices t0,t1,t2 with
C=psi_A(t0), E=psi_A(t1), |H|=psi_G(t2). As in the pinned
    ProductPell proof, C^2|E implies C|t1; also t1>=2, 1<=t0<=t1,
and F=chi_A(t1)^2. Set k=chi_A(t1)>0.

If H>=0, the original proof applies verbatim: H=psi_G(t2),
psi_A(t2)=C modulo k, and t2=B modulo C. The usual Pell
index-congruence lemma gives B=t0 or B=-t0 modulo C, and the
productPell_index lemma gives C=psi_A(B).

If H<0, then psi_A(t2)=-C modulo k. Let
`M=[[2A,-1],[1,0]].` The determinant of M is 1 and the trace of M^t1
is 2chi_A(t1)=0 modulo k. Cayley-Hamilton therefore gives
M^(2t1)=-Id modulo k, and M^(4t1)=Id modulo k. Choose a positive
integer Q large enough that n=4t1 Q-t2>=0. The inverse-matrix
identity for the Pell sine coordinate gives

    psi_A(n)=-psi_A(t2)=C modulo k.

Since G=1 modulo C, psi_G(t2)=t2 modulo C. Thus H=-psi_G(t2)
implies -t2=B modulo C. As C|t1, the reflected index satisfies
n=-t2=B modulo C. Apply the same ordinary index-congruence lemma
now to n in place of t2. Its conclusions are n=t0 or n=-t0
modulo C, so again B=t0 or B=-t0 modulo C, and the unchanged
productPell_index conclusion follows. This proof does not require
j>=0 or H>=0. The case H=0 causes no issue for the nonnegative
branch; alternatively F>C and F|H-C exclude it.

## Application to the Jones ratio conditions

Retain the guards on g,s,w,phi and the positivity consequence for h.
They imply `R>0,A>1,C>=B=2R+1>1,` with B odd. Keep i!=0 but drop
the guard j0>=0: put j=j0+1 with j0 an arbitrary integer.
From JF|QF+J(H-C) and gcd(J,F)=1, derive J|Q and F|H-C.
The signed-H lemma yields C=psi_A(B). The standard constructive
product-Pell theorem then supplies fresh positive i',j' for these
same A,B,C,J. Their F',H' satisfy F'|H'-C. Together with J|Q this
restores JF'|QF'+J(H'-C), and D F' I' is square. The radicand a0
and margin m do not depend on i,j, so they remain unchanged.
Thus any signed-j ratio solution can be replaced by a genuine
positive-j ratio solution. Completeness is immediate because the
original positive witnesses are still allowed.

This removes one guard witness from the coprime Pell stack. It uses
ordinary Pell theory and matrix arithmetic, not a newly compiled
formal theorem. The exact source proof inspected is
Computability/HilbertTenthProblem/Lean/Diophantine/Paper1982/ProductPell.lean,
psi_of_ProductPellConds and productPell_index, at commit
`8c6eec9d19ef80538c8e61ff6e0180040583446a`.


# Verification and reproducibility

The archive records a pinned source ledger and exact arithmetic circuits.
Its root verifier first checks immutable file hashes, then runs the new
checks in a temporary copy. Source programs received from the repository
are preserved as inert text or data; no received program is executed by the
release verifier. The archive includes the symbolic identities and full
proof text rather than presenting random evaluation as proof.

The finite checks include independent reconstruction of the coefficient
payloads and controller hypotheses; exact live-gate counts; the quartic
register identity; formal multiplication of the radical norm factors;
formal-Laurent degree checks for all positive variants; independent
three-root determinant evaluation; and signed Pell matrix-reflection
identities. Complete machine-readable receipts and a check plan are included.

Some bounded signed-Pell searches have no admissible hits. These are not
reported as evidence for a universal theorem; the mathematical reflection
proof establishes that result. Actual fixed-coefficient evaluations and
uniform nonzero leading-term proofs are distinguished from diagnostic
modular specializations.

A positive computational result here means that the stated finite check
passed. It is not a successful search for a solution of the Con(ZFC)
equation. There is no such search or witness claimed in this report.

# Further research questions

1. Can the remaining signed Pell guards be reduced without restricting the
   Jones ratio witnesses to a family lacking a completeness theorem?
2. Can a general formal theorem expose the cofinal choice of Jones radix,
   so that square-scaled substitutions no longer require inspection of the
   existing completeness proof?
3. Can the carrier translations be optimized systematically, with a symbolic
   valuation certificate tracking every radical branch and its cancellation?
4. Can another quartic register be eliminated by an identity modulo retained
   equations, rather than by direct substitution that raises degree?
5. Can the new exact coefficient layout and actual-rank controller be
   formalized once as a reusable compiler interface?
6. Can coefficient expressions be reduced further without concealing their
   materialization cost or changing the meaning of the operation metric?
7. Can an explicit instantiation of a smaller unrestricted-integer universal
   representation improve this archive's count while retaining a complete
   coefficient recipe and a manageable proof?

# Sources attribution and limitations

The primary source is the pinned ProveIt catalogue and its packages 24--30:

<https://github.com/VladimirReshetnikov/ProveIt/tree/8c6eec9d19ef80538c8e61ff6e0180040583446a/SetTheory/Cardinals/docs/reports/hilbert-tenth-problem/con-zfc-diophantine-forms>

The source ledgers identify exact files and Git blob hashes. The mathematical
contributions of the earlier packages, Jones's reduction, the K215
construction, and the compiler ancestry remain credited in the retained
notices. This report and its newly authored checks are OpenAI-assisted
research prepared for Vladimir Reshetnikov's ProveIt project. Independent
audits described here are separate checks within that collaboration, not
external human endorsements.

New material follows ProveIt's MIT No Attribution terms. Inherited third-party
material retains its own licence; the Wade licence and K215 attribution notice
are included. Historical source notices may name paths in their original
packages. The active release paths and coefficient bindings are defined by
the root README and binding manifests, not by those historical references.

Sun's 2026 preprint states in Theorem 1.1 a representation of every recursively
enumerable subset of the natural numbers using ten unrestricted integer
witnesses. This prevents any interpretation of our count as a global
fewest-variable record. Our contribution is an explicitly instantiated
polynomial with a fixed coefficient recipe and a detailed dependency chain;
we have not instantiated Sun's general construction for the particular
ZFC-refutation predicate. See <https://arxiv.org/html/2609.01594v2> and the
archive's scope note for the exact distinction. We have not independently
audited the complete proof of that external preprint.

There is no global minimality theorem, proof of Con(ZFC), new kernel-checked
end-to-end result, or claim that every large fixed numeral is materialized.
