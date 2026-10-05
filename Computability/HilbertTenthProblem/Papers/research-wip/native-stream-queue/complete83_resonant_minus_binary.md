# Binary completion in the resonant minus family

For every fixed authentic original five-adic compiler using the minus shape, the resonant selectors supplied by the fixed-prime and subpower constructions satisfy the binary population condition on a sufficiently large tail. Together with their already proved odd-scale construction, this gives complete positive zeros of the unchanged shared-projection83 source on that tail. The ordinary inputs are constructed, not prescribed; this note does not prove that any of them is rejected by the compiled program or that83 is universal.

The new mechanism is an exact source residue followed by a joint population estimate for seven correlated periodic words. Root supplied the selector-residue observation and independently helped check the Mersenne nonvanishing bound. No circuit is changed. All source/compiler/native/Pell conclusions invoked below retain their preceding scopes.

## 1. Fixed masks and the source residue

Fix the actual compiler, and distinguish the fixed cell exponent d from the varying exponent D=dn. Put

```
B=2^d, m=B−1, Q=B^n=2^D, rep=(Q−1)/m,
q=Q(2Q−1), A=2Q−1,
U=m−MC, V=MF_native, MF_source=m+V,
e=popcount(U)=popcount(V), kappa=popcount(K).
```

Here `0<U,V<m`, U is odd, and V is the native mask with its added low bit; MF_source is the actual source numeral. Equality of the two populations follows from the authentic modified-mask identity `pc(MC)+pc(V)=d`. Write pc for binary population throughout. The selector z is positive and odd, F=Kz, and the literal source gives

```
R=q²(q²−1)+(MC+q*MF_source)J−(1+qK)(q²−1)z,
J=(q−1)/m.                                       (1)
```

Every resonant selector under consideration has A dividing R+1. Reducing m(R+1) modulo A, with q=0 modulo A, gives

`0=−MC+m*z+m modulo A`,

so `m*z=−U modulo A`. Since Q=1 modulo m, A=2Q−1=1 modulo m and therefore gcd(m,A)=1. The integer

`z_A=2U*rep=U(A−1)/m`

is in(0,A), is even, and satisfies `m*z_A=−U modulo A`. Consequently

```
z=2U*rep+(2Q−1)h, with h>=1 odd.                (2)
```

The subpower selector bound makes `h=Q^o(1)`, meaning `log(h+1)=o(D)` along the chosen family. Indeed h<z/A and, for every positive delta, z<=Q^(1+delta) eventually. No lower divergence assumption on h is needed here; bounded positive odd h also satisfies the proof.

## 2. A sufficient sparse-mask inequality holds for the actual compiler

The argument needs only the following strict fixed-constant inequality:

```
d>2*kappa*e+2e.                                  (3)
```

Here is its actual source justification. In the native layout let a>=1 be the tile alphabet size, k>=2 the number of allowed windows, and M=M0. The accepted clause census gives

```
M>=k+15a,
|E|=M−6a+4<=M−2,
b>M/3, L>213M, d=bL>71M².
```

The modified remainder mask removes exactly the End bit and adds exactly one further permitted dummy bit, so `e=|E|`. The14 occurrences of each selector coefficient, the9a copy coefficients, four anchors and at most six other explicit monomials give

```
kappa<=2(14k+9a+4)+6=28k+18a+14<28M.
```

The inequality counts binary populations, allowing carries; it does not require disjoint support of the summands. Therefore

`2*kappa*e+2e<(56M+2)(M−2)<71M²<d`,

proving(3). These are the actual modified75/76/77/78 layout facts, not assumptions inferred from arbitrary positive scalar constants.

## 3. Cyclic population and three nonzero residues

For an integer x let w(x) denote pc of its least residue modulo m in[0,m−1]. Binary cyclic carrying gives

```
w(x+y)<=w(x)+w(y),
w(2x)=w(x),
w(−x)=d−w(x) when x!=0 modulo m.                 (4)
```

The first inequality can be proved by replacing two units at a binary position by one unit at the next position, with positions taken modulo d. Population decreases at every such replacement. Starting with a positive finite multiset, the process terminates with a nonempty0/1 cyclic word; if its residue is0, that word consists of all d ones. In particular every positive integer multiple of m has population at least d. Reducing a positive integer to its least residue cannot increase population, and the zero-residue case only makes the first inequality weaker. The second formula rotates the d bits; the third is their complement.

Put

```
T=2KU modulo m,
U1=T+2U+V modulo m,
U4=6T+8U modulo m,
mu=kappa*e.
```

All three residues T,U1,U4 are nonzero. Indeed their positive raw representatives `2KU`, `2KU+2U+V` and `12KU+8U` have respective population at most

`mu`, `mu+2e`, and `2mu+e`,

each strictly less than d by(3). None can be a positive multiple of m. This avoids any assumption about gcd(K,m), and rules out the zero-residue exceptional cases needed below. Also `w(T)<=mu`.

## 4. Exact polynomial and seven periodic residues

In this section regard Q as an indeterminate and h as an integer parameter. Let q=2Q²−Q and set

```
Zpoly=2U(Q−1)+m(2Q−1)h,
P(Q)=m(q^4−q²)+(m−U+q(m+V))(q−1)
     −(1+qK)(q²−1)*Zpoly.
```

Equation(1) and(2) give mR=P(Q). Since P(1)=0, there is an integer polynomial

```
H(Q)=P(Q)/(Q−1)=sum_(i=0)^7 c_i(h) Q^i,
R=rep*H(Q).                                      (5)
```

Each c_i(h) is affine in h with fixed integer coefficients. Let C_i be its least residue modulo m, and write `c_i=m*a_i+C_i`. Direct expansion modulo m gives the following residues:

| i | C_i modulo m |
|---:|---|
| 0 | U |
| 1 | −(T+2U+V) |
| 2 | 2T−2U |
| 3 | T+8U+4V |
| 4 | −(6T+8U) |
| 5 | 12T |
| 6 | −8T |
| 7 | 0 |

In particular these residues are independent of h. Moreover

```
c7=16m, a7=16,
c6=−16m−16KU−16Kmh,
a6=−16−16Kh−ceil(16KU/m).                        (6)
```

Let `Wsum=sum_(i=0)^6 pc(C_i)`. The three nonzero residues from Section3 make C1,C4,C6 genuine complement words. Keeping C0 and C5 and discarding the nonnegative contributions of C2,C3, formula(4) gives

```
Wsum >= e+3d−w(U1)−w(U4)−w(T)+w(12T).
```

Now `w(U1)<=w(T)+2e` and `w(U4)<=w(6T)+e=w(12T)+e`. Therefore

```
Wsum>=3d−2w(T)−2e>=3d−2mu−2e,
Wsum+d>=3d+gamma, gamma=d−2mu−2e>0.              (7)
```

The positive C5 word compensates for the population loss in the negative C4 word. Treating the three complements independently would miss this cancellation.

## 5. Carry-safe periodic interiors

The following elementary normalization argument includes the case C_i=0. From(5), using m*rep=Q−1, the unnormalized base-Q coefficients of R are

```
R=16Q^8+sum_(i=0)^7 (C_i*rep+epsilon_i)Q^i,
epsilon_i=a_(i−1)−a_i, a_(-1)=0.                (8)
```

Define an integer

```
Hbound=3+2*max_(0<=i<=7)|a_i|,
ell=the least integer >=2 with Hbound<B^(ell−1).
```

The constants are fixed and a_i=O(h+1), so `ell=O(1+log(h+1))=o(n)` when h is subpower. Eventually n>=ell+1. In particular every perturbation epsilon_i, including an incoming carry of−1 or0, has absolute value less than Hbound.

Normalize(8) upward from its least significant coefficient. If C_i is nonzero, then `1<=C_i<=B−2`, and the word C_i*rep is at least B^(n−1) away from both endpoints0 and Q−1. A perturbation of magnitude below Hbound therefore leaves the normalized coefficient strictly within[0,Q−1], with outgoing carry0. If C_i=0, the normalized coefficient has outgoing carry−1 or0, since its magnitude before normalization is below Q. Induction proves that every carry into positions0 through7 is−1 or0.

For a nonzero C_i, its lowest ell base-B digits have value `C_i*(B^ell−1)/(B−1)`. Both that value and its complement inside ell digits are at least B^(ell−1)>Hbound. Thus adding the signed perturbation creates no carry or borrow beyond those ell digits. The B-digits at positions ell through n−1 remain exactly C_i, and the population of the i-th Q-block is at least

`(n−ell)*pc(C_i)`.

For zero C_i the same lower bound is0 and needs no periodic assertion. At position7, equations(6) and(8) give the negative coefficient

`epsilon7=−32−16Kh−ceil(16KU/m)`.

After its incoming carry, the normalized digit is exactly Q−a, where

`a=32+16Kh+ceil(16KU/m)−carry6`,

so `0<a<Hbound<B^(ell−1)`. This digit has population `D−pc(a−1)>=D−d*ell`. Its outgoing carry is−1, leaving the top digit15; that additional positive contribution is not needed in the lower bound.

All eight blocks are disjoint. Consequently

```
pc(R)>=(n−ell)*Wsum+D−d*ell
      =(n−ell)*(Wsum+d)
      >=(n−ell)*(3d+gamma).                      (9)
```

Since gamma is a fixed positive integer and ell=o(n), eventually the right side is at least3dn+2=3D+2. For a given member, the explicit sufficient conditions are `n>=ell+1` and `gamma*n>=ell*(3d+gamma)+2`. These use the actual h of that member. No claim that a first passing parameter certifies every successor is required for the asymptotic theorem.

## 6. Source completion and remaining language boundary

The fixed-prime theorem provides the exact resonance A|(R+1), positive outer coordinates and an input representative with A³|Y. Its sharper selector construction ensures h is subpower, and retains the old positive-slack threshold. The present theorem applies to every such minus-shape selector once sufficiently large, not merely to one specially chosen low limb.

The source-coupled input choice has u>=10D+b and keeps R fixed during the odd-prime lift. Its accepted binary criterion is exactly `pc(R)>=3*v2(q)+2`; here v2(q)=D. Equation(9) proves that criterion. Thus q³|Y and the accepted conditional converse supplies all18 positive witnesses of the unchanged83 source.

This proves completed positive source zeros at constructed ordinary inputs on a sufficiently large minus-family tail. It does not identify a rejected input for an arbitrary compiled program. It also does not prove equivalence of the83 language to the intended input language, or establish a new circuit minimum. The plus shape is outside this note. The result concerns authentic fixed compiler constants and the resonant source residue; it is not a statement for arbitrary small scalar masks or arbitrary subpower selectors.

## 7. Evidence and provenance

The complete source-coupled proof and the fixed-prime/subpower constructions were read as inert text. The literal census was checked against complete76 Section1, complete77 Section1, complete78 Sections1–2 and the modified75 mask definitions, together with the accepted sparse-coefficient proof. The companion authenticates these nine immutable inputs:

| File | SHA256 |
|---|---|
| complete83_fixed_prime_quotient_carries.md | 53ed811331899dba52536c9946cfe370888ac8826376351800d785f87549cd46 |
| complete83_subpower_selector_bound.md | 3c52050218676fa59fdd83f60699e0d884b1e885e16cc3864146d6dd66010eb4 |
| complete83_source_coupled_input_lifting.md | 822d192578f379e1e81a00caafbb3612db24989902411748f35ee23343d5934f |
| complete83_outer_family_sparse_two_primary.md | bda0275af08ceaf1637b6bfa3ba8a8347205f5a674783cec7105ca263bf3fb97 |
| complete83_shared_projection_scout.json | dd9e105d295bf2fb3e3b0246234bb68cb78487ee919405bc052f2b67a9def34c |
| FIXED_RAW_UNIVERSAL_76_PROOF.md | 75a13b5fd0c44c3ec91366306fb5876a3ea2f867e464b84cebd46ca08d060f87 |
| FIXED_RAW_UNIVERSAL_77_PROOF.md | 292acdfe5ff598201c3dd9cd7defff07b45d743637c1f3836a21065888053a41 |
| FIXED_RAW_UNIVERSAL_78_PROOF.md | b28ddb9aec5225cda7dabc85fb952daf49de4041cf35910f62dabf3893749d39 |
| complete75_half_binomial_compiler.md | 68edf3bc40238ccf47b023d7358e4be62664a2d78a60b6fae19de14b67208117 |

The fresh symbolic calculation expands the35-term polynomial P in the six independent variables Q,m,K,U,V,h, checks its exact quotient by Q−1, all eight residue coefficients, and the two highest coefficients in(6). Twenty-three literal actual83 rows bind the outer input/slack, index and transport expressions; the83-row/18-witness packet is authenticated, not executed or recompiled.

Fresh finite checks include86,367 cyclic-subadditivity pairs,1,792 positive-Mersenne-multiple cases and408 scalar census inequalities. Another288 relaxed scalar layouts satisfying(3) check2,304 normalized Q-blocks, including384 zero-residue blocks, the exact whole source formula, every nonzero periodic interior and the joint population bound. Of these layouts,136 satisfy the explicit sufficient population threshold; the largest R has33,004 bits. These are synthetic masks and coefficients, not actual compiled machines. No X=2^R, half-binomial value or Pell tuple is materialized.

Root independently read and challenged the whole mathematical draft, including a separate expansion of the residue polynomial and the signed carry argument, without a finding. Any independently pinned review is a separate artifact. No supplied, archived, committed, frozen or copied predecessor helper was executed or imported. Only this fresh companion ran, and its finite checks corroborate rather than replace the quantified proof.

Fresh writer, normal and optimized-Python exact receipt replays passed from `/` before freeze.

Final helper SHA256: `f327e4bad18f8ab9ca9065a41ef0814a958fb1302a6e1c0d9124c5e7a88b5e25`.

Final receipt SHA256: `a7e0c91ad1e51e1eb5e517fb2ff6328ce69b5ed1e839caadc9083d05ad563cf4`.
