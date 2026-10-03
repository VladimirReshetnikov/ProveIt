# A smaller quotient offset in the complete U9 polynomial

The [source](neary_woods_universal_tail_quotient253.py) changes one operand in two actual saved [product-scale U9 sources](neary_woods_universal_product_scale253.md). Each remains **253=132M+121A**, with a252-operation certificate, one comparison,43 strictly positive witnesses and ordinary positive input. The conservative total-degree bound drops from **1147 to982**. The default is the merged four-program-parameter interface; the second emitted source keeps the separate fifth duration-bound parameter. Computation time remains existential and unbounded.

This is a positive-zero bijection on the parent's valid shifted U9 program/input slices. It retains the actual U9 table, all11 fixed compiler numeral recipes, the ordinary-input loader, program parameters, history and finalizer. The signed coordinate identity holds on every tuple, while positivity of the inverse is proved only after native recovery. This packet emits saved layouts7 and15, without rerunning historical builders, changing factor partitions, or claiming a new optimal universal bound. The separate74/86 results are unaffected.

## 1. The actual paid change

Use the joint native names `q,X,Y,k,c,a,E` and let

\[
 Z_0=(q-1)F_3,\qquad
 S=A_{pad}+1+(q+1)(B_{pad}+Z_0),\qquad r=(q-1)S.
\]

These are the existing registers `factored_pack_Z`, `factored_pack_inner` and `and__bs_packed`. Here `F3` is the complete joined output port, not a single history digit. Change only

```
and__bs_X_bound = factored_pack_inner + and__bound_beta
```

to

```
and__bs_X_bound = factored_pack_Z + and__bound_beta
```

and retain the existing multiplication `X=q*and__bs_X_bound`. Both summands are already paid. The supplied positive `and__bound_beta`, denoted beta below, has exactly this one consumer; the sum has exactly the one consumer `and__wn2`. No consumer, coordinate, factor or finalizer is removed. All253 gates remain live.

Thus the complete output polynomials obey, over every commutative ring,

\[
 F_{new}(\beta,\mathbf v)
 =F_{old}(\beta+Z_0-S,\mathbf v).                 \tag{1}
\]

The checker verifies the actual producer cones, expands the local affine identity, and compares all253 register expressions through that proved cut. All16 actual factors and their complete product-minus-one finalizer are included. This is not a same-coordinate polynomial identity.

The forward map at parent zeros is `beta_new=beta_old+S-Z0`. The unchanged pretyping argument below gives `S>Z0>0` there, so this map is positive. No unconditional off-zero positivity assertion is needed. The reverse map in(1) is signed away from zeros: with every supplied coordinate and diagnostic numeral set to1 it is negative in both layouts, and those assignments are not zeros.

## 2. Untyped outer bounds are unchanged

Write `P` for the history scale, `b=c_h D` for its radix, `J` for its selector sum, and `T=P^9`. The actual fixed compiler multiplier `c_h` is dyadic and at least32. Every factor is an integer unit at a positive zero of the complete product-minus-one source, without presupposing any sign. The scalar proof in [product_scale253, Section2](neary_woods_universal_product_scale253.md#2-strict-scalar-fields-before-any-binary-semantics) gives

\[
 P\ge6,\quad J\ge1,\quad b\le P+2,\quad J\le P/6,
 \qquad 0\le H_0,M_0,Z<T.
\]

It handles either sign of the history repunit and permits height `D=1`. In particular it does not use binary typing or the old joint quotient bound. The unchanged high tags

\[
 H=H_0+2T,\quad M=M_0+T,\quad Q_{high}=bT
\]

give `H-Z>=T+1`, `M-Z>=1` and `Qhigh-H-M+Z>=(b-5)T+2`. The unchanged low recoder argument gives `0<a0,b0,z0<q0` before its signs are resolved. After joining the low and high ports, the four truth fields satisfy

\[
 F_0=q-A_{pad}-B_{pad}+F_3-1>0,\quad
 F_1=A_{pad}-F_3>0,\quad F_2=B_{pad}-F_3>0,
\]

\[
 \sum F_i=q-1,\quad
 (F_0,F_1,F_2,F_3)=(1,4,2,8)\pmod {16},\quad q\ge16.
\]

The private quotient beta is absent from every step of these outer estimates. Consequently

\[
 r=\sum_{j=0}^3q^jF_j\ge4369,\quad
 r<q^3(F_3+1),\quad r=1\pmod {16},\quad F_3\ge8.
\]

Also `A_pad+1=F1+F3+1`, `B_pad=F2+F3`, so `S>Z0>0`.

The new positive quotient and retained positive odd multiplier yield

\[
 X=q(\beta+(q-1)F_3),\quad Y=(2\,odd\_half+1)q\ge3q.
\]

Therefore, before any Pell or radix recovery,

\[
 E=XY>3q^2(q-1)F_3>2r+3,\qquad a=Y(X+1)>2r+3,
 \qquad X\ge16.                                \tag{2}
\]

For the strict comparison,
`E-2r>q²((q-3)F3-2q)>=q²(6q-24)>3`.
**The proof does not assume `X>r` at this stage.**

## 3. Normalized strong equation and native recovery

Both emitted sources use normalized strong cores. The changed joint source literally computes

\[
 \rho=ic^2,\quad \Delta=(a+2)^2-1,\quad
 N_s=f^2-\Delta\rho^2,\quad
 N_a=\Delta^2\rho^2(V^2-y^2)+y^2,\quad V=of-c.
\]

These are `and__f_square_minus_one` and `and__P17`; their names do not replace their actual formulas. The other relevant factors are the first norm, main norm, index unit `K-r` and linear unit `V-jc+2K`, where `K=k-hE`. All norm factors are protected against−1 modulo4. For the normalized strong factor, `Delta` is0 or3 modulo4, so `f²-Delta*rho²` cannot be−1. Hence `Ns=1`.

To apply the ordinary relaxed-rank lemma, set the **proof-only** positive integer

\[
 i_{ordinary}=\Delta i,\qquad T_{aux}=i_{ordinary}c^2=\Delta\rho.
\]

Since `a>0`, `Delta>0`. The exact identities are

\[
 T_{aux}^2-\Delta(f^2-1)=-\Delta(N_s-1),\qquad
 \Delta^2\rho^2=T_{aux}^2.                       \tag{3}
\]

Thus both the ordinary strong equation and its matching auxiliary coefficient hold. This is a one-way lemma conversion at zeros, not a claimed coordinate bijection between normalized and ordinary cores. The emitted source still has its original normalized witness `i` and all original factors.

With(2) and(3), the native recovery in [the group tail-offset theorem, Sections3–4](group_projective_tail_quotient_shift.md#3-native-recovery-including-both-index-signs) applies to the literal joint core. The needed source identities are the same first-root, ratio, main-root, index and coupled-linear equations; the normalization(3) supplies precisely its ordinary strong hypothesis. To expose the bootstrap order, write `K=r+epsilon` and `V-jc+2K=lambda`, with both signs initially allowed. Then `0<K<E` and `0<2K-lambda<E`. First and main Pell indices satisfy `n=K mod E`, `n>=r-1`, and `p>n`; the retained ratios give

\[
 c>Y(r-1)>2(2r+3),\quad c>2p,\quad c>(a+2)\Delta^2.
\]

The [relaxed-rank lemma](../../1980/PELL_RELAXED_AUXILIARY_PROOF.md) and [strict signed step-down](../../1980/EXPLORATION_FIXED_MINUS_INDEX_PARITY.md) then recover `p=2K-lambda`, `n=K`. Strict duplication excludes `lambda=-1`. Set `r'=r` or `r-2` according to epsilon; the ordinary index equations now have `p=2r'+1,n=r'+1`.

The lower ratio, valid independently of `X>r'`, gives `Y>=X^r'` and `a>X^(r'+1)`. Since `X>=16`, it follows that `6r'/a<1/2` and `2^(2r'+1)<a`. The exact main recurrence congruence and its positive representatives therefore recover

\[
 X=2^{2r'+1}
\]

before invoking the old bound. The unchanged quantitative upper-ratio/binomial argument now gives `q=2^popcount(r')`. Once q is dyadic, the positive checksum fields imply `popcount(r)>=log2(q)`. The residue `r=1 mod16` gives `popcount(r-2)>=log2(q)+2`, excluding the negative index sign. Thus

\[
 r'=r,\qquad X=2^{2r+1}.                         \tag{4}
\]

All quantitative and signed cases used here are spelled out in the pinned group theorem, the [native selector proof](native_controller_binary_selector56.md#3-lower-ratio-first-then-the-direct-binary-exponent), and the [half-parameter kernel](../../1980/HALF_PARAMETER_PELL_92_PROOF.md). No old complete theorem requiring `X>r` has been applied before(4).

## 4. Positive inverse and inherited unbounded language

Since `q<r`, `S=r/(q-1)<r` and `2^(2r+1)>r²`, equation(4) gives

\[
 \beta_{old}=\beta+Z_0-S=X/q-S>0.                \tag{5}
\]

All other supplied coordinates are unchanged. Equations(1) and(5) produce a positive parent zero; conversely the positive parent-to-child map in Section1 produces a child zero. Their compositions are the identity because neither S nor Z0 depends on beta. This proves a bijection of complete positive zero tuples at each inherited valid shifted program/input slice, without changing any normalized witness.

After restoration, the parent's complete U9 theorem applies directly. Its dyadic history-scale recovery, joint AND typing, ordinary-input loader, exact physical counter and unbounded chronology are inherited as a whole. They are not reconstructed from an unchecked small numerical example. No new program decoder or numerical machine is postulated. Arbitrary choices of the fixed numeral values used for algebraic diagnostics are not asserted to define valid U9 program slices.

## 5. Full costs, degree scope and reproduction

Both saved sources have the same current ledger:

| Quantity | Value |
|---|---:|
| Complete operations |253=132M+121A|
| Certificate before final subtract1 |252=132M+120A|
| Comparisons / positive witnesses |1 /43|
| Supplied program parameters |4 default;5 separate duration|
| Fixed compiler numeral roles |11|
| Complete total-degree upper bound |982|

The numeral dictionaries are fixed integer recipes from the pinned compiler and actual U9 recipe, not witnesses or uncharged runtime exponentiations. Every multiplication by such a numeral remains paid. All supplied coordinates, including every program parameter, have formal degree1; only fixed numeral leaves and literal integers have degree0. Specializing the program parameters to a particular program can lower degree. **982 is an upper bound; this packet does not claim exact degree on either the full parameter polynomial or a specialized slice.**

The upper-degree computation uses only all-value arithmetic identities. At both native main norms it verifies the complete producer cone and expands

\[
 (X+ac+G)^2-(a^2+H)c^2
 =X^2+2Xac+2XG+2acG+G^2-Hc^2,
\]

where `G=ga*H` and `H=4a+3`. Every other gate uses ordinary degree propagation. No native equation is substituted into the polynomial. In the joint core, q and F3 have degrees15 and14, while X falls from59 to44. The changed factor bounds are:

| Joint factor | Parent | New |
|---|---:|---:|
| Main norm |168|138|
| Auxiliary norm |404|344|
| First norm |93|78|
| Normalized strong norm |220|190|
| Index unit |76|61|
| Coupled-linear unit |76|61|

The ten unchanged factors contribute110, giving982 for the full product-minus-one. Historical1147 metadata is explicitly kept under `historical_parent_ledger`; the active ledger and degree object contain the new values.

The standard-library CLI authenticates every parent and proof pin on each canonical public construction. It does not import a historical module. `evaluate` and `integer_pullback` accept an explicit diagnostic numeral dictionary; these check algebraic specializations and do not validate that arbitrary supplied constants encode the fixed machine. The public source is the recipe-bearing DAG. All returns own their mutable metadata.

```
python3 neary_woods_universal_tail_quotient253.py --root PATH_TO_WIP \
  --expect neary_woods_universal_tail_quotient253.json
```

The receipt contains both complete sources, exact affine-cut proofs for all506 registers and32 factors,48 full numeric identities including8 rational specializations,768 factor evaluations,384 padded-field bootstrap cases,112 population/inverse-size cases and24 normalization identities. It also checks the two negative off-zero inverse examples, strict mode/packet rejections and defensive copies. These finite checks supplement the proof; no astronomical compiler numeral or complete native Pell zero is materialized, and no historical partition census is rerun.
