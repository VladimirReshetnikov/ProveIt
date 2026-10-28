# Independent review: two-alphabet polynomial-space schedule

**Verdict: valid relative to the imported exact contraction framework and the already checked asymmetric-packing/full-orientation Cauchy ingredients.** I found no integration failure from changing the alphabet from 17 at the root to 13 below the root. The resulting coefficient is

`66.12052562523922...`,

strictly below the fixed-alphabet adaptive coefficient `66.19272369357722...` by `0.07219806833800...`. This is a modest further improvement of a normalized exponential upper-bound coefficient, not a new logarithmic order or a practical running-time prediction.

## Definition

Let `lambda=ceil(log2 s)`, `g=ceil(sqrt(lambda))`, and `b=ceil(6 log2 lambda)`. Define nonnegative integers

`B=max{j:17^(20j)<=2^(lambda-g)}`,

`A=max{j:13^(10j)<=2^(lambda-g)}`.

Use `r_0=17`, `r_d=13` for `d>=1`,

`u_0=B`,

`u_d=floor((5/7)(A-B)(2/7)^(d-1))` for `d>=1`,

and `a_d=sum_{j=0}^d u_j+(d+1)b`. The leaf threshold is `H=ceil(s/lambda)`. For bounded sizes at which any parameter is inadmissible, use exhaustive contraction. Both integer maxima are well-defined and polynomial-time computable by integer comparisons. For large lambda, `A>B>0`.

Put

`b0=1/(20 log2 17)=0.012232527105911302...`,

`a=1/(10 log2 13)=0.027023815442731972...`.

Then `B/lambda -> b0`, `A/lambda -> a`. Since the unfloored tail has sum `A-B`, we have

`a_d<=A+(d+1)b`.

## Alphabet change and locality

The source packing proof (`quantitative-contraction.tex`, `lem:tensor-packets`) uses strings in `[r]^a` and orbits of ordered label pairs under swapping unequal symbols. For an orbit with a' unequal coordinates, there are `2^a'` ordered label pairs; divisibility by `L=2^a` supplies the orientation slots. This reasoning works for every integer `r>=2`; it does not require r to be even or a power of two.

At each call, the group labels are freshly assigned. The recursion retains original tensor ports and immutable creation-time tensor descriptions, not a requirement that later calls retain the same label alphabet. The child construction places all retained vertices from both parent sides on one side, and fresh packet tensors on the other. Consequently the bounds `R_d<=Delta` and `C_d<=2L_(d-1)` still hold. The full-orientation Cauchy basis reads one source group and targets one other group within the current call; it has no cross-depth alphabet dependence. The per-level group counts are bounded by 17, so this change adds no new asymptotic branching factor.

## Uniform parameter proof

First consider every hypothetical active call of depth

`d<=d_*:=ceil(log_5 lambda)+2`, `M>H`.

The tail ratio is `z=2/7`. Uniformly over those depths,

`u_d >= lambda^(eta+o(1))`,

where

`eta=1+log_5(2/7)=0.22161460295122537...>0`.

Thus the floors have uniformly vanishing relative effect. The cumulative additive buffers are `O((log lambda)^2)=o(g)`.

At the root, `Q_0=17^a_0`, both side degrees are bounded by `Delta=ceil(s^0.9)`, and

`Q_0^2 Delta lambda^2/M <= 2^(-g/10+O(log lambda))=o(1)`.

The row-load term `Q_0 Delta/M` and rounding term `L_0 Q_0^2/M` have strictly smaller powers. Below the root, `Q_d=13^a_d`, and

`Q_d R_d/M <= 2^(-g/10+O((log lambda)^2))=o(1)`.

Using `C_d<=2L_(d-1)` and `a_d<=A+O((log lambda)^2)`, both the fresh-column and rounding terms satisfy

`Q_d^2 C_d lambda^2/M, L_d Q_d^2/M <= 2^(-(1-2log2(13)*a-a)lambda+o(lambda))`.

The positive margin is

`1-(2log2(13)+1)a=0.772976184557268...`.

New packet degrees are at most `s^(a+o(1))`, with `a<0.9`. These bounds prove uniform `(1+o(1))` padding. Since `2/17<1/5` and `2/13<1/5`, every child eventually has size at most `M/5`, closing the depth bootstrap. More precisely,

`M_0=s`,

`M_d <= s (2/17) (2/13)^(d-1) (1+delta_s)^d`, `d>=1`,

for one uniform `delta_s -> 0`.

The original additive-buffer precision proof is unchanged. In particular, `D_i>=2^(a_(d-1)+b+1)` and inherited precision `p=O(s lambda^2 2^a_(d-1))` give

`p/(M D_i/u_d)=O(lambda^4/2^b)=o(1)`.

All precisions and label-set sizes remain polynomial in s. Leaves, polynomial branching factors, original tensor evaluators, and packet evaluators contribute `o(s/sqrt(lambda))` to the logarithm of the total time. The immutable-description convention must remain explicit.

## Coefficient calculation

For the full-orientation Cauchy basis the local natural-log coefficient is

`kappa_r=pi sqrt(2(1-1/r))`.

The root therefore contributes `kappa_17/sqrt(b0)`. The tail is a convergent geometric series with ratio

`q=(2/13)/sqrt(2/7)=0.2878197989826109...<1`.

After converting natural logs to base two, the coefficient is exactly

```
C = (pi sqrt(2)/ln 2) * [
      sqrt(16/17)/sqrt(b0)
      + (2/17) sqrt(12/13)
        / (sqrt((5/7)(a-b0)) * (1-(2/13)/sqrt(2/7)))
    ].
```

Numerically the root and tail contributions are

`56.22336654200492...` and `9.89715908323430...`,

giving `C=66.12052562523922...`. No assertion of optimality among all schedules is needed or justified by this construction. The comparison should include the composed existing-ingredient baseline, and the final theorem should retain `C+o(1)`.
