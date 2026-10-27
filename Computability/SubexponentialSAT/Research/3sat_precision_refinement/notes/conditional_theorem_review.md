# Independent review of the conditional acceleration theorem

**Status:** the implications below are proved conditional on a new structured-mode summation algorithm. The required summation algorithm has not been constructed or proved. These notes must not be presented as an improved SAT algorithm.

**Source checked:** OpenAI, *The Exponential Time Hypothesis is False*, revision dated October 25, 2026; GitHub commit `42907c9e999cc00d6abe7a50bfc1023250edd1b9`; in particular `quantitative-contraction.tex` and `quantitative-reduction.tex`.

## 1. Sufficient acceleration hypothesis

Keep the source's coefficient rings, packet construction, deformation, canonical lifts, tapered Hermite multiplicities, and definitions of the generated child tensors.

For a call having `M` wires, retention parameter `u`, and global root-size parameter `s`, suppose a uniform deterministic procedure evaluates the source's structured expression

`sum_beta product_g Z_(g,beta) (mod 2^{p_t})`

using at most

`s^{O(1)} exp(O(M/u))`

recursive contractions, each on a network of the same admissible generated type, with at most `M/8` wires, the source's unchanged maximum-degree bound, and the same applicable precision accounting. The procedure must preserve the source's polynomial description lengths and polynomial-space, depth-first evaluation. Its nonrecursive work per generated call/term may have the source's `exp(O(s^{9/10}))` entry-evaluation factor and a fixed polynomial in the original description length, but no additional larger exponential cost.

The query count must be polynomial in `s`, independently of the input description length. The latter is a fixed polynomial *per-call work factor*, as in the source proof, not a branching factor repeated at every depth. This distinction preserves the stated fixed polynomial dependence on description length.

This is a hypothesis about the actual generated expressions and tensor descriptions. It is not a black-box assertion that arbitrary unrelated summands can be added after examining only a small subset of them. Existing explicit tuple enumeration does not meet this hypothesis.

## 2. Retuning the contraction recursion

Let `lambda=ceil(log_2 s)`. Replace the source leaf threshold by

`H=ceil(s/lambda)`.

Keep `r=64`, `epsilon=1/(128*1024)`, `Delta=ceil(s^{9/10})`,

`u_d=floor(epsilon lambda / 2^d)`,

`a_d=2 sum_{j=0}^d u_j`, `L=2^{a_d}`, and `D_arr=r^{2a_d}`.

At an active call,

`s/lambda < M <= C s 8^{-d}`.

Consequently `8^d<C lambda`, so

`d <= (log_2 lambda)/3 + O_C(1)`

and, uniformly at active depths,

`u_d=Theta_C(lambda/2^d)=Omega_C(lambda^{2/3})`.

Thus the source's old auxiliary lower bound `u>=lambda^{4/5}` should be replaced, for example, by `u>=lambda^{3/5}` for sufficiently large `s`. Nothing essential uses the old exponent `4/5`; the proof needs a power of `lambda` that tends to infinity sufficiently quickly to dominate logarithmic factors after exponentiation.

The cumulative bound `a_d<=4 epsilon lambda` is unchanged. Therefore `L,D_arr<=s^{1/1000}` still holds eventually. The packing conditions remain valid because

* `2 D_arr^2 Delta = O(s^{9/10+2/1000}) = o(s/lambda)`;
* `L D_arr = O(s^{2/1000}) = o(s/lambda)`;
* `2L <= Delta` eventually.

The source child construction still gives at most `6M/r=3M/32<M/8` wires and preserves `Delta`.

### Precision

The inherited-precision estimate remains

`p <= s lambda^{O(1)} 2^{a_{d-1}}`.

For every retained interpolation point, `i<u_d`, and hence

`D_t=2^{a_d-i} >= 2^{a_{d-1}+u_d}`.

Since `M>s/lambda`,

`p / (M D_t/u_d) <= lambda^{O(1)} 2^{-u_d} = o(1)`.

Also `M(a_d+1)=O(MD_t/u_d)`. Together with the source's `h<=4M/u_d`, the same child precision

`p_t=p+8hD_t+8M(a_d+1)`

therefore satisfies `p_t=O(MD_t/u_d)`. All precisions remain polynomial in `s`. The coefficient ring, interpolation-point supply, exact arithmetic, and canonical-lifting arguments require no other change.

### Time and space

At depth `d`, the exponential contribution from the hypothesized evaluator is

`O(M/u_d)=O((s/lambda)4^{-d})`.

These contributions sum geometrically to `O(s/lambda)`. The polynomial branching factors over `O(log lambda)` levels add `O(lambda log lambda)` to the logarithm of the call count, which is `o(s/lambda)`.

A leaf costs

`exp(O(H)+O(s^{9/10})) = exp(O(s/lambda))`

times a fixed polynomial description factor. This proves the conditional contraction bound

`(s+description_length)^{O(1)} 2^{O(s/log s)}`

with polynomial space, provided the acceleration hypothesis includes the stated streaming/space guarantee and immutable shared descriptions.

For bounded-density fixed-width CNF, the source's ordinary clause network has `s=Theta(n)`. Therefore the conditional counting bound is

`poly(n,m) 2^{O(n/log n)}`.

## 3. General-density reduction: two necessary additional changes

Changing only the contraction theorem is insufficient: the source has two independent branching factors of order `exp(n/sqrt(log n))`. Both must be retuned.

Write `lambda=ceil(log_2 n)` and `nu=ceil(log_2 lambda)`.

### Sparsification

Take `sigma=1/lambda`, a valid rational parameter for the source sparsification lemma. The number of tree nodes is

`poly(n,lambda) 2^{n/lambda}`.

The occurrence bound becomes

`B=O_k((lambda log(2lambda))^{k-1})=lambda^{O_k(1)}`.

Thus all initial-check sizes, additional row lengths, candidate-system sparsities, and candidate enumeration counts remain within the source's `exp(lambda^{O_k(1)})` bounds. Their fixed powers of `lambda` are `o(n nu/lambda)`, so these costs remain negligible relative to the target exponential term.

### High-incidence variables inside each sparse-system query

Replace the threshold in the sparse-system contraction lemma by

`D_* = max(1,ceil(N_0/n)) lambda`.

The number of variables that occur in more than `D_*` scopes is at most `N_0/D_*<=n/lambda`. Their exhaustive assignments cost at most `2^{n/lambda}`.

All remaining degree, scope, and entry-evaluation bounds retain a fixed polylogarithmic factor. In particular the group-incidence degree is still at most `n^{3/4} lambda^{O(1)}`, eventually below `(n nu)^{9/10}`. The wire count remains `M=O(n nu)`, the precision and truncation order remain `n+1`, and entry evaluation costs remain `exp(lambda^{O(1)})`.

Apply the conditional contraction theorem at `s=n nu`. Its exponent is

`O(s/log s)=O(n nu/lambda)`.

The degree-array enumeration contributes `O(sqrt(n) log n)=o(n nu/lambda)`. The two branching exponents are both `O(n/lambda)`, also absorbed. Thus, for each fixed width `k`, the conditional general-density bound is

`(n+m)^{O_k(1)} 2^{O_k(n log log n / log n)}`

with polynomial space.

This reasoning applies to every sparse-system query, including discarded greedy candidates, exactly as required by the source. It does not assume that the current parity checks already exclude all nonsatisfying assignments.

## 4. Exact finite-grid taper lower bound

This is a proved statement about the source's Hermite multiplier loss; it is not a universal lower bound on algorithms or on every possible recovery method.

Let integers `a>=2u`, `u>=1`, and `L=2^a` be given. Let `q_i>=0` be supported on `0<=i<u`, and assume `q_i<=C M`. Suppose the Hermite completeness condition is

`L sum_{i=0}^{u-1} 2^{-i} q_i > M(2L-1)`.

Define the finite normalized loss

`ell_i^(a) = sum_{j=1}^{a-i} j 2^{-j}(q_i-q_{i+j})`,

and the full loss

`ell_i^(inf) = sum_{j>=1} j 2^{-j}(q_i-q_{i+j})`.

All undefined `q_i` with `i>=u` are zero. Put

`W=sum_{i=0}^{u-1} 2^{-i}q_i`.

Let `H=max(0,max_{0<=i<u} ell_i^(inf))`. Since `sum_{j>=1}j2^{-j}=2`,

`q_i <= H/2 + sum_{j>=1} [j/2^{j+1}] q_{i+j}`.

The coefficients in brackets sum to one and are supported on positive `j`. Backward induction from `i=u-1` gives

`q_i <= (H/2)(u-i)`.

Therefore

`W <= (H/2) sum_{i=0}^{u-1} (u-i)2^{-i}`

`  = H (u-1+2^{-u}) <= H u`,

so

`max_i ell_i^(inf) >= W/u > M(2-1/L)/u`.

The exact tail identity is

`ell_i^(inf)-ell_i^(a) = q_i (a-i+2) 2^{-(a-i)}`.

The function `(x+2)2^{-x}` decreases for nonnegative integer `x`. Thus, uniformly for `0<=i<u`,

`0 <= ell_i^(inf)-ell_i^(a)`

`  <= C M (a-u+3) 2^{-(a-u+1)}`

`  <= C M (u+3) 2^{-(u+1)}`,

where the last inequality uses `a>=2u`. Combining the estimates proves the explicit bound

`max_{0<=i<u} ell_i^(a)`

`  > M(2-1/L)/u - C M (a-u+3) 2^{-(a-u+1)}`.

As `u` tends to infinity with fixed `C`, the tail is `o(M/u)`, so the maximum finite loss is `Omega(M/u)`; for all sufficiently large `u`, it exceeds `M/u`.

### Zero multiplicities and negative losses

If `q_i=0`, then both loss expressions are nonpositive, since every term is `-j2^{-j}q_{i+j}`. Such indices cannot supply the positive maximum forced by completeness. They nevertheless satisfy all inequalities used above. Thus the maximizing positive loss occurs at an active level with `q_i>0`; no assumption that every retained level is active is needed.

In the source notation,

`v_2(E_t(0)) = -D_t ell_i^(a)` for `i=v_2(t)`.

Consequently at some active level this scalar multiplier has a valuation loss `Omega(MD_t/u)`. This rules out eliminating that loss merely by selecting a different bounded taper supported on the same `u` levels. It does **not** exclude a method exploiting additional divisibility of the particular polynomial being recovered, cancellations across interpolation terms, or an entirely different summation/recovery representation.

## Review conclusion

The conditional rate improvements and the finite-grid taper inequality are mathematically sound under the explicit assumptions above. The decisive new structured-mode summation hypothesis remains open in this work; none of the retuning calculations constitutes a proof of that hypothesis.
