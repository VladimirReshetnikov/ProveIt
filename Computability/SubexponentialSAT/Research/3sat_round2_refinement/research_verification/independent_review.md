# Independent adversarial review: matching packing and the two-stage coefficient

## Verdict

**Cleared as a compatible analytic refinement of the pinned contraction construction.**
I found no mathematical obstruction to the stated normalized certificate

\[
 (s+\mathcal L)^{O(1)}2^{(84.06627149423657\ldots+o(1))s/\sqrt{\lceil\log_2s\rceil}},
\]

or its sufficiently-large-size safe coefficient 85, using the exact two-stage schedule below. This conclusion is conditional on the unchanged deformation, integral-evaluation, recursive factorization, and input-interface claims of the pinned source. It is not independent validation of the entire ETH manuscript, formal verification, or an implementation of the full SAT algorithm. It improves a declared upper-bound coefficient, not the logarithmic order or a measured runtime. The crossover may be enormous.

Reviewed candidate: `../research_constants/combined_constant_proof.md`, with root `r=37`, `u=floor(10 lambda/1043)`; tail `r=8`, `u_d=floor(lambda/[236(5/2)^(d-1)])`; `a_d=sum_{j<=d}u_j+(d+1)g`, `g=ceil(log_2 lambda)^2`; leaf cutoff `ceil(s/lambda)`. Changing the convention to `ceil((log_2 lambda)^2)` has the same proof but is not necessary.

The normalized interface is important: at most **s** initial edges, degree at most `ceil(s^.9)`, initial precision and truncation length at most s, and fixed initial entry allowance `poly(s+description length) 2^(A s^.9)`. An untracked `M<=C s` or SAT reduction constant cannot be silently dropped. The coefficient 85 cannot be transferred directly to the number n of SAT variables.

## 1. Matching potential and exact bit complexity

Greedy edge coloring of a loop-free bipartite multigraph uses at most `2 Delta-1` colors: each edge is adjacent to at most `2 Delta-2` already colored edges. Parallel edges cause no problem, because a color class still has disjoint endpoints. No independence between different colors is required.

For `z=1+1/lambda` and `T_j=ceil(z m_j/q^2+10 lambda^2)`, independence within a matching gives

\[
 E z^{X_{j,\gamma}-T_j}
 =z^{-T_j}(1+1/(\lambda q^2))^{m_j}
 \le e^{-10\lambda^2\ln z}\le e^{-5\lambda}.
\]

The first inequality uses `(1+x) ln(1+x)>=x`; the second uses `ln(1+1/lambda)>=1/(2lambda)`. Since the candidate has `K q^2<=4s^2`, the initial summed potential is less than one eventually. The slightly stronger sufficient condition `Kq^2<=s^2` from the initial proposal is unnecessary.

After any prefix of fixed vertex labels, distinct matching edges still depend on disjoint remaining variables. Their probabilities are exactly in `{0,1/q^2,1/q,1}`, so the conditional potential is the stated product of rational factors. Trying every next label and minimizing does not increase its expectation. At the end, every `X<T_j`; since X is integer, `X<=ceil(A)-1<A`, which removes any extra ceiling term. Therefore

\[
 X_\gamma < (1+1/\lambda)M/q^2+10K\lambda^2
 \le (1+1/\lambda)M/q^2+20\Delta\lambda^2.
\]

The algorithm really is polynomial, although not practical. There are polynomially many candidates and summands; each factor is rational with polynomial bit length; `T_j=O(s+lambda^2)`; the product has at most s factors. A common denominator formed by multiplying polynomially many denominators still has polynomial bit length. Exact comparisons and updates are therefore polynomial-time/space. This does not rely on approximate logarithms for label decisions.

## 2. Packet count, crossing fraction, and changing alphabets

With common padded class size H divisible by `L=2^a`, put `B=Hq^2`. The source packet arrangement has exactly `B/L` packets. For an unordered coordinate-pair pattern with k unequal coordinates, its `2^k` pair labels occupy `H2^k` slots and therefore `H2^k/L` packets. All these packets have the same equality/inequality status in each coordinate. Summing over patterns proves that the unequal-coordinate packets are **exactly** `(1-1/r)B/L`, not merely bounded by that expression. Each contributes `2^(i+1)` tile families, hence

\[
 c\le 2(1-1/r)B/D_i.
\]

Per-coordinate symbol counts are `B/r` on each side. Thus every child has at most `2B/r` edges; packet vertices have at most `2L` ports; old degrees are unchanged. Empty tiles only help.

Every recursive call constructs a fresh labeling and fresh packets. Existing tensors retain their ports, creation-precision representatives, and immutable descriptions, not any constraint on the alphabet of the next call. Consequently changing r from 37 to 8 is compatible. The cumulative a schedule is needed only for precision domination; it does not require compatible coordinate alphabets across calls.

## 3. Packing exponents and noncircular depth bootstrap

Let `A=10/1043+5/708`. Root packing is certified by the **exact integer** inequality

\[
 37^{200}<2^{1043},
\]

which implies `.9+2(10/1043)log_2(37)<1`. Tail packing is certified by

\[
 .9+6A=307654/307685<1.
\]

The gap contribution is `O(log^3 lambda)=o(lambda)` over a candidate `O(log lambda)` depth range. Consequently `q^2 Delta lambda^3/s=o(1/lambda)` and `Lq^2 lambda/s=o(1/lambda)`. For active `M>s/lambda`,

\[
 B/M=1+O(1/\lambda)+o(1/\lambda).
\]

A circularity concern was identified and resolved in the author's final note: first consider candidate depths up to `N=ceil(log_3 lambda)+3`. All parameter bounds hold uniformly on that range, and tail children shrink by at most 1/3 eventually, so no active call reaches N. This establishes `O(log lambda)` depth independently. Accumulated `1+O(1/lambda)` overhead over those depths is then `1+o(1)`, giving the sharp tail bound

\[
 M_d\le (1+o(1))s(2/37)4^{-(d-1)}.
\]

Active u values grow at least as a positive power of lambda; under the sharp bound the exponent is `1-log(5/2)/log(4)>0`. Floors are uniformly lower order. Root and tail L have exponents below .017, so `2L<=Delta` eventually and all packet-entry costs remain lower order.

## 4. Recovery precision and immutable representatives

For the supplied exact linear taper, the condition count is

\[
 hL(2u-2+2^{1-u}),
\]

and the candidate h is the smallest positive integer making that count exceed `M(2L-1)`. Hence `h=(1+o(1))M/u` uniformly in active calls. The exact rational Hermite multipliers have valuation `-B_i`, and evaluation of the jet at `-t/2^(a+1)` loses exactly at most `(q_i-1)(a+1-i)`. This verifies the candidate's sufficient precision, with positive increments.

At a retained level, `D_i>=2^(a_prev+g+1)`. Inherited precision is at most `s lambda^O(1)2^a_prev`; active `M>s/lambda` and `u=O(lambda)` therefore give

\[
 p_{\rm inherited}/(MD_i/u)\le\lambda^{O(1)}2^{-g}=o(1).
\]

The jet evaluation loss is negligible by the same superpolynomial factor. Thus `p_t<=(6+o(1))MD_i/u` uniformly. This is a valid replacement for the source's much larger doubled-taper gap. Precision increases along every recursive path, so creation-time representatives remain canonical at every later precision. No use is made of the false assertion that canonical lifting preserves multiplication.

All precisions remain polynomial in s; Hermite common denominators have polynomial bit length; the field degree `4lambda` still supplies enough residue-distinct interpolation points since the deformation degree is below `s^4` eventually.

## 5. Factorial features do not incur hidden precision loss

For an actual crossing row, `d0=t-y0+x` has valuation at most i. With `T=t+2^(a+1)zeta` and `z_x=2^(i+1)/(T-y0+x)`,

\[
 z_x/2-2^i/d0\in2^{a+1-i}\mathcal O.
\]

The finite tile range is `b<D_i/2=2^(a-i-1)`, safely inside the range required by the supplied near-prime-subring factorial-divisibility lemma. The exact finite Cauchy identity then gives weights `1+b+2v_2(b!)`.

The source binomial is computed as an ordinary integer. Its remaining denominators are odd integers; target denominators are `1-hz_x`, which are units because `z_x` is even. The extra factorial is **multiplied** into the target. There is no nonunit factorial division and no lost precision. Factoring the known power of two from `d0+2^(a+1)zeta` also does not require extra input precision: its integral expression is evaluated directly.

The audit used the original packet-entry expansion routine, already sufficient here. The optional streamed finite-difference routine is not needed for this certificate and was not independently revalidated in this pass. Therefore any independent question about that optional routine does not affect this verdict.

## 6. Entropy, recursion, arithmetic, and space

Weights grow as `3b+O(log(b+2))`, so their generating product has upper envelope `(pi sqrt(2)/3+o(1))sqrt(cp)`. One may use all padded tile families, including unused ones, to obtain a clean upper bound. Here `p/c` has scale `D_i^2/u`, and `D_i>=2^g`; the saddle tends to zero uniformly. The logarithmic-weight perturbation contributes at most `O(c log^2(1/theta))`, which is lower order uniformly because `theta=Theta(sqrt(u)/D_i)`.

Combining the sharp c and p bounds gives local base-two coefficient

\[
 K(r)=\frac{2\pi}{\ln2}\sqrt{\frac23(1-1/r)}.
\]

Summing along a path produces

\[
 C=\frac{K(37)}{\sqrt{10/1043}}+
 \frac{(2/37)K(8)}{\sqrt{1/236}(1-\sqrt{5/2}/4)}.
\]

I independently recomputed `C=84.06627149423657...`. A rigorous safe-85 certificate does not need floating point: use `pi<22/7`, `ln2>693/1000`, and the exact square comparisons

\[
 \sqrt{12516/185}<8226/1000,\quad
 \sqrt{413/3}<11734/1000,\quad
 \sqrt{5/2}<1582/1000.
\]

They yield

\[
 C<1659638632/19727253=84.129231\ldots<85.
\]

The logarithm bound follows already from the first four positive terms of `ln2=2 sum_{k>=0}1/((2k+1)3^(2k+1))`. The classical `pi<22/7` also follows from the positive integral `integral_0^1 x^4(1-x)^4/(1+x^2) dx=22/7-pi`.

Polynomial branching accumulated over `O(log lambda)` levels adds only `O(lambda log lambda)` to the binary exponent. Leaf summation adds `O(s/lambda)`; original entries add `A s^.9`; new packet entries add `O(L log s)`. Each is `o(s/sqrt(lambda))`. Immutable descriptions avoid multiplying entry-routine nesting costs. Branching is independent of the original description length, so its factor remains one fixed polynomial. A depth-first traversal stores only polynomially many field/ring coordinates, partial sums, tuples, and description references. Thus the proposed coefficient preserves polynomial working space.

## 7. Independent executable evidence

Only newly written local standard-library code was executed; no supplied executable, installation script, or upstream mutation was used.

* `verify_combined_independent.py`: all guards are explicit exceptions, active under `python -O`.
* `independent_checks_normal.json`: PASS.
* `independent_checks_optimized.json`: PASS, byte-identical to the normal result.

Coverage:

* 3 multigraph labeling fixtures; 17 exact conditional-expectation identities checked against 279 exhaustive label completions.
* 12 padded-packet fixtures, explicitly counting 20,274 padded slots, including exact crossing fraction and row/column symbol balance.
* 1,264 actual interpolation-row fixtures in `Q[U]/(U^2+U+1)` (unramified at 2), with 2,480 exact finite Cauchy separation identities and 2,480 target valuation checks. Non-prime-subring shifts U and 1+U are included.
* 30 exact taper schedules and 432 independently constructed rational Hermite multipliers, including exact jet count, minimal h, positive precision increment, and the full multiplier precision bound.
* Exact root/tail packing inequalities and the rational safe-85 certificate.

These checks support local algebra and transcription; they do not establish the asymptotic proof by themselves. No access, permission, installation, or computation blocker remained in this review.
