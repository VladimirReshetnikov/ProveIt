# Independent audit of the proposed new results

This note records an independent review of `rectangular_theorem.tex`, the corrected `rectangular_schedule_certificate.py`, and `order_improvement.md`. It audits the new deductions relative to their explicitly imported mathematical interfaces. It is not an independent formal certification of the underlying SAT theorem.

## Rectangular cached contraction certificate

**Outcome:** no fatal mathematical gap found in the corrected result. The first version of the checker omitted the positive epsilon on the near-quadratic branch; the schedule agent caught and corrected this before the final review. The precise constants are distinct:

- time: `33.99389085923207 < C_T < 33.99389085923500`;
- space: `33.99372089062761 < C_S < 33.99372089063055`.

Thus 34 is a valid eventual coefficient for each, with subexponential space. The equal-coefficient shorthand is only appropriate for the rounded 34/34 statement.

### Rectangular arithmetic

Write the three logarithmic matrix dimensions as x≥y≥z. The two external facts are α>3/10 and ω<19/8 over the rational field. Interpolation between dimensions `(n,n^(3/10),n)` at exponent `2+epsilon` and square multiplication at exponent19/8 gives

`max{x+y, x+(47/56)y+(15/28)z}+epsilon*y`.

Indeed `(19/8−2)/(1−3/10)=15/28`; the coefficient of y is `1−(3/10)(15/28)=47/56`. The two base logarithmic sizes are `(y−z)/(1−3/10)` and `(z−(3/10)y)/(1−3/10)`, both nonnegative in the interpolated regime. Rounding their recursion depths independently incurs constant multiplicative padding and rank overhead, since the finite algorithms are fixed. The endpoint z≤.3y is handled by padding the inner dimension. Degenerate constant-size dimensions can be handled directly within the same bound.

The corrected envelope is

`max{(1+epsilon/2)(x+y), x+(47/56+epsilon)y+(15/28)z}`,

because y≤(x+y)/2. Omitting epsilon from the first branch would not be justified by a fixed exponent2+epsilon algorithm.

The dimension-permutation step uses the trilinear symmetries of the finite matrix multiplication tensor. Permute the three vector factors in the finite bilinear rank identities, then execute the resulting algorithm; it is not necessary to transpose an arbitrary cached program or assume the desired output is merely a trace. The largest of the three pairwise dimension products is always one of the original input/output array sizes.

The common-tilt entropy estimate applies to each of the six possible logarithmic-dimension orderings. Maximizing its squared weight norm over permutations aligns the largest squared weights with the largest **cardinalities**, by rearrangement. This justifies the cardinality formula without assuming the actual logarithmic dimensions have the same ordering as their class cardinalities.

### Exact bit cost and space

A fixed rational bilinear algorithm has finitely many fixed denominator primes. On every other odd prime it remains an exact identity. In the polynomial-rank coefficient module, each pair of coordinates can be lifted to nonnegative integers and multiplied exactly by CRT. Every scalar product entry is bounded by `d_2 (2^p−1)^2`; log(d_2) and p are polynomial in s. Therefore polynomially many polynomial-bit primes suffice, with polynomial bit overhead. Signed ring multiplication-table coefficients are applied only after the nonnegative coordinate products are reconstructed. No division by2 or a nilpotent in the coefficient ring is involved.

For space, schedule one recursive rank product at a time and accumulate its contribution to the output. Each fixed base algorithm has constant rank and dimensions; inputs, output, and one product's temporary arrays occupy a constant multiple of the largest input/output array. Along a recursion path all dimensions shrink by fixed factors, so the array sum is geometric. The same holds for tensor products and for transposed identities; large-dimension blocking and coordinate/CRT loops are sequential. The extra field bits per ring cell are polynomial. Hence the claimed table-size space exponent is sound.

### Numerical and recursive accounting

The independent execution of the exact certificate passed all gates. The four time candidates are enclosed by:

1. `[33.99389085923207, 33.99389085923500]`;
2. `[32.81282130766373, 32.81282130766667]`;
3. `[31.41262913532471, 31.41262913532757]`;
4. `[33.65738535090702, 33.65738535091035]`.

The root is strictly largest. The memory candidates have upper endpoints33.99372089063055,9.59064106659042,2.31744103041941,1.15866939856963. Ancestor and descendant arrays add rather than multiply. Recursive child multiplicities are explicitly charged through `a_r K_i`; they have not been dropped from the time recurrence.

The smallest high-degree packing slack occurs at the root: exponent499997/500000<1. All other displayed packing gates also have positive fixed slack. The active-depth bootstrap is valid: eventual shrink≤11/20 and taper ratio5/8 ensure `u_min >= lambda^(1−ln(8/5)/ln(20/11)+o(1))`, whose exponent is positive. The thin gap b=ceil(6log2 lambda) absorbs inherited precision, and packet degrees remain s^(0.0499+o(1)). Choosing tolerance O(lambda^-2) makes accumulated padding over O(log lambda) depths vanish.

The scalar arithmetic certificate verifies parameters and inequalities. It does not implement the field algorithms or the full contraction engine. Description-length work must be charged as a fixed polynomial per visited node, while recursion multiplicity factors depend only on s, as in the inherited immutable-description interface.

## Asymmetric Hermite minimax theorem

**Outcome:** the new asymmetry extension and finite real minimax formula are valid as stated, provided the scope remains the independent-jet top-cardinal precision certificate.

- The highest raw jet at node t has coefficient `E_t(0)(−t/2^N)^(q_t−1)`, because the reciprocal expansion of E_t at t has constant term1. Its displayed valuation loss is correct for integer multiplicities.
- Writing valuations as congruence indicators gives the exact subtree-mass identity. The depth-N leaf contribution supplies the q_t left after cancellation with the highest-jet term.
- The extension of the active-node maximum to all leaves is valid. An inactive leaf that shares a positive-mass annulus can be improved by moving into the positive child at its nearest positive-mass ancestor. The remaining zero-branch terms and normalization D_i are constant on the annulus. An empty annulus has strictly negative auxiliary loss.
- Consequently the all-node objective is convex on nonnegative real multiplicity vectors. Automorphisms of the rooted residue tree fixing0 preserve v2(t) and v2(t−v), and act transitively on each valuation annulus. Averaging is therefore allowed and cannot increase the objective.
- The symmetric finite formula follows directly from summing class sizes: the positive term is `(2D_i−1)q_i`, and a later annulus h contributes negative coefficient `(h−i)D_h q_h`. After division by D_i these are exactly the stated coefficients.
- The backwards r_i,c_i recurrence gives a componentwise upper envelope on every feasible symmetric profile. Its saturated profile attains the required mass and objective. Scaling c for mass below C retains nonpositive losses. This proves the exact real relaxation, not merely a heuristic symmetric candidate.
- Rounding every symmetric q_i upward increases each normalized affine loss by less than2, since its own diagonal coefficient is below2 and all other coefficients are nonpositive. Thus the arbitrary-node integer optimum lies in the claimed additive interval, without asserting exact integer optimality.
- The path-expansion perturbation bound for R and the comparison C/R≤(a+1)/D_min are valid. Under the stated thin-gap regime, the leading optimum is `(6+o(1))M/u`.

The inherited coarse Markov-chain proof also works for real nonnegative profiles: it never uses integrality. Thus the coarse asymmetry extension is valid when the subsequent highest-jet term is nonnegative under its M≥8u assumption.

This theorem does **not** assert independence of the jets actually attainable from a tensor-network deformation. It therefore does not rule out correlated recovery, cancellation among different nodes, a different deformation, or a new summation architecture. It establishes that asymmetric multiplicity selection cannot lower the specified precision certificate's optimal leading scale.

The asymmetric Hermite checker was also independently rerun: 6+125+2187=2318 exhaustive multiplicity vectors and112 rational finite-minimax cases passed. These finite checks support the proof but are not a formal certificate for all sizes.

## Closing twenty-packet audit and polynomial-space result

The initial audit covered nineteen refinement packets. The final review cutoff is **twenty** at `dde01c4a63b822c25b8eb345299346c36f837b49`. Placement commit `450252e9d86c155f188b485629b9755c5c665371` added `sat_adaptive_contraction`. The parent verified byte identity of180 files from the four initially incoming packets after placement. This was the parent's byte audit; the new mathematical audit below was performed independently here.

The new adaptive packet's recursive-conditioning identity and exact call ledger are valid. With pair weights fixed, all pair-index domains form a Cartesian product. Conditioning on a balanced separator leaves independent internal sums; their costs add over sibling branches. A leaf's true child-contraction call count is the product of the ancestor-cut domain sizes, and the total is the sum of these products over leaves. Internal work is covered by the same ledger, and depth-first evaluation uses polynomial space. The path profile v(r) is correctly computed by its balanced-bisection recurrence, with v(16)=170.

The packet's generic polynomial-space coefficient55.70947831891 is valid relative to its source interface. Its factor sqrt(17/24) changes the uncached summation organization, not the pair entropy constant, so it cannot be applied as a blanket multiplier to a cached theorem. Combining this identity with the already-filed multistage schedule gives the stronger prior coefficient55.40466590661. The new streamed theorem correctly compares against that composed value.

The new `streamed_theorem.tex` uses arities16,16,8,6,5,4 thereafter; path cardinalities170,170,42,24,18,10; wire factors1,1/8,1/64,1/256,1/768,1/1920; and the stated rational retained fractions. The cumulative capacities and all six high-degree packing gates were independently checked. The other packing exponents are below1/4. The minimum active taper diverges by the same shrink11/20 versus taper5/8 bootstrap. The precision guard, immutable descriptions, polynomial description-length factor, and true child-oracle costs are retained.

Independent execution of `streamed_schedule_certificate.py` gave these exact interval enclosures:

| Quantity | Lower endpoint | Upper endpoint |
|---|---:|---:|
| New streamed coefficient | 53.97753119806754 | 53.977531198072846 |
| Stronger prior composition | 55.404665906606695 | 55.404665906612024 |
| Newest packet's standalone coefficient | 55.709478318909945 | 55.70947831891013 |

No fatal issue was found in the new theorem. It gives eventual polynomial-space coefficient54. Its numerical comparison and source attribution correctly treat recursive conditioning itself as imported from the newly reviewed packet.

The adaptive packet also has a valid cached three-triple partition theorem with generic time36.75031252383623 and memory34.02417800749051, plus a stronger-premise root-degree≤s^(1/12) branch at time15.3919331988 and memory14.2501611298. The latter must be retained in the final portfolio; neither generic34 nor generic54 should be described as numerically dominating it on its narrower class.

The cached rectangular theorem remains valid at C_T≈33.993890859235 and C_S≈33.993720890631. The final conclusions therefore improve the explicit generic certificates in both resource regimes while retaining the same s/sqrt(log s) logarithmic order. They do not resolve the stronger conditional summation targets, establish a numerical coefficient per SAT variable, or rank the separate manuscript's unspecified hidden constants.
