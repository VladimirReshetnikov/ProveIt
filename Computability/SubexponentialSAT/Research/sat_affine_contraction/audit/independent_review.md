# Independent audit of the four-direction affine cached construction

This note audits the new local support argument, the paid recurrence, and the explicit rational schedule. It does not independently reprove the inherited Cauchy, precision, packing, or SAT-reduction identities.

## 1. Correct local cost model

Combine the two directed mode-list domains on each unordered pair of groups. For the resulting unordered entropy vector h, for each fixed nonnegative support w, the directed weighted entropy estimate gives `w dot h <= (sqrt(2)||w||_2/r + o(1))*K`, where `K=(pi*sqrt(2)/ln 2)*M/sqrt(u)`.

At a binary table merge, group the index sets into the left-to-right, left-to-outside, and right-to-outside axes. If their entropy lengths are X,Y,Z, rectangular blocking of a square matrix algorithm of exponent at most 12/5 gives exponent `X+Y+Z-(3/5)*min(X,Y,Z)`. This equals the maximum of three linear forms with coefficients 2/5 on one of the three axis classes and 1 on the others. The integer support coordinates are therefore exactly {0,2,5}, divided by 5. The same model applies to the final triangle contraction.

The working memory of the fast multiplication must be stated explicitly. A fixed-block bilinear algorithm can process recursive products sequentially and accumulate the outputs, retaining O(input entries + output entries) scalar storage, up to polynomial overhead. For rectangular blocking the temporary square block fits within those same input/output bounds. Thus boundary size, rather than operation-count exponent, can correctly control space. The established coordinate/CRT bridge must also retain its polynomial bit and coordinate overhead.

All expensive evaluations of each original group factor are separate recursive child contractions. They are paid by the coefficient `alpha_r=sqrt(2(r-1))/r`, not hidden in the matrix supports. The correct recurrence is the sum of a recursive term with this coefficient and the nonrecursive table-work term.

## 2. The affine support argument

For r=9, identify the groups with F_3^2 and take the four partitions into the fibers of x, y, x+y, and x+2y. A pair of distinct points is internal in exactly one partition. Within each triple, first merge its last two vertices, then merge the first vertex; contract the three completed blocks as a triangle.

For each plan there are 21 time supports (seven operations times three discounted axis choices) and 15 boundary supports (nine singleton caches, three intermediate pairs, three completed triples). The six-group intermediate in contracting the final triangle has the same cut as the complementary three-group block and is therefore covered. The scalar final result uses no further boundary.

Let t denote a time support already divided by 5 and b a zero-one boundary support. The checked uniform bounds are:

- `||t||^2 <= 486/25`;
- between different plans, `t dot t' <= 288/25`;
- `||b||^2 <= 18`;
- between different plans, `b dot b' <= 8`;
- between different plans, `t dot b <= 48/5`.

For a plan j put `F_j=max_t t dot h` and `G_j=max_b b dot h`. Choose a support realizing the maximum of `F_j` and `rho*G_j` in each plan. If k of the four selected supports are time supports, the square norm of their sum is at most

`Q_k(rho) = k*486/25 + k*(k-1)*288/25`
`             + rho^2*((4-k)*18+(4-k)*(3-k)*8)`
`             + 2*k*(4-k)*rho*48/5`.

This is a valid worst-case bound even when the individual pairwise maxima are not simultaneously attainable. Their simultaneous attainability is not required for an upper bound.

The clean strongest value supported by this certificate is `rho*=3/sqrt(7)`. At k=0, `Q_0=168*rho*^2=216`; at k=4, `Q_4=216`. For k=1,2,3, use `rho* < 567/500`; Q_k is increasing in rho on the positive axis. The exact positive margins at this rational upper bound are respectively

`216-Q_1=9261/125000`,
`216-Q_2=7443/62500`,
`216-Q_3=11799/125000`.

Equivalently, the sharper symbolic identity is
`Q_k(rho*) = 216 - 8*k*(4-k)*(6/5-rho*)^2 <= 216`.
This identity and the independent rational bounds agree.

Therefore the average support z has norm squared at most 216/16=27/2. By the unordered entropy estimate,

`min_j max(F_j,rho*G_j) <= (1/sqrt(3)+o(1))*K`.

The corresponding local time and space coefficients are exactly

`beta_time=1/sqrt(3)`, `beta_space=sqrt(7/27)`.

## 3. Exact selection without real logarithms

For each plan form the integer products

`Ptime = max_v product_e |I_e|^(v_e)` and
`Pspace = max_b product_e |I_e|^(b_e)`.

They satisfy `log2(Ptime)=5F_j` and `log2(Pspace)=G_j`. Let

`A=(Ptime-1).bit_length()=ceil(log2(Ptime))`,
`B=(Pspace-1).bit_length()=ceil(log2(Pspace))`.

Select a plan minimizing the entirely integral score `max(7*A*A,225*B*B)`, breaking ties by plan index. This score is 175 times the square of `max(A/5,(3/sqrt(7))*B)`. Ceiling errors increase that objective by at most `3/sqrt(7)`, uniformly. Hence the selected real F,G satisfy the same leading bounds with an O(1) additive exponent error. All products and their bit lengths are polynomial in the root size in this framework. Empty mode-list arrays are skipped before selection. No irrational comparison or uncomputed logarithm is hidden in this rule.

The ceiling-and-square rule attains the limiting coefficient above while using only integer comparisons.

## 4. Independent twelve-group finite check

The four twelve-group plans delivered in `data/twelve_plans.json` were independently reconstructed, the two-pair-then-four-group operations were rebuilt using cut sets, 30 supports per plan were generated, and all 30^4=810000 sums were exhaustively computed. The results are:

- maximum squared norm of the unnormalized support sum: 9864;
- sum of all those squared norms: 3494275200;
- one maximizing tuple of support indices: [27,27,28,27];
- normalized coefficient squared: `2*9864/(16*25*12^2)=137/400`.

This independently agrees with the primary certificate. The finite enumeration concerns the complete explicitly stated support family, not an empirical sample of input entropy vectors.

## 5. Rational schedule and global time

The current checked schedule file uses the prefix alphabets 9,12,9,7 and tapers

`eta0=1577/100000=0.01577`,
`eta1=303/25000=0.01212`,
`eta2=73/20000=0.00365`,
`eta3=1/250=0.004`.

The eventual alphabet is 4 with tail ratio 63/100, total tail budget 723/50000=0.01446, and first tail taper 26751/5000000. The total budget is 1/20. These are the exact parameters used in both report and code.

The child mass coefficients are 1,2/9,1/27,2/243,4/1701. With `u_d=floor(eta_d*(lambda-ceil(sqrt(lambda))))` and packet exponent `a_d=sum_{j<=d}u_j+(d+1)*ceil(6 log2 lambda)`, the inherited-degree packing gates are strict in the prefix and attain the permitted boundary only in the four-group tail, where the square-root reserve supplies the margin. Fresh-side and packet-rounding exponents are <=1/4+o(1). Generated tensor degrees stay below the generic root degree cap.

The eventual child ratio is at most 11/20, while the taper ratio 63/100 exceeds 11/20. Thus the least active taper grows as a positive power of lambda, floors have vanishing relative error, and the inherited precision buffer dominates ancestral precision uniformly. There are O(log lambda) active levels.

The logarithm of the paid time recurrence is the maximum of `sum_{j<d} alpha_j*K_j + beta_d*K_d` and the terminal sum of alpha terms, with lower-order leaf cost. Independent numerical values, for transcription checking only, are:

| Endpoint | Coefficient |
| --- | ---: |
| root | 29.468832852887598 |
| depth 1 | 30.25703561149638 |
| depth 2 | 30.01092197330065 |
| depth 3 | 30.087811788920224 |
| first tail local work | 30.050062557957002 |
| infinite paid terminal sum | 30.24246506295925 |

The dominant branch is depth 1. Exact rational interval certificates remain the authoritative numerical validation.

## 6. Global space

The ancestor multiplication counts do not multiply live memory: child calls are processed one at a time, retaining only the already built parent tables and the stack. Thus space is governed by the maximum local table exponent across levels, up to polynomial overhead. The root dominates, including the live O(log lambda) levels and the fast-matrix workspaces discussed above.

With the optimal joint selector, the global root space coefficient is

`(pi*sqrt(2)/ln 2) * sqrt(7/27) / sqrt(1577/100000)`
`=25.989067718690217...` (the exact interval checker is authoritative).

This is about 15.49% below the reviewed cached space coefficient 30.753912832055..., with the time coefficient about 2.0523% below 30.891018920366.... These are comparisons of asymptotic upper-bound certificates under identical normalized-wire premises, not measured running times. The recurrence still has the s/sqrt(log s) scale and the inherited SAT reduction still has the prior logarithmic order.

## Conclusion

The local affine joint argument and the twelve-group finite support certificate are sound under the stated entropy and matrix-work interfaces. The revised rational schedule closes the paid recurrence. The stronger joint selector above improves the space constant without changing the time proof. A complete deliverable should state the imported identities, the exact schedule, the paid child evaluation coefficient, the near-quadratic matrix workspace, and the source-only status of the new Anthropic formalization explicitly.
