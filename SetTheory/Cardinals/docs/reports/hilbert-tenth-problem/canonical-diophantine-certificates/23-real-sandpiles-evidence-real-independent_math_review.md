# Independent review: orthant-exact binary finite-prism certificates

3 October 2026. This review independently checks the real-zero argument, coefficient support, and revised arithmetic ledger. No frozen input packet was modified.

## Verdict

**Pass, with a stronger primary construction.** Let `Q` be the base cubic for any admissible nonempty finite prism and natural-valued input in the frozen packet. Replace its vertex product `f_v g_v` by

`f_v (g_v + k_v + c_v)`.

Call the resulting polynomial `Q_R`. Equivalently,

`Q_R = Q + sum_v f_v(k_v+c_v)`.

Then, in the unchanged coordinate space,

`{x in R_{≥0}^W : Q_R(x)=0} = {x in N^W : Q(x)=0}`.

Consequently this real zero set is either empty or consists of the unique complete natural witness from the base theorem. Existence is still exactly the stated finite global binary-stabilization condition; it is not asserted for every input or prism.

The merged construction uses **no new coordinates, no new displayed summands, no new collected monomials, no higher degree, and no higher collected coefficient height**. It preserves the full natural zero fiber, not just the projection to the odometer.

The original proposed `Q_sharp`, adding all three category pair-products per vertex and all ten selector pair-products per edge, also has the same real-zero theorem and unchanged collected support. Its extra penalties are unnecessary for real soundness.

## 1. Sources and verification boundary

Read sources (original-read hashes preserved below; relative locators identify
the byte-identical snapshots now bundled for portable replay):

- `approved_base/PROOF.md`, SHA256 `6e5a053e7f599a17ee77c49e3092e041c7ea3e0de62156095fe9ece5e761d60e`
- `approved_base/prism_certificate.py`, SHA256 `bf22889eebe546593e933c120c72efb95e5504e6e2ab7d2bc10da4a5dd6623a2`
- The current newly authored `real_certificate.py`, including its `merged`, `flat`, and `sharp` variants

All computation used local code with bytecode writing disabled. No upstream program, giant universal prism, real algebraic solver, or infinite sandpile was executed. The all-real conclusion below is an exact proof; finite coefficient checks supplement it.

## 2. Every displayed term is nonnegative

The base terms are unweighted affine squares, affine squares weighted by sums of nonnegative coordinates, or products of nonnegative coordinates/sums. The new product `f(g+k+c)` has the same property.

Thus at a nonnegative-real zero every displayed term vanishes individually. Equivalently, because `Q_R=Q+sum f(k+c)` and both pieces are nonnegative, both the base equations and all equations `f(k+c)=0` hold. In particular the original equation `fg=0` remains valid.

## 3. The base edge gadget is already one-hot over the reals

This does not require new selector pair-products or integral ranks.

Write the oriented rank difference as `delta=r_w-r_v` and the nonnegative edge gap as `sigma`. The simplex square forces the five nonnegative selectors to sum to 1. A positive selector, through its own weighted-square term, forces respectively one of

- `delta=-2-sigma <= -2`
- `delta=-1`
- `delta=0`
- `delta=1`
- `delta=2+sigma >= 2`

These five conditions lie in pairwise disjoint subsets of the real line. Therefore at most one selector can be positive. Their sum being 1, precisely one is 1 and all others are 0.

In a middle case, the term `(lambda_neg+lambda_zero+lambda_pos)sigma` forces `sigma=0`. In an extreme case the corresponding equality uniquely determines the nonnegative gap. This proves exact comparisons and a unique gap before rank integrality is established.

In particular the expressions in the base compiler are exactly

`A_v = number of internal neighbors w with r_w >= r_v`,

`B_v = number of internal neighbors w with r_w >= r_v-1`.

The additional important identity is

`B_v-A_v = number of internal neighbors w with r_w = r_v-1`.

Although a generic real comparison would count the interval `[r_v-1,r_v)`, this gadget permits no edge difference in `(-1,0)`. Thus its only possible difference in that interval is exactly `-1`. Both orientations in the compiler give this identity: lower endpoints use the `neg` selector and upper endpoints the `pos` selector.

## 4. The merged vertex product forces binary support

At a vertex put `u=k+c` and `r=k+2c+beta`. The category square gives `f+u=1`; the added condition gives `fu=0`. All coordinates are nonnegative. Hence exactly one of the following holds:

1. `f=1,u=0`, so `k=c=0`; the original `(f+k)beta=0` then gives `beta=0`, hence `r=0`
2. `f=0,u=1`, so `k+c=1` and `r=1+c+beta >= 1`

Thus the support variable is already binary and **every rank is either 0 or at least 1**. This conclusion does not assume that `k` and `c` are individually binary.

At every vertex with `c>0`, both weighted residuals apply, since then `u=1`:

`z=A+g`,

`B=z+1+h`.

Consequently `B-A=1+g+h >= 1`. The exact comparison identity from Section 3 proves that this vertex has a neighbor of rank exactly `r-1`.

Suppose now that an active vertex had both `k>0` and `c>0`. The term `(f+k)beta=0` forces `beta=0`; since `k+c=1`, its rank is `r=1+c`, strictly between 1 and 2. Its required predecessor would have rank strictly between 0 and 1, contradicting the rank dichotomy just proved.

Mixed active categories are therefore impossible. The only cases are

- `f=1,k=c=0,beta=0,r=0`
- `k=1,f=c=0,beta=0,r=1`
- `c=1,f=k=0,r=2+beta >= 2`

So the vertex categories become one-hot without adding `kc`.

## 5. Finite descent makes all ranks integral and bounded

Every category-`c` vertex has a predecessor at rank exactly one less. Since its own rank is at least 2, that predecessor has rank at least 1 and lies in the active support.

Follow predecessors while the current vertex is category `c`. Successive ranks strictly decrease by exactly 1, so no vertex can repeat. There are only `N=|supp(u)|` active vertices. The chain must terminate at an active vertex that is not category `c`; the preceding classification says this is necessarily category `k`, of rank 1.

If the chain has `m` edges, the initial rank is exactly `m+1`. Therefore every active rank is an integer in `{1,...,N}`. This also excludes arbitrary real offsets, fractional rank components, and cycles consisting solely of category-`c` vertices.

## 6. Every coordinate is natural

Once `u` is binary, the balance residual and natural input heights give

`z_v = eta(v)-6u_v+sum_{w~v in P}u_w`,

an integer. Orthant nonnegativity and `z+ell=5` give `0<=z<=5` and integral `ell`.

The remaining coordinates are determined as follows:

- Category coordinates and edge selectors are already 0 or 1
- `beta=0` off category `c`, and `beta=r-2` on category `c`
- On active vertices `g=z-A`; off the support `f=1` forces `g=0`
- On category `c`, `h=B-z-1`; otherwise `(f+k)h=0` forces `h=0`
- Extreme edge gaps are `abs(delta)-2`; middle edge gaps are 0
- A halo gap is `5-eta(x)-u_neighbor`

Every right-hand side is integral; every coordinate is nonnegative by the domain. Thus the complete real witness belongs to `N^W`.

As in the base theorem, `z,ell,g,h` and halo gaps are at most 5; `beta` and edge gaps are at most `max(N-2,0)`. No real auxiliary coordinate remains free.

## 7. Full natural fibers, soundness, completeness, and uniqueness

Any natural zero of the base polynomial has one-hot categories by its category simplex. Therefore `f(k+c)=0` at that same tuple. It remains a zero of the new polynomial, with no extension or choice of new coordinates.

Conversely Sections 2–6 prove that every nonnegative-real zero of the new polynomial is a natural zero of the base polynomial. This proves equality of the complete fibers and transfers the original existence theorem and uniqueness theorem without weakening either.

There is also a direct soundness/uniqueness check:

- Fire active vertices in increasing integral rank, with any ordering inside tied layers
- Immediately before an active vertex fires, its height is `z_v+6` minus the number of its active neighbors not yet fired
- Such neighbors have rank at least `r_v`; their number is at most `A_v<=z_v`, so the firing is legal
- Balance gives the final interior height `z`; the halo constraints give stable exterior heights; all other exterior sites are initially stable and unchanged

Thus a real zero produces the finite legal global binary stabilization, and the finite sink odometer is unique by least action.

Given the resulting unique `u,z`, the ranks are also unique. At parallel round `j`, inductively the remaining support is precisely `{v:r_v>=j}`. Rank-`j` vertices are eligible by `z>=A`. If `r_v>j`, preceding-round failure gives

`z_v < B_v = deg_{r_neighbor>=r_v-1}(v) <= deg_{r_neighbor>=j}(v)`,

so such a vertex is not eligible. The assigned layers are exactly the earliest parallel burning layers. Hence the ranks, categories, and every listed gap are forced.

## 8. Boundary cases checked

- **Empty support:** all vertices have rank 0; every edge selects equality and has gap 0. There is no descent argument to perform, and every other coordinate is still forced
- **Singleton prism:** `A=B=0`. A category-`c` vertex would require `B=z+1+h>=1`, impossible. A binary active witness is category `k`, rank 1
- **Rank 2:** its predecessor is rank 1, necessarily category `k`; an inactive rank-0 vertex cannot serve
- **Mixed rank in `(1,2)`:** the forced predecessor lies in `(0,1)`, which is prohibited by binary support and the category residual
- **Rank ties:** equality selectors are exact; legality permits any tied-layer ordering while the witness still records the unique parallel layers
- **Differences `-2,-1,0,1,2`:** the two extreme boundary differences have gap 0 and are disjoint from the three middle cases; there is no double choice
- **Inactive/active edges:** rank-0 vertices are allowed as neighbors, but are excluded from all active success counts and category-`c` predecessor counts by the relevant thresholds
- **Sides of length 1:** internal degree changes but each vertex retains six total internal/exterior incidences; neither the descent argument nor coefficient computation assumes positive internal degree
- **No certificate exists:** the real zero set is empty, not a nonintegral alternative

The documented spurious base zero for a singleton of height 1 has `f=5/6,k=1/6,c=0`. The new penalty there equals `5/36>0`, so that counterexample is removed.

## 9. Exact coefficients of all proposed penalty monomials

At every vertex, in the **fully collected base polynomial**,

`[fk]Q=2`, ` [fc]Q=2`, ` [kc]Q=86`.

The first two coefficients come only from the category square. For `kc`, the contributions are

- 72 from the vertex's balance square, whose coefficients of `k,c` are both 6
- 2 from its category square
- `2d_v` from balance squares at its internal neighbors
- `2(6-d_v)` from its exterior halo incidences

Their sum is `72+2+2d_v+2(6-d_v)=86`. No other term produces a pure degree-2 `kc` monomial: rank-square interactions are selector-weighted cubics or selector/category cross terms; the success and failure residuals do not add such a monomial.

For every pair of distinct selectors belonging to one edge,

`[lambda_i lambda_j]Q=2`.

The contribution is exactly the edge simplex square. Other terms involving two edge selectors carry a vertex-category weight and therefore have degree 3.

It follows that the merged/flat construction changes only `fk,fc`, from coefficient 2 to 3. Every changed monomial was already in the support and remains there. No coefficient is cancelled. Its collected support and degree are exactly those of `Q`.

The coefficient height is also **exactly unchanged**: the only changed absolute coefficients become 3, whereas the unchanged coefficient 86 of `kc` occurs at every vertex and the prism is nonempty.

For the optional full-pair construction, `kc` becomes 87 and same-edge selector pairs become 3. Thus support and degree remain identical there too. Exact coefficient-height equality is claimed for the merged/flat construction; it need not hold for the full-pair construction.

## 10. Exact ledger changes for the merged display

The old product `f*g` has residual length 1 and weight length 1. The new product `f*(g+k+c)` has residual length 1 and weight length 3, with three distinct variables in its weight.

Under the base packet's stated cost convention, per vertex this changes

- Raw records: 1 to 3, increase 2
- Evaluation multiplications: 3 to 5, increase 2
- Evaluation additions inside the product: 0 to 2, increase 2
- Expansion coefficient multiplications: 1 to 3, increase 2

The number of displayed terms and their final summation additions do not change. Therefore, writing `R,X` for the old raw-record and expansion totals,

- Witnesses: `8V+6E+H`, unchanged
- Displayed summands: `8V+7E+H`, unchanged
- Plain squares: `3V+E+H`, unchanged
- Weighted squares: `2V+5E`, unchanged
- Product summands: `3V+E`, unchanged
- Raw records: `R+2V`
- Expansion coefficient multiplications: `X+2V`
- Evaluation multiplications: `35V+76E+4H`
- Evaluation additions: `23V+63E+3H+A+L-1`

Here `A,L` have the base packet's meanings. These formulas concern the specified straight-line convention, not Python's implementation-level operation count.

## 11. Independent finite checks

Two locally run checks used every length triple in `{1,2,3}^3`, prism lower corner `(-2,3,-4)`, backgrounds 0 and 5, and additions `(7i mod 19)` at the lexicographically indexed vertices. This gives 54 input/geometry cases.

First, an independent sparse affine-polynomial multiplier expanded each displayed base term without calling its `records()` expansion. Its fully collected result equalled the compiler's polynomial in every case. It verified

- 1,296 vertex penalty pairs: 432 each of `fk,fc,kc`
- 6,480 distinct same-edge selector pairs
- Base coefficients 2 in all 7,344 relevant cases and 86 in all 432 `kc` cases
- Exact support preservation and degree 3 for the flat and full-pair additions

Second, the current `RealCompiler` implementation was checked on the same 54 cases. All passed:

- `merged.polynomial() == flat.polynomial()`
- Exact merged/base support equality
- Exact merged/base coefficient-height equality
- Fully collected stream equals the globally collected polynomial
- Every shared key of the enumerated and closed merged ledger agrees
- All stated merged ledger deltas hold exactly
- Enumerated and closed flat/sharp ledgers also agree

These checks are not a proof of absence of spurious real zeros. Sections 2–7 provide that proof for arbitrary admissible finite prisms and natural inputs.

## 12. Reproducible independent checker and receipts

The checks in Section 11 are preserved in `independent_coefficient_ledger_checks.py`, with full per-case results in `independent_coefficient_ledger_receipt.json`. An optimized run is preserved in `independent_coefficient_ledger_receipt_optimized.json`; the two receipts are byte-identical. Checks use explicit exceptions and remain enabled under Python `-O`. The checker pins and verifies the frozen base compiler hash before import and again after all checks, and suppresses bytecode writes.

Reproduce from this directory with:

```sh
PYTHONDONTWRITEBYTECODE=1 python -B independent_coefficient_ledger_checks.py --output independent_coefficient_ledger_receipt.json
PYTHONDONTWRITEBYTECODE=1 python -B -O independent_coefficient_ledger_checks.py > independent_coefficient_ledger_receipt_optimized.json
cmp independent_coefficient_ledger_receipt.json independent_coefficient_ledger_receipt_optimized.json
```

This 54-case routine is separate from the main `exact_checks.py` receipt's 18 expansion cases and 9 exact-real LP branch cases. It performs no LP or root search. Its independent sparse expansion reads the compiler-provided summand affine forms; it does not claim independently authored summand construction. The main `exact_checks.py` supplies that additional independently constructed-formula check.

A final skim of the new `PROOF.md` found no mathematical defect. In particular, its alternate order of proof (finite predecessor integrality before category purity) is valid: binary support first makes every positive rank at least 1, and every rank greater than 1 has `c>0`, so its supplied predecessor is in the same finite active set.

## 13. Final portable packaging review

The approved base source and proof are now bundled under `approved_base/`. Their SHA256 values were checked against the frozen originals and agree exactly with the two values in Section 1; the originals remain unchanged. `real_certificate.py` resolves its dependency relative to its own file and checks the same pinned base compiler hash before importing it. The independent checker likewise now uses `HERE / 'approved_base' / 'prism_certificate.py'`, so its replay does not require the sibling frozen packet directory.

After this packaging-only change, both normal and optimized 54-case checks were rerun successfully. The refreshed receipts are byte-identical and hash the final portable compiler (`073e164feadc6bd4850ed043043889c5755e27c809f3afcdd3b52a14b9a1a299`) and updated checker (`aff8aced2e15bb5d5782f35ef3466b6a64be286dc988d55a01999e816e1ffb48`). No polynomial formula or mathematical theorem changed.

The independent checker performs no LP and makes no assertion about independently certified LP infeasibility. The separate main branch search is solver-assisted: accepted candidates are directly checked, but rejected/infeasible branches do not come with independently checked Farkas certificates. This limitation does not enter the all-real mathematical proof or the independent coefficient/ledger checks in this review.
