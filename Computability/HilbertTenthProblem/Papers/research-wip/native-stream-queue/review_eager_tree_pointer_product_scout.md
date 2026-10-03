# Independent review of the finite pointer-product Tree scout

**PASS on the repaired frozen author trio.** The replacement gives an exact existential projection of the complete natural zero set onto the retained row fields. It removes all forward pointers and the last two unused `u,v` fields. The complete paid counts and growing exact degree agree with the source. It does not preserve the full polynomial or give a bijection of witness fibers, and no signed semantic theorem or fixed-arity universal bound follows.

Reviewed artifacts are [the source](eager_tree_pointer_product_scout.py), [full receipt](eager_tree_pointer_product_scout.json), and [proof note](eager_tree_pointer_product_scout.md). This review's [checker](review_eager_tree_pointer_product_scout.py) and [receipt](review_eager_tree_pointer_product_scout.json) authenticate all six current/parent files before executing the current public API. No historical Python module or author `verify()` function is executed.

| File | SHA256 |
|---|---|
| `eager_tree_pointer_product_scout.py` | `35fab9c363c38421a2d4b569bfd56f1cddf95717f9dfaa37ada4ce7dc6fe49bd` |
| `eager_tree_pointer_product_scout.json` | `9d0eaa72ffee7c900f8e348c305293193a8b4ebaa066c534902795f6b87ba4cc` |
| `eager_tree_pointer_product_scout.md` | `c0c5991e451ae74fc9a6b9c15e996a4e2f80dd04b33d2bb2a433d03142bf47b3` |
| `eager_tree_coded_lookup_scout.py` | `b2769ca2c8b8754f5b5c9d65c0ad97a5f590c5b6ebc5712a2964ac1d1a1d0e73` |
| `eager_tree_coded_lookup_scout.json` | `acfcbd04609e49150a0e9089c7937ca0fcd20b852a337a3e39248a4e582d01c6` |
| `eager_tree_coded_lookup_scout.md` | `81d9be0663b212039802c1c841dd200e82baedc02ecf1005957e8f90beef457b` |

## Natural-domain proof

For each row and slot, write `A=t3+t4` for the first two slots and `A=t3` for the third. The retained natural one-hot equation makes every tag Boolean and `A` either zero or one. A parent's pointer row sum is `A`; thus an inactive slot has all pointers zero, while an active slot has exactly one pointer equal to one. Its coded lookup identifies the selected later row's code with the branch target `D`. Consequently `A product_{j>i}(Cj-D)` vanishes on every parent natural zero.

Conversely, an active product residual at a natural child zero gives a zero product in the integers, so at least one difference is zero. Choosing the least matching later row and setting just that pointer to one restores the row sum and lookup. Inactive targets themselves are zero because their tag coefficients vanish; all their pointers can be zero. The source audit confirms that no retained residual or other constraint uses the deleted pointers. Therefore independent slot choices restore the whole parent at once. This is a finite algebraic restoration, without a new execution or decoding hypothesis.

When `i=N-1`, the product is empty and equal to one. The actual three residuals are `t3+t4`, `t3+t4`, and `t3`, with both copies of the first expression retained in the final sum of squares. A natural zero forces `t3=t4=0`. The last target cones have no remaining consumer, and last-row `u,v` have no consumer in any common residual. Restoring them to zero preserves the parent's inactive target equations. Conversely their arbitrary old natural values have no effect on the projection of a parent zero.

The coded parent relates the matched natural codes to triples through `P(u,v)=(u+v)^2+u` and `C(x,y,z)=P(z,P(x,y))`. For fixed natural sum `s`, the values of `P` occupy `[s^2,s^2+s]`; these intervals are disjoint for successive `s`, and the remaining value determines `u`. Thus the inherited injectivity argument is applicable. The reviewer also expands all actual paid row/target code cones independently, including the parent's reused `F(a,y)` arithmetic, rather than treating codes as free operations.

The resulting theorem is precisely

`Fchild(r)=0 iff there exist natural deleted pointers and last u,v with Fparent=0`.

The chosen lift is a right inverse on child zeros. Distinct matching rows yield different valid pointer lifts; independently varying unused last fields also changes a parent witness without changing its projection. The saved concrete duplicate-leaf example and a separate `u=29,v=41` variation were checked against both complete sources. No zero-fiber bijection is possible for this coordinate deletion. The existing external-size finite-certificate interpretation is preserved; this is not an ordinary-input/unbounded-history compiler.

## Whole source and complete cost

The checker independently reconstructs the sixteen emitted sources from the authenticated parent's literal rows. It derives each active port from the actual pointer-sum residuals, builds the ordered differences and products, traces dependencies backwards, removes the dead cones, and emits every residual square and final addition. Each reconstructed complete list must agree exactly with the public packet and saved receipt. All retained source gates are thereby charged, and every remaining gate and supplied field is live.

For a slot with `m>0` possible targets, both old and new lookup schedules cost `m` multiplications and `m` additions/subtractions. The old empty lookup instead has one subtraction; the new empty lookup aliases the active port. Across all rows:

- deleting pointer sums saves `3N(N-1)/2+3` additions;
- deleting three empty lookups saves three additions;
- deleting the last target-code cone saves 13 multiplications and 20 additions;
- deleting `3N` net residuals saves `3N` squares and `3N` final additions.

Thus the exact saving from the matching coded parent is `(3N+13)M + (3N(N+1)/2+26)A`, or `3N(N-1)/2+6N+39` operations. The independent literal counts agree for every emitted form, including `N=1`.

With `c=1` for cleanup and `c=0` otherwise, the complete source has

- `M=(3N^2+81N-24)/2`;
- `A=(3N^2+(131-2c)N-38)/2`;
- total `3N^2+(106-c)N-31`;
- `13N-2` natural witnesses, and `8N+3` residual occurrences.

At `N=8,c=1`, this is **1,001=408M+593A**, with **102 witnesses and 67 residuals**. At `N=1,c=1`, it is **77=30M+47A**, with 11 witnesses and 11 residuals. No code, active-port, constant multiplication, square, or final addition is omitted from these counts.

## Polynomial and degree boundaries

All retained residuals are literally identical and independent of every deleted coordinate. The independently reconstructed finalizer therefore proves the all-value identity

`Fchild(pi(v))-Fparent(v) = sum(new product residuals squared) - sum(deleted old pointer-sum and code-lookup residuals squared)`.

This includes arbitrary old pointers and last `u,v`, over the integers or rationals. It is a correction identity, not an off-zero equality. Its algebraic scope does not extend the natural zero-set theorem to signed or real domains.

Each row code has degree four and each tagged target degree five. A nonempty product row with `m` later targets has degree at most `5m+1`. For `N>=2`, the root third-slot residual has leading homogeneous form

`(-1)^(N-1) t_03^N (u_0+v_0)^(4(N-1))`.

This follows from the actual target-cone expansion; the target's degree-five term dominates each degree-four row code. Its square cannot cancel against other highest homogeneous squares over the reals. For `N=1`, the retained input residual has the nonzero degree-five term `-t_04(a_0+b_0)^4`, even though natural zeros force the last active tags to zero. These establish exact full degree `max(10,10N-8)`, not a degree after imposing zero equations. The checker independently propagates every complete source with all remaining variables equal to an indeterminate and obtains the same attained degrees with positive leading coefficient, as well as the all-gate upper bounds.

## API and bounded evidence

The public `build`, `checked`, `project_zero`, and `restore_zero` interfaces were exercised. Sizes are exact integers 1 through 8, cleanup is an exact Boolean, packets must equal the full canonical descriptor recursively, and map assignments must contain exactly the required natural integer fields. Maps reject nonzeros. All parent source/receipt/proof pins are rechecked on every call; returned assignments and mutable packet fields are copied.

One finding was resolved before the reviewed freeze: the first draft returned its module-level `PINS` dictionary directly as packet metadata. Root reported this alias and the author replaced it with a deep copy, also copying receipt provenance. This independent checker now clears every returned mutable top-level field, forges a nested `parent_pins` value, and then checks subsequent public results. The repaired source passes; no unresolved finding remains.

The saved independent receipt records:

- 16 entire reconstructed circuits and finalizers, 8,324 live paid gates, 16 exact degree certificates;
- 56 expanded row-code and 216 expanded target-code polynomial identities;
- 128 whole correction evaluations, including 32 rational cases, and 3,264 retained residual value comparisons;
- 72 independently constructed natural-zero projections and 72 chosen lifts, covering all five eager rules and padded cases;
- two explicit nonunique-parent examples;
- 65 rejected public calls, including 12 warm pin failures; 13 mutable-packet copy checks, two assignment-copy checks, and optimized-Python rejection.

Finite checks verify the particular emitted schedules and representative maps. The general product-zero, natural one-hot, empty-product, exact-degree and ledger arguments above supply the uniform mathematical template. The public implementation deliberately emits only the sixteen saved sizes/options. This review does not assert formal proof-assistant verification or a global arithmetic optimum.

Portable replay, using only the standard library:

```sh
python review_eager_tree_pointer_product_scout.py \
  --source /path/to/eager_tree_pointer_product_scout.py \
  --root /path/to/coded-parent-trio \
  --expect review_eager_tree_pointer_product_scout.json
```

The current source's companion JSON and Markdown must be beside it. `--output FILE` writes a deterministic receipt; `--expect` compares the entire object with exact recursive types. All source bytes are authenticated before execution via direct `compile`, with no bytecode-cache trust. The review writes only its requested output and temporary private pin-test copies, and does not mutate the repository or rerun historical author suites.
