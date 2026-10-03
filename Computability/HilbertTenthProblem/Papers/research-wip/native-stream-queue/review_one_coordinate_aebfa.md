# Independent review: The Price of One Coordinate

Archive `one_coordinate_certificates.zip`, SHA256 `453ae5f3b3726a288ae30325cbf8e1b6aa15bf6495fb5f23f4e8e8985f713829`. All 22 member hashes and sizes matched the intake inventory before safe private extraction. Read the complete article, README, and all four substantive Python files. No mathematical defect was found in the bounded-height obstruction, eleven-row compiler, all-solution reconstruction, full-witness packing bijection, quartic finalizer, or labelled-history extension.

## Mathematical and resource scope

The finite-state obstruction has the right quantifiers: it rules out even input-dependent linear systems representing an undecidable language if **some** solution on every positive instance has a total computable coefficient-height bound. It does not assume uniqueness and does not prove decidability for unrestricted linear systems over `N[X]`. The memory has `(B+1)^(nd)` states; a shortest drain after the finite inhomogeneous prefix gives the stated degree bound, including `d=0` and `B=0`.

The primary literature distinction is accurate. [Dong's paper](https://arxiv.org/html/2209.13347v2) states polynomial-time decidability for a single homogeneous equation with every unknown nonzero, and explicitly contrasts Narendran's undecidable general systems over `N[X]`. The original IEEE Narendran page was blocked by its JavaScript verification, so that original paper was not independently reread in this review. No novelty-priority assertion is established here.

The positive construction proves its geometry before using it. `S+E=X+XE` forces a positive-degree monomial stride by finite nonnegative ray flow. The two clocks become monomials/prefixes; evaluating the source-mask equation at one synchronizes their heights. Calibration then gives `W=m+2h+2`. Only after this equality are exponent blocks proved disjoint, masks Boolean, and tile occupancy unique. Injective weighted features now recover single symbols and true local windows. The shift `XS` moves outputs one horizontal place into the next block without collision. First acceptance is enforced on every source row, and the terminal ray permits exactly one accepting cell, not an arbitrary chosen accepting cell. The `h=0`, empty-prefix, and multiple-first-acceptance cases are handled correctly.

The eleven rows use `s³+s+7` **polynomial** unknowns, each with unbounded degree. Every nonlinear term contains `S`. This is not an ordinary scalar tuple of that length. A universal fixed CA exists via the proved one-head simulation interface, but the archive does not instantiate or independently verify a numerical universal machine table. The four-symbol rule is an example. The bounded scalar export requires an externally supplied degree cutoff; at `L=74` its 75 polynomial variables expand to 5,625 natural scalar variables and at most 1,661 coefficient rows. That complete bounded scalar system is described by a theorem, not emitted as an ordinary fixed-arity universal polynomial.

The whole-witness uniqueness theorem is sound over finite natural polynomials. It does not settle ordinary single-fold Diophantine representation. The sum-of-squares equivalence uses the leading coefficient in `Z[X]`, so signed intermediate coefficients do not permit cancellation of the highest residual-square coefficient. The quartic degree is exactly four; the support and maximum-degree formulas include all blank guards and auxiliary coordinates. The labelled-history extension correctly requires a unique all-blank transition, preventing unrecorded choices in the infinite exterior.

## Concrete constructor finding and isolated repair

**P2, direct `System` descriptor boundary (`code/compiler.py:171`):** the constructor freezes residual maps but does not validate their coefficients. With a valid binary `Rule`, one can construct

```python
System(rule, (0,), ('x',),
       {'test': {(0, ()): float(2**60), (0, ('x',)): -1.0}}, 1)
```

Its checked natural witness `{'x': {0: 2**60+1}}` is reported as a zero, because floating arithmetic rounds the residual −1 to zero. The high-level `compile_system` emits integer descriptors, so its theorem and normal generated results are unaffected. The direct frozen descriptor also retains caller-owned `word` and `names` lists. Additionally, converting accepting symbols to a frozenset before validation can discard a Boolean/float alias following an integer, such as `[1, True]`.

The isolated `one_coordinate_exact_system_inputs.patch` validates exact integer residual coefficients, nonnegative integer exponents, sorted in-interface variable tuples, labels, feature count, and the rule/word/name interfaces. It snapshots all descriptor containers and validates accepting symbols before set coalescing. It continues to support arbitrary well-formed residual systems; it does not falsely authenticate arbitrary descriptors as the canonical eleven-row compiler. The explicit internal `evaluate(..., validate=False)` path remains unchecked as documented. No archive was modified.

## Verified ten-row projection over N[X]

The helper implements an actual source-level projection to **ten quadratic identities on `s³+s+6` natural-polynomial unknowns**. Put

`S = X S₀`, `E = X E₀`, `D = S₀ B`.

Retain all other unknowns, replace these terms in the first nine identities, replace the stride identity by

`S₀ + E₀ = 1 + X E₀`,

and delete calibration. Every product still contains the shared unknown `S₀`; unknown-degree remains at most two. The largest coordinate shift multiplying an unknown monomial rises from `X²` to `X³`, which is an explicit tradeoff.

The natural lift is total: multiplying by `X` and forming `S₀B` preserves nonnegative coefficients. At any original zero, the constant coefficient in `S+E=X+XE` forces both `S` and `E` divisible by `X`. Cancelling `X` in calibration gives `D=S₀B`. Conversely, the new stride row lifts to the old stride row multiplied by `X`; the calibration row vanishes identically, and every other old row becomes the corresponding new row. Since `Z[X]` has no zero divisors, the projection and lift are inverse on the full natural-polynomial zero sets. This argument does not presuppose typed computation rows or a known horizon.

If `P` and `P′` are the complete old and new sums of squares and `r` is the new stride residual, the exact all-value identity on the restoration graph is

`P(lift(v)) = P′(v) + (X²−1) r(v)²`.

This is not pointwise polynomial equality between the two finalizers. Their zero equivalence follows from the complete residual correspondence (or each sum-of-squares theorem), not from a sign claim about `X²−1`.

The helper checks this identity by exact sparse expression expansion for 25 complete emitted schemas. At a zero of height `h`, the maximum new witness degree is `W(h+1)−1`, including `h=0`, and total witness mass decreases by one because `D` is deleted. The four-step example has 74 polynomial variables, 10 rows, 88 nonzero witness coefficients, maximum witness degree 74, and a fully expanded new quartic with 12,373 terms. Its coefficient degree is 12. The receipt includes every new residual and the complete witness. This is a proved polynomial-semiring projection prototype, not a hardened standalone universal scalar compiler or an unmeasured ordinary arithmetic-gate improvement.

## Portable replay and finite evidence

The helper authenticates every archive member and the patch before imports, rejects `python -O`, and uses private copies with `patch --batch --fuzz=0`:

```sh
python review_one_coordinate_aebfa.py \
  --root /path/to/untouched/one_coordinate_certificates \
  --patch one_coordinate_exact_system_inputs.patch --authors \
  --output /path/to/new.json --expect review_one_coordinate_aebfa.json
```

Original and repaired private copies both pass:

```sh
python code/verify.py
python code/export_example.py
```

Patch SHA256: `a7a1013b214624a30d3166aab758e5c6e48cae426a1b0cd59cf2e3e562b0ab55`; repaired compiler SHA256: `8f5d075ed4047c9036cdf6ff3e77a92217fe43dd4beb1e24002fb8540b3a1985`.

All seven original suites reproduce, all 14 saved JSON objects agree exactly, and all three full mathematical exports remain byte-identical. The compact review receipt stores canonical SHA-256 digests of those 14 author objects, after comparing them in full, instead of duplicating the large regenerable quartic. The complete new projected schema and witness remain in the receipt. Author evidence includes 7,168 binary-rule cases, 576 multistate and 576 feature-variant cases, 4,096 independently selected tile assignments, 6,561 ray candidates, 432 clock combinations, 729 bounded linear systems, 253 coefficient/off-region mutations, and four complete expanded-quartic evaluations. The binary suite largely concerns time-zero acceptance, as the article explicitly notes.

The new independent helper completes **1,395 assertions** and additionally verifies 103 dense-semantics cases and emitted projected interfaces, 25 full symbolic quartic graph identities, 24 arbitrary signed residual graphs and complete quartic evaluations, 16 natural zero bijections, 880 projected false-witness insertions, 32 independently exhaustive two-unknown bounded linear systems, witness and descriptor exact-type guards, immutable ownership, and preservation of repaired exports. These checks support the general written proofs; no finite enumeration is presented as a proof of universality or all-solution uniqueness.
