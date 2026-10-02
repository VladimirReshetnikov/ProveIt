# Seven-unit partition frontier for the complete ordinary U15 compiler

The complete ordinary-input compiler has four nondominated schedules in the finite family studied here:

| Full operations | Multiplications | Additions/subtractions | Exact degree | Finalizer |
|---:|---:|---:|---:|---|
| 511 | 211 | 300 | 4881 | One unit product anchors the remaining SOS |
| 513 | 211 | 302 | 3120 | Two unit-product equations, then SOS |
| 515 | 211 | 304 | 2116 | Three unit-product equations, then SOS |
| **517** | **211** | **306** | **1936** | **Four unit-product equations, then SOS** |

Every form has the same 87 positive witness coordinates and the same complete supplied integer zero set as the pinned 523-operation ungrouped source. In particular, 517 improves its operation count by six while preserving exact degree 1936. Ordinary input, valid-program qualification, and unbounded first-halt duration are inherited without a new encoding or witness projection. These numbers do not improve the separate 87-operation universal-polynomial bound.

The finite family consists of all 877 set partitions of seven named factors, with either a complete sum of squares or any one group used as an integer anchor. This gives 4,140 actual complete straight-line programs. The result is an exhaustive optimum within this family; it is not a lower bound for other arithmetic circuits or other Diophantine representations.

## 1. Authenticated source and factor identities

The parent is [`u15_packed_composed_units511.py`](u15_packed_composed_units511.py), SHA-256 `234a2fcd12e9049ae8903cb44a5c545a61857eba71e4484a0cf3c572827cfc38`, called as `build(True, grouped=False)`. Its complete polynomial uses 523 operations, 31 comparisons, and 87 positive witnesses. The guarded local rewrite is imported from [`u15_packed_unit_product524.py`](u15_packed_unit_product524.py), SHA-256 `667de9e6648af91c2fa1fe22801786fb78fd82156bce3132be05e9f10e513611`. Both source hashes are checked before import, and the parent rechecks its inherited source dependencies even after cache population.

The helper invokes the 524 source guard and degree-packet validator before removing its six literal product gates. The remaining base contains the same 431 certificate gates, seven factor registers, and 24 retained original comparisons. No theorem is applied to an untyped lookup or caller-supplied list of purported factor degrees. The public packet must equal a fresh canonical emission, including metadata, source, complete finalizer, ledger, and comparison maps, before evaluation or degree auditing.

Number the actual factors as follows:

| Index | Actual factor | Exact degree |
|---:|---|---:|
| 0 | Geometry main norm | 12 |
| 1 | Geometry auxiliary norm | 78 |
| 2 | Loader AND main norm | 332 |
| 3 | Loader AND auxiliary norm | 726 |
| 4 | History main norm | 898 |
| 5 | History auxiliary norm | 834 |
| 6 | Loader checksum | 65 |

The total factor degree is 2945. Write the old residual associated with factor `i` as `R_i`. The six norms are exactly `1+R_i`. The checksum is exactly `1-R_6`, because the original comparison orientation is reversed. These are polynomial identities on every integer tuple, and the receipt checks them against the emitted source.

For each native prefix, put `H=4a+3`, `Delta=a²+H=(a+2)²−1`, `T=i c²`, and use the actual registers `d`, `c`, `V`, `y`. The two factors are

```
N = d² − Delta c²,
A = T²(V²−y²) + y².
```

For every integer assignment, `Delta` is 0 or 3 modulo 4. Thus `N` is congruent to either `d²` or `d²+c²`, never 3. Since `T²` is 0 or 1 modulo 4, `A` is congruent to `y²` or `V²`, also never 3. Consequently none of the six norm factors can equal −1. This uses no positivity, prior native equation, Pell interpretation, or input-typing conclusion. The checksum is the only unrestricted factor.

## 2. Zero-set theorem for every partition and anchor

Let `G_1,...,G_g` be any set partition of the seven factors, and let `U_j` be the product in group `G_j`. Let `S` be the sum of squares of all 24 retained original residuals.

The SOS form is

```
F = S + Σ_j (U_j−1)².
```

An integer zero forces every retained residual to vanish and each group product to equal 1. Every factor of an integer product equal to 1 is a unit, hence ±1. The six norm sign exclusions force those six factors to be +1. The group containing the sole checksum then forces it to be +1 too. Therefore all seven removed original residuals vanish. The converse is immediate.

For any chosen group `a`, the alternative complete polynomial is

```
F_a = U_a [1 + S + Σ_(j≠a) (U_j−1)²] − 1.
```

At an integer zero the bracket is a positive integer. Its product with the integer `U_a` can equal 1 only if both are 1. Therefore every retained residual and every other group residual vanishes, while `U_a=1`. The same factor argument proves equivalence with the old complete system. Again the converse is immediate.

These are same-coordinate equivalences of the entire supplied integer zero sets. Their positive-coordinate restrictions therefore preserve the parent's exact ordinary relation. The seven-singleton SOS form is identical to the old polynomial: all six norm residuals are unchanged, while the checksum residual is negated before squaring. Metadata records this exception as `full_polynomial_identity=True`. For the other forms, the claimed relation is zero-set equivalence. The displayed formulas, with `S` and each factor reconstructed from old residuals, are the exact off-zero output identities. They also show why replacing integer coefficients or inputs with floating-point approximations would invalidate the contract. A corresponding zero-set theorem over all reals is not asserted.

Current metadata records every retained old-to-new comparison and every grouped factor's old comparison. The inherited ancestor comparison map is retained only as `pre_unit_ancestor_comparison_map`. The old loader comparison count is explicitly historical; `current_comparison_counts` records 15 retained loader rows, nine retained history rows, and `g` new unit-group rows. Groups may mix the loader and history factors, so they are not silently assigned to either source subsystem.

## 3. Complete paid schedules

Every group is multiplied in increasing factor-index order. This uses exactly `7−g` multiplication gates. The factor-source base is the same 431-gate source in every form. Thus the certificate cost is

```
438−g operations = (187−g) multiplications + 251 additions/subtractions.
```

There are `24+g` comparisons. A literal SOS costs `3(24+g)−1` gates. The single-anchor schedule has `23+g` squared residuals, each charged for subtraction, square, and addition into an accumulator beginning at 1, followed by one multiplication and one subtraction. It has the same total cost.

Both complete schedules therefore use

```
509+2g operations = 211 multiplications + (298+2g) additions/subtractions.
```

Every source gate is checked to be reachable from the final output. Constants, arbitrary-integer additions/subtractions, and multiplications follow the same unit-cost straight-line model as the parent. No native factor evaluation, final sum, or helper multiplication is omitted.

## 4. Exact degrees and finite optimum

Let `w_j` be the sum of the seven table weights within group `j`. The retained SOS has exact degree 1936. The exact complete degrees are

```
SOS:       max(1936, 2 max_j w_j),
anchor a:  w_a + max(1936, 2 max_(j≠a) w_j).
```

These equations are verified against each actual emitted source, not assumed from a list of weights. The three main norms use the guarded exact source cancellation

```
d = a c + X + ga H,       H = 4a+3,
d² − (a²+H)c²
  = 2ac(X+ga H) + (X+ga H)² − Hc².
```

After that exact identity, ordinary degree propagation gives an upper bound. Evaluating the corresponding highest homogeneous coefficients modulo each of 1,000,000,007 and 1,000,000,009 gives a nonzero coefficient for every factor and for every complete output. The dependence tracker proves that these highest coefficients contain no fixed-program parameters. Consequently the degree is exact for every fixed program slice, not merely for the finite program numbers used to evaluate coefficients. The receipt contains both certificates for all 4,140 forms. The compiler ledger separately reports its conservative literal-SLP upper bound and leaves `exact_degree_claimed=False`; the checked degree audit supplies the stronger exact certificate.

For the four-group 517 form, the group weights are `487,726,898,834`. Every new squared group residual has degree at most 1796, strictly below the retained degree-1936 SOS. Thus its exact degree 1936 also follows directly from the parent's surviving degree-968 residual.

The complete census has the following minima for each number of groups and each finalizer family:

| Groups | Operations | Best SOS degree | Best single-anchor degree |
|---:|---:|---:|---:|
| 1 | 511 | 5890 | 4881 |
| 2 | 513 | 3120 | 3918 |
| 3 | 515 | 2116 | 2950 |
| 4 | 517 | 1936 | 2128 |
| 5 | 519 | 1936 | 1948 |
| 6 | 521 | 1936 | 1948 |
| 7 | 523 | 1936 | 1948 |

Representative Pareto partitions, using the factor indices above, are:

```
511 / 4881: [0,1,2,3,4,5,6], anchored.
513 / 3120: [0,1,2,4,6] [3,5], SOS; weights 1385,1560.
515 / 2116: [0,1,4,6] [2,3] [5], SOS; weights 1053,1058,834.
517 / 1936: [0,1,2,6] [3] [4] [5], SOS; weights 487,726,898,834.
```

Some short combinatorial bounds also explain the SOS minima. With two groups, the three weights 726,834,898 force one pair together, at least 1560. With three groups, the four weights 332,726,834,898 force one pair together, at least 1058. The displayed partitions attain these bounds. Four groups attain the unavoidable retained degree 1936. Exact single-anchor minima and the absence of further nondominated forms are established by the complete 4,140-form census.

## 5. Reproduction and public contract

Run from the packet directory, or supply `--root` pointing to the maintained `native-stream-queue` directory:

```sh
python u15_unit_partition_frontier.py --root /path/to/native-stream-queue
```

The default command recomputes and type-sensitively compares the saved receipt. `--write` regenerates it explicitly. The parent compiler family requires Python with SymPy; this wrapper uses only the standard library. Source paths are relative to the helper or supplied root, with no permanent `/tmp` dependency.

`build(groups=None, anchor=None)` emits the 517 form by default. Other groups must be an exact list of nonempty exact lists, with strictly increasing integer indices within each group and increasing first indices across groups, covering 0 through 6 exactly once. `anchor=None` selects SOS; an exact valid integer group index selects its anchor. Booleans, floating-point indices, duplicate factors, and incomplete partitions are rejected. The public `checked`, `polynomial_source`, `degree_audit`, `evaluate`, and `identity` methods authenticate the whole supplied packet. Evaluation requires every coordinate to be an exact positive integer; explicit `signed=True` permits arbitrary integers for algebra checks. Returned packets and parent descriptors are defensive copies.

The receipt records every complete schedule's typed source digest, exact ledger, two degree certificates, and signed full-source output check. It also includes the four complete frontier packets, positive and signed public API cases, all old residual identities, source/degree tampering rejections, inexact-scalar rejections, and cache-copy checks. None of the numerical cases is presented as a materialized full Pell witness or as a replacement for the source-level zero-set proof.

The [independent source review](review_u15_unit_partition_frontier.md), [portable checker](review_u15_unit_partition_frontier.py) and [receipt](review_u15_unit_partition_frontier.json) confirm the complete frontier. They independently enumerate all objective records and evaluate every coefficient of each frontier polynomial at two modular specializations, without the author's leading-term shortcut. A [separate mathematical review](review_u15_partition_math.md), [census](review_u15_partition_math.py) and [receipt](review_u15_partition_math.json) use two independent partition enumerations and prove the exact degree formulas. Fresh repository replays pass; no unresolved finding remains within this finite-family scope.
