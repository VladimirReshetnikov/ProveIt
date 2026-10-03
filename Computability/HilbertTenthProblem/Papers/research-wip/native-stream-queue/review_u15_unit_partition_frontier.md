# Independent review of the ordinary U15 unit-partition frontier

**PASS.** The four complete frontier schedules have `(operations, exact degree)` equal to `(511,4881)`, `(513,3120)`, `(515,2116)`, and `(517,1936)`. The source-level integer-zero theorem, paid ledgers, finite partition census, and uniform fixed-program degree claims agree with the actual emitted circuits. No unresolved finding remains in this bounded review.

The reviewed compiler is [`u15_unit_partition_frontier.py`](u15_unit_partition_frontier.py), SHA-256 `8e0514876e26b716e792dd7d8332c773fe15989eb558fc7e4fedff8046249ccf`, with its [author receipt](u15_unit_partition_frontier.json), SHA-256 `3f3fd17dcb0f36f19b83f7aba7d3ebe081926c73786015d498540bf225bc6fc0`. The full [companion proof](u15_unit_partition_frontier.md) was read at SHA-256 `61b4e92a6a78756966eeafe544b3dc90ce3a4f630999846d45dd883d9f353fa5`, before any added review-provenance paragraph. Its two source links resolve. The review helper is [self-contained](review_u15_unit_partition_frontier.py); its [receipt](review_u15_unit_partition_frontier.json) records the exact checks below.

## Scope and independent checks

This review reads the entire new compiler and proof. It independently enumerates all 877 partitions and all 4,140 SOS/single-anchor choices, checks every saved objective against that enumeration, and separately reconstructs and executes the four complete frontier circuits. The author/root replay covers the complete source emission and degree certificate for every one of the 4,140 forms; this independent helper does **not** repeat all of those full-source evaluations. Nor does it repeat the unchanged ancestor 511/524 API audit or reconstruct their universality proof from scratch.

The independent helper checks:

- 877 distinct restricted-growth partitions, matching the author's separately written recursive partition generator, and all 4,140 finalizer choices;
- each of the four saved complete frontier packets against fresh public emission, including its source, coordinates, comparison map and ledger;
- exact closure, absence of dead gates, unchanged free-coordinate sets, 87 witnesses, and every emitted arithmetic operation in the four circuits;
- 160 independently executed complete outputs, including 80 signed assignments, with 1,120 individual factor identities and 3,840 retained residual identities;
- eight literal full polynomial evaluations over finite fields, retaining **all** univariate coefficients rather than using the author's main-norm degree override;
- an independently implemented upper-degree and leading-dependency analysis, after checking the exact local source rows needed for all three main-norm cancellations;
- 24 noncanonical frontier packets rejected by the public degree API.

The helper pins the compiler and author receipt before import, and the compiler authenticates the inherited source lineage. The review restores caller module objects and import paths on exit. No complete universal Pell witness is materialized; the finite tests supplement the source identities and integer proofs.

## Source transfer and integer domain

The canonical parent is the actual 523-operation ordinary source from `u15_packed_composed_units511.build(True, grouped=False)`. The independent executor locates the six original native comparisons by their literal left and right registers, plus the loader checksum comparison. It verifies that all other 24 comparison residuals are unchanged.

Writing the removed residuals as `R_i`, the six native factors are exactly `1+R_i`, and the checksum is `1-R_6`. The norm factors have the forms

```
N = d² − ((a+2)²−1)c²,
A = T²(V²−y²) + y².
```

For integer coordinates, the discriminant is either 0 or 3 modulo 4. Hence `N` is congruent to a square or to the sum of two squares modulo 4, never 3. Also `A` is congruent to `y²` or `V²`, never 3. Thus each of the six norms excludes −1 without using positivity or any other equation. The seventh factor, the checksum, has no such sign protection.

For a partition with group products `U_j`, let `S` be the sum of squares of the 24 retained residuals. The complete emitted outputs are exactly

```
S + Σ_j(U_j−1)²
```

or, for one chosen anchor group `a`,

```
U_a [1+S+Σ_(j≠a)(U_j−1)²] − 1.
```

An integer zero of the first expression makes every group product 1. Therefore every factor is an integer unit. All six norms must be +1, and then the sole checksum must be +1 as well. For the anchor expression, the bracket is a positive integer, so a product equal to 1 forces both the bracket and `U_a` to be 1. This reduces to the same argument. Conversely, every old zero makes each factor 1 and every retained residual zero.

This proves equality of the entire supplied **integer** zero sets, on identical coordinates. Restricting to positive coordinates preserves the parent's ordinary-input relation for its valid fixed program numerals. It is not an assertion about all real zero sets or unrestricted program parameters. In general the complete polynomials differ away from zero; the seven-singleton SOS form is the exact exception, since only the checksum residual changes sign before squaring. The current metadata states this exception correctly.

## Paid schedules and finite-family optimum

The common factor source has 431 gates, including all seven factor evaluations. A partition into `g` groups requires `7−g` further multiplications, giving the certificate ledger

```
438−g gates = (187−g) multiplications + 251 additions/subtractions.
```

The SOS and single-anchor finalizers each produce the complete ledger

```
509+2g gates = 211 multiplications + (298+2g) additions/subtractions.
```

There are `24+g` comparisons and the same 87 witness coordinates. These are literal straight-line costs, with subtraction charged as an addition/subtraction operation. Neither the unit products nor the finalizer are omitted.

The seven exact factor weights are `(12,78,332,726,898,834,65)`, totaling 2945. The retained SOS has degree 1936. For group weights `w_j`, the full degree objective is

```
SOS:       max(1936, 2 max_j w_j),
anchor a:  w_a + max(1936, 2 max_(j≠a) w_j).
```

The independent partition census by number of groups is `1,63,301,350,140,21,1`. Including SOS and one choice for every anchor gives 4,140 forms. The minimum degrees at operation costs `511,513,515,517,519,521,523` are respectively `4881,3120,2116,1936,1936,1936,1936`.

Several short bounds independently explain why no unlisted schedule beats the four frontier points:

- With one group, SOS has degree 5890, while anchoring has degree `2945+1936=4881`.
- With two groups, two of the three weights 726, 834, 898 must share a group, whose weight is at least 1560. Thus SOS degree is at least 3120, attained by the displayed frontier. For any two-group anchor, if the other group has weight `r`, its degree is `2945−r+2 max(968,r)`, at least 3913, so it cannot improve 3120.
- With three groups, two of 332, 726, 834, 898 must share a group, whose weight is at least 1058. Thus SOS degree is at least 2116, attained. An anchor containing a weight at least 332 has degree at least 2268. Otherwise all three large weights 726, 834, 898 lie in the other two groups, forcing degree at least 3120. Hence no three-group anchor improves 2116.
- For four or more groups, SOS degree is at least the retained 1936; an anchor has strictly higher degree because its group weight is positive. Four groups attain 1936.

The result is an exact frontier in this fixed seven-factor, disjoint-partition, SOS/single-anchor family. It does not exclude different factor identities, coordinate changes, arithmetic circuits, or computational substrates. It does not improve the separate 87-operation universal-polynomial bound.

## Independent full-coefficient degree certificates

For each frontier circuit, the review substitutes a degree-one polynomial for each nonfixed coordinate and an integer constant for each fixed-program parameter. It then executes every literal source gate over `F_p[t]`, retaining every coefficient. Multiplication uses exact carry-free base-`2^64` Kronecker convolution, guarded at every product by `min(len(a),len(b))*(p−1)^2 < 2^64`. Reduction modulo `p` happens after every gate. This calculation therefore detects actual cancellations in the emitted polynomial without assuming the guarded norm simplification.

| Operations | Degree | Leading coefficient modulo 1009 | Leading coefficient modulo 1013 |
|---:|---:|---:|---:|
| 511 | 4881 | 257 | 187 |
| 513 | 3120 | 715 | 385 |
| 515 | 2116 | 9 | 350 |
| 517 | 1936 | 984 | 453 |

Each test also independently obtains all seven factor degrees listed above. A separate abstract propagation verifies the exact source rows for

```
d = ac+X+gaH,  H=4a+3,
d²−(a²+H)c² = 2ac(X+gaH)+(X+gaH)²−Hc²,
```

then propagates upper degree and the possible fixed-parameter dependencies of the highest homogeneous form. For every factor and every complete frontier output the leading dependency set is empty, and the resulting upper degree is attained by the literal modular calculation. Thus the certified highest homogeneous form is independent of the fixed program parameters, and the exact degree holds on every fixed program slice. A merely favorable numerical parameter substitution would not establish that uniform statement; the separate dependency check is essential.

## Reproduction

With all files alongside the maintained sources:

```sh
python review_u15_unit_partition_frontier.py \
  --source u15_unit_partition_frontier.py \
  --receipt u15_unit_partition_frontier.json \
  --root . \
  --expect review_u15_unit_partition_frontier.json
```

Use `--output PATH` instead of `--expect PATH` to save a fresh independent receipt. Expected receipts are compared with exact recursive types, so Boolean/integer equality cannot conceal a changed record. The original compiler receipt is read and authenticated, never rewritten by this helper.
