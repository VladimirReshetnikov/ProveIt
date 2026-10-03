# Independent audit: deleting implied conservative-signal guards

PASS for the proposed deletion on the actual corrected 18-particle numeric packet. The complete natural zero sets are in bijection by forgetting/restoring the deleted slack coordinates. The complete parent polynomial, after the stated affine restoration, equals the reduced polynomial on arbitrary signed tuples as well. No unchanged-coordinate polynomial identity or unrestricted signed zero-set bijection is claimed.

This is a bounded second review of the guard transformation, literal source schemas and paid sparse-affine schedule. It does not repeat the original ten author suites, the full collision-table literature audit, or the independent mode-closure algorithm. [Portable checker](review_signal_guard_projection_independent.py) pins `numeric/compile_packet.py`, `numeric/MORITA_18_SIGNAL_MACHINE.json`, and the corrected `code/quadratic_packet.py` before importing them; [receipt](review_signal_guard_projection_independent.json) records those hashes and exact results. Imports preserve existing module entries. The source root may be either a private extraction or the unchanged maintained placement.

## Exact transformation and natural proof

For a branch let `c_i=v_i-v_(i+1)`, let `J` be its selected edges, and put `j=min(J)`. Every actual selected edge has strictly positive integer closing speed. The source's equality rows are the mode equation and `c_j h_i-c_i h_j=0` for `i in J\{j}`. Its strict rows are the nonnegative-speed germ gaps, total span, positive pivot delay and all unselected endpoint forms.

Retain every equality, `h_j>0`, and `c_j h_i-c_i h_j>0` for all unselected edges with `c_i>=0`. Delete every germ row, the span row, and endpoint rows for `c_i<0`. This matches the actual emitted source; the review independently reconstructs every coefficient from the mode speeds and codes for all 80,501 branches.

The complete packet is a sum of affine squares plus terms

```
(E-e_r) * sum_i X_(r,i),   E=sum_r e_r.
```

On natural assignments every summand is nonnegative. A zero makes `E=1`, so exactly one selector is one; complementarity makes every inactive copy zero. The global input/output rows and local guards then recover the active branch in the standard way. All inactive retained slack coordinates are zero.

For the active copy, the retained pivot row gives `h_j>=1`. A selected gap has `h_i=(c_i/c_j)h_j>0` by its tie equality. An unselected gap with `c_i>=0` is positive by its retained endpoint inequality. These gaps are integers, so each is at least one and satisfies the deleted germ row. The span is positive because it contains `h_j`. For any `c_i<0`, naturality of `h_i` gives

```
c_j h_i - c_i h_j = c_j h_i + |c_i| h_j >= 1.
```

Thus every removed strict form `L` is at least one. Restore its slack by `s=L(copy)-e_r`. This is nonnegative in the active branch and zero in each inactive branch. The parent strict row uniquely determines this value. Conversely every natural parent zero projects to a reduced zero simply by discarding the removed squares/slacks, since each retained summand still vanishes. Projection and restoration are inverse on complete natural zero sets; input, output, selectors, all copies and every retained slack are preserved.

Under the same restoration on arbitrary signed coordinates each removed residual is identically `L(copy)-e_r-[L(copy)-e_r]=0`. Every global row, retained local row and complementarity product is unchanged. This proves the complete graph identity, without a positivity assumption and without a dense polynomial expansion. It does not assert that every arbitrary signed parent zero lies on that graph: outside the natural domain unsquared complementarity terms can be negative.

The natural domain cannot be broadened to nonnegative reals for the slack bijection. The checker constructs a complete reduced real zero for the actual branch `641→657, J=(0,2)`, pivot speed `12`, with selected gap `h_2=3/4`. All retained slacks, inputs and outputs are nonnegative; the unique old `germ:2` slack is `-1/4`. Strict physical positivity still follows, but the integer-unit encoding `L-1-s=0` is stronger over real coordinates.

## Counts from the actual source

If `g` is the number of nonnegative closing speeds, the deleted rows are `g` germ rows, one span row, and `17-g` negative-speed endpoint rows. Negative-speed edges cannot be selected, so all those endpoint rows exist. Therefore exactly 18 rows/slacks disappear per branch, independently of the size of `J`.

The exhaustive literal census gives 1,233,405 deleted germ rows, 80,501 spans and 135,112 negative-speed endpoint rows, totaling 1,449,018. With 80,501 branches and 95,445 retained equality guards:

| Quantity | Parent | Reduced |
|---|---:|---:|
| Strict rows/slacks | 2,667,479 | 1,218,461 |
| Natural auxiliary coordinates | 4,196,998 | 2,747,980 |
| Squared affine rows | 2,762,961 | 1,313,943 |
| Complementarity products | 80,501 | 80,501 |
| Polynomial degree | 2 | 2 |

Here auxiliaries exclude the 18 supplied input and 18 output coordinates. The source formulas are `19B+T` auxiliaries and `37+E+T` affine rows. A concatenated external horizon `K` consequently uses `2,747,998K-18` auxiliary coordinates under the original interface convention; it is still a family whose arity grows with `K`.

## Independent paid schedule

The schedule is explicit even though a 25-million-gate file is not materialized. For every affine row, start with a positive coefficient term, charge one multiplication per coefficient of absolute value greater than one, and combine the signed terms by additions/subtractions. Every actual row has a positive term. The one-hot row has the sole affine constant `-1`; retain the preceding selector sum `E` for all complementarity terms. No coefficient scaling is treated as free, and coefficient bit length is outside this operation-count model.

If `N` is the total affine variable-coefficient incidence count and `R` the number of squared rows, forming the rows costs `N-R+1` additions, where the one extra operation pays the sole constant. Each complementarity factor costs 17 additions to sum its 18 copy coordinates and one subtraction `E-e_r`. Adding all `R+B` resulting terms costs `R+B-1` operations. Hence the complete schedule has

```
M = nonunit_affine_coefficients + R + B
A = N + 19B.
```

The checker derives these totals by independently charging each actual local row, then the literal global input/output/selector rows and full finalizer. It does not merely import the author's ledger formula.

| Complete one-step schedule | Multiplications | Additions | Total |
|---|---:|---:|---:|
| Parent | 8,539,514 | 16,853,008 | 25,392,522 |
| Reduced | 6,820,272 | 11,082,826 | 17,903,098 |

The saving is 7,489,424 operations in this specified schedule. Affine incidences fall from 15,323,489 to 9,553,307; nonunit coefficient multiplications fall from 5,696,052 to 5,425,828. The reduced circuit is not claimed optimal. No compression to a fixed-arity unbounded-history equation or improvement to the separate universal 87-operation benchmark follows.

## Reproducible coverage

The independent checker reconstructs every original guard and endpoint matrix and verifies the exact deletion schema for all 80,501 actual branches. A deterministic digest binds the full sequence of literal old rows, matrices and deletion names. For bounded subsets of those actual branches it then evaluates the complete packet, including all global equations and unsquared complementarity products, under arbitrary signed assignments and the restoration map. It separately constructs complete natural zeros for every active position in those subsets and passes both parent and reduced packets through the actual corrected public `Branch/Guard/polynomial_value` implementation. The exact case counts are in the receipt. This avoids mistaking isolated guard satisfiability for equality of complete packet polynomials.

Reproduce with

```
python review_signal_guard_projection_independent.py --root /path/to/conservative-signal-release --expect review_signal_guard_projection_independent.json
```

The graph identity and natural proof above justify all tuples; finite signed/public fixtures check their transcription. No full expanded trillion-monomial export or universal trajectory was generated for this second review.
