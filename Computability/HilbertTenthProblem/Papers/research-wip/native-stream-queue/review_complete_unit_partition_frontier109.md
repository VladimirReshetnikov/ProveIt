# Independent review of the complete 37-partition compiler

**PASS, with no requested author changes.** This reviews the complete emitted source and public interface of [complete_unit_partition_frontier109](complete_unit_partition_frontier109.md), supplementing the separately frozen [independent mathematical census](review_index_unit_partitions_math.md). The new default is **109 operations = 53M + 56A, exact degree 28, 24 supplied positive witnesses and 11 equations**. Its entire integer zero set agrees with the selected asymmetric 113-operation parent on the same coordinates. The computational interpretation still requires the inherited admissible fixed-program and positive-domain hypotheses.

The reviewed author pins are:

| Artifact | SHA-256 |
|---|---|
| Source | `ff9c9f43372aeac2b808f9ee8821011ea0e6ceff397225c934493ac26926da41` |
| Receipt | `d62818ee997fb0324da5d6d4105e28091b22dca25ae9f87871d87ae476f6e0a1` |
| Proof/API note | `d45817fbd03d2c5709bf39f90dd645428847308826eadfa011db050d53a2053a` |

The [independent checker](review_complete_unit_partition_frontier109.py) and [receipt](review_complete_unit_partition_frontier109.json) authenticate these three files, the frozen mathematical-review trio and all 25 parent dependencies. Python source is executed directly from its authenticated bytes, without a bytecode-cache lookup. Historical author Python modules and the author's `verify()` routine are not executed. The only reused mathematical utilities are the prior independent review's sparse-polynomial class and canonical partition enumerator; their source and receipt are explicitly pinned.

## Full source and integer-zero proof

The checker takes the literal 75-gate unit core from the preceding authenticated [index packet](complete109_index_unit_tradeoffs107.md), independently constructs each canonical block product, appends the eight retained comparisons and every subtraction, square and finalizer sum, and compares every gate and comparison with both the saved packet and public `build`. It verifies all 69 common computed registers by exact polynomial coefficients, the five selected unit residuals with their correct signs, and the eight unchanged residuals. The first residual is `1-N0`; its sign reverses under the norm-port representation but its square is unchanged. The index identity is the all-value polynomial identity `(k-r)-hE-1 = k-(r+1+hE)`.

The parent sources establish the literal forms

```
Nm = d^2 - (a^2+4a+3)c^2,
Ni = mu^2 - (a^2+4a+3)kappa^2,
Na = (i*c^2)^2((j*c-r)^2-y_aux^2)+y_aux^2.
```

On all integer supplied tuples, the first two cannot equal −1 modulo four; the third is a square modulo four, according to the parity of `i*c^2`. Consequently a product-one block containing at most one of the unprotected units N0 and Nk forces every member to be +1. This proves the complete integer-zero equivalence in both directions, without assuming the strong equation or positivity for this local grouping argument. Positive universality is inherited only after applying the existing parent's domain and source theorem; this review supplies no new ordinary-input theorem.

The old private comparison ports have no live downstream consumer except their intended comparisons, and the replacement computations are paid. The 75-gate core is `40M+35A`. With g blocks, the complete schedule pays `5-g` product multiplications and the full SOS finalizer for `8+g` equations, giving `53M+(50+2g)A`. All supplied fields and emitted gates are live. The independently reconstructed 37 sources contain **4,039 gates: 1,961 M and 2,078 A**, including 2,846 certificate gates and 410 comparisons.

The full correction is checked as an exact coefficient polynomial in the five actual unit ports:

```
F_partition-F_parent
 = sum_blocks (product(block)-1)^2 - sum_units (unit-1)^2.
```

This symbolic identity, together with the literal source cuts and unchanged eight residuals, proves the complete off-zero correction over any commutative ring. It is zero only for the all-singleton member of this emitted family. That member correctly has `full_polynomial_identity=True`; all other 36 correctly have it false. Integer-zero equivalence is a distinct, stronger-domain statement and is not asserted over arbitrary rational or real supplied tuples.

## All degrees, census and metadata

All five source unit polynomials are expanded independently. Their weighted degrees are `[12,4,7,10,7]`, with the six fixed program ports weighted zero. Every one of the 37 degree certificates is reconstructed from the actual unit leaders and the exact eight ordinary residuals. The review compares every coefficient of the sum of **all** maximal residual squares, not merely a propagated degree bound or one selected maximal row. The positive polynomial witness in the fixed parameter `Bm1` confirms uniform nonvanishing on every inherited admissible fixed-program slice.

For the default `[[0],[1,3],[2,4]]`, put `b=Bm1`, `J=Jrep` and

```
Mtop=(b*w*J+4*ga*a)^2+2*a*c*(b*w*J+4*ga*a).
```

The complete highest homogeneous polynomial is exactly

```
i^4*j^4*c^12*Mtop^2
 +16*b^8*h^2*w^2*s^2*J^8*delta^4*a^10.
```

The coefficient of `ga^4*a^4*i^4*j^4*c^12` is 256, independently of all fixed ports. The earlier frozen math review additionally expanded the entire default polynomial, obtaining 11,842 monomials and the same degree-28 leader. Its bytes remain unchanged.

The independent canonical enumeration gives 52 partitions, of which 37 separate indices 0 and 4. Their counts by 2,3,4,5 blocks are 8,19,9,1. The exact frontier within these literal schedules is `(107,42), (109,28), (111,24)`, with respectively 1,1,2 attaining partitions. The 15 excluded actual partitions are outside this sign criterion; neither author nor reviewer asserts that they are unsound. There is no unrestricted circuit lower bound or optimality claim.

Every current interface register is present in the source. The parent and original-raw comparison maps are reconstructed independently. Deleted positive definitions and previous ledgers, coordinate relations and degrees are kept under explicitly historical provenance. The supplied input, six fixed numeral ports, 24 witnesses and domain text remain exactly those of the selected parent. The entire proof/API note was read, including its fixed-program qualifications and singleton exception; no stale source or degree claim was found.

## Bounded API evidence and replay

The independent receipt records 37 complete source/degree/correction and metadata checks; 148 full numerical corrections (74 signed, including 37 rational), 1,924 parent-residual values and 111 public integer evaluations. The rational calculations exercise polynomial identities through the reviewer's own evaluator; the public author evaluator correctly requires exact integers.

The bounded interface audit rejected 123 malformed calls, including all 15 excluded partitions, noncanonical order/coverage/types, altered complete packets and metadata, invalid assignments and invalid mode flags. Twelve copy checks cover caller partitions, nested packets, parent/source accessors and degree certificates. Each of the 25 dependencies was changed in a private copy after a successful build and rejected on the next call; the three actual relative proof paths were still rejected when a valid flattened fallback existed. Optimized Python execution was rejected. No shared mutable packet cache or imported parent-module cache is involved.

These tests support the documented canonical API; they are not a claim about arbitrary hostile Python runtime manipulation. The mathematical integer-zero theorem and uniform degree argument do not follow merely from the finite evaluations. No giant universal Pell zero or additional historical author suite was materialized or replayed.

Replay uses explicit portable paths and the standard library:

```
python /path/to/review_complete_unit_partition_frontier109.py \
  --source /path/to/complete_unit_partition_frontier109.py \
  --receipt /path/to/complete_unit_partition_frontier109.json \
  --note /path/to/complete_unit_partition_frontier109.md \
  --root /path/to/native-stream-queue \
  --math-root /path/to/frozen-math-trio-directory \
  --output /tmp/review-unit-partitions-replay.json \
  --expect /path/to/review_complete_unit_partition_frontier109.json
```

`--math-root` contains the sibling `review_index_unit_partitions_math.py`, `.json` and `.md` files. In the repository all these artifacts can be siblings under the WIP directory. Replay compares the entire saved independent receipt with recursive exact type checks. Original parent and author artifacts were not modified.
