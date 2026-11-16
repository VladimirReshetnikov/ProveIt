# Sources and provenance

Access date: 2026-11-16 (America/Los_Angeles).

## Statement inventory

- English Wikipedia, **Median**: <https://en.wikipedia.org/wiki/Median>
  - finite odd/even definitions and balance definition;
  - finite/probability medians, particular distributions, L1 optimality, and
    mean-median bounds;
  - Jensen inequality, algorithms, exact/asymptotic sample laws;
  - multivariate and conditional medians;
  - interpolated median, pseudomedian, Theil-Sen, median filter, k-medians,
    median-median line, and median-unbiasedness.

Wikipedia is used as a list of target claims. The report supplies its own
proofs, hypotheses, corrections, and counterexamples.

## ProveIt repository baseline

Repository: <https://github.com/VladimirReshetnikov/ProveIt>

Main-branch commit inspected:

```text
df3ff8cc28be5eb713a14809a9df167e9aa94ab1
```

Commit timestamp reported by GitHub: 2026-11-16T18:04:09Z.

Lean toolchain:

```text
leanprover/lean4:v4.32.0
```

### iPRA foundations and checked derivations

- `Logic/PrimitiveRecursiveArithmetic/README.md`
  - first-order intuitionistic logic, primitive-recursive symbols and defining
    equations, successor axioms, and quantifier-free induction;
  - distinction between checked derivations and informal proof packets.
- `Logic/PrimitiveRecursiveArithmetic/Derivations/README.md`
  - reusable object-language library and the `Prf PRAAx` endpoint.
- `Logic/PrimitiveRecursiveArithmetic/Derivations/Lean/IPRADerivations.lean`
  - aggregate import list.
- `.../Core/Definitions.lean`
  - `PTm.toPR`, `recDef`, finite sums/products, powers, factorial.
- `.../Core/Order.lean`
  - quantifier-free order, totality, antisymmetry, decidable equality,
    monotonicity, and cancellation.
- Relevant additional modules named in the derivation index:
  `Pairing`, `Parity`, `BoundedSums`, `Search`, `SumLemmas`, `MultiSums`,
  `Permutation`, `Division`, and `Combinatorics/Binomial`.

### Existing list-median design

- `Logic/PeanoArithmetic/ListCoding/Lean/PAListCoding/Predicates.lean`
- `Logic/PeanoArithmetic/ListCoding/Lean/PAListCoding/Aggregates.lean`

The PA/I-Sigma-1 development defines a division-free `TwiceMedian` using a
sorted permutation and odd/even cases. It also contains the ordinary-list
specification, coding equivalence, existence, functionality, and examples.
This packet reuses the design, not the proof strength: the requested new
endpoint is an iPRA `Prf PRAAx` derivation.

### Effective probability architecture

- `Logic/PrimitiveRecursiveArithmetic/docs/proofs/probability/central_limit_ipra_2026-11-15/README.md`
- `.../lean/FiniteCLTBlueprint.lean`

These files motivate the split between exact finite rational laws and
continuous/infinite laws represented by primitive-recursive regular names with
explicit tail, continuity, and approximation moduli.

## Local generated evidence

- `code/median_ipra_reference.py` performs exact integer/Fraction checks.
- `code/validation.json` records a passing run over 1,662,266 cases.
- `paper/pdf_inspect.txt` records PDF metadata and embedded-font inspection.

The executable checker is regression evidence only, not part of the proof
basis.
