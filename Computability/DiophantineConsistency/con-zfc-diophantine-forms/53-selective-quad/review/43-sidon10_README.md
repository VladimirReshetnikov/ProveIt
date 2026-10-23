# A smaller ten-integer Diophantine equation for Con(ZFC)

**One fixed polynomial in ten unrestricted integer unknowns, of exact total
degree 237,520,456, evaluated by an 809-operation arithmetic circuit.** Its
lack of integer solutions is provably equivalent in ZFC to `Con(ZFC)` for
the repository's calibrated proof predicate.

The improvement is a new direct encoding of the parent's **22 quadratic
equations** using a 32-element Sidon set. It avoids applying exponentially
spaced digit positions to their quartic sum of squares. The subsequent
ten-integer Lucas reduction and finalizer are inherited from Sun and
ProveIt's package 31.

| Measure | Previous package-31 ten-integer equation | This package |
|---|---:|---:|
| Unrestricted integer unknowns | 10 | 10 |
| Exact total degree | 589,042,901,992,797,851,562,527,064 | **237,520,456** |
| Binary arithmetic operations | 1,442 | **809** |
| Fixed coefficient tuple | Complete 121-by-8801 tuple | Same complete tuple |
| New end-to-end proof-assistant certificate | None | None |

The degree decreases by a factor exceeding **2.47 x 10^18**. The displayed
evaluation circuit uses **43.9% fewer operations**. These are comparisons
with the specific package-31 equation at the pinned revision, not global
minimality claims. The earlier nine-natural-variable and other low-degree
systems optimize different measures and are not displaced by this result.

The operation ledger counts binary additions, subtractions, and
multiplications, including multiplication by a numeral. Shared expressions
are evaluated once; constant-only calculations are folded, and constructing
the fixed coefficient leaves is outside this evaluation count. The count
is an arithmetic-circuit measure, not a bit-complexity bound.

## The equation and its proof status

The complete polynomial is the division-free directed acyclic graph in
[`generated/signed10_b2.json`](generated/signed10_b2.json). Its unknowns are

    f, g, h, k, l, w, x, y, z, m

and all range over **Z**. Fixed leaves are literal integers or the fully
specified coefficient recipes in
[`generated/source_records.json`](generated/source_records.json). There are
16 such coefficient recipes plus the fixed source base `2^2134940`. None
of these fixed values is an existential unknown. Every exponent used by
the builder is a fixed nonnegative integer and is compiled into binary
multiplications; the polynomial has no variable exponent, division,
radical, conditional expression, or unresolved r.e. index.

The result is an **ordinary mathematical proof**, with an independently
audited source lemma and finite implementation certificates. It inherits
the parent K215/compiler calibration, Sun's 2021 arithmetic lemmas, Sun's
2026 ten-integer reduction, and package 31's finalizer proof. It is not a
new end-to-end Lean or Rocq theorem. The equivalence proves neither
consistency nor inconsistency of ZFC, and no solution search was performed.

The article is supplied as [`report.tex`](report.tex) and
[`report.pdf`](report.pdf). Additional proof and review notes are under
[`proof-notes/`](proof-notes/).

## Why the smaller source works

The 31 nonnegative source coordinates occupy the 31 positive positions of
a 32-element Sidon set containing zero. Its largest position is 799, and
all 528 unordered pair sums are distinct. The square of the packed digit
polynomial therefore separates every quadratic monomial. Each of the 22
quadratic residuals receives one reversed coefficient block, with stride
1599. Its selected coefficient recovers exactly twice that residual.
A binary no-carry mask tests all selected coefficients simultaneously.

The highest reversal exponent is 35177 and the highest convolution
exponent is 36775. The source's binomial-interface modulus is
`N=4 B^37576`. These replace the large powers of five in the previous
source, while keeping its two source unknowns and the same later
ten-integer bridge.

The proof establishes positivity and bounds for **every** permitted value
of the packed witness, before the no-carry mask has decoded it. It also
checks the zero-position convention, signed coefficients, the overlap of
unselected coefficient bands, and all hypotheses of the downstream bridge.

## Authoritative fixed instance

[`INSTANCE.json`](INSTANCE.json) is the active package-level binding.
The four compressed payloads in `data/` are one complete
`wang943-mixed-121x8801` compiler tuple:

| Polynomial port | Payload | Convention |
|---|---|---|
| `beta` | `data/beta.bin.gz` | `B_compiler-1` |
| `K0` | `data/K.bin.gz` | Complete compiler transport coefficient |
| `MC` | `data/MC.bin.gz` | Compiler low mask |
| `MF` | `data/MF_source.bin.gz` | **Already shifted** by `B_compiler-1` |

Do not splice ports from other tuples or shift `MF` a second time. The
historical bindings embedded in the preserved parent source, and the old
relative proof link inside `data/coefficients_binding.json`, are provenance
metadata. They do not override `INSTANCE.json`. The active coefficient
adapter proof is
[`vendor/package31/coefficients/COEFFICIENT_PROOF.md`](vendor/package31/coefficients/COEFFICIENT_PROOF.md).

The comparison revision is ProveIt
`22e75dd6b87b1b199bb08c778d7cf075ae5aae08`. Source bytes and payload hashes
are checked by the independent audit. The complete fixed instance can be
reconstructed without a GitHub connection.

## Reproduce the arithmetic and audits

Only **Python 3.10 or newer and its standard library** are needed for the
arithmetic builder and checks. From the package directory, run:

```bash
python3 reproduce.py
```

The same command works from any directory when given the absolute path to
`reproduce.py`. It regenerates the circuit and source records, runs the
independent symbolic/circuit audit, checks the source interface on small
systems, verifies the Sidon certificate, and reconstructs the four active
coefficient payloads from the preserved generator in a temporary copy.
It checks the active `INSTANCE.json` binding and writes receipts under
`generated/` and `vendor/`. It exits with a nonzero status if a step fails. Do not use
Python's `-O` option for the full audit, because some inherited checks use
assertions; the driver explicitly rejects optimized execution.

The most important receipts are:

- `vendor/REBUILD_RECEIPT.json`: byte identity of all four reconstructed
  coefficient payloads, pinned source hashes, and the literal K215 transition
  table supplied to the compiler.
- `generated/INDEPENDENT_AUDIT.json`: exact symbolic recovery of all 22
  residuals, actual coefficient bounds and hashes, 809-operation ledger,
  and the exact-degree certificate.
- `generated/SOURCE_INTERFACE_AUDIT.json`: 699 source-interface checks on
  small quadratic systems, including invalid encodings and boundary cases.
- `generated/SIDON_AND_TOYS_AUDIT.json`: independent Sidon construction and
  source examples, including negative controls.
- `generated/REPRODUCTION.json`: the complete run's status and step receipts.

The exact-degree certificate combines a syntactic upper bound with a
nonzero leading coefficient after the specialization assigning the same
indeterminate to all ten unknowns, reduced modulo a prime. This certifies
an exact degree rather than estimating it from random evaluations.
The finite tests support implementation correctness; the article supplies
the unbounded mathematical argument.

For an inexpensive modular evaluation of the delivered polynomial, run:

```bash
python3 evaluate.py --modulus 1000003 1 1 1 1 1 1 1 1 1 1
```

The ten arguments follow the variable order shown above. A zero modulo the
chosen modulus is not a certificate of an integer zero.

## Build the PDF

The PDF is already included. To rebuild it using a TeX installation with
`latexmk` and the article's standard mathematical packages:

```bash
make pdf
```

`make verify` runs the Python reproduction. `make all` performs both tasks.
The Python reproduction does not require a TeX installation.

## Integration and research directions

Keep this directory intact when incorporating it under the existing
`con-zfc-diophantine-forms` report collection. `38-b2-blocks` is a suggested
directory name if it is still available at integration time. The numbered
placement and collection-level README update remain the maintainer's choice.
The delivered reproduction uses paths relative to its own location and does
not rely on the development workspace or omitted upstream copies.

Further directions include exploiting the residuals' sparse support for
tighter position sets and block layouts, formalizing the multi-residual
source lemma, and developing corresponding improvements to the
nine-natural-variable reduction. The article distinguishes these open
questions from the proved construction.

See [`NOTICE.md`](NOTICE.md) and the preserved vendor notices for attribution.

