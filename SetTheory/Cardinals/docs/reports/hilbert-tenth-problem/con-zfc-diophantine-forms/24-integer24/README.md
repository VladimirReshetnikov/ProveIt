# Smaller explicit Diophantine forms of ZFC consistency

AI-assisted synthesis for the ProveIt repository, 22 October 2026.

**Main new result:** a polynomial in **24 unrestricted integer variables**,
of exact degree **1936**, with a **167-operation** division-free evaluator,
whose absence of integer zeros is provably equivalent in ZFC to `Con(ZFC)`.
Its three-equation version has maximum degree 1920 and 162 operations.

The report and complete standalone source are `con_zfc_synthesis.pdf` and
`con_zfc_synthesis.tex`. The editable section sources are in `sections/`.

## Exact scope

The proof establishes, by ordinary mathematics formalizable in ZFC,

\[
\exists x\; P(x)=0
\iff \text{the blank K215 machine halts}
\iff \text{ZFC has a finite refutation}.
\]

Negating gives the requested consistency equivalence. The report does not
prove that ZFC is consistent, does not test the actual existence of a zero,
and does not claim a new end-to-end proof-assistant formalization. It
supplies proofs for the new reductions and explicitly identifies the
inherited compiler, signed-domain and K215 calibration results.

Comparisons are with ProveIt commit
`ae3007ca4467011e0e051c84acb4a1dd13971b0e`, not a moving branch. The source
snapshot is recorded in `evidence/SOURCE_PINS.json` and the original
comparison note is preserved in `upstream/collection_at_pin.md`.

## Main constructions

Operations count every binary addition, subtraction and multiplication,
including operations by fixed numerals. Reuse and system comparisons are
free. Degrees are total polynomial degrees with the four coefficient ports
fixed; all named intermediate expressions are abbreviations, not extra
variables.

| Domain and form | Variables | Equations | Exact degree / maximum degree | Operations |
|---|---:|---:|---:|---:|
| New signed separating product | 24 integers | 1 | 1936 | 167 |
| New signed separating system | 24 integers | 3 | 1920 | 162 |
| New signed sum of squares | 24 integers | 1 | 3840 | 170 |
| Tightest separating product | 12 positive | 1 | 1069 | 123 |
| Tightest separating system | 12 positive | 3 | 1060 | 118 |
| Tight separating product | 12 positive | 1 | 1073 | 121 |
| Tight separating system | 12 positive | 3 | 1064 | 116 |
| Simpler separating product | 12 positive | 1 | 1081 | 120 |
| Simpler separating system | 12 positive | 3 | 1072 | 115 |
| Refactored existing norm | 12 positive | 1 | 1353 | 113 |
| Refactored existing norm system | 12 positive | 3 | 1344 | 108 |
| Refactored monic merger | 13 positive | 1 | 319 | 89 |
| Refactored monic merger system | 13 positive | 4 | 288 | 81 |
| Inherited P67, new coefficients | 15 positive | 1 | 155 | 67 |
| Inherited retained system, new coefficients | 16 positive | 7 | 24 | 59 |

The other five delivered packets are the three positive sum-of-squares
versions and the exact-refactored twelve-variable monic product/system.
The latter has degree/operations 1529/114 and 1520/109 respectively and is
included as an identity-preserving comparison, not a new best tradeoff.
Here an exact refactoring means a polynomial identity with coefficient
ports held equal. Binding that arithmetic template to the new complete
tuple is a separate step justified by the coefficient-adapter proof.

The collection's nine-natural-variable Jones construction remains smaller
in coordinate count, at its much higher degree. The 67-operation single
equation and 59-operation system also retain those advantages. There is no
claim of global optimality, eleven positive variables, or fewer than 67
operations for a single equation.

## Which files define the equation?

- `circuits/signed_separating_saturated24_product.json` is the primary
  unrestricted-integer equation.
- `circuits/optimized_tightest_separating12_product.json` is the positive
  degree-1069 equation.
- Replacing `product` with `system` selects the associated system.
- `circuits/optimized_norm12_product.json` is the 113-operation refactoring
  of package 21's twelve-variable polynomial.
- `coefficients/COEFFICIENT_BINDING.json` gives the one complete fixed
  coefficient tuple for all delivered circuits and the checksums of its
  four binary payloads.

A circuit's `witnesses` are its quantified variables. Its `source` is an
ordered list `[name, operation, left_operand, right_operand]`. Integer
operands are literal constants; string operands refer to prior registers
or ports. The `output` is equated to zero, or each pair in `comparisons` is
equated. All gates and all supplied variables are live.

**Do not mix coefficient tuples.** The four ports are
`beta = B-1`, `K0 = DC+B*DR`, the native low mask `MC`, and the **shifted**
high mask `MF = native_high_mask+B-1`. They are four specific integers, not
additional unknowns. The base is

\[
B=2^{6364399},\qquad 6364399=529\cdot12031=23^2\cdot53\cdot227.
\]

The gzip files contain minimal unsigned little-endian byte strings. The
total is 3,545,690 uncompressed bytes and 18,319 compressed bytes. These
payloads are already materialized, without any search for a machine halt.
The previous compact Wang943 tuple used 5,312,269 uncompressed bytes.

## Offline verification and reconstruction

Requirements: Python 3.10 or later with its standard library; a conventional
TeX Live installation only if rebuilding the PDF. No network access or
repository checkout is needed for the arithmetic checks.

From this directory:

```sh
python3 verify.py
python3 reproduce.py
```

`verify.py` checks the supplied DAGs, operation ledgers, provenance and
payload hashes, exact identities, comparison circuits, and full
finite-field degree diagnostics using the actual coefficient residues.
It writes its detailed receipt under `evidence/`.

`reproduce.py` rebuilds the four fixed integers and the principal new
circuit families, restores/refactors the inherited circuit sources,
reapplies the common coefficient binding, then runs verification. The
preserved original packets needed for these operations are included in
`upstream/`.

The finite diagnostics corroborate the exact circuit formulas. Universal
semantic equivalence and uniform degree claims rest on the proofs in the
report. In particular, finite-field checks are not substituted for the
signed root-recovery argument or for native compiler soundness.

To rebuild the PDF directly from its standalone source:

```sh
pdflatex -interaction=nonstopmode -halt-on-error con_zfc_synthesis.tex
pdflatex -interaction=nonstopmode -halt-on-error con_zfc_synthesis.tex
```

To incorporate edits made in the individual section files first:

```sh
python3 code/assemble_report.py
```

The root `Makefile` provides `verify`, `reproduce` and `pdf` targets.
`SHA256SUMS` records the shipped file bytes; it is a release record rather
than a promise that a rebuilt PDF will have byte-identical creation
metadata.

## Layout and proof provenance

| Path | Contents |
|---|---|
| `con_zfc_synthesis.tex`, `.pdf` | Complete report and compiled document |
| `sections/` | Editable report sections and wrapper |
| `circuits/` | Twenty explicitly bound arithmetic DAGs |
| `coefficients/` | Complete coefficient binding and four gzip payloads |
| `code/` | Standard-library builders, algebra checks and packaging helpers |
| `evidence/` | Finite audit receipts and source checksums |
| `proofs/PROOF_DEPENDENCIES.md` | Dependency and review boundary |
| `upstream/` | Pinned source proofs, machine table, tiles and original circuits |
| `licenses/`, `NOTICE.md` | Preserved licenses and attribution |

The inherited Lean endpoint is included for provenance, not as a standalone
build of the complete Lean project. No GitHub files were modified by the
preparation of this archive.
