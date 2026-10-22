# A twelve-variable equation for Con(ZFC)

This package improves the explicit Diophantine constructions in ProveIt at
commit `f0ae4e0991ca44a7bb4e5671d42e33d775e48035`.

The main equation is an integer polynomial in **12 strictly positive
unknowns**, with exact degree **1353** and a **116-operation** arithmetic
circuit. ZFC proves that its absence of positive solutions is equivalent to
Con(ZFC). A separately proved conversion gives **26 unrestricted integer
unknowns**, degree 2657 and 168 operations. A positive-domain alternative
has degree 1177 at 123 operations.

Independently, the fixed-coefficient recipe reduces the local alphabet from
37,075 to **5,280** tiles and the base from `2^(5^18)` to **2^(5^15)**.
Thus the binary length of the fixed coefficient `B-1` is 125 times smaller.
All four coefficient ports must be supplied from one complete recipe.

## Read first

- `report.pdf` is the complete article.
- `report.tex` is its LaTeX source.
- `proofs/NORM12_PROOF.md` gives the main algebraic proof.
- `proofs/NORM12_INDEPENDENT_AUDIT.md` and
  `proofs/INTEGER26_PROOF.md` give the independent review and domain extension.
- `proofs/REDUCED_T4_PROOF.md` and
  `proofs/COEFFICIENT_ADAPTER_REVIEW.md` establish the new coefficient adapter.
- `COEFFICIENT_BINDING.json` identifies the exact default four-tuple.

## Results

| Circuit | Domain | Unknowns | Equations | Exact degree | Binary operations |
|---|---|---:|---:|---:|---:|
| `norm12_system` | Strictly positive | 12 | 3 | max 1344 | 112 |
| `norm12_product` | Strictly positive | 12 | 1 | 1353 | 116 |
| `norm12_sos` | Strictly positive | 12 | 1 | 2688 | 119 |
| `norm12_system_integer26` | All integers | 26 | 3 | max 2640 | 164 |
| `norm12_product_integer26` | All integers | 26 | 1 | 2657 | 168 |
| `norm12_sos_integer26` | All integers | 26 | 1 | 5280 | 171 |
| `norm12_system_lower_degree` | Strictly positive | 12 | 3 | max 1168 | 119 |
| `norm12_product_lower_degree` | Strictly positive | 12 | 1 | 1177 | 123 |
| `norm12_sos_lower_degree` | Strictly positive | 12 | 1 | 2336 | 126 |

The four fixed coefficients are not quantified variables. Every temporary
register is a polynomial abbreviation. Arithmetic operations count binary
addition, subtraction and multiplication, including multiplication by
numerals; reuse and system comparisons are free.

The earlier 67-operation product remains smaller by operation count. This
work improves variable count and coefficient size, with degree/operation
tradeoffs. It makes no global minimality claim and does not supersede the
classical abstract nine-unknown representation result.

For the smallest operation count, `upstream/PRODUCT67.json` preserves the
existing 15-positive-variable, degree-155, 67-operation circuit. Supply the
new complete coefficient tuple using the port aliases in
`COEFFICIENT_BINDING.json`. This improves its coefficient size while keeping
its arithmetic unchanged. The copied JSON's own metadata retains its
original source context; the package binding supplies the new recipe.

## Reproduce

Python 3 with its standard library suffices for all arithmetic and finite checks:

```sh
python3 verify.py
```

This runs both emitters, the independent circuit audit, and the finite
coefficient checker. It verifies all shipped upstream hashes and the literal
machine binding. Results are saved in `verification/REPRODUCTION.json`.
It does not expand the huge four integer coefficients or seek a K215 halt.

With a standard TeX Live installation:

```sh
latexmk -pdf -interaction=nonstopmode -halt-on-error report.tex
```

## Circuit format

Each arithmetic JSON has `witnesses`, `fixed_numerals`, and an ordered `source`.
A source row `[name, op, left, right]` defines one binary operation; operands
are earlier registers, input ports, or integer literals. A single equation
sets the register named by `output` to zero. A system requires equality of
each pair in `comparisons`. `ledger` records operation counts and liveness.
The fixed ports are `beta`, `K0`, `MC`, `MF`, with `MF` the shifted mask.

The primary product's SHA-256 is
`ed0232c9530cebd14abfb079285eae16c2c603c624f0777aeb81447cba3d3021`.
The 26-integer product's SHA-256 is
`1964e6c561674106683a21f24499d1b145b427972b2525af3d0ece76991d9016`.
These JSON files remain byte-identical to the independently reviewed packets.

## Proof status

The new norm reduction, rational auxiliary-Pell integrality argument,
integer-domain extension, and coefficient adapter have ordinary
mathematical proofs with independent audits and finite implementation
checks. They are **not new end-to-end Lean/Rocq formalizations**.
The exact K215/refutation endpoint has pre-existing formal proofs recorded
in ProveIt; those builds were not rerun for this delivery.

The statement is an equivalence provable in ZFC, not a proof of ZFC
consistency. No accepting K215 run or positive witness to inconsistency is
provided. The final huge coefficients are exact finite recipes, not
materialized digit expansions.

## Integration

The package is self-contained for its finite checks and may be placed as a
new report source beside the existing packages. `SOURCE_MANIFEST.json` binds
the included upstream proof excerpts to their original paths and snapshot.
The excerpts retain references in their original context. Their presence
does not make the copied Lean endpoint a standalone Lean project.

The new content is supplied for ProveIt under MIT No Attribution terms.
Original ProveIt and Andrew James Wade license texts and inherited
machine/source notices are retained in `upstream/`. See `NOTICE.md`.
