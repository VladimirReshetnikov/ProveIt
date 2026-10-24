# Explicit quartics for Con(ZFC)

This research package constructs fixed ordinary Diophantine equations whose
absence of solutions is provably equivalent in ZFC to Con(ZFC). The main
results are **407 nonnegative integer variables**, **888 unrestricted integer
variables**, and a **917-integer alternative with smaller coefficients**.

Read `report.pdf` for the mathematical proof and complete printed residual
lists of the three main equations. Its editable source is `report.tex`.
The article explicitly identifies the inherited calculus calibration and
the boundary between mathematical proof and finite computational checking.

## Exact results

Each equation is the sum of the squares of its listed residuals. All
coefficients are literal integers; all exponents in the final polynomial
are fixed. Nonnegative integers include zero.

| Directory | Domain | Variables | Residuals | Degree | Expanded monomials | Coefficient height |
|---|---|---:|---:|---:|---:|---:|
| `equations/natural407` | Nonnegative integers | 407 | 323 | 4 | 8,420 | 83,843,774 |
| `equations/natural410` | Nonnegative integers | 410 | 326 | 4 | 7,029 | 211,184,624 |
| `equations/integer888` | Integers | 888 | 470 | 4 | 10,156 | 2,445,790,974,704 |
| `equations/integer917` | Integers | 917 | 499 | 4 | 6,986 | 63,906,036 |

Height means the maximum absolute coefficient of the fully expanded single
polynomial, after collecting equal monomials.

The 407-variable equation improves the inspected direct quartic baseline of
522 naturals by 22.03% in variables and 58.37% in expanded monomials. The
888-variable equation improves the inspected direct quartic baseline of
1,690 integers by 47.46% and 52.50%, respectively. This is a specific
degree/coefficient tradeoff. ProveIt contains other constructions with far
fewer variables and different degrees or coefficient payloads; no globally
smallest equation or worldwide priority is claimed.

The comparison snapshot is ProveIt commit
`85ae4070019efd66ea3e58e9a67d287528094e8b`; the inherited logical calibration
is pinned to `08200eb10fde2db408c69dffd840d6920a569b1f`.

## Main changes

- Replace exact range-binomial values by the divisibility relation actually
  used by the CRT certificate. Choose the radix divisible by that modulus.
- Require carry-free lower digits only. An existing factorial numerator
  then supplies the radix bound, avoiding a separate power computation.
- Store a difference square with one total nonnegative quadratic gate.
- Derive three requested Pell indices by addition, leaving 15 seed tests.
- Certify natural-coordinate restorations by exact rational square
  decompositions, allowing signed expanded coefficients.
- Infer 523 coordinate signs from the existing equations. Only 167 seeds
  require independent integer guards.

These changes are combined with the inherited eight-column projection and
synchronized arithmetic. The source is the calibrated numerical calculus
C222; the construction does not simulate K215 or use Jones's universal
polynomial or Sun's variable reduction.

## Verify or reproduce

Python 3.10 or later and its standard library suffice. From this directory:

```sh
python3 verify.py
python3 -O verify.py
python3 reproduce.py --output /path/to/new-empty-directory
```

The verifier authenticates 51 inherited source files, rebuilds the source,
checks literal arithmetic identities and bound certificates, independently
checks the inverse maps and sign proofs, expands the four final quartics,
rejects deliberately corrupted certificates, and reproduces the delivered
coefficient lists in an isolated temporary directory. It does not overwrite
the delivered equations or search for solutions. Verification receipts from
both Python modes are in `receipts/`.

Compile the article using a TeX installation with the packages named in its
preamble:

```sh
python3 code/render_residuals.py
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

The rendering script deterministically produces the complete residual
appendices from the literal equation JSON files.

## Data format

In each `equation.json`, `variables` specifies the coordinate order and
`residuals` lists the polynomials to be squared and summed. A term
`[c, [i, j, ...]]` means the integer coefficient `c` times the product of
the indicated variables, with repetitions representing powers. An empty
index list denotes a constant. Thus `[7, [2, 2]]` means `7*x_2^2` and
`[-3, []]` means `-3`. Indices begin at zero.

`expanded_polynomial.json` gives the completely collected single polynomial
in the same coefficient/monomial representation. No extra domain condition
is attached to the integer equations. Their sign guards are already part
of the supplied polynomial.

## File map

| Path | Purpose |
|---|---|
| `report.tex`, `report.pdf` | Mathematical construction, proof, limitations, complete main equations |
| `appendix/` | Generated full residual lists in LaTeX |
| `equations/source690/` | Uncontracted natural source, majorants, gate and arithmetic ledgers |
| `equations/natural407/`, `natural410/` | Natural equations, full expansions, inverse certificates |
| `equations/integer888/`, `integer917/` | Integer equations, sign conversion, inverse certificates, full expansions |
| `code/` | Builders and independently implemented finite checkers |
| `proofs/` | Detailed mathematical notes for the new transformations |
| `upstream/` | Pinned inherited source and its original notices |
| `provenance/` | Comparison inventory, source hashes, prior projection proof |
| `receipts/` | Exact verification outputs and document checks |
| `SHA256SUMS` | Byte digests for the released files |

The archive contains the immediate calibration files and their source pins,
not the entire Lean dependency closure. The ordinary mathematical proof
uses the named calibration theorems. This contribution supplies no new
end-to-end Lean/Rocq theorem or emitted object-language ZFC proof. Finite
algebra checks support the construction but do not replace its unbounded
proofs. No assumption of Con(ZFC), and no proof of Con(ZFC), is claimed.

The package is suitable for review as a self-contained ProveIt incoming
contribution. See `NOTICE.md` for attribution and `LICENSE` for permissions.
