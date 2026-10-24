# Synchronized arithmetic certificates for ZFC refutability

**Main result:** a fully specified quartic in **522 nonnegative integer variables**, with 400 quadratic residuals, 20,225 expanded monomials, and coefficient height 83,900,628. Its lack of solutions is provably equivalent in ZFC to Con(ZFC), by the ordinary proof in `report.pdf` / `report.tex` and the explicitly identified inherited calculus calibration.

The package also supplies a fully expanded quartic in **2,088 unrestricted integer variables** with the same consistency equivalence. The construction directly encodes the calibrated numerical calculus C222. It does not simulate K215, and it does not use Jones's universal polynomial.

## Exact results

Every listed equation is the sum of squares of its supplied quadratic residuals, and every listed degree is exactly four.

| Directory | Domain | Variables | Residuals | Expanded monomials | Maximum absolute coefficient |
|---|---|---:|---:|---:|---:|
| `equations/source895` | Nonnegative integers | 895 | 773 | 4,863 | 63,908,265 |
| `equations/natural596` | Nonnegative integers | 596 | 474 | 7,263 | 63,909,160 |
| `equations/natural529` | Nonnegative integers | 529 | 407 | 10,782 | 211,184,624 |
| **`equations/natural522`** | **Nonnegative integers** | **522** | **400** | **20,225** | **83,900,628** |
| **`equations/integer2088`** | **All integers** | **2,088** | **922** | **26,791** | **83,901,150** |

The 522-variable form uses the fewest variables among these materialized variants. The 529-variable form uses seven more variables and approximately half as many monomials. The 596-variable form trades further variables for a smaller expression and smaller coefficients. The 895-variable form is the independently audited parent of all three natural contractions.

The immediate incoming direct baseline has 3,614 natural variables, degree four, 2,954 residuals, 15,996 monomials, and coefficient height 127,778,545. Thus the new 522-variable equation reduces its variable count by **85.56%** and lowers its coefficient height. The repository already has much lower-variable equations with other degree/coefficient tradeoffs. No global simplicity optimum or worldwide priority is claimed.

## The mathematical change

The arithmetic certificates are chosen for an entire finite circuit:

1. A common radix certifies all 14 binomial requests. The digit graphs are deferred until the semantic upper arguments are known.
2. One global Pell frame certifies all 27 positive-power requests. Its defining norm gives an exponential bound, not just a quadratic bound.
3. There is one Pell-index block per distinct exponent (22 blocks), one modulus per distinct base (10 moduli), and one common auxiliary Pell solution and CRT base for every index.
4. The conditions `V = product(Y_i^2) * (v+1)` and `B = 1 + 4*V*(q+1)` replace whole families of separate divisibility certificates.
5. Local proof bounds remove two remainder coordinates and a separate uniform bound. A checked majorant uses 23 squarings instead of a duplicate source evaluation.
6. Exact nonnegative polynomial substitutions remove 373 coordinates from the 895-coordinate parent. Their complete inverse maps are supplied.

The common-frame and shared-index completeness proofs are essential: merely identifying independently existential witnesses would be invalid. The report proves that compatible witnesses exist simultaneously. It also resolves the apparent cycle introduced by choosing a common radix after semantic values.

## Read and reproduce

Start with `report.pdf`; `report.tex` is its complete editable source. The `proofs/` directory contains detailed supplementary arguments and scoped mathematical reviews. The full coefficient data are under `equations/`.

Python 3.10 or later and its standard library are sufficient:

```sh
python3 verify.py
python3 -O verify.py
```

The verifier checks file hashes when `MANIFEST.sha256` is present, authenticates inherited calibration files, checks all local numerical code definitions, audits the shared arithmetic construction, exactly regenerates the entire equation tree in a temporary directory, replays every contraction, independently expands the resulting polynomials, and rejects three deliberate certificate corruptions. It does not overwrite the delivered equations and does not search for a solution.

To create a fresh equation tree:

```sh
python3 code/release.py --output /path/to/new-empty-directory
```

To rebuild the article with pdfLaTeX:

```sh
sh build_report.sh
```

Alternatively run `pdflatex -interaction=nonstopmode -halt-on-error report.tex` twice from this directory.

## Literal polynomial format

`equation.json` gives the ordered variable list and the ordered residual list. Each residual term is `[coefficient, variable_indices]`, with integer coefficient and a sorted multiset of zero-based indices. `[]` denotes the constant monomial; `[3,3]` denotes the square of the fourth coordinate. The single polynomial is the sum of the squares of every residual.

`expanded_polynomial.json` gives the complete expanded and collected coefficient list using the same term convention. All coefficients are literal decimal integers. There are no variable exponents, factorials, binomial coefficients, variable-length products, or unspecified coefficient ports in these files.

Each natural contraction also has `elimination_certificate.json`. It lists the original pivot indices, the exact monic residual, its nonnegative restoring polynomial, and the final coordinate renaming. To lift a target zero, insert retained coordinates and apply the restorations in reverse order. The support cap never truncates an expression. A quadratic restoration is permitted only when the pivot occurs as a degree-one monomial everywhere else, so every final residual remains quadratic.

The integer companion retains the 522 coordinates and adds three integer witnesses per coordinate, with residual `8*x_i + 1 - a_i^2 - b_i^2 - c_i^2`. Legendre's three-square theorem proves that these guards express exactly the original nonnegative domain. The integer conversion preserves existence and is not asserted to have unique lifts.

Digest fields inside elimination/conversion certificates are SHA-256 hashes of canonical JSON (`sort_keys=True`, compact separators, no final newline). The outer `MANIFEST.sha256` and `CENSUS.json` hash actual file bytes. Their different purposes and encodings are intentional.

## Provenance and proof boundary

Comparison snapshot: **a88aefd7ddab4771534bb049c67350e397c91b9a** in `VladimirReshetnikov/ProveIt`.

Immediate source: `docs/incoming/ConZFC_Shared_Certificates_2026-10-24.zip`, whose exact archive hash is in `PROVENANCE.json`. Its inherited arithmetic and calibration files remain unchanged under `provenance/upstream/`. Their calibration snapshot is **08200eb10fde2db408c69dffd840d6920a569b1f**, a different pin from the comparison snapshot.

The logical interfaces are `KEndpoint.c222_iff_zf_refutation` and `ConstructibleChoice.zf_refutation_iff_zfc_refutation`. The arithmetic proof uses Pell classification and `PellRepresentation.criterion_iff_pell`; the new global frame supplies its own exponentiation argument. Immediate source files and original license notices are included. The entire transitive Lean dependency closure was not rebuilt.

The report gives ordinary proofs formalizable in ZFC and separates them from exact finite artifact checks. There is no new full Lean/Rocq proof term or emitted object-language ZFC derivation. There is no proof that ZFC is consistent and no proof that the polynomial has no solution. The result is the equivalence, with neither consistency nor inconsistency assumed.

## Integration

Import this contribution as a new proposal directory with its report, code, equations, proofs, receipts, and provenance together. Existing packages need not be replaced. Record the natural and unrestricted-integer equations separately in frontier comparisons. This release makes no GitHub changes by itself.
