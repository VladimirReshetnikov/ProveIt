# Factorial-free direct quartics for Con(ZFC)

The principal artifact is the single equation

\[
P(x_0,\ldots,x_{241})=\sum_{j=0}^{177}R_j(x_0,\ldots,x_{241})^2=0,
\qquad x_i\in\mathbb Z.
\]

The complete coefficient lists of every quadratic residual are in
`principal/equation.json`. The complete, collected quartic is in
`principal/expanded_polynomial.json`; `principal/residuals.tex` and
`principal/residuals.txt` display the same residuals. No polynomial is left
unspecified by a program index or by an existence theorem.

The accompanying mathematical report proves, using the inherited C222 proof
calculus calibration, that ZFC proves

\[
\neg\exists\vec x\in\mathbb Z^{242}\;P(\vec x)=0
\quad\longleftrightarrow\quad\operatorname{Con}(\mathrm{ZFC}).
\]

The proposed improvement is the removal of factorial authenticity from the
direct CRT construction. It uses the size majorant
`F = (2(t+1))^t`, a generalized CRT argument, the beta parameter
`y = F(2v+1)^2`, and the odd-square radix `q = (2z+1)^2` with strengthened
amplifier `H = 2 + sum(actual CRT representatives)`. These are semantic
descriptions; the final equation contains only ordinary polynomial operations.

## Exact metrics

| Equation | Integer variables | Quadratic residuals | Total degree | Collected monomials | Coefficient height |
|---|---:|---:|---:|---:|---:|
| Principal | 242 | 178 | 4 | 5,018 | 7,968 |
| Companion | 241 | 177 | 4 | 12,774 | 7,968 |
| Retained parent | 252 | 182 | 4 | 5,340 | 128,446 |

Both selected equations have residual coefficient height 64. Height means the
largest absolute coefficient after collection; variable indices are zero-based.
The companion eliminates one more integral affine coordinate at the cost of a
larger expanded support. The principal provides the preferred sparse equation.
The word "principal" does not claim a global minimum in variable count: other
Diophantine representations in the repository use fewer variables with very
different degrees, coefficients, and presentation costs.

## Reproduce and check

Run from any working directory, with Python 3.10 or later and its standard
library:

```sh
python3 -B direct/reproduce.py --receipt direct/review/REPRODUCTION_LOCAL.json
```

If this directory itself is the current directory, use `python3 -B reproduce.py`.
The driver rebuilds 18 JSON files byte for byte, checks the twelve principal and
companion alias files, runs the independent finite algebra checker, runs the
separately authored power-interface checker, and regenerates all six readable
exports in memory for exact comparison. It performs no optimization search and
does not access the network.

For the separate coefficient/projection audit alone:

```sh
python3 -B direct/check_factorial_free.py --affine-only
python3 -B -O direct/check_factorial_free.py --affine-only --skip-parent
```

The checker replays 18 Horn factorization edits, 202 unit-monic projections,
the complete source mutation, coordinate translations, six coordinate shears,
five affine-exposure row operations, three or four affine projections, and the
34 or 36 final row operations. It independently multiplies and collects every
coefficient of the selected quartics. Seven deliberate corruptions are rejected.
The normal receipt also records the separate audit of the inherited 252-variable
parent. The power-interface audit independently reconstructs all 18 power
requests, 37 distinct frame atoms, 14 principal Pell pairs, five base moduli,
and the derived consecutive-index pair.

These are exact checks of finite algebraic artifacts. They do not constitute a
new kernel-checked proof of the unbounded generalized CRT argument, the Pell
theorems, or the proof-calculus calibration. Those mathematical obligations and
the scope of inherited results are stated in the accompanying report.

## Layout and file formats

- `principal/` and `companion/` are convenient exact aliases for the two final
  equations, their collected expansions, metrics, variable maps, and readable
  residual lists.
- `factorial_free_affine/` contains the complete edited raw source, mutation
  ledger, Horn factorization, integral projection and translation certificates,
  and the 245-coordinate intermediate equation.
- `factorial_free_affine242_balanced/` and
  `factorial_free_affine241_balanced/` retain the final coordinate and row
  certificates. Their equation files are byte-identical to the aliases.
- `parent/` is the pinned direct component from the common-remainders archive,
  including its finite checker, proof closure, calibration source excerpts,
  provenance, and license. Its historical proof files retain their historical
  assumptions; the new report supplies the replacement factorial-free argument.
- `sources/` records the inherited odd-square and affine-exposure ideas. The
  new construction does not claim those mechanisms as new discoveries.
- `review/` contains the normal and optimized-interpreter audit receipts.
- `SOURCE_LEDGER.json` pins the repository commit and the three relevant source
  archives by SHA-256.

Each sparse term is `[coefficient, [variable_indices...]]`; an empty index list
denotes the constant monomial, and repeated indices denote powers. The fixed
quartic is exactly the sum of the squares of the listed residuals. All
coordinates range over unrestricted integers.

`evaluate.py point.json` evaluates the principal equation at an explicitly
supplied JSON list of 242 integers; add `--companion` for 241 integers. It is an
exact evaluator, not a solver.

## Attribution and proof dependencies

The construction is based on the ProveIt repository at commit
`3ecd6a6cf53d47519228328567f45fb7ee9781d9`. The exact parent and auxiliary archives
are identified in `SOURCE_LEDGER.json`. The retained C222 calibration uses the
interfaces `KEndpoint.c222_iff_zf_refutation` and
`ConstructibleChoice.zf_refutation_iff_zfc_refutation`; the ordinary mathematical
proof and finite artifact audits must be distinguished from a fresh Lean build.
Inherited licenses and notices are preserved in their directories.
