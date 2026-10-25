# Shared residue bounds for Diophantine ZFC refutation certificates

**Principal result:** an explicit polynomial in **260 unrestricted integer
variables**, of exact degree **4**, with **4,770** nonzero collected monomials
and coefficient height **9,191**. It is the sum of the squares of **186
quadratic residuals**, every one printed in `report/paper.pdf` and specified
in `equations/principal/equation.json`.

The ordinary mathematical proof, composed with the explicitly retained
ProveIt source calibration, establishes in ZFC:

    P has no integer zero if and only if Con(ZFC).

There is no new complete end-to-end Lean or Rocq verification claim. Finite
checks certify the literal arithmetic and coefficient files; the paper
proves the unbounded reduction and identifies its inherited logical and
number-theoretic dependencies. No consistency assertion or global
simplicity minimum is claimed.

## What changed

The current direct predecessor in the inspected Round 17 incoming archive
has 282 variables, 192 quadratic residuals, 5,491 monomials and coefficient
height 128,446. Eleven individual remainder bounds can be replaced by three
shared quadratic bounds because their canonical low binomial residues are
already much smaller than their moduli. Two groups use adjacent radix
powers and can share their witnesses. This gives 260 variables. A frozen
sequence of 76 invertible integral coordinate shears then lowers the
coefficient height and support without changing the integer zero set.

The coefficient bound is used in a proved acyclic order: recover powers,
recover the factorial digit alone, identify the factorial, then decode the
remaining digits. In particular the proof does not assume F=t! to validate
the digit from which F=t! is recovered.

## Supplied alternatives

| Equation | Integer variables | Quadratic rows | Degree | Monomials | Height |
|---|---:|---:|---:|---:|---:|
| Principal after shears | 260 | 186 | 4 | 4,770 | 9,191 |
| Grouped bounds companion | 261 | 185 | 4 | 5,332 | 128,446 |
| Wider projection companion | 259 | 185 | 4 | 23,960 | 240,653 |

The 259-variable equation trades a much denser polynomial for one fewer
variable. The repository also contains few-variable quartics using large
fixed coefficient tuples; the present result improves the direct route
with small literal coefficients, not those equations' variable counts.

## Files

- `report/paper.tex`, `report/paper.pdf`: the research article, complete
  mathematical reduction, calibration status, future questions, and every
  principal quadratic residual. The generated TeX includes are beside them.
- `equations/principal/`: final residuals, every collected coefficient,
  exact metrics, 76 shears, and the full integral linear coordinate map.
  JSON indices are zero-based; printed z subscripts are one-based.
- `equations/shear_stages/`: immutable intermediate records used by the
  independent coordinate checker. Their variable metadata describes
  historical origins; final coordinates are named z_1,...,z_260.
- `certificate/`: the portable arithmetic source package, immutable parent
  inputs, all three selected pre-shear variants, exact projection records,
  original producers and checks, and the retained ordinary proof closure.
- `certificate/grouped_centered/`: the 261-variable companion.
- `certificate/merged_cap32_centered/`: the 259-variable companion.
- `review/`: mathematical reviews, actual verification receipts, and the
  scoped internal-ZFC calibration audit with its inspected source files.
  That source bundle is not the entire Lean import closure.
- `code/`: deterministic principal reconstruction and independent checks.
- `SOURCES.json`: comparison pin, source URLs, and exact selected hashes.
- `MANIFEST.sha256`: hashes of the final release files.

## Verify and reconstruct

Python 3 and its standard library suffice. No network or proof search is
needed. From the extracted archive directory run:

```bash
python3 verify.py --receipt review/local_check.json
python3 -O verify.py --receipt review/local_check_optimized.json
```

To regenerate all three arithmetic variants into temporary directories and
compare every produced JSON file byte for byte, add `--rebuild`:

```bash
python3 verify.py --rebuild --receipt review/local_rebuild.json
```

To reconstruct the principal coordinate transformation, coefficient files,
and printed residual appendix directly from the frozen source and shears:

```bash
python3 code/generate_principal.py --check
```

Omitting `--check` rewrites those generated files deterministically.
The shear-search heuristic is not needed to reconstruct or verify the
fixed mathematical object. Its successful frozen sequence is the certificate.

To build the PDF with a standard LaTeX installation:

```bash
cd report
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

The archive retains actual normal and optimized verification receipts,
including 29 semantic-certificate corruption controls and three coordinate
corruption controls. Such controls exercise the checkers; the unbounded
mathematical proof remains separate.

## Source and integration boundary

Comparison snapshot:
`e0c98c629bf10d30b695884f6b1d2ab361bdf513` of
https://github.com/VladimirReshetnikov/ProveIt .

The source is the latest `strict_dimension` signed direct construction in
`docs/incoming/ConZFC_Cofinal_Anchors_Height_One_Round17_2026-10-25.zip`.
The older Cantor and actual square-shell syntax conventions are explicitly
bridged in `certificate/inherited_proofs/SHELL_ENCODING_PROOF.md`.

This packet is intended for integration as a new research package under
`Computability/DiophantineConsistency/con-zfc-diophantine-forms`, or first
through `docs/incoming`. No repository commit, pull request or remote file
modification was made by this research task.

The note and new code were prepared with AI assistance. Earlier authorship
notices and license files remain in the inherited component. The standard
three-square representation, integral shears and elementary residue bounds
are not claimed as new general number-theoretic discoveries. The new
contribution is their proved composition in this signed source and its
fully specified smaller equations.
