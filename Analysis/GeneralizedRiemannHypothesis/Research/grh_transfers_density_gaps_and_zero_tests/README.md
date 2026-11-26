# Geometric progressions and nonabelian zero tests

Read **report.pdf**. The PDF bookmarks link to the proofs. The complete LaTeX source starts at **report.tex**. All other TeX files are included by that file.

## Results

- Sections 2–4 prove strict density gaps for geometric-progression-free sets, including affirmative answers to McNew's Questions 7.1 and 7.3. Section 2.2 proves existence of maximizing sets for natural density on the integers.
- Section 5 proves finite-degree Jensen results for the nonabelian conductor-23 Artin factor, gives a counterexample to a general cubic kernel assertion, and proves a necessary condition on Gaussian perturbations. It explains the dependencies for each claimed degree range.
- Sections 6–7 solve the two character-degree optimization problems over odd finite fields. The arithmetic application describes the new estimate still needed.
- Section 8 lists open research questions. The JSON file gives the pinned source and links to the earlier reports.

## Replay

Use Python 3.10 or newer. The scripts use only the standard library. Run each script below with python3. The reference outputs are in the verification directory.

| Checker | Calculation |
|---|---|
| check_integer_gap.py | All subsets through 12, common integer gap, and the four-prime upper bound on natural density |
| check_integer_prefix.py | Exact prefix losses through 80, separate gap bounds for rational and integer ratios |
| natural_density_check.py | Largest-factor distribution inequalities and weighted smooth polynomial optima |
| check_gap.py | Binary polynomial prefixes and field-by-field rational gap bounds |
| check_cubic.py | Rational interval certificate for the negative cubic discriminant |
| check_height.py | Fixed-point and rational enclosure of the full height-four rectangle |
| check_odd_psl2.py | Direct small matrix-group checks of the minimizing character |
| check_affine.py | Fixed-vector dimensions in representative affine subgroups |
| check_small_subgroups.py | Complete exceptional-subgroup calculation for the remaining small fields |

The finite checks support the general paper proofs. The upstream Lean build and Ng's high-zero verification were not rerun. The growth and classification arguments have not been formalized in Lean.

To rebuild with a standard TeX Live installation, run **latexmk -pdf report.tex**, or run **pdflatex report.tex** twice. To verify file integrity, run **sha256sum -c SHA256SUMS** from the extracted directory.
