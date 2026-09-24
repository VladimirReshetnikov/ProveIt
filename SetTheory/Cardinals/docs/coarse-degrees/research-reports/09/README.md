# Perfect Exact Pairs in Coarse-Description Classes

Research note prepared for Vladimir Reshetnikov, 18 September 2026.

## Result

For a binary set X, let C_X be all its density-zero modifications and let
I_X be the sets computable from every member of C_X. The article proves that
C_X contains a perfect family of pairwise Turing-incomparable members whose
pairwise common lower cones are exactly I_X. One can simultaneously arrange
exact intersections with the lower cones of any prescribed countable family
of oracles.

An explicit guarded diagonalization produces a computably enumerable,
many-one complete X with trivial core and no computable coarse description.
Its uniform and nonuniform coarse classes therefore contain Turing minimal
pairs, have no least Turing degree, and have no countable coinitial family of
representative degrees. A perfect family can be chosen whose members form
minimal pairs with the halting degree itself. The relative construction
realizes any principal lower cone as the core.

## Status: separate the theorem from the novelty claim

The literal negative answer to C1 in the uploaded survey already follows from
Hirschfeldt–Jockusch–Kuyper–Schupp (2016), particularly the result attributed to
Igusa as Theorem 4.3. It is not a new solution to a previously unresolved
problem, even though Gerdes (2025), Question 7, asks the literal question.

The stronger simultaneous exact-pair and perfect-family theorems have complete
conventional proofs in this note. Their novelty has not been established.
They have not been independently refereed or checked in Lean. The companion
finite program does not verify the infinite theorems.

The effective-dense question C2 is not answered. Absence of a least degree or
a countable coinitial subset does not assert absence of individual minimal
degrees.

## Files

- `coarse_degree_attack.tex`: self-contained LaTeX article.
- `coarse_degree_attack.pdf`: locally compiled and visually inspected article.
- `checks/check_finite_lemmas.py`: deterministic exact-arithmetic checks.
- `checks/results.json`: the actual check results, including case counts.
- `proof_audit.md`: dependency ledger and critical mathematical checks.
- `sources.md`: primary references, provenance, and search scope.
- `verification/build_summary.json`: local build and PDF inspection summary.
- `source/turing_degrees_unified.tex`: unchanged source supplied by the user.
- `build.sh` and `build.ps1`: rebuild scripts for Unix-like shells and PowerShell.
- `MANIFEST.sha256`: hashes of the other archive files.

## Reproduce

Requirements: Python 3.9 or later and TeX Live or MiKTeX with the ordinary
packages used in the source. Python needs no third-party modules. Fonts are
provided by the TeX installation through the `lmodern` package.

On Linux or macOS:

```sh
sh build.sh
```

On Windows with PowerShell:

```powershell
./build.ps1
```

Or run the individual commands from the archive root:

```sh
python checks/check_finite_lemmas.py --output checks/results.json
pdflatex -interaction=nonstopmode -halt-on-error coarse_degree_attack.tex
pdflatex -interaction=nonstopmode -halt-on-error coarse_degree_attack.tex
```

The build scripts put intermediate TeX files in `_build/` and copy the final
PDF to the archive root. The source survey is included for provenance only;
it is not included as a LaTeX dependency and is not recompiled.

The shipped run passed 302,579 finite cases. They check finite metric and
patch inequalities, arithmetic column counts, a finite guarded enumeration
model, and majority decoding. They do not decide totality, test an infinite
oracle, prove a density limit, perform the Baire construction, or certify
mathematical novelty.
