# A6 nonabelian RH transfer

**Status:** proved character identities, local zero-order inequalities, degree/support optimality in stated character classes, and analytic equivalences; the class-sensitive prime bound itself remains open. No claim of full nonabelian GRH or literature priority.

Read `report.pdf`; `report.tex` is the complete source. The theorem takes RH as input, consistent with the stated premise and upstream Lean theorem. The upstream theorem is Dirichlet GRH, not general Hecke or Artin GRH. The source was inspected at commit 72fead102f663d5c7a407964a13dc0cf9d977207, but not rebuilt or kernel-replayed here.

## Reproduce

From the extracted directory:

```sh
python verify_characters.py
python verify_field.py # requires SymPy
pdflatex -interaction=nonstopmode -halt-on-error report.tex
pdflatex -interaction=nonstopmode -halt-on-error report.tex
```

`verify_characters.py` reconstructs A6 and all subgroups/linear characters used in the report, verifies the three identities on all 360 elements, checks the character norms and small-degree obstruction, and writes `character_certificate.json`. It needs only Python's standard library. `verify_field.py` certifies the discriminant and finite-field factors at 3, 5 and 109, cross-checks the Galois group using SymPy, and writes a small sample census `sample_patterns.csv`. The counts are not a proof of any asymptotic statement. Logs `character_check.txt` and `field_check.txt` record the successful runs.

`source-audit.tsv` records exact Git blob identifiers for inspected source files. `prior-audit.md` describes the selected earlier reports actually inspected. The proof of the analytic reduction uses standard Artin formalism, Hecke theory, Chebotarev estimates, and the explicitly proved Mellin–Landau argument. These are mathematical inputs, not checked by the finite scripts. No new Lean proof was built.
