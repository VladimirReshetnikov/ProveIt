# Coarse Classes Without Least Turing Degrees

Research continuation of `turing_degrees_unified.tex`, target C1.
Prepared for Vladimir Reshetnikov, 18 September 2026.

## Main result

Let `R(A)(n) = A(v_2(n+1))`. The report proves that the Turing-degree
spectra of its density-zero agreement class and its uniform and nonuniform
coarse-equivalence classes are all exactly

    { deg_T(B) : A <=_T B' }.

For every `A` not computable from the ordinary halting set, the class has
no least Turing degree. The explicit example takes `A = emptyset''`.
Its spectrum is the unrestricted high degrees: `b' >= 0''`.

The central finite-extension construction produces two density-zero-agreeing
representatives with only computable common Turing lower bounds, and with
both jumps equivalent to `A join emptyset'`. A countable version and the
classification `R(A) <=_uc R(B) iff R(A) <=_nc R(B) iff A <=_T B join 0'`
are included with proofs.

In contrast, the effective-dense classes of `R(A)` have spectrum
`{deg_T(B): A <=_T B}` and least degree `deg_T(A)`. Thus C2 is NOT settled.

## Priority and verification status

This is not a claim of a previously unknown resolution of an established
open problem. The negative coarse answer also follows from older results
of Jockusch--Schupp and Hirschfeldt--Jockusch--Kuyper--Schupp (the latter
result is credited to Igusa). The paper explains this status correction.
Priority of the specific strengthened formulations is not established.

The infinite assertions are supported by the written proofs, not by the
finite tests. No Lean development was produced or compiled. There is no
independent expert-review certificate. The noncomputable oracle construction
is stated with its actual oracle requirements; the package does not claim
to compute an ordinary finite representation of the second Turing jump.

## Files

- `coarse_counterexample.pdf`: typeset article with full proofs.
- `coarse_counterexample.tex`: complete, standalone LaTeX source.
- `code/finite_model.py`: finite column, restraint, sparse-coding, and
  finite-query decision-tree models.
- `code/check_finite.py`: reproducible finite regression checks.
- `verification/finite_checks.json` and `.log`: actual recorded test results.
- `verification/proof_audit.md`: proof obligations and caveats.
- `verification/source_audit.md`: source identities and status distinctions.
- `verification/build_verification.json`: PDF/build checks performed.
- `build.sh`: commands for rebuilding and rerunning the finite checks.

The supplied unified report is cited, not duplicated in this package.

## Reproduce the finite checks

Requires Python 3.10 or later; no third-party packages.
From the package root:

    python3 code/check_finite.py

Do not use Python's `-O` flag: these checks use assertions. The program also
explicitly rejects that flag. The recorded result is PASS, with 184,701
finite checks/classified cases. Some categories overlap; this number is not
an assertion of independent tests or a measure of proof strength.

The product tests exhaust all finite tables with two binary oracle queries
and outputs in `{divergence, 0, 1}` for the specified condition family.
Their finite semantics make absence of a witness decidable in that model.
They do not approximate an unbounded negative halting answer.

## Rebuild the PDF

Requires a TeX installation with pdfLaTeX and the packages listed in the
source, including Latin Modern, amsmath, amsthm, hyperref, and microtype.
No external images, bibliography processor, custom font files, or shell
escape are required.

    pdflatex -interaction=nonstopmode -halt-on-error coarse_counterexample.tex
    pdflatex -interaction=nonstopmode -halt-on-error coarse_counterexample.tex

A third pass may be needed after changing pagination. Alternatively run:

    sh build.sh
