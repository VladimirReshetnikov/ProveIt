# Microscopic Condensation in Exponential-Feedback Transseries

**Sharp coefficients, Gaussian–Poisson limits, finite-perturbation universality,
and refined Borel growth**

Research article prepared for Vladimir Reshetnikov, 29 September 2026.

## Main result

For the formal fixed point

    U(q) = sum_{j>=1} q^j exp(lambda_j U(q)),

assume nonnegative slopes with

    lambda_j = j^2 + alpha*j + eta*j/log(j) + o(j/log(j)).

Set b = 1 + lambda_1 and let r = r_n be the unique positive root of

    r*(r+1)*exp(2*r) = n.

The article proves

    [q^n] U(q) ~ exp((2*r+1)*n*r/(r+1) + b*r^2 + alpha*r + eta/2)
                   / sqrt(2*r^2 + 4*r + 1).

It also proves a microscopic one-large-action/ones/twos reduction, a joint
Gaussian–Poisson approximation in total variation, a central pointwise local
limit theorem, a three-level perturbation law, a multiplicative positive-axis
Borel-growth equivalent, and a least-term equivalent. Nine further research
topics and a staged formalization route are included.

The specific target is the subsection “Beyond logarithmic coefficient
asymptotics” in ProveIt's Exponential_Feedback_Regularity_Classification/article.tex.
The inspected snapshot and all source references are recorded in PROVENANCE.json
and in the article bibliography.

## Contents

- `article.tex`: self-contained LaTeX source, including bibliography.
- `article.pdf`: compiled A4 article.
- `code/verify.py`: exact integer recurrence, independent rational partition
  checks, and numerical asymptotic diagnostics.
- `data/coefficients.csv`: exact coefficients through degree 256 for four models.
- `data/diagnostics.json`: asymptotic ratios and exact-weight probability diagnostics.
- `data/asymptotic_ratios.csv`: numerical ratios in tabular form.
- `data/finite_perturbations.json`: normalized finite-perturbation comparisons.
- `data/verification.json`: executed check report and environment information.
- `requirements.txt`: the numerical diagnostic dependency.
- `build.sh`: three-pass PDF rebuild script.
- `PROVENANCE.json`: repository snapshot, source paths, scope and limitations.
- `BUILD_REPORT.json`: final document build and inspection report.

## Reproduce

Use Python 3.10 or newer and a standard TeX Live installation.

```sh
python -m pip install -r requirements.txt
python code/verify.py --order 256 --check-order 18
sh build.sh
```

The verification script takes no network actions. The exact recurrence and
partition comparisons use Python integers and `fractions.Fraction`. mpmath is
used only for logarithms, the scalar saddle root, and displayed numerical ratios.
The LaTeX source needs no external image or bibliography file. The build script
places intermediate files in `build/` and copies the resulting PDF to `article.pdf`.

## Verification and limits

All 72 independent exact comparisons passed: degrees 1–18 for each of four
models (quadratic slopes; lambda_1=0; lambda_1=3; lambda_2=7). Exact coefficients
were computed through degree 256 for every model. The main diagnostic table also
computes the exact mass of configurations with one part at least 3 and all other
parts equal to 1 or 2.

The finite-order approach to the asymptotic equivalent is slow. For the
quadratic model at n=256, the exact coefficient divided by its leading equivalent
is about 1.38404, not a value artificially close to one. The article states
precisely what the finite checks do and do not establish.

The proofs are conventional mathematical proofs, not Lean-verified proofs.
No claim of certified global novelty or publication priority is made. The
Borel theorem concerns the positive real axis; it does not prove negative-ray
summability. The least-term theorem is not an analytic remainder estimate.
The computations are not directed interval arithmetic or a substitute for the
asymptotic proofs. Independent mathematical review remains appropriate.

No files or branches in the ProveIt repository were modified.

## Editorial amendments (ProveIt, 2026-09-29)

The package was filed in batch 48 (see `docs/incoming/README.md`). The
following changes were made after filing; everything else is as delivered.

- `article.tex`: an unnumbered "Editorial note (ProveIt, 2026-09-29)"
  environment was added to the preamble. An editorial note after the abstract
  records that "We resolve that question" is stale in the repository: the
  finite-core package (`Finite_Core_Universality_Exponential_Feedback/`, filed
  in batch 47, before this package and not cited by it) proves the same
  coefficient theorem for eventually exact `j^2` as the `p = 2`, `a = 1` case
  of its first-correction formula, with the same variance and least-term
  index; the two are independent proofs of one theorem with agreeing
  constants, and the note lists what is new here. It also records that this
  article proves the total-variation Poisson law at diverging intensity that
  the Poisson-layer package lists as open. Editorial notes after four
  further-research questions name the later packages that answer them and how
  far: the cloud hierarchy (partly, the finite-core and Poisson-layer
  packages), compositional inverses (the weighted-type package for the type;
  the two batch-49 quadratic-inverse packages, unreviewed, for the
  coefficients), angular growth and negative-direction summation (fine sense:
  the negative-ray package; angular sense, negatively: the natural-boundaries
  package) and the actual sectorial remainder (the sectorial-summability
  package; the comparison with the least term stays open). The tagged display
  (Q) became an `equation*`, which removes a duplicate hyperref destination
  (`equation.2.2`) without changing any label, tag or number. A bibliography
  entry `ed:finitecore` cites the finite-core package. Every change is
  marked in the source by a `% ed. (2026-09-29)` comment.
- `article.pdf`: rebuilt from the amended source (24 pages; the delivered PDF
  had 22).
- `BUILD_REPORT.json`: the three SHA-256 digests (`article.tex`,
  `article.pdf`, `code/verify.py`), the page count, the source line count, the
  engine and the pass count were recomputed for the amended files, and a note
  says so; the rendering statement describes the delivered build. Rebuilding
  with `build.sh` overwrites `article.pdf` and makes the recorded PDF digest
  stale again.
- `code/verify.py`: the CSV and JSON writers emit LF line endings on every
  platform. A rerun on a copy (`--order 256 --check-order 18`) reproduced
  `data/coefficients.csv`, `data/asymptotic_ratios.csv`,
  `data/diagnostics.json` and `data/finite_perturbations.json` byte for byte;
  `data/verification.json` differed only in `elapsed_seconds`. The program
  rewrites the recorded `data/` files in place; run it on a copy.
