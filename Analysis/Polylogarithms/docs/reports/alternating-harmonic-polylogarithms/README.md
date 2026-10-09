# Reflection, certified evaluation, and a depth–exponent transition

**A research continuation for ProveIt / Analysis / Polylogarithms**  
Prepared for Vladimir Reshetnikov with OpenAI assistance, October 7, 2026.

The article is `article/reflection_envelopes_depth_transition.pdf`; its complete
LaTeX source is alongside it. The manuscript contains proofs, a targeted audit
of the existing Gaussian/Eisenstein drafts, a sampled Stieltjes-rank discussion,
and six directions for further research. The original repository is unchanged.

## Main results

For the elementary harmonic symmetric functions

`e_r(n) = [u^r] product_{j=1}^n (1+u/j)`,

study `T_(p,r)(a) = sum_n (-1)^n e_r(n)/(n+a)^p` and the Gaussian specialization
`S_(p,r) = 2^(-p) T_(p,r)(1/2)`. The manuscript proves:

- An incomplete-beta reflection identity and a finite triangular reduction
  for every harmonic index, with explicit gamma-coefficient recurrences.
- An all-weight formula for the draft's `S_(2m+1,1)`, replacing finite numerical
  evidence by an analytic proof.
- Signed first-omitted-term bounds for every truncation, even before summand
  magnitudes become decreasing, and exact Taylor radii after pole stripping.
- A uniform joint asymptotic at `p/r = log r + c`, with profile
  `exp(-exp(-c)/2)`, an explicit first correction, and a proved all-orders
  polynomial construction. A separate theorem covers fixed p and growing r.
- A geometrically convergent evaluator with an explicit rational error bound
  in the Gaussian case, implemented using exact rational interval arithmetic.

The transition concerns the *harmonic index / displayed nesting length*;
it is not a theorem about minimal motivic or numerical depth. General
polylogarithm parity reductions are established in the literature cited in
the article. Priority for these normalization-specific formulas and
asymptotic results is not asserted.

## Contents

| Path | Purpose |
| --- | --- |
| `article/*.tex`, `article/*.pdf` | Full research article, proofs and references |
| `corrections/PROPOSED_CORRECTIONS.md` | Seven precise correction proposals |
| `corrections/replacement_parity_statement.tex` | Editorial insertion with uniform theorem and proof |
| `corrections/apply_goncharov_fix.py` | Hash-guarded preview/apply script for one integral-order typo |
| `code/polylog_research.py` | Exact certificates and main numerical cross-checks |
| `code/transition_polynomials.py` | Exact symbolic coefficients through order four |
| `code/additional_diagnostics.py` | Second-order and fixed-exponent diagnostics |
| `code/test_core.py` | Fast exact-arithmetic and patch-transform regression tests |
| `results/` | Retained outputs, including full rational interval endpoints |
| `provenance/` | Source manifest, environment and build/test status |
| `SHA256SUMS` | Checksums of packaged files, excluding the checksum file itself |

## Reproduce

Python 3.10 or later is recommended. The tested versions are pinned in
`requirements.txt`; `mpmath` is needed for the main script, and `sympy` for
the symbolic compiler. TeX Live with `latexmk` and the packages declared by
the article is needed only to rebuild the PDF.

```sh
python -m pip install -r requirements.txt
make test
make verify
make polynomials
make diagnostics
make pdf
```

The equivalent commands are:

```sh
python code/test_core.py
python code/polylog_research.py --full
python code/transition_polynomials.py
python code/additional_diagnostics.py
cd article
latexmk -pdf -interaction=nonstopmode -halt-on-error \
  reflection_envelopes_depth_transition.tex
```

The scripts use no network access. `make verify` and the other generators
replace their files under `results/`; retain the original files separately
when comparing environments. `make clean` removes only LaTeX auxiliary files
and Python bytecode, not the PDF or recorded results.

## Verification and limits

The main retained run completed 156 exact or numerical consistency checks
and recorded 12 transition diagnostics. Eight constants have **exact rational
interval certificates**, with widths between approximately 2.90e-56 and
2.97e-53. Their full endpoints are in `results/certified_intervals.json`.
The decimal quadrature fields in that file are independent checks, not the
source of certification. The additional script checks 15 asymptotic cases,
and the fast regression suite has seven test methods.

The interval construction uses rational arithmetic, rigorous bounds on log 2
and inverse sqrt 2, and the analytic Cauchy tail theorem. The other quadrature
and asymptotic computations are not interval-certified. Agreement of
numerical values or overlapping intervals is not treated as a proof of an
identity. Universal results rest on the written mathematical proofs. No Lean
or Wolfram execution was performed, and independent mathematical review is
still appropriate before adopting the draft as a final publication.

## Proposed corrections

The most important findings are an incompatible simplex order in the
Goncharov definition, unconditional depth lower bounds inferred from
non-detection by PSLQ, and an unsupported move from ambient motivic dimensions
to minimal depth of particular numerical values. The positive Gaussian
reductions are retained and proved uniformly. The detailed audit carefully
separates incorrect inferences, a localized typesetting error, and statements
whose supplied evidence is only finite computational evidence.

The correction script defaults to a diff preview. It accepts only the exact
reviewed blob, creates a backup before writing, and never makes Git commits.
It was tested on synthetic fixtures, not applied to the original source.

## Integration

A self-contained destination is:

`Analysis/Polylogarithms/docs/articles/reflection-envelopes-depth-transition/`

Copy this directory there; the relative paths and build commands then remain
valid. Alternatively place the article in the existing flat articles folder
and keep this companion package in a clearly linked support directory.
Review `corrections/PROPOSED_CORRECTIONS.md` before editing the historical
articles. Do not automatically replace entire drafts or erase their numerical
provenance. No material has been pushed to GitHub by this package.
