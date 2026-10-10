# Sharp Euler Bounds, Golden Ladders, and Double Radial Turning Points

Research continuation prepared for Vladimir Reshetnikov, 10 October 2026.

The article continues **Polylogarithms and their Arithmetic Bridges** in
`VladimirReshetnikov/ProveIt`, at the pinned baseline commit
`3447bc59b78d138a7f0d536b66ac6e5cc5d5e49f`.

The source manuscript is at
`Analysis/Polylogarithms/docs/manuscript`. This is a self-contained
contribution for review and integration; the source repository has not
been modified remotely.

## Main results

1. **Sharp universal real-order Euler bound.** For every positive real
   pair `(a,b)`, the Euler sums converge absolutely and decrease to the
   principal Gaussian value. For every `N >= 2`, the error is strictly
   less than `(9/8) 2^(-N)`. The optimal constant valid for all `N >= 1`
   is exactly `max_b [beta(b) + 2^(-b) eta(b)]`. The baseline's axis
   maximum theorem is a credited prerequisite; the all-tail uniform
   kernel bound is proved here.

2. **Two remaining golden weight-five evaluations.** Complete exact
   rational-function tensor certificates prove the displayed index-20
   and third golden formulas. A written derivative, endpoint, and
   triangular-descent argument gives all companions at weights 1–5.
   The article prints six reduced lower-weight identities, two
   open-interval functional identities, and the complete coefficient
   tables. The already proved first ladder is credited and replayed
   with a 12-row normalization certificate.

3. **Certified double radial turning.** A rational interval certificate
   proves local uniqueness of a simultaneous zero of the quadratic and
   quartic radial coefficients. Its negative sextic coefficient and
   nonzero parameter Jacobian yield a local region with a minimum
   followed by a maximum, an exact local fold classification, and
   square-root and fourth-root radius laws.

4. **Constructive full Cayley quotient.** An explicit all-weight
   projector has kernel exactly the ideal of convergent Cayley
   relations and all their shuffle multiples. A separating-coordinate
   theorem gives `-166348800` for the frozen S6 target, proving its
   nonmembership in that full ideal. This does not prove or disprove
   the numerical S6 identity. The complete projected imaginary normal
   form contains 3,444 nonzero rational coordinates.

The novelty claims are relative to the audited manuscript and identified
prior continuations. They are not assertions of worldwide priority.

## Read and rebuild

- `article.pdf`: complete article.
- `article.tex`, `sections/`, `references.tex`: complete LaTeX sources.
- `integration/INTEGRATION.md`: proposed source insertions, replacement
  prose, label mapping, and retained open questions.

Build from the extracted package directory with a standard TeX Live
installation including `latexmk`, `lmodern`, `cleveref`, and `xurl`:

```bash
latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex
```

The supplied figures are already included, so rebuilding the PDF does
not require Python.

## Replay the certificates

Python 3.10 or later is required. The delivered replay was run with the
versions recorded in `verification/replay_summary.json`.

```bash
python3 -m pip install -r requirements.txt
python3 code/run_all.py
```

Each script can also be run individually, from any working directory.

| Script | Exact premises checked | Output |
| --- | --- | --- |
| `code/certify_euler_bound.py` | Three polynomial identities; 462 positive rational Bernstein coefficients; exact axis lower witness | `data/euler_polynomial_certificate.json` |
| `code/review_euler_certificate.py` | Independent symbolic reconstruction, every Bernstein coefficient, disjoint interiors and full partition volume | `data/euler_independent_review.json` |
| `code/certify_double_turning.py` | Outward rational interval arithmetic, logarithm and exponential remainders, transition box, Jacobian and sextic signs | `data/double_turning_certificate.json` |
| `code/certify_golden_ladders.py` | Full tensor identities at weights 2–5, rational prime factors, golden specialization, endpoint constants, elementary algebraic factorizations | `data/golden_certificate_verification.json` |
| `code/verify_cayley_projection.py` | Projector identities on 780 words and 2,150 product pairs; independent Eulerian implementations; separator through weight seven; full frozen target | `data/cayley_projection_verification.json`, `data/cayley_s6_normal_form.json` |

`data/golden_rational_certificates.json` contains the complete golden
input rows. The proof does not require rerunning an integer-relation
search or trusting a numerical cancellation. SymPy factors all rational
functions afresh during replay; rational contents are retained.

The Euler producer and the radial certificate use only Python's
standard library. SymPy is needed for the golden replay and independent
Euler review; mpmath is used only for separate golden diagnostics.
The Cayley arithmetic is exact rational arithmetic.

To regenerate the illustrative figures as well:

```bash
python3 code/run_all.py --figures
```

The axis plot is a numerical diagnostic. The radial plot is the
proved limiting local model, explicitly labeled as such; it does not
represent a certified finite-radius computation. Their numerical
parameters are in `data/figure_diagnostics.json`.

## Proof status and limitations

The complete analytic and algebraic proofs are in the article. Finite
computational premises are exposed by the exact data and scripts;
independent mathematical reviews are included under `verification/`
and `integration/`. These are not proof-assistant formalizations.

The following remain open in this contribution:

- The golden weight-6 through weight-9 reconstructions.
- The numerical S6 and S8 conjectures.
- Global uniqueness of the quartic transition and the full-disk
  count of radial turning points.
- An explicit effective size for the local double-turning neighborhood.
- The optimal universal constant restricted to later Euler steps.
- Arithmetic independence of periods, and completeness beyond the
  explicitly stated formal relation algebras or finite alphabets.

No false displayed baseline formula was established in this audit.
The integration changes chiefly promote proved statements and clarify
their exact scope. The article proposes twelve concrete further
research directions, with suggested proof and computation routes.
