EXACT MARGINAL CROSSOVER FOR A QUARTIC BOSE GAS
A convergent expansion, rigorous computation, and uniform lattice corrections
Research draft, version 1.0 — 8 October 2026

START HERE

Read article/marginal_bose_crossover.pdf. The complete LaTeX source is
article/marginal_bose_crossover.tex. The article is 22 PDF pages, including
the title page and bibliography. It contains full proofs, not numerical
conjectures inferred from the supplied data.

THE CONCRETE RESEARCH CONTRIBUTION

The target is Section IV.2, equations (22)–(25), of Maciej Łebek and Paweł
Jakubczyk, Physical Review A 102 (2020), 013324; arXiv:2003.07458v3.
Their marginal Bose-gas crossover formula specifies the leading logarithm
and explicitly leaves the next nonlogarithmic coefficient unspecified.

For Psi(u)=integral_R exp(-x^4-u*x^2) dx and
G(s)=sum_{n>=1} Psi(s*sqrt(n))/n, this report determines the complete
convergent expansion, the exact radius sqrt(8*pi), and an explicit error
bound. The constant in the published theta=s^2/8 normalization is pi/2.
It also proves a uniform O(log(1/epsilon)) special-function evaluation
count, a convergent Lambert-W inverse correction expansion, global
conditioning bounds, and an all-orders low-temperature expansion for a
specified finite-range lattice dispersion, uniform in positive stiffness.

This is a precise strengthening of a known result. It is not a claim to
solve a famous open conjecture. The general Mellin-transform method is
classical. The literature comparison is bounded: publication priority
beyond the reviewed sources is not established. The arguments were
developed with ChatGPT and checked in separate analytic, algorithmic, and
lattice audits. They have not undergone external peer review or a
proof-assistant verification.

REPOSITORY INSPIRATION

https://github.com/openai/math
Inspected commit: fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb
Family 271, The first lattice correction to Bloch's law, subsection
"The explicit lattice correction", inspired the heat-kernel organization.
No interacting-spin theorem from that collection is an input to this work.
The exact source path and primary references are in source_manifest.json.

CONTENTS

article/    Complete .tex source and compiled .pdf.
code/       Reference evaluator, certified Arb evaluator, independent
            quadrature, inverse generator, validation scripts, plotting.
tests/      29 reference checks and 13 certified-enclosure checks.
data/       Validation outputs, exact symbolic inverse coefficients,
            figure data, environment information, and an audit record.
figures/    Two vector PDF figures and their PNG previews.
build.py    Portable command wrapper for compiling and optional validation.
requirements.txt
            Exact Python package versions used for this run.
source_manifest.json
            Source attribution, inspected versions, and research roles.
SHA256SUMS.txt
            Integrity hashes of the archive contents (excluding this file).

INSTALLATION

Python 3.12 was used. Install the packages in an environment of your choice:

    python3 -m pip install -r requirements.txt

The PDF build requires XeLaTeX, latexmk, the Latin Modern OpenType text and
math fonts, and standard TeX packages: geometry, fontspec, unicode-math,
amsmath, amsthm, microtype, graphicx, booktabs, longtable, array, enumitem,
xcolor, fancyhdr, lastpage, needspace, and hyperref. These are available in
ordinary TeX Live installations; the tested engine is recorded in
data/environment.json. No network access is used by the supplied scripts.

The PDF and figures are already included; Python is unnecessary if you
only want to read the article or compile the existing LaTeX source.

REBUILD AND VALIDATE

From the extracted package root:

    python3 build.py

This rebuilds the PDF from the existing source and vector figures.
Alternatively:

    cd article
    latexmk -xelatex -interaction=nonstopmode -halt-on-error marginal_bose_crossover.tex

From the package root, run the quick test suite and rebuild figures:

    python3 -m pytest -q
    python3 code/make_figures.py

Optional complete regeneration (the independent quadrature is slower):

    python3 build.py --full-validation

Or run individual scripts:

    python3 code/generate_inverse.py --order 6
    python3 code/validate_algorithm.py
    python3 code/bose_certified.py --validation data/certified_validation.json
    python3 code/validate_temperature.py
    python3 code/validate_independent.py
    python3 code/lattice_validate.py
    python3 code/make_figures.py

Each script resolves its default output location relative to its own path.
The independent integral validator permits --dps, --reference-dps,
--target-digits, and --output. The lattice validator permits --coarse-order,
--fine-order, and --output. Coefficient generation permits --order and
--output. Full numerical regeneration takes minutes on the tested machine;
the 42-test suite took approximately 14 seconds. Timing is descriptive,
not an asymptotic claim or a portable performance guarantee.

EVALUATE A CERTIFIED VALUE

The command-line evaluator applies for every positive stiffness:

    python3 code/bose_certified.py 0.1 --atol 1e-30 --dps 90
    python3 code/bose_certified.py 10 --atol 1e-30 --dps 110

It returns a real ball, its total radius, its analytic-tail contribution,
the representation used, and the working precision. The requested atol
bounds the final radius, including numerical rounding. Failure to meet
the radius at the supplied precision raises an error; it never silently
labels an overwide result as accurate. Decimal or rational strings should
be used as inputs instead of previously rounded binary floating-point
values. The low-level positive_sum_enclosure routine reports its actual
width without promising an accuracy target; use evaluate or
accelerated_enclosure when a prescribed total radius is required.

Python API example, run from the package root:

    import sys
    sys.path.insert(0, 'code')
    from bose_certified import evaluate, critical_temperature_enclosure
    print(evaluate('0.1', '1e-30', 90).as_dict())
    print(critical_temperature_enclosure(
        '0.359500750128335309891857687832384873520295167',
        '0.01', '0.1', density_relative_tolerance='1e-45', dps=120))

The last function uses one certified density evaluation and the proved
global logarithmic-derivative bounds. A poor positive temperature guess
still produces a valid, wider root enclosure. The density tolerance does
not promise that an arbitrary initial guess is close to the root.

REFERENCE API

code/bose_crossover.py exposes:
  evaluate, small_s_expansion, accelerated_positive_sum,
  large_s_expansion, psi, regular_coefficient, normalized_coefficient,
  critical_density, critical_temperature, inverse_parameters,
  inverse_approximation, temperature_bracket_from_density.

Its Approximation objects report analytic truncation bounds evaluated
with mpmath. They explicitly set rounding_certified=False. Their lower
and upper values must not be mistaken for outward-rounded intervals.
The separate Arb implementation supplies that stronger guarantee.

EVIDENCE AND LIMITS

1. All 42 integrated tests passed. The inverse recursion is verified by
   exact symbolic substitution through order six.
2. Mellin enclosures at eight stiffnesses have total radii below 1e-30.
   Independent Bessel/Hurwitz enclosures at s=1,3,4.9 have radii below
   6e-57 and overlap the Mellin balls. Validation checks both width and
   overlap, so an excessively wide interval cannot count as agreement.
3. Seven independent polylogarithm quadratures, including the positive
   convergence boundary, agree within the recorded analytic bounds.
   These quadratures are numerical evidence, not interval certificates.
4. A 115-digit continuum temperature calculation agrees with the Arb
   root enclosure; see data/critical_temperature_crosscheck.json.
5. Lattice quadrature operates on the infrared-subtracted difference.
   Its coarse–fine differences are diagnostics, while its omitted-tail
   bound is analytic. The floating-point evaluation of that bound is
   not itself outward rounded. At zero stiffness the individual
   densities diverge; only their common-cutoff difference is used.
6. The complexity theorem counts special-function evaluations and
   elementary operations at unit cost. It is not a bit-complexity bound.
7. The continuum s-series is convergent; the lattice sqrt(T)-series is
   an all-orders asymptotic expansion. The first lattice terms dominate
   the remaining exponentially small continuum stiffness corrections
   on the fixed-density inverse critical line.

The ten further-research directions are developed in Section 12 of the
article. They include complex singularities, joint coefficient bounds,
higher-order soft directions, nonseparable quartic forms, bit complexity,
certified lattice inversion, finite-size effects, lattice universality,
controlled interactions, and proof-assistant formalization.
