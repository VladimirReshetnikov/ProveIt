# Uniform q-Multinomial Transseries and Certified Inversion

Research draft prepared on 29 September 2026 in response to the request to develop substantial transseries results connected with the ProveIt repository.

## Main result

For a fixed positive ray a=(a_1,...,a_r), r>=2, A=sum(a_j), a_*=min(a_j), the paper constructs a normalized expansion for the logarithm of the Gaussian multinomial interpolation, including its gamma-quotient endpoint at q=1. Write q=exp(h), h>=0. If T_K is the specified core plus K Bernoulli corrections, the exact remainder R_K=F_h-T_K has sign (-1)^(K+1) and satisfies

    0 < (-1)^(K+1) R_K(h,x)
      < magnitude of the first omitted term
      <= |B_(2K+2)|/(2K+2) * x^(-2K-1) * sum_j a_j^(-2K-1).

The bound holds for EVERY h>=0 and x>0, with no positive lower bound on hx. It closes the explicitly recorded endpoint-uniformity gap in the inspected companion volume.

With N=2K+1 the nearest odd integer to 2*pi*a_*x, and a_*x>=1, a sharper theorem gives

    |R_K(h,x)| < 2*r*exp(-2*pi*a_*x), uniformly for h>=0.

The paper also proves the exact Borel transform and its nearest poles, a sharp q=1 remainder equivalent with an x^(-1/2) prefactor, a fixed-h resonance equivalent that rules out ANY prefactor tending to zero in an all-h bound, a uniform derivative comparison, and explicit residual-to-inverse enclosures. It includes ten further research directions.

## Files

- `uniform_q_multinomial_transseries.pdf`: complete article.
- `uniform_q_multinomial_transseries.tex`: self-contained LaTeX source.
- `numerical_table.tex`: generated table included by the article.
- `verify.py`: reproducible high-precision checks and reference implementations.
- `verification_results.json`: recorded results, including forward, inverse, endpoint-sharpness and resonance examples.
- `requirements.txt`: numerical dependency.
- `build.sh`: PDF build command.
- `source_provenance.md`: inspected repository snapshot, source labels, and primary literature.

## Reproduce

Python 3.10 or newer:

    python -m pip install -r requirements.txt
    python verify.py

This regenerates the JSON report and LaTeX table. The recorded run used 240 decimal digits and passed 812 forward inequality checks, 24 inverse checks, 36 resonance checks, 48 peak-sensitive moment checks, and additional elementary moment and endpoint-coefficient checks.

Build the paper with a TeX distribution providing pdflatex and the packages listed in its preamble:

    sh build.sh

The build requires no downloaded images or ProveIt-specific style/notation files. A third LaTeX pass is included to settle cross-references and the table of contents.

## Status and limitations

This is an unrefereed mathematical research draft. The results are supported by the explicit proofs in the article, not by an external referee or proof assistant. No Lean verification is claimed. Numerical tests are high-precision consistency checks, not proofs or interval arithmetic. In particular, the printed inverse-enclosure endpoints are NOT outward-rounded machine certificates; validated evaluation of the finite residual and bound remains necessary to produce such a certificate.

The article resolves a specific gap in the inspected repository source. The Bose partial fractions, modular identity, Binet formulas, and general resurgence framework are established mathematics. A targeted primary-literature check was performed; worldwide publication-level novelty and priority are not established. The draft does not claim to settle a named general transseries conjecture or to give a complete global Stokes theory.

No repository files were modified. The package contains no copied repository volumes and no bundled font files.
