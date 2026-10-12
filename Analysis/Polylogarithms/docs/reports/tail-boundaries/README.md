# Bilinear Tail Identities, Polylogarithmic Resonances, and Stieltjes Boundary Products

**Research continuation for ProveIt — 11 October 2026**

This bundle contains a complete article, modular and single-file LaTeX sources,
exact arithmetic certificates, independent verification programs, numerical
diagnostics, and proposed repository integration notes.

## Main results

1. **Complete rational two-adjacent-product classification.** For tail
   denominators `P,Q` and nonzero inner colors `alpha,beta`, a nonzero rational
   coefficient pair exists exactly when `t^2 alpha beta=1` and
   `P(z)/Q(z)=rho h(z)h(z+1)` with `h` rational. A finite divisor criterion
   constructs `h` or proves nonexistence within this certificate class.
2. **Two independently shifted Nielsen-beta kernels.** The article evaluates
   both ordinary and alternating outer sums, gives all mixed polygamma
   derivatives, identifies an exact rank-two kernel, and integrates it to an
   anchored Gamma–Hurwitz summation law with its finite upper endpoint.
3. **Complex-order Mellin/polylogarithm identities.** A paired Lerch expression
   and an entire neighboring-order polylogarithm combination give finite
   factored operators at every integer Mellin resonance. The article includes
   all logarithmic moments, mixed derivatives, generalized Stieltjes
   differences, scaled evaluations, and ordinary integrals isolating a single
   Stieltjes constant at every index.
4. **The missing quadratic Stieltjes derivative edge.** Every fixed-coordinate
   finite part with one undifferentiated Stieltjes factor and one positive
   argument derivative has a terminating ordinary-zeta formula. Together with
   the inherited positive-positive theorem, a uniform coefficient dictionary
   covers every positive total argument-derivative order. An explicit endpoint
   law handles integration by parts at all indices.
5. **Complete reconstruction at smaller orders ten and twelve.** The first-q
   formal moment prefix has full rank for every even `q>10` when `p=10`, and
   every even `q>12` when `p=12`. One five-by-five finite-field certificate
   finishes order ten. A written analytic threshold and all 11,513 remaining
   exact finite cases finish order twelve. Two different complete algorithms
   reproduce the order-twelve residue list.

The article distinguishes new completions relative to the inspected corpus
from inherited reductions and classical identities. It does not assert an
exhaustive worldwide priority search, arithmetic independence of periods,
proof-assistant formalization, or interval-certified quadrature. The general
unequal-order conjecture and the entire fixed-gap-six family remain open.

## Files

| Path | Purpose |
|---|---|
| `Tail_Kernels_and_Boundary_Products.pdf` | Complete article, including proofs, exact examples, source reconciliation, and research questions |
| `Tail_Kernels_and_Boundary_Products.tex` | Self-contained LaTeX source; no external bibliography or figures required |
| `article.tex`, `preamble.tex`, `references.tex`, `sections/` | Modular source for editing and repository integration |
| `build.py` | Regenerates the single-file source from the modular source and builds the PDF |
| `verify_all.py` | Runs all exact certificates and routine numerical diagnostics |
| `verification/kernels/` | Rational tail algebra, divisor test, shifted kernels, primitives, and numerical records |
| `verification/mellin/` | Exact Mellin-operator tests, direct quadratures, and numerical audit |
| `verification/stieltjes/` | Finite coefficient algorithm, endpoint tests, and independent finite-part quadratures |
| `verification/tails/` | Complete order-ten and order-twelve certificates, independent replays, and inherited proof inputs |
| `integration/INTEGRATION.md` | Proposed landing locations and exact research-status changes |
| `provenance/sources.json` | Pinned source paths, target locations, and primary literature |
| `provenance/stieltjes_source.json` | Precise earlier archive containing the missing-edge question |
| `CLAIM_STATUS.json` | Machine-readable claim scope, status, proof labels, and evidence |
| `verification/visual_review.md` | Final PDF layout inspection record |

## Rebuild the article

A standard LaTeX installation with `pdflatex` is sufficient; `latexmk` is used
when available. Packages include the AMS packages, Latin Modern, `mathrsfs`,
`geometry`, `microtype`, `booktabs`, `longtable`, `enumitem`, `hyperref`, and
`fancyhdr`.

```sh
python build.py
```

Alternatively, compile `Tail_Kernels_and_Boundary_Products.tex` directly with
`pdflatex`, repeating enough times to resolve its contents and cross-references.
The single-file source is generated: edit the modular source and rerun the
build script to keep both versions synchronized.

## Replay the verification

The recorded Python environment used Python 3.12.14, SymPy 1.14.0, and
mpmath 1.3.0. The two libraries are specified in `requirements.txt`.

```sh
python -m pip install -r requirements.txt
python verify_all.py
```

The default command runs every exact certificate, including the complete
independent order-twelve replay, and the routine kernel/Mellin quadratures.
The more expensive option also recomputes the Stieltjes quadratures and builds
the independent C++17 verifier in a temporary directory:

```sh
python verify_all.py --full
```

The complete C++ scan and the Stieltjes numerical suite were run successfully
when preparing this bundle; their actual JSON outputs are included. The
top-level default command was also run successfully from the assembled bundle.
No network access is needed to replay the supplied mathematical certificates
after installing the declared software.

The exact evidence includes 2,002 Mellin checks, 81 Stieltjes endpoint checks,
144 rational bilinear cutoffs, 72 shifted-kernel cutoffs, 3,125 divisor strings,
and all 11,513 required order-twelve determinants. These finite implementation
checks supplement the written all-parameter proofs. Numerical diagnostics are
recorded separately. A failed exploratory numerical differentiation method
is disclosed in `verification/mellin/NUMERICAL_AUDIT.md` and is excluded from
the successful quadrature claims.

## Source state and integration

The primary source snapshot is ProveIt commit
`da2792fc9cc8ef19c6a314be6c65e1437fbdc66b` (11 October 2026, 21:44:07 UTC).
The current manuscript and all five incoming archives were indexed and
examined for the relevant statements. An earlier archive is separately pinned
for the original Stieltjes question. Exact inherited proof and certificate
inputs needed by the reconstruction argument are preserved with attribution
under `verification/tails/provenance_inputs/`.

The proposed initial landing is the intact ZIP under `docs/incoming/`.
The integration note then maps the mathematical sections to proposed manuscript
chapters and identifies only the conjecture-status entries that should change.
This bundle does not modify the repository.
