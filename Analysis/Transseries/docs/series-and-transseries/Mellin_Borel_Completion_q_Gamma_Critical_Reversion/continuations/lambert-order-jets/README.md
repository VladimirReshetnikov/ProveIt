# Order Derivatives Recover Hidden Polylogarithmic Transseries

**Exact completion, resonance jets, and finite reflection rigidity**  
Research report prepared for Vladimir Reshetnikov / ProveIt, 12 October 2026.

Read `main.pdf` (22 pages). Its editable, self-contained source is `main.tex`.

## Main results

For `F_s(t,a) = sum_{ell>=0} Li_s(exp(-(ell+a)t))`, with a real shift
`0<a<1`, the article proves the following.

1. At every positive integer order m, the reflection combination with fixed
   sign `epsilon_m = (-1)^(m+1)` has a finite Laurent polynomial plus an
   **exact convergent dual polylogarithm series** in `Q=exp(-4*pi^2/t)`.
2. Its first derivative in the order has an explicit **double-pole Borel
   transform**. With the article's normalization, its Stokes jump is exactly
   `pi*i` times the hidden exponential remainder of the undifferentiated
   reflection combination. The derivative's exact linear-median and lateral
   completions include a separate logarithmically weighted dual series.
3. For arbitrary finite real atomic shift sets, termination of the ordinary
   tail is equivalent to the appropriate reflection parity. A finite
   Fourier–Möbius/Vandermonde certificate detects that condition. A nonzero
   admissible r-atom measure has a hidden action among the first r actions;
   midpoint grids attain the bound for odd m.
4. On all finite complex shift measures, the joint kernel of the ordinary
   and first-order-derivative tail coefficient maps is precisely the span of
   Lebesgue measure. On finite atomic measures, the pair is injective.
5. Every order of the local resonance collision has an explicit coefficient
   formula. Reflection cancels the explicit Stieltjes contribution and
   lowers the logarithmic degree by one.

The real-t identities continue to the right half-plane with the specified
logarithm and lateral conventions. The real-shift Fourier kernels are **not**
claimed to work for nonreal shifts.

## Evidence and status

The article contains conventional proofs. No result is claimed to be
proof-assistant formalized or independently refereed. The delivered runs
record **732 passing exact symbolic/arithmetic assertions** and **61 passing
floating-point diagnostics**. The numerical checks are not interval
certificates. Their domains, working precisions, thresholds, and the exact
scope of the symbolic tests are recorded separately.

The existence of scalar Lambert-series hidden sectors is earlier work of
Dorigoni–Kleinschmidt. The m=1 shifted q-product completion and a rational
Fourier–Möbius argument overlap existing ProveIt work, credited in the
article. The all-order first-jet completion and finite rigidity statements
are developed here; first-priority in the entire literature is not asserted.
This report does not claim to settle the separate S6/S8 conjectures.

## Contents

- `main.tex`, `main.pdf`: article and compiled reading artifact.
- `verification/verify.py`: exact checks and high-precision diagnostics.
- `verification/exact_results.json`: recorded exact run.
- `verification/numerical_results.json`: recorded numerical run.
- `notes/SOURCE_AUDIT.md`: reviewed source ranges, overlap, and limitations.
- `notes/CROSS_REFERENCE_CORRECTION.md`: one confirmed documentary correction.
- `notes/PROOF_REVIEW.md`: normalization, endpoint, and finite-part checks.
- `notes/INTEGRATION.md`: proposed repository placement and catalog text.
- `notes/BUILD_REVIEW.json`: PDF build and visual-inspection record.
- `provenance.json`: source pin and evidence scopes.
- `requirements.txt`, `Makefile`: replay and PDF-build instructions.

## Reproduce

Install the two pinned Python dependencies in an environment of your choice:

```sh
python -m pip install -r requirements.txt
python verification/verify.py --mode exact --output verification/exact_results.json
python verification/verify.py --mode numerical --output verification/numerical_results.json
make pdf
```

`make pdf` requires pdfLaTeX and ordinary TeX Live packages, and performs three
passes without shell escape. The article uses no external graphics or BibTeX
step. `make verify` reruns the two verification modes separately.
Use a copy when preserving the original recorded outputs matters: the script
replaces its explicitly named output file. A Python replay does not need
network access once dependencies are installed.

## Source and integration boundary

The detailed q-Gamma source comparison is pinned to ProveIt commit
`7bd1ce58abe522b83cd3368bbafa1be97837b75d`. Initial repository indexes were read
on live `main` on 12 October 2026. The incoming archives were inventoried but
not unpacked; this is not an exhaustive repository audit.

Suggested placement:
`Analysis/Transseries/docs/series-and-transseries/Lambert_Polylogarithm_Order_Jets/`,
with a cross-reference from the Polylogarithms program. No repository files
were changed, no archives were uploaded, and no prior source was overwritten.
See `notes/INTEGRATION.md` for proposed catalog wording.

Prepared with ChatGPT assistance for the user's research program. This is an
AI-assisted research draft, not an independent peer-review certificate.
