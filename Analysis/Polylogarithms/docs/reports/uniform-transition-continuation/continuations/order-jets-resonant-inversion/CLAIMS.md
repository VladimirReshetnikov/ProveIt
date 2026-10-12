# Claim status and mathematical scope

This ledger accompanies **Polylogarithm Order Jets and Resonant Inversion**.
The inspected ProveIt revision is
`9ec0f0406afe7a5475b03ff65ed91f7e283979b8`. Exact predecessor paths and proposed
integration locations are in [INTEGRATION.md](INTEGRATION.md).

“Proved” below means that the article gives a conventional mathematical proof
under its stated hypotheses. It does not mean Lean-formalized, interval-certified
numerically, or established as new in the world literature.

## Theorem ledger

| Statement | Status and contribution | Essential restrictions |
|---|---|---|
| Uniform complex-sector resonance, `thm:sector` | Proved extension of the predecessor's explicit R1. Pole pairing and its real all-integer-order antecedent are attributed. | A fixed logarithm sheet; `0 < |t| <= t0 < 2 pi`; closed subsectors; compact order-displacement and shift sets; `Re T -> infinity`. The remainder is absolute, including at zeros of the leading profile. |
| Raw order-jet logarithmic polynomials, `prop:rawjet` | Proved coefficient identity from the classical paired expansion. Used as a transparent input, not an independent priority claim. | Fixed finite derivative order; all factorial and Stieltjes signs use the printed convention. |
| Pure logarithmic normal form, `thm:purejet` | Proved finite triangular Gamma transformation: `Y_(p,q,a)(t) = t^p(L^q + t R(t))`, with explicit Hurwitz-zeta derivative coefficients and analytic `R`. | Fixed integers `p,q >= 1`, `Re a > 0`, a specified branch of `L=-Log t`, and `|t| < 2 pi`. A polynomial Taylor subtraction is part of the definition. |
| Local monodromy, `prop:monodromy` | Proved exact polynomial finite-difference law and nilpotence degree `q+1`. | Concerns continuation in the argument around `t=0`; it is not a lateral Borel jump. No finite ramification makes the displayed nonconstant logarithmic polynomial single-valued. |
| Convergent higher-degree inverse chart, `thm:inverse` | Proved equality in two Lambert coordinates and the support `T eta^q`; tail zeros give further powers of `T`. | A sufficiently small positive target and a real analytic tail select the real root. Complex continuation is local on compatible sectors. This is a convergent multivariable chart; no global inverse is asserted. |
| Finite inverse coefficient formula, `thm:coefficients` | Proved all-order finite Lagrange formula; coefficients are rational in `eta`, with possible poles only at `p/q`. | Each fixed coefficient is considered as a rational function. Convergence of the chart near `(T,eta)=(0,0)` is a separate local result. |
| Sharp poles, `thm:sharp-poles` | Proved exact pole order `2n-1` and its nonzero Catalan leading constant. | Requires the first analytic-tail coefficient `r0 != 0`. The auxiliary coefficient pole does not identify the nearest singularity of a globally selected inverse. |
| Exponential critical-point and critical-value chart, `cx:critical-chart` | Proved jointly holomorphic chart in `(epsilon,tau)` with exact algebraic-sector formulas. | Evaluation at `tau=exp(-2 pi i k/epsilon)` requires the printed logarithm-compatibility condition. Independent chart variables are not unrestricted principal-sheet parameters. |
| Principal-sheet critical-value accumulation and local exhaustion, `cx:critical-lattice`, `cx:critical-exhaustion` | Proved infinite sequence of distinct simple critical points and distinct critical values, with an explicit geometric ratio. The sequence exhausts all sufficiently small principal-sheet critical points in this regime. | Fixed sufficiently small `epsilon=i beta`, real nonzero `beta`, and integers with `k beta > 0` sufficiently far along the sequence. The classification is local at the endpoint and does not include unrestricted imaginary order or other sheets. |
| Necessary line for accumulating principal-sheet zeros, `cx:necessary-line` | Proved zero exclusion near the endpoint for fixed `Re s != 1`, and for `s=1`. | A possible accumulating sequence therefore requires `Re s=1` and `s != 1`. This is a necessary condition, not a sufficient classification for every point on that line. Orders are fixed and the logarithm sheet is fixed. |
| Resonant two-root splitting, `cx:split` | Proved convergent square-root/exponential chart and an exact count of two simple roots in the stated local disc. | Fixed nonzero integer resonance `lambda0=2 pi i k`; large real `Y`; target `y=exp(-Y)` and order displacement `epsilon=lambda0/Y`. The count is local near `t=y`. |
| Common chart for exact lattice resonances, `cx:uniform-lattice-splitting` | Proved index-independent holomorphic chart in `sigma=sqrt(epsilon)` and `z=y/epsilon`, recovering the fixed-index chart by substitution. | Physical target `y=exp(-Y)>0`, exact condition `epsilon Y in 2 pi i Z` with nonzero integer, compatible square root, and both chart coordinates sufficiently small. The resonance index may grow only under these explicit conditions. |
| Transverse unfolding and exact fold, `cx:eta-unfolding`, `cx:exact-fold` | Proved analytic critical locus, square-root normal form, and exchange of the two local branches around that locus. | The away-from-fold chart uses a chosen square-root branch on compact parameter sets avoiding the limiting fold. The exact fold theorem supplies a separate local description at the fold. |
| Explicit Borel transform and lateral completion, `thm:borel-exact` | Proved paired Borel series, exact lateral identity, discontinuity, and arithmetic-average identity. Complete Fermi--Dirac asymptotics are established literature and are attributed. | The exact integral theorem is stated for real `x>0`, `Re s>-1`. Boundary values and their signs are fixed. Complex-`x` extensions are not silently inferred. |
| Reconstruction from integer-order jets, `thm:borel-jet-reconstruction` | Proved triangular recovery of the opposite-argument exponential series from order derivatives of the discontinuity. | The analytic family of jets or its discontinuities is supplied. The terminating Borel polynomial at one integer order alone contains insufficient information. |
| Factorial coefficient tails and higher polygamma jets, `prop:borel-factorial-tail` | Proved exact formulas following reflection of a reciprocal-Gamma zero. | The displayed tail formulas require `2k>N>=0`; derivatives are with respect to the order, not the argument. |
| Meromorphic first-order-jet kernel, `thm:borel-meromorphic-jet` | Proved exact lateral/PV representation and pole residues recovering all opposite-argument exponential coefficients. | Integer `N>=0`, real `x>0`; the full prefactor is restored before order differentiation. Pole integrals use contour limits or symmetric principal values, not absolute improper integration on the real ray. |
| Convergent integer-order exponential inverse, `prop:borel-inverse` | Proved specialization of analytic Lagrange inversion with explicit rational sector coefficients and a uniform small-amplitude disk. | Fixed `N>=1`, large positive polynomial-core coordinate. It is not a classification of complex inverse sheets. |

## Established inputs and originality boundaries

The paper explicitly relies on classical Jonquiere/Lerch expansions, Gamma and
Hurwitz-zeta identities, the analytic implicit function theorem, Rouché's
theorem, ordinary Lagrange inversion, Lambert W, Euler products, and standard
Borel/Laplace arguments. The inspected repository already contains the real
uniform resonance theorem, a single-logarithm inverse chart, a real confluent
chart, and analytic inverse transport. Those facts are not claimed anew.

The explicit finite Gamma transformation, the combination with sharp inverse
coefficient poles, the complex resonant branch-splitting and unfolding formulas,
and the order-jet Borel reconstruction are proved contributions of this report
relative to the inspected inputs. Their global publication priority remains
unestablished. A targeted search and a bounded source audit do not certify
worldwide novelty.

No unrelated special-value conjecture is claimed to have been resolved. The
report's strongest directly identified repository-question resolution is the
fixed-sheet complex-sector version of P1's R1. Comparisons with other open
questions are scoped extensions, not declarations that broader research
programmes are complete.

## Confirmed correction and non-corrections

No new confirmed mathematical error was found in the directly used ProveIt
predecessor theorems. In particular, already incorporated P1 corrections must
retain their existing provenance.

During review, this report's own draft was corrected to distinguish an
asymptotically linear inverse from an analytic endpoint inverse. The presence of
a nonzero linear leading term does not remove the later logarithmic singularity.

The external-draft comparison following `cx:necessary-line` has a precise
mathematical basis: on a fixed logarithm sheet,
`|q^(-s)| = |q|^(-Re s) exp(Im s arg q)`; the angular exponential is not an
additional power of `|q|`. The theorem excludes the cited fixed-order,
principal-sheet accumulation claim in the stated off-line regime. It does not
exclude a large finite collection of zeros, a joint large-imaginary-order limit,
or zeros distributed across varying logarithm sheets. The exact external source
attribution belongs to the article bibliography and must be preserved.

There is also a precise correction to an external overview. Section 8.1 of
Cormac O'Sullivan's *Zeros of the dilogarithm*, printed page 18 of the
[author-hosted PDF dated 15 December 2014](https://fsw01.bcc.cuny.edu/cormac.osullivan/Research/dilog_zeros_final.pdf),
states finiteness of principal-branch zeros for general complex orders satisfying
`Re s > 0`. This statement cannot hold on the whole stated range. For every
sufficiently small fixed nonzero real `beta`, the proved critical lattice gives
infinitely many distinct zeros of `Li_(1+i beta)(z)` with `|z|<1`, accumulating at
`z=1`. A safe correction must exclude this blanket inclusion of the line
`Re s=1`; any broader replacement finiteness theorem requires its own precise
hypotheses and proof. The local necessary-line result alone does not prove
global finiteness away from that line.

This corrects the overview as written. Its cited original Gawronski theorem was
not inspected, and this package does not attribute an error to that theorem.
The result for positive real order in O'Sullivan's Theorem 8.1 is unaffected.

## Verification and its limits

`verify_local_jets.py` performs exact symbolic checks for finite index ranges:

- 15 Gamma-conjugation identities for `p=1,2,3` and `q=1,...,5`.
- 60 comparisons of independently computed implicit-recursion and Lagrange
  coefficients for `p=1,2,3`, `q=1,...,4`, and `n=1,...,5`.
- 60 sharp-pole constants, plus 36 explicit first-coefficient and derivative
  identities.

Its numerical reference for the local jets uses directly summed, exponentially
convergent log-weighted defining series, with a recorded monotone tail estimate.
It does not finite-difference an integer-order `mpmath.polylog` evaluation.
Four complex-argument checks and two inverse diagnostics are recorded in
`verification_local_jets.json` at 85 decimal digits. These are useful independent
computational checks. Floating-point rounding is not enclosed by intervals, and
the values do not establish any infinite-index or analytic-continuation theorem.

Other supplied verification files record their own precision, index ranges, and
reference formulas. Their counts should be reported from the actual packaged
results, rather than inferred from this local-jet subset. No test count should
be described as a formal proof of the whole paper.

`verify_principal_sheet.py` provides a separate branch diagnostic, recorded in
`principal_sheet_check.json`. For `s=1+0.2 i` and lattice index `k=1`, it locates
the root using eleven terms of the convergent paired tail, then independently
evaluates

`Gamma(s)^(-1) integral_R exp(s v) / (exp(exp(v)+t)-1) dv`.

This is the defining Bose integral after the real substitution `v=log(u)`;
`Re t>0` ensures `|exp(-t)|<1`. At 90 decimal digits the computed integral
residual is about `2.03e-90`. The integral is truncated to `[-300,8]`, with
analytic absolute bounds

- Left tail: `exp(-300)/(Re(t) |Gamma(s)|) < 2.35e-117`.
- Right tail:
  `exp(-exp(8))/((1-exp(-exp(8))) |Gamma(s)|) < 10^(-1294.59)`.

These are cutoff bounds, not bounds on quadrature rounding. The quadrature is
not interval-certified, and its residual is not a formal zero certificate.
The root-construction series and the integral reference are different
representations; no integer-order finite-difference derivative is used.

## Questions intentionally left open

- Uniformly growing derivative order and general expanding resonance windows.
- Unrestricted winding or passage through the nearest argument singularities
  at `t=+/-2 pi i`.
- Classification of critical points for larger imaginary order, on other
  logarithm sheets, or globally away from the endpoint; the sufficiently small
  fixed purely imaginary regime is classified locally by the exhaustion result.
- Principal-sheet accumulation at every fixed order on `Re s=1`.
- Quantitatively certified polydisks for all analytic charts.
- Complex-`x` Borel domains with explicit branch bookkeeping beyond the printed
  real-positive theorem.
- General shifted or cyclotomic order-jet Borel kernels and their nonlinear
  inverse transport.
- Global publication priority and Lean formalization.

