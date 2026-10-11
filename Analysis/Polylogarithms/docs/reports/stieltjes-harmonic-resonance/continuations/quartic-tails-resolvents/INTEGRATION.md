# Proposed ProveIt integration

Baseline: `7bd45777a8a127e5dc69aff8887ca36a79a3059d` (`New research reports`, 2026-10-11 01:57:13 UTC).

This is a self-contained continuation. The proposed changes below are reviewable integration guidance; no repository patch was applied. Retain the canonical source's notation conventions when extracting individual sections.

## 1. Contribution placement

Preserve the delivered ZIP in `docs/incoming` under its supplied name, or unpack it into an appropriately named continuation directory under `Analysis/Polylogarithms/docs/reports`. The single-file TeX version and PDF can be preserved as the immutable report snapshot. The modular sources are supplied for editorial integration.

Suggested report slug: `quartic-tails-complex-resolvents`.

The core modules are:

| Module | Mathematical contents | Main labels |
|---|---|---|
| `sections/quartic_bridge.tex` | Quartic finite part, strict depth-three bridge, convergent arithmetic kernel, normalized primitive, all derivatives | `q4:main`, `q4:ML`, `q4:primitive`, `q4:derivatives` |
| `sections/mixed_even_tails.tex` | Every even pair and moment; finite Bernoulli blocks; fixed arithmetic span; `(2,4)` eliminations | `tail:ordinary`, `tail:all-moments`, `tail:fixed-space`, `tail:rational-polygamma` |
| `sections/mixed_even_tail_generators.tex` | General analytic EGF and explicit `Li_2`–`Li_6` example | `tail:generator`, `tail:24-Li-body` |
| `sections/complex_powers.tex` | Branch, Euler–polylog transform, Hurwitz transform, all resonant completions, logarithmic moments, parameter primitives | `power:eulerthm`, `power:hurwitzthm`, `power:completion`, `power:logcor`, `power:normalizedprimitive` |
| `sections/moments.tex` | Gamma–Gauss ordinary generator, digamma–Lerch first moment, generalized-harmonic Bernoulli moments | `moment:thm:exponential`, `moment:cor:first`, `moment:thm:bernoulli` |
| `sections/contact_verification.tex` | Independent all-integer residue proof of the finite negative-power contact | `contact:residue`, `contact:identity` |

The remaining sections contain conventions, audit, research questions, and numerical reproducibility. The two tail sections are intended to stay together: the finite formula feeds the analytic EGF. The complex-power and ordinary-moment sections share the same branch and half-plane coordinates.

## 2. Exact status updates

### Cubic harmonic report: Question 6

Source archive:
`docs/incoming/ProveIt_Cubic_Harmonic_Mixed_Orders_2026-10-11.zip`

Internal source:
`ProveIt_Cubic_Harmonic_Mixed_Orders_2026-10-11/sections/07_audit_research.tex`

Paragraph: “6. Obtain a general power-to-harmonic formula.”

Proposed update:

> The explicitly requested quartic case is proved in the quartic/tails/complex-resolvents continuation. The coordinate finite part of the digamma fourth power is reduced with all finite corrections to the linear Laurent coefficient of `Z_3(1+u,1,1)`, the inherited `Z_2` coefficient, and ordinary zeta/Stieltjes terms. A combination with the cubic moment removes the depth-two coefficient. The general all-power reduction and a further arithmetic reduction of the depth-three coefficient remain open.

Preserve attribution to the cubic report's contour and harmonic reduction strategy. The new quartic calculation is distinct from fourth Tornheim ray derivatives.

### Harmonic-parity report: R1

Source archive:
`docs/incoming/ProveIt_Harmonic_Parity_and_Resolvent_Identities_2026-10-11.zip`

Internal source:
`ProveIt_Harmonic_Parity_and_Resolvent_Identities_2026-10-11/sections/07_research.tex`

Paragraph: “R1. Evaluate mixed even-tail moments in a controlled algebra.”

Proposed update:

> The pure two-even-tail family is now evaluated for every even pair and every nonpositive even spectral argument by a finite Bernoulli formula. The values lie in a fixed ordinary-zeta span independent of the moment order and have a convergent classical-polylogarithm generator. The requested first mixed pair `(2,4)` is explicit and is generated rationally by its first four moments. The additional factors involving powers of `H_n` and odd-order harmonic numbers remain open.

Do not mark all of R1 solved: its embellished harmonic products are broader than this result.

### Harmonic-parity report: R4

Same archive and internal source as R1.

Paragraph: “R4. Complex powers with moving endpoint exponents.”

Proposed update:

> The branch-consistent complex-power Hurwitz transform and joint Stieltjes completion are proved for every nonreal resolvent parameter. Full moving amplitudes are removed before coefficient extraction; at negative integer powers the smooth two-endpoint term is removable but nonzero. The formulas include arbitrary logarithmic powers, exact parameter derivatives, and normalized primitives. Away from integer powers the pole-removed transform directly gives the generalized coordinate finite part.

The requested one-resolvent extension is resolved. Products of distinct resolvents and nonlinear products of continuous polygamma orders are separate later questions.

### Higher-reflection report

Source archive:
`docs/incoming/ProveIt_Higher_Reflection_Identities_2026-10-11.zip`

Internal source:
`ProveIt_Higher_Reflection_Identities_2026-10-11/sections/06_audit_research.tex`

Topic: “Centered products beyond a trigamma square.”

Add a cross-reference for the all-pair two-tail theorem and EGF. Preserve the remaining four-tail and spectral-derivative scope.

## 3. Normalization and notation

- `gamma_m(x)` uses the standard Laurent expansion with `(-1)^m/m!` at `s=1`; therefore `gamma_0(x)=-psi(x)`.
- Strict multiple zeta functions have the largest summation index first.
- `eta` and `theta` are coefficients of `u^1` in the stated strict Laurent expansions, without a hidden factorial or sign.
- Coordinate finite parts use `x` and `1-x`. They are not defined by taking an arbitrary path to a meromorphic resonance.
- Every removed polynomial in a mixed-tail sum remains inside the summand. The article proves the equivalence with the continued spectral value.
- The resolvent branch is continuous from `Log R_z(x) ~ log x` at zero and approaches argument `epsilon*pi` at the other endpoint.
- Use the regularized Gauss function at third-parameter resonances. The Gamma quotient's Taylor disk and its logarithmic series disk differ when the quotient has a zero.

All article labels use `intro:`, `conv:`, `q4:`, `tail:`, `power:`, `moment:`, `audit:`, `research:`, `repro:`, or `contact:`. Check label collisions if merging modules into a larger existing document. The common macros are `\Li`, `\Log`, `\FP`, and `\dd`; the preamble supplies them.

## 4. Corrections and conjectures

No new false theorem was found in the relevant source material. The new source changes are scoped progress updates and added normalization examples.

The exact boundary counterexample `p=2, u=1, lambda=1` should accompany any future broad statement equating meromorphic continuation with a newly convergent specialized integral. The ordinary specialized integral is `0`; the fixed-power spectral limit is `-1`. This does not refute the incoming theorem within its stated domain.

Do not change the canonical proof status of `S6` or the revised `S8`. The already established complete convergent-Cayley-ideal obstruction plus 5,131 specified extra rows remains a formal relation-space result. The larger 51,244-row double-shuffle calculation was interrupted after 8,500 pivots and is not an exhausted search.

## 5. Reproducibility

Run `python3 build.py` and `python3 run_verification.py` from a copy of the extracted package. The delivered replay passed all four suites. The exact totals and numerical limitations are recorded in the article, README, and JSON outputs. Source archive and manuscript hashes appear in `provenance/source_manifest.json`; deliverable hashes appear in `SHA256SUMS`.

