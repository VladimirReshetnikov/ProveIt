# Proposed ProveIt integration

This package supplies a standalone research continuation, its complete proofs,
replayable verification artifacts, a claim ledger, and a separate minimal source
correction patch. The baseline is ProveIt commit
[`e0d9463bdee9685dfb1dddb819059cc738540c57`](https://github.com/VladimirReshetnikov/ProveIt/tree/e0d9463bdee9685dfb1dddb819059cc738540c57).
No upstream repository changes were made. The placement and crosslinks below
are proposals for maintainer integration.

## Recommended placement

Place the standalone package under:

```
Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/twisted-harmonic-laurent/
```

The principal entry points are
[polylogarithms_finite_parts.tex](../polylogarithms_finite_parts.tex) and
[polylogarithms_finite_parts.pdf](../polylogarithms_finite_parts.pdf).
Preserve the relative `sections/`, `code/`, `data/`, `verification/`, and
`integration/` directories, together with the bibliography, build files, and
README. The supplied [README](../README.md) documents building and replay.
[article_standalone.tex](../article_standalone.tex) provides the flattened TeX
alternative; it is generated from the modular source and should not become a
second independently edited master.

This report location follows the explicitly open twist question in the existing
convolution-algebra continuation. The harmonic Laurent results also merit a
crosslink from the depth chapter; they need not be separated from the report to
make that connection.

## What should be recorded as new, established, or open

The machine-readable [claim ledger](claim_ledger.json) is the authoritative
mapping of article labels, proof status, source comparison, and qualifications.
Its status `established_here_source_addition` means that this package supplies
a proof and adds the stated formulation to the inspected source set. It does
not assert exhaustive global priority. `consolidated_existing` includes
classical results, already proved repository results, and the separately
identified prior rejection of an older conjectural vector.

| Material | Article labels | Integration status |
|---|---|---|
| Nonintegral Lerch finite parts and all-index multiplication | `tw:thm:family`, `tw:prop:cutoff`, `tw:thm:normalform` | Proved source addition; answers the explicitly open singular half-twist normalization target and extends it to every real nonintegral twist |
| Every covariant derivative contact term | `tw:thm:contacts` | Proved source addition; includes all ordinary delta derivatives contained in the covariant expression |
| Convergent alternating Stieltjes integrals and the quarter-Gamma evaluation | `tw:thm:alternating`, `tw:cor:quarterGamma` | Proved consequences of the normalized half-twist table |
| Reflected half-twist products | `tw:cor:reflection` | Proved with the required modulated reflection, not bare reflection |
| Covariant primitives and the exact zero-mode limit | `tw:thm:primitives`, `tw:thm:zerolimit` | Proved source additions; the ordinary Gamma-ratio primitive has classical antecedents |
| Shifted harmonic Laurent data at all nonpositive integers and at one | `harm:thm:negative`, `harm:thm:one`, `harm:cor:residue` | Complete proofs supplied for arbitrary outer shift and strict elementary harmonic depth; prior unshifted Laurent work is credited |
| Reflection, multiplication, and finite-part antiderivatives of those coefficients | `harm:thm:reflection`, `harm:thm:multiplication`, `harm:thm:FPprimitives` | Proved finite coefficient calculus, including explicit half-shift examples |
| Positive-integer beta evaluations and their rational cyclotomic specialization | `harm:thm:beta`, `harm:cor:cyclotomic` | Established baseline and applications; Young's beta-derivative framework and repository antecedents are credited |
| Untwisted periodic Stieltjes algebra, contact laws, and primitive tower | `per:thm:family`, `per:thm:contact`, `per:thm:Bell`, `per:thm:polycorr`, `per:thm:primitive` | Consolidation of results already in the pinned continuations |
| Untwisted two-parameter polylogarithm kernel and order-zero Stieltjes identities | `poly:master`, `poly:gamma1`, `poly:symmetric`, `poly:individual` | Consolidation or consequences of the established kernel; no new-to-repository kernel claim |
| Negative-real inverse-hyperbolic-tangent branch | `audit:prop:arctanh`, `audit:eq:arctanh-corrected` | Confirmed correction, with proof and a concrete counterexample to the printed branch |

The explicit source target is the subsection **“Twists, characters, and alternate
endpoint normalizations”** of the pinned
`continuations/convolution-algebra/article.tex`. It requests an all-index
half-twist table with point-supported counterterms. This package resolves that
specified target. An older G2-style question about the *untwisted* periodic
normalization had already been answered by the pinned `convolution-algebra`,
`convolution-calculus`, and `shifted-hurwitz-jets` continuations. Those are
different status statements and should remain distinct in any intake summary.

The modified Stieltjes functions and the ordinary nonsingular alternating
convolution are established antecedents, credited to Hu and Kim and to Zhu, Hu,
and Kim. The singular extension, endpoint normalization, covariant contact
terms, and limiting zero mode specify the present contribution. The harmonic
section similarly credits existing elementary-harmonic, beta, residue-filter,
and Mellin-subtraction methods. Its contribution is the stated arbitrary-shift,
all-depth Laurent coefficient rule and its exact coefficient identities. See
[source_provenance.md](source_provenance.md) and the focused
[harmonic source comparison](../verification/harmonic_source_overlap.md) for the
inspection boundary, including the external unshifted Laurent paper whose full
text was unavailable.

### Surviving source conjectures

The package does not prove `cycloquot:conj:S6` or `s8new:conj:S8`; both remain
open. The already rejected vector in `research:prop:S8-rejected` is an older,
different S8 candidate. It must not be substituted for the surviving candidate.
S2 and S4 are already proved in the pinned sources
(`s2proof:thm:S2`, `s4proof:thm:s4`, and `gaussian:thm:S4`). This package neither
claims those proofs as new nor reruns their earlier certificates. These exact
source identities and statuses are recorded separately in the claim ledger.

## Suggested manuscript and report crosslinks

The following additions can be short references to this standalone report.
They do not require replacing established chapter proofs.

| Existing location | Relevant continuation |
|---|---|
| `chapters/04-depth.tex` | Define the outer-shift family alongside the established elementary harmonic coefficients; link its Laurent rules and the reflection, multiplication, and antiderivative theorems |
| `chapters/08-differentiation.tex` | Link the covariant contact formulas and the residue term in differentiation of harmonic finite parts; the existing ordinary interior differentiation identities remain valid |
| `chapters/07-integration.tex` | Link the convergent half-twist digamma integral, the quarter-Gamma evaluation, and both the covariant and harmonic finite-part primitive formulas |
| `continuations/convolution-algebra/article.tex`, final twist question | Record that the specified nonintegral/half-twist normal form and point-supported counterterms are proved here |
| `chapters/10-discovery.tex` and the intake/status ledgers | Record the resolved twist target and new harmonic results while preserving the distinct S2, S4, S6, and two S8 statuses |

All labels in the package use the prefixes `per:`, `tw:`, `harm:`, `poly:`, and
`audit:`. A collision search found none of these prefixes in the 72 inspected
canonical chapter texts. This was not a search of every historical report, so
directly including the modular sections in a larger TeX master still calls for
the normal label/reference check. Keeping the report standalone avoids sharing
its theorem counters and preamble definitions with the manuscript.

## Separate proposed source patch

[confirmed_source_corrections.patch](confirmed_source_corrections.patch) changes
only `chapters/03-algebraic.tex` and contains two narrow repairs:

1. In `cleo:eq:lintanh`, use the real logarithm
   `log(abs(tan(theta/2)))` for negative real input and define the zero value by
   continuity. At `lambda = -1/2`, the printed principal-log expression has the
   exact spurious term `-i*pi^2/6`.
2. Retain the diagonal integral evaluation while removing the unsupported
   “non-elementary” characterization. The replacement explicitly avoids
   claiming either elementary reducibility or a nonreduction theorem.

The patch passed an application dry run against the authenticated pinned local
sources. It remains **proposed and unapplied**. Because its context is pinned,
review any upstream changes before integrating it with a later checkout.

The coefficient-field discussion following `integral:res:parity` in
`07-integration.tex` receives an editorial clarification in the article, not a
patch. Its adjacent quadratic-character example is valid. A general character
or additive-coordinate statement may require cyclotomic, character-value, or
Gauss-sum fields; the article does not mislabel the displayed quadratic example
as false.

## Conventions that integration must preserve

The proofs depend on explicit normalization choices. In particular:

- Retain every integer Fourier mode in the nonintegral twist. Its convolution
  unit is `delta_0`; the mean-zero untwisted unit is `delta_0 - 1`.
- Preserve the stated logarithm of `2*pi*i*(n+theta)`. For the half twist,
  frequency reversal is `J U(x) = exp(-2*pi*i*x) U(-x)`.
- The phase `exp(-2*pi*i*theta*x)` is used in ordinary representatives on
  `(0,1)` and in local endpoint subtraction. For noninteger `theta` it is not a
  globally smooth periodic multiplier.
- Keep raw Laurent finite parts distinct from their derivative-compatible
  versions. The displayed covariant contact terms are part of the identities.
- In the harmonic family, the parameter shifts the **outer denominator only**.
  The harmonic coefficients retain their original integer arguments.
- The nonpositive-integer coefficient rule determines the full principal part
  and the constant coefficient. It does not give an ordinary sum of a divergent
  series, and it does not permit discarding the analytic Mellin remainder when
  computing higher regular Laurent coefficients.

## Evidence to retain with the report

[source_manifest.json](source_manifest.json) authenticates the source bytes;
[source_provenance.md](source_provenance.md) states what was inspected and the
limits of the comparison. The [independent mathematical
review](../verification/independent_review.md) contains analytic sign,
normalization, finite-part, and source-status checks. The executable checks and
their saved JSON output provide exact polynomial verification and independent
numerical diagnostics. These have different purposes: source authentication is
not a mathematical proof, numerical agreement is not a proof of a conjectural
period relation, and this package does not claim proof-assistant verification.

The complete definitions, statements, and proofs remain in the TeX and PDF.
The ledger and this note are integration aids, not replacements for those
mathematical statements or their domains.
