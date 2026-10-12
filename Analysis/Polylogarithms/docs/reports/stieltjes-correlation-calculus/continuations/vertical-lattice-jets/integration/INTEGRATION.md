# Proposed integration

No repository write has been performed. Preserve the delivered package before
editing a canonical source. Suggested new continuation directory, not an existing
path asserted to have been created:

`Analysis/Polylogarithms/docs/reports/stieltjes-correlation-calculus/continuations/vertical-lattice-jets/`

## Dependency and insertion order

| Article label | Mathematical content | Status and cautions |
|---|---|---|
| `def:compensation`, `lem:vertical`, `lem:periodization` | Fixed Euler–Maclaurin normalization, normal convergence, periodization | Classical foundations, supplied with the argument needed here |
| `thm:sampling` | Entire spectral continuation of an ordinary compensated lattice sum | Proof on Re(s)>-2M; continuation outside it is not an ordinary-sum assertion |
| `thm:stieltjes` | Every compensated Stieltjes lattice sum | Ordinary absolute convergence at all fixed indices |
| `eq:Q-finite`, `eq:Q-unit` | Finite polylogarithm identities for horizontal differences | No unevaluated Lambert series in these differences |
| `thm:primitives` | Anchored all-index primitives | Anchor and fixed tau must be preserved |
| `cor:Gamma` | Gamma/q-Pochhammer specialization | KNOWN: Arabi Ardehali–Rosengren (2026), Eq. (13); do not relabel as novel |
| `thm:negative`, `prop:T-explicit` | Parity contact and harmonic-number formulas | Symmetric sums for even N, absolute for odd N |
| `cor:filters` | Mean-zero periodic weights remove all first-jet contacts | Preserve normalization tau/d and shifted bases |
| `thm:negative-jets` | All higher oversubtracted negative-integer jets | L>N/2 is essential; harmonic corrections have the printed signs |
| `thm:bilinear` | Finite Hurwitz–Lerch expression for each polygamma image | Integers r,t>=2; a,b,h>0 |
| `thm:diff-jets`, `eq:central-coeff` | Every Stieltjes-difference pairing | Nonzero mixed jets remain explicit logarithmic integrals |
| `thm:fourshift` | Four-shift digamma closure | Only grouped order-one expressions are finite |

The article is self-contained and can be retained without importing any macros
into the existing manuscript. If sections are copied into the collective book,
namespace the labels and macros and retain all hypotheses and attribution.

## Do not change these unrelated statuses

This package does not resolve S6, revised S8, or the general unequal harmonic-tail
optimal-prefix conjecture. It does not assert numerical period independence.
It is not a proof-assistant formalization, and floating-point residuals are not
interval certificates. Incoming ZIP interiors were not audited.

## Correction

`remove_duplicate_readme.py` is a guarded, local-copy-only proposal for the
specific duplicate passage in the inspected README. It does not edit historical
originals or GitHub. Its output must be reviewed before any canonical edit.

The Gamma contact warning in the article is not attributed to an existing false
repository theorem. It corrects a tempting but invalid interchange, not a
source occurrence that was never found.
