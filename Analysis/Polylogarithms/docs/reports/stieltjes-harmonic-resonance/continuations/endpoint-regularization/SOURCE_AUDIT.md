# Source audit and attribution boundary

## Repository anchor

Repository: `VladimirReshetnikov/ProveIt`

Reviewed commit: `fc4d3bf80534ad7c901d3b8c9e71baf2df0064ed`

Commit metadata returned by the repository connector: 10 October 2026,
21:30:46 UTC; commit message “New research reports”. Initial navigation used
`main`; the substantive selected chapter reads used the pinned commit.

## Text and metadata actually inspected

| Repository path | Scope used |
|---|---|
| `Analysis/Polylogarithms/docs/manuscript/README.md` | Canonical proof-status and organization record |
| `Analysis/Polylogarithms/docs/manuscript/polylogarithms.tex` | Main driver, chapter structure and editorial conventions |
| `Analysis/Polylogarithms/docs/manuscript/chapters/04-depth.tex` | Selected initial harmonic-depth material, including the existing alternating/Gamma reduction |
| `Analysis/Polylogarithms/docs/manuscript/chapters/07-integration.tex` | Selected initial integration material and the PSLQ paragraph labelled `integral:neg:psim2` |
| `Analysis/Polylogarithms/docs/manuscript/chapters/07-loggamma-moments.tex` | Returned initial portion, including classical cubic-moment attribution; not a full audit of the long file |
| `Analysis/Polylogarithms/docs/reports/alternating-harmonic-polylogarithms/README.md` | Existing alternating elementary-harmonic reflection and verification scope |
| `docs/incoming/README.md` | Intake and placement instructions |
| `docs/incoming/` | Directory metadata and filenames only for binary archives |

The canonical README reports a 417-page manuscript. This continuation did
not audit all 417 pages. Some long connector responses were truncated; no
claim is based on treating an unreturned portion as reviewed.

## Incoming archives: listed, not inspected internally

The directory listing exposed:

- `ProveIt_Resonance_Correlations_2026-10-10.zip`
- `ProveIt_Shifted_Hurwitz_Jets_2026-10-10.zip`
- `ProveIt_Stieltjes_Convolution_2026-10-10.zip`
- `ProveIt_Stieltjes_Correlation_Closure_2026-10-10.zip`
- `Stieltjes_Convolution_Calculus_2026-10-10.zip`

Their binary payloads were not extracted or reviewed. The available text
fetching established the listing and intake policy but not those contents.
No claim of complete novelty relative to these files, and no allegation of
an error inside them, is made. Integration should include that comparison.

## Primary literature consulted

The NIST Digital Library of Mathematical Functions was consulted for Gamma,
beta, Hurwitz-zeta, hypergeometric and Lerch identities:

- https://dlmf.nist.gov/5.7
- https://dlmf.nist.gov/5.12
- https://dlmf.nist.gov/15.4
- https://dlmf.nist.gov/25.11
- https://dlmf.nist.gov/25.14

Kaneko and Sakata, *On multiple zeta values of extremal height*,
https://arxiv.org/abs/1505.01014, was inspected, including rendered PDF pages
for the height-one Gamma identity, the cutoff/shuffle conventions, and the
bibliography. Its ascending index convention is reversed in the present
article. It supplies the bibliographic links to Hoffman, Aomoto, Drinfeld,
and Ihara–Kaneko–Zagier.

The Ihara–Kaneko–Zagier preprint record was also consulted:
https://archive.mpim-bonn.mpg.de/id/eprint/725.
The complete IKZ paper was not independently re-audited here. Hoffman,
Aomoto and Drinfeld are cited for established attributions recorded in the
consulted primary article, not as papers fully checked page by page during
this continuation.

## Claim classification

**Classical ingredients retained with attribution:** finite symmetric-sum
relations, Gamma regularization of harmonic/polylogarithmic asymptotics,
Hurwitz/polygamma recurrences, beta/Gauss evaluations, and the unshifted
height-one Gamma generating identity. The elementary Catalan and integer
shift specializations are not asserted to be previously unknown.

**Proved here as a unified continuation:** explicit common-shift and
log-decoration coefficient formulas; complete endpoint subtraction
polynomials; arbitrary single-decoration cancellation; higher-decoration
examples; Gamma-conjugated differential recurrence; diagonal/ray finite-part
correction formulas; beta-weighted moment and antiderivative consequences;
and finite-shift and cyclotomic scale transport. These may overlap with
results elsewhere; no exhaustive priority claim is made.

**Not claimed:** S6/S8 resolution, rational or algebraic independence of
periods, minimum numerical or motivic depth, analytic convergence of the
multilog Gamma-moment master series, exhaustive repository review, or
proof-assistant verification.

The targeted correction is a methodological wording issue about rational
independence, not a new numerical mis-evaluation. See
`PROPOSED_CORRECTIONS.md` for the exact scope.
