# Source audit and attribution boundary

Project date: 2026-10-11. Some file-build timestamps fall on 2026-10-12 UTC,
still 2026-10-11 in the user's Pacific time zone.

## Repository access and baseline

Sources were read using the connected GitHub read tools. No remote writes
were performed. The observed main ref during the session was:

    9ec0f0406afe7a5475b03ff65ed91f7e283979b8

Initial index reads used moving `main`. Later source comparisons were
explicitly pinned. This is not an atomic full checkout, and the manifest
must not be interpreted as a full-tree audit. Returned blob identifiers
and actual reading boundaries are recorded in `sources.json`.

The most important source comparison was the existing critical-Hahn chart
in `Critical_Hahn_Transseries_Beyond_Finite_Action_Folds/article.tex`.
The fixed `1 < alpha < 2` chart `x = T V(T,T^(2-alpha))`, its Cauchy estimate,
and its exact multi-index formula already exist. The present article
credits this overlap. It changes the problem to a varying order approaching
an integer and derives a second scaled-order resonance and exact critical
locus. It does not claim that convergent polylogarithmic inversion or the
analytic implicit-function method is new.

## Historical correction: not a new error claim

The historical `polylog-polygamma-bridge.tex` abstract overstates exact
classification and independence on the basis of finite numerical searches.
Its own status discussion is more cautious. The current canonical
`EDITORIAL-LEDGER.md` already says to replace the “exactly crystallographic”
and independent-new-atom conclusions with exact reductions and bounded
searches. The current research does not rediscover an uncorrected result.

Proposed action: preserve the canonical correction and add an explicit
supersession pointer whenever the historical file is circulated standalone.
A ready-to-use note is in `integration/HISTORICAL_SUPERSESSION_NOTE.md`.
Do not overwrite historical provenance silently and do not label the note
as a newly proved independence result.

No new false mathematical assertion was established in the inspected
current canonical material. This limited conclusion is not a warranty for
uninspected files or statements.

## Classical identities actually used

The exact normal form is derived from DLMF 25.12.12 (Jonquière continuation).
The Gamma logarithm series comes from DLMF 5.7.3, the Stieltjes convention
from DLMF 25.2.4, and the tail convergence argument uses the zeta functional
equation in DLMF 25.4.2. Lambert reductions are compared with DLMF 4.13.
These are credited classical ingredients, not candidate new discoveries.
All paper bibliography entries correspond to sources actually accessed.

## Search scope

GitHub semantic/code queries included `polylogarithm`, `Jonquiere`, and
`order-resonance`, restricted to `VladimirReshetnikov/ProveIt`. The last
returned no result. Other hits and index references led to the scoped reads
in the manifest. A no-hit query does not prove repository-wide absence.

The final bounded public-web search used these exact queries:

    polylogarithm inverse integer order double scaling Gamma zeta resonance
    polylogarithm inversion variable order logarithmic singularity Lambert W
    "polylogarithm" "Stieltjes" "fold"
    "polylogarithm" "critical locus"

The search returned broad special-function background, unrelated uses of
critical loci, and generic inverse-polylogarithm discussions. No exact
antecedent for the package's combined formulas was established. Unrelated
hits were not adopted as mathematical sources. The verified classical
background used in the proofs is the DLMF material above.

This was not an exhaustive journal, book, preprint, or language-spanning
priority search. A different notation may conceal a prior equivalent
result. The correct label is **candidate model-specific contribution with
proof supplied, publication priority unestablished**.

## What has not been claimed

No unrestricted inverse-polylogarithm classification; no global zero count;
no global gluing of primary and secondary inverse branches; no growing-k
uniformity; no new Borel summability, resurgence, or Stokes theorem; no
interval-certified convergence radius; no Lean formalization; no numerical
independence theorem for zeta or Stieltjes constants.
