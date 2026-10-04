# Bounded Mellin–Borel/Stokes placement review

PASS for exact placement. One guide qualification is recorded below; no selected
local-interface defect was found. This is not a full audit of either analytic
manuscript or its claims about external conjectures.

Publication commit: `05304d5ecce537c9a237d4e3a85a18c4519230fe`.
Parent: `6132faa30bf6e7674158ad43c9178ab730f560e0`.
Arrival: `f300069cfc840fc3d178f0ba31bcb3596a35d7a3`.

## Exact placement and provenance

All 20 changed paths are authenticated in the JSON: 16 added files, two modified
guides and two retired ZIPs. Before/after Git blobs, byte sizes, SHA-256 values
and full raw-diff hashes are recorded wherever the corresponding version exists.
Every added file equals its original archive member. The total placed size is
**1,179,277 bytes**, matching the placement declaration. Both retired archives
equal their arrival bytes; no replacement archive is silently substituted.

| Arrival archive under `docs/incoming/` | SHA-256 | Members / placed files |
|---|---|---:|
| `critical_stokes_q_reversion.zip` | `0f57c3117c3b24020934025c3f63137f87adc36bec47bd557df742ad2a0e66ba` | 10 / 9 |
| `transseries_q_stokes_reversion.zip` | `df17c699bb754962b499db013aa5e0cc43f581e05ed7b4a8befde1727685f6bd` | 8 / 7 |

The destinations under `Analysis/Transseries/docs/series-and-transseries/` are
`Mellin_Borel_Completion_q_Gamma_Critical_Reversion/` and
`Exact_q_Product_Completion_Stokes_Aware_Reversion/`, respectively. All 18 regular
members were read as bytes, CRC-checked by the ZIP reader and SHA-256 hashed.
The two delivered checksum ledgers have exactly 9 and 7 entries and verify
every other member. Only those ledgers are absent from the placement, as the
guide explicitly records. The delivered READMEs still list their original
`SHA256SUMS.txt`; that historical package listing must be read with the host
guide's explanation that the ledgers were deliberately not shipped.

The two standalone sources retain 142 and 154 distinct literal labels, with
104 and 127 recognized internal reference occurrences; none is unresolved in
the fresh parser's stated scope. These are source-text checks, not rendered
cross-reference or compilation checks.

The guide's increments from 61 to 63 arrivals and from 39 to 41 discarded
ledgers are consistent with these two additions. The prior cumulative inventory,
page counts, “under 1%” 8-gram comparison, literature dates, claimed ray-integral
confirmation, and all older cross-report theorem correspondences were not
independently recertified. The commit message and full guide changes were read
as attributed editorial/provenance claims, not accepted as new proof certificates.

## Actual reading and the earlier intake boundary

I read the complete modified guide diffs: 16 lines for
`Analysis/Transseries/README.md` and 225 for the group README. I also read the
complete commit message and both complete delivered READMEs and internal
proof/provenance reviews (109, 118, 103 and 136 lines). The applicable
`Analysis/Transseries/AGENTS.md` and incoming standing retention rule were read.
The JSON records exact immutable byte-line span hashes.

New manuscript coverage is limited to **978 lines**:

- Mellin source: 94–183, 184–288, 663–703, 928–986 and 1845–1906.
- Exact-product source: 92–177, 299–338, 586–741, 745–860, 1655–1739,
  1793–1819 and 2100–2210.

These spans cover conventions/provenance, the completion statements, formal and
analytic inverse hypotheses, finite reflection/cancellation proofs, the
finite-multiplicity rescaling, and certification limitations. Search hits used
to locate them do not count as additional proof reading.

The earlier `review_new_foundations_f300069cf.md` was reread in full as a scope
ledger. For this pair it had read both guides/internal reviews and the
abstracts, **not the Mellin or inverse body proofs**. Its two archive and all
18 member pins agree with the fresh calculation. Its coverage is not promoted
to a full proof review here; repeated guide reading and newly selected body
spans are distinguished above.

## Retained guide qualification

**Review Remark 1 — range of the reflection criterion.** The immutable group
README, lines 2350–2354, says:

> For any finite set of real shifts, the median reconstructs a weighted sum
> exactly when the weights are antisymmetric under `a ↦ 1 − a`, and the Stokes
> jump vanishes exactly when they are symmetric

The actual theorem begins with a finite set **`S ⊂ (0,1)`** in the exact-product
source, 589–618. The entry earlier mentions `0<a<1`, so the later phrase can be
read under that context; stated without it, “any finite set of real shifts” is
too broad. At `a=0` the product has the factor `1−1`, and its logarithm is not
defined. The theorem does not assert the formula for that input. The precise
minimal replacement is:

> For any finite set of real shifts in `(0,1)`, the median

This preserves the following reflection criterion verbatim. The original clause
and explicit excluded-input example are retained here under the standing rule.
This is a guide-domain clarification, not a refutation of the source theorem.
Root was notified; no repository text was edited by this review.

## Selected mathematical and arithmetic interfaces

The two completion statements distinguish the original logarithmic product from
each lateral sum and from their linear average. A jump determines an odd-phase
difference; it does not determine the jump-free even completion. At `a=1/2`,
the displayed dual-product series has a nonzero first coefficient while the
sine jump vanishes. This is a concrete reason to retain completion data when
inverting. I did not read the full Mellin contour shifts, principal-value
interchanges or external Fantini–Rella text, so the claimed conjecture resolutions
remain attributed to the sources/placer within their stated version and domain.

Conditional on the printed completion identity, the finite reflection proof is
coherent: divisor inversion recovers phase moments, then a finite Vandermonde
system separates the distinct nonzero phases. Cosine and sine moments detect
the symmetric and antisymmetric weight parts. The delay bounds `p` and `p−1`
use that the zeroth sine moment already vanishes. They require finitely many
phases and give detection indices, not paid arithmetic gate counts.

The formal fixed-point statements require a complete separated filtration and
an already well-defined filtration-raising substitution. Iteration computes a
specified filtration truncation only in that supplied setting; it is not a
general finite evaluator for arbitrary transseries. Normally summable analytic
perturbations likewise need a weighted summability bound and do not automatically
provide formally locally finite supports.

The analytic inverse theorem uses a selected univalent chart and an explicit
Rouché boundary bound on a target disk. Its convergent amplitude expansion and
Cauchy tail estimate retain those data. The ramification proof substitutes
`z=s^m`, `x=alpha+s^r*u` and divides by `s^(mr)` only after the lower completion
coefficient functions vanish identically. Separation from the rescaled critical
value makes the initial roots simple. The example `x²+zx+z³=0` correctly warns
that vanishing only at the critical center does not justify a `z^(3/2)` scale.
These read local arguments do not establish the unreviewed uniform hypotheses
of every application elsewhere in the manuscripts.

The analytic action conversion “24,” half-action folds, finite phase counts and
high-precision digits are not integer circuit costs. An ordinary-integer
implementation would still require finite representations, charged coefficient
operations, certified analytic bounds and domain/inverse-branch guards. No
fixed-arity integer certificate or complete paid universal polynomial is
provided by the selected interfaces.

## Unread and execution boundaries

The full Mellin/principal-value and parameter-uniformity proofs, most gamma-fold
applications, all external-source comparisons and priority claims remain outside
this review. The source's own unresolved questions and the placer’s list of
unchecked closure/uniformity hypotheses remain on record; no claim is deleted
or silently upgraded. The two manuscripts are byte-preserved deliveries whose
editorial pass is deferred, not newly unified or independently certified Parts.

No supplied/archived/frozen/predecessor program or copied version was executed
or imported. No verifier, builder, TeX/Lean run or PDF rendering occurred. The
source-reported 144 and 19 symbolic checks and 110/150-digit numerical runs
remain historical claims, not interval certificates or results reproduced here.
Only fresh standard-library metadata code ran, normally and with `python -O`
from `/`, producing identical receipt bytes. No repository/Git mutation occurred.

Frozen metadata helper:
`/tmp/review_mellin_stokes_placement_05304d5ec_metadata.py`, SHA-256
`9eb39617f9826abb1c1e48c1aa0d866fbf193356dfe4284abc71243b82b52c11`.
Receipt: `/tmp/review_mellin_stokes_placement_05304d5ec.json`, SHA-256
`2ddf01c9f533197ad7f72c3c167d670a841c74915a09bdc1bd0749e553135dea`.
