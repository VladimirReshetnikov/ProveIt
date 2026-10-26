# Final delta audit: incoming proof-refinements archive

## Identity and scope

Frozen repository commit: `09d65a93c9df8684c1a226341d6a5120623d1cdb`.
Source member: `docs/incoming/diophantine-lean-proof-refinements-2026-10-26.zip`.
Archive: 538,237 bytes; SHA-256 `bab188a31d586762212096523ab818c9135824b6d443b2a577827bf8759583c4`.

Public source URL: https://github.com/VladimirReshetnikov/ProveIt/blob/09d65a93c9df8684c1a226341d6a5120623d1cdb/docs/incoming/diophantine-lean-proof-refinements-2026-10-26.zip

Read the full substantive manuscript, README, novelty audit, incoming-exclusion ledger, final refresh, structural/Wang findings, independent patch review, and all four patches; searched every TeX/Markdown/Lean/patch/text member for potentially overlapping mechanisms. Secure extraction rejected absolute/traversing paths and symlink members. `inventory.json` records each member's size/hash. This is a delta novelty review; compilation logs in the incoming ZIP are historical evidence, not newly reproduced builds.

## Decisions

| Proposed item under review | Decision against this new archive | Exact reason and evidence |
|---|---|---|
| Apply the existing linear coefficient bound twice | Retain against this archive | Its four proposals are syntax constructor minima, canonical-order cancellation, period-one orbit rigidity, and sharing exact band-quotient properties. It supplies no linear-operator coefficient-bound composition. Its historical exclusion catalogue mentions prior coefficient envelopes; those were already part of the earlier exclusion audit. |
| Normalize the two scalar exponential thresholds | Retain against this archive | Proposal A's threshold is the fixed syntax-code bound 44, proved from outer-constructor monotonicity and closed minima 67/133. That does not normalize exponential bases or shift an exponent to a standard growth inequality. See `report/lean-proof-refinements.tex:102-167`, particularly 112-134 and 147-158. |
| Optional explicit allowed-tile index decoder for quotientWord | Retain, with existing cost/axiom qualifications | Proposal D shares the matching/binding proof for the existing quotient word, without changing its data definition. It does not use `recoveredIndex`, supply `indexOfAllowed`, or remove `Classical.choose` from data production. The distinction is explicit in `report/lean-proof-refinements.tex:302-318`, `audit/wang-findings.md:66-74`, and `audit/independent_patch_review.md:64-66`. |
| RefinedPair expansion injectivity and finite-tuple cleanup | No overlap in this archive, but separately excluded | Parent reports packet w already proposes this mechanism. This delta review does not override that exclusion. |

## Optional decoder versus the closest proposal

The new archive's `band_quotient_properties` starts with a `let a :=` naming the unchanged `quotientWord (extend (band ...)) ...`, exports `MarkedWord` plus pointwise binding, then feeds those facts to two wrappers. The archive explicitly says this creates no new word and leaves `quotientWord`, `band`, `extend`, and `canonicalWord` unchanged (`report/lean-proof-refinements.tex:305-316`; `audit/independent_patch_review.md:64-66`).

The optional proposal under review instead supplies a deterministic literal tile index using the already-existing `recoveredIndex`, changes quotientWord's data expression from classical choice to that index, and proves equality to the legacy quotient function. It remains a representation/computability improvement, not a net proof-size reduction: +13 physical lines, with Classical.choice still appearing in the inherited axiom footprint. Neither a generic exact-witness interface nor re-proving tile injectivity is claimed new.

The archive also changes `row_zero_of_helix` in the same HelicalQuotient module. Its hunk does not overlap the decoder hunk. Exact textual application of the decoder hunk to the incoming archive's helical-rigidity overlay succeeds uniquely, changing 136 lines to 149 (+13). This is a source-composition check only; the combined module has not been compiled. Integrate the patch, not the old full-file overlay, to preserve the assumed period-one refactor.

## Future-question audit

The new archive's four future questions (`report/lean-proof-refinements.tex:378-386`) extend: (1) outer-constructor syntax minima; (2) weaker canonical-order/cancellation assumptions; (3) global period-one orbit recurrences; and (4) exact band-quotient contracts for later completeness witnesses.

The reviewed report's coefficient-composition question (`report.tex:679-687`) and scalar-normalization question (`704-716`) do not repeat them. Its optional computational-client question (`718-725`) asks whether direct index evaluation justifies the +13-line representation cost; it does not propose another shared exact-witness theorem. The RefinedPair further question should be removed alongside its now-excluded main proposal because packet w, audited separately, already contains the underlying mechanism.

## No additional recommendation

No new recommendation is inferred from this incoming archive. All four of its proposals and all four future directions are now part of the exclusion baseline. In particular, period-one helix/seam simplification and exact CycleBand/BandMarker witness sharing must not be reintroduced as fresh ideas.
