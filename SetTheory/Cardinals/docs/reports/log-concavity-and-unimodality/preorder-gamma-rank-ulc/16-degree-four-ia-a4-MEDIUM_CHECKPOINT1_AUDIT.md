# Four-attachment medium batch: independent checkpoint-one audit

## Approved results

The immutable checkpoint independently proves nine additional complete templates:

17, 18, 25, 27, 31, 32, 38, 51, 53.

Together with the separately approved small batch, this gives 42 of the 76 canonical four-attachment templates. The full degree-four conjecture is still open.

The complete medium selection is the twenty templates with full legal-type counts six or seven:

2, 5, 7, 12, 15, 17, 18, 22, 24, 25, 27, 30, 31, 32, 38, 40, 46, 51, 53, 60.

The other eleven selected templates are not yet approved as complete. Exactly fifty representative-face tasks remain in this batch, all for the third (sextic) gap. Every second-gap task of the medium batch is now covered, but that alone is not a complete-template theorem.

## Independent verification

The generic standard-library verifier `audit_population_batch.py` is the generalized version of the small-template checker. A regression run reproduced every small-batch coefficient, identity count, and complete-template verdict before the new checkpoint was used.

For the medium batch it independently reconstructed G=24γ from the Hall-audited binomial support arrays, recomputed both ordinary Newton gaps, applied the zero/positive face substitutions, and verified all 1,579 source target polynomials and both scale/coordinate maps. The identity 720·gap=(5/4)·gap(G) was checked coefficient by coefficient, including its exact divisibility. Source IDs were matched against the complete globally audited task ledger, not treated as template or normalized target IDs.

All 1,528 explicit certificate identities passed exact Fraction expansion. Their terms comprise 31,098 positive-weight binomial squares, 1,195 positive-weight general squares, and 203,863 positive monomials. The smallest positive weight is 1/2391339019187118. No floating-point tolerance or sampled population value is used.

The sole absent quartic certificate is discharged through the separately approved global template-2 gap-two identity. This is handled at the source-task level: a global proof applies only to its matching template and gap, and does not falsely mark an unrelated normalized target as certified. Every underlying global receipt, verifier, and certificate hash is checked again before this route is accepted.

## Completeness and pending work

A template is approved only when every one of its audited outstanding orbit tasks is covered by a checked explicit identity or a matching independently approved global gap. Restriction of the original task ledger to the selected template list is checked exactly. The nine approved IDs are derived from this coverage test, not copied from the producer's candidate list.

The fifty remaining source IDs are recorded per template in `medium_checkpoint1_batch_audit.json`. They all map independently to gap three. The already established first inequality, lower-degree conventions, component reductions, and full integer-face orbit coverage remain the same approved inputs as in the earlier audits.

Run `audit_population_batch.py --batch .../medium-faces --name medium_checkpoint1 --certificates .../certificates_checkpoint1.jsonl --approved-global-receipt .../global_gap2_templates2_10_34_receipt.json` to reproduce. The audit imports no producer module. Its receipt pins every authoritative source and certificate and records exact per-template coverage. Input hashes must remain unchanged during verification.

This is an incremental integer-population result for the exact listed templates. It does not assert positivity for fractional populations between zero and one, for the fifty pending tasks, or for every face of a larger legal-type family having only six or seven occupied types.

## Checkpoint two addendum

The second immutable ledger preserves every previous certificate byte-for-byte at the parsed-record level and adds exactly normalized targets 579 and 1084. Both new binomial-square identities passed independent exact replay. Template 22 is consequently complete. The medium total is now ten complete templates, and the overall a4 total is 43 of 76. Exactly 48 medium source tasks remain, all sextic, across ten templates.

The verifier replayed all 1,579 source mappings and all 1,530 explicit identities. It counted 31,104 binomial squares, 1,195 general squares, and 204,626 positive monomials independently. A corrected diagnostic loop count in the producer's search report is not an input to this audit and has no effect on the exact identities or coverage. The new receipt is `medium_checkpoint2_batch_audit.json`; the first receipt is preserved.
