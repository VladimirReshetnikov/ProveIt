# Integrated paper mathematical audit

Date: October 1, 2026. Verdict: **APPROVED**.

The six-page integrated manuscript faithfully combines the two previously
audited structural results. This review covered the complete TeX source,
the final PDF's extracted mathematical text, the copied source snapshots and
approval receipts, the added literature comparisons, the reported finite-check
counts, and the design of the package verification driver.

## Mathematical findings

- The bipartite physical polynomial has homogeneous degree equal to its chosen
  shore size. Exterior extraction and core merging enforce physical
  disjointness without counting matching witnesses. The overlap corollary uses
  `|P∪Q|`. Componentwise shore reversal and removal of zero-weight arcs are
  legitimate refinements
- Actual-degree ULC from that theorem is asserted only when positive-weight
  saturation identifies the shore order with the actual degree. The displayed
  counterexample to arbitrary Lorentzian monomial cancellation is correct
- The pendant theorem preserves the HPP seed hypothesis and the unique-parent
  condition on each head outside `Q`. Its signed monomer substitution,
  recurrence, physical merge, nonzero zero-weight limit, and root transfer are
  correct. These give actual-degree real-rootedness directly, including degree
  drops, without a Lorentzian cancellation argument
- The arbitrary-rank elementary-symmetric seed formula keeps universal elements
  distinct, counts every basis once, and treats ranks zero and one separately
- The overlapping non-bipartite example has coefficients `1,16,47,31,4`, with
  99 ordered supports and 163 directed matching witnesses, as independently
  reproduced in the underlying audit

One integration ambiguity was corrected before approval: in the split seed,
matchability of role copies does not yet require physical disjointness. The
final text now states this explicitly. The upper-half-plane convention and
definition of real stability were also made explicit.

## References and computational reporting

Brändén--Huh and Borcea--Brändén theorem use agrees with the underlying audits.
The newly added comparisons were checked in primary sources:

- Röhrle--Ulirsch, Theorem A, normalizes by the smaller ground-side cardinality.
  The publisher confirms volume 30, pages 501–523 (2026), despite online
  publication in 2025: https://link.springer.com/article/10.1007/s00026-025-00780-z
- Alexandersson--Jal v3, June 30, 2026, Corollary 4.1, uses the board's number of
  rows: https://arxiv.org/pdf/2410.00127v3

Every computational count quoted in the manuscript matches the packaged
receipts. Both independent checker copies are byte-identical to the approved
originals. The verification driver runs copied scripts in temporary directories
and compares deterministic receipt fields while excluding elapsed times; it
does not rewrite the frozen receipts.

This is mathematical/content approval. The producer's separate
`qa/visual-qa.json` records inspection of all six final rendered pages. A fresh
archive replay is recorded separately after the release archive is assembled.

## Approved content hashes

- TeX: `4d1e557f6da47f9491a8ee45649b785a64d9e7352d71059a81c1fe392d8398a4`
- PDF: `3748dee5ca8ab3ddd59adebe4ab473891564d645443fb66914bce770a7b94a91`

No general five-role-cover theorem, unrestricted actual-rank normalization of
the bipartite result, arbitrary seed edge weights, or stability of arbitrary
transversal matroids is claimed or approved.
