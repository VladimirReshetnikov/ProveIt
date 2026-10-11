# Source audit and provenance

## Inspected sources

Repository: `VladimirReshetnikov/ProveIt`.
Targeted source anchor: `b1df802799851c62a860570c3ac78ee31b9f5c04`.
The GitHub connector supplied the readable source content; the chapter reads
were explicitly pinned to this revision. Input Git blob IDs are in
`source-provenance.json`; they are not SHA-256 digests.

- `Analysis/Polylogarithms/docs/manuscript/chapters/07-mixed-twist-identities.tex`:
  complete chapter read. It proves the fractional beta mixture and positive
  integer partial fractions and leaves finite mixed Stieltjes jets separate.
- `Analysis/Polylogarithms/docs/manuscript/chapters/07-twisted-stieltjes.tex`:
  source lines 1–180 read, covering Fourier phases, the entire normalized
  family, Gamma factors, endpoint residues, and initial Stieltjes coefficients.
- `Analysis/Polylogarithms/docs/manuscript/README.md`: current overview read.
- `Analysis/Polylogarithms/docs/manuscript/EDITORIAL-LEDGER.md`: opening and
  later reconciliation milestones read, especially the ninth/tenth intake
  and unequal-twist scope. This was targeted reading, not a complete audit of
  every historical source referenced by the ledger.
- `docs/incoming`: directory inventory read. The returned listing was partly
  truncated. No claim of a full census or exhaustive binary-archive content
  audit is made.

A Library search found related earlier reports, including nested harmonic jets,
shifted Hurwitz correlations and periodic contacts. These were context leads,
not additional unexamined theorem assumptions. The report does not infer
archive content from titles or use earlier finite replay as proof acceptance.

## Corrections and safeguards

No new mathematical error was found in the targeted canonical chapters. Their
frequency-interval and normalization qualifications are retained. The only
specific editorial synchronization issue identified is that the ledger opening
reports 439 textual sources while the later milestone and README report 746.
The inventory was not independently recounted. Recommend dating the older
count or referring to one authoritative inventory rather than silently
presenting both as current counts.

The new proofs demonstrate why several shortcuts would be invalid: deleting
the twisted zero mode, discarding Pochhammer zero-order jets, differentiating
an integer-only identity in a discrete label, omitting a contact term, freezing
a Fourier phase before order differentiation, or forgetting the pole's
conductor logarithms. They are integration safeguards, not alleged errors in
the canonical source. The unequal-shift spectral-ray example does rule out a
joint value at the origin for the new family without a stated prescription.

## External primary references checked

The article cites NIST DLMF Sections 25.11, 25.14, 25.12, 5.7 and 5.15 for
classical normalizations and identities. The publisher page for Lagarias and
Li, *The Lerch Zeta Function III. Polylogarithms and Special Values*, Research
in the Mathematical Sciences 3 (2016), article 2, DOI
10.1186/s40687-015-0049-2, supplies broader Lerch-function context.

These references support classical background. No exhaustive priority review
of the derived identities, independent peer review, or proof-assistant check
is claimed. Full URLs appear in the article bibliography and the provenance
JSON. The user should retain attribution when integrating the work.
