# Four Borel-report ancillary placements at 54ece48ab

**PASS for byte placement; manuscript publication is still pending at this
commit.** The change adds 17 ancillary files and retires four archives. It
does not modify the host guide, article source, or PDF. The description
“Parts XVIII–XXI” names the intended subsequent integration, not four parts
already printed by this change. No new mathematical defect was identified
within the bounded coverage below; this is not a new full proof audit.

## Immutable scope and achieved checks

The reviewed commit is `54ece48ab0b52e823bd66814b38c330b9198224b`, parent
`3e4a450350d28ea960c4c1ae3b207a7eadd247f1`. It is a direct parent of merge
`23eee75ef157b65c897d3364d052bd43a4b50ff3`. The new read-only helper uses
these immutable objects, not the moving working-tree report.

| Intended source/part | Retired archive under docs/incoming | Arrival | Regular members | Placed files | Manifest entries checked |
|---|---|---|---:|---:|---:|
| 24 / XVIII | Borel_Conjugacy_Divisibility_Threshold.zip | 62846e17a | 6 | 2 | 5 |
| 25 / XIX | glazer_proveit_support_complexity.zip | 7be14aa84 | 8 | 4 | 7 |
| 26 / XX | Borel_Flows_Glazer_ProveIt.zip | fb9f5884b | 9 | 5 | 8 |
| 27 / XXI | Two_Derivations_Borel_Conjugacy.zip | 78528873b | 10 | 6 | 9 |

All four parent archive bytes equal their arrival-commit bytes. Their 33
regular members were independently inventoried and hashed from Git ZIP
objects. Every one of the 29 shipped checksum entries matches, and each
manifest covers all its package's other regular files.

Every added file has exactly one matching member in its corresponding
archive. The 17 files total **131,536 bytes**, contain no CR bytes, and have
maximum repository-path length 140. The complete per-file map, Git blob,
size and SHA256 are in the JSON. The grouped placement is:

- Source 24: the jet verifier and its saved JSON report.
- Source 25: sources ledger, verifier, Makefile and saved check output.
- Source 26: claim ledger, sources ledger, verifier, build script and saved
  verification JSON.
- Source 27: source audit, verifier, build script, requirements and the two
  saved verification reports.

Exactly four members per archive were not placed: the TeX manuscript, PDF,
delivery README and checksum manifest. They remain recoverable from the
authenticated arrival and parent Git objects. The archives are absent from
the child tree. This review does not interpret archive retirement as proof
that their manuscript bodies have already been integrated.

The host is
`Algebra/SurrealNumbers/docs/foundations-and-computation/polish-models-of-omnific-arithmetic/`.
Its three relevant files have identical parent/child blobs:

| File | Unchanged Git blob | Bytes |
|---|---|---:|
| README.md | 90c4dd049546b8a5a80e7fa9773f385f94abfe1d | 135,929 |
| article.tex | c7918aecaec9dca7bc6c3e0063cf524fcc52e3d8 | 2,018,989 |
| article.pdf | ed7eb5464d8e3bffcb8519348f08a06800544bf3 | 4,773,924 |

The guide still lists twenty contributing manuscripts through source 23 /
Part XVII. The TeX has 17 `\part` headings. There are zero occurrences of
the proposed label prefixes `pma:bct:`, `pma:spc:`, `pma:bfl:` and `pma:tdv:`.
Thus no new body-to-host label mapping, new guide link, or new PDF rendering
can be certified at this placement. The commit message itself expressly
defers manuscript, notation and cross-reference work to “the write.”

## Exact reading and inherited research coverage

This review read the full placement commit message, all four newly placed
provenance/status notes (59+63+87+91=300 lines), and all four delivery
READMEs (101+52+86+83=322 lines). It read host README lines 1–110 and the
17 individual TeX part-heading lines; those headings are locators, not a
read of intervening manuscript proofs. The flow manuscript lines 160–172
were read only to authenticate the previously reported broken reference.
Applicable `Algebra/SurrealNumbers/AGENTS.md` was read in full, together
with the incoming retention rule at `docs/incoming/README.md` 426–438.

All spans have inclusive endpoints and exact byte hashes in the JSON.
The entire changed-path list and full diff are authenticated; the full
code/data diff was **not** read. All four note additions were read as full
text; they have no replaced parent text. Scripts, Makefile and saved data
are authenticated as placements, not re-executed tests. All PDFs are hash
only: no reading, rendering or build.

The following prior review notes were read in full at their immutable
54ece48ab bytes. Their receipts and helper files are also byte-pinned,
but no previous collector or mathematical check was replayed:

| Prior note in research-wip/native-stream-queue | Lines | SHA256 |
|---|---:|---|
| review_new_borel_62846e17a.md | 1–98 | 38305b2f1c7ac9f5c83253b678b43b8b0ba7bdec764b9ed54d04cb7c843b1575 |
| review_new_support_complexity_fb9f5884b.md | 1–71 | 5e5bcf816561bd38a9e3a1731569e37eccfa263f1b4f6474133e4d2b1d729486 |
| review_new_borel_flows_fb9f5884b.md | 1–218 | 8b4d051f36c080ac8ffe040ff8433a8cd5d39b5a6eed8cd910878b89655a318d |
| review_two_derivations_78528873b.md | 1–253 | ed6f235ed6a8493176c8872588ee0d916c02065847a6c1392698722fb5c9637d |

Their inherited mathematical scopes remain distinct:

- Conjugacy uses real coefficients, left-finite supports, a fixed subgroup
  `Z <= Gamma <= Q`, and coefficient-Borel **ordered** automorphisms. The
  recorded negative effective example uses a particular decidable-membership
  exponent group whose scaling-unit problem conceals nonhalting.
- Support complexity concerns countable orders/groups and real coefficient
  arrays with infinite certificate sequences. The prior review accepts its
  stated classical descriptive-set-theoretic dependencies. Its computable
  legal-array/no-computable-name and nonhalting recognition examples are
  reviewer deductions, not new claims attributed to the source.
- Flows assume a nonzero countable **divisible** subgroup of the real
  exponents and jointly coefficient-Borel real-parameter actions. They may
  have higher rational rank. The conjugacy review's generally nondivisible
  halting-height example does not automatically transfer to this setting.
- Two derivations concerns named noncommuting ordered pairs on the
  rank-one field and ordered Borel coordinates. The prior review's
  co-c.e.-complete slice uses total coefficient programs with an unknown
  finite-support endpoint. It does not apply to polynomials supplied as
  explicit finite coefficient lists. The obstruction is invariant equality,
  even when its scalar normalizer is already the identity.

These previous notes report complete manuscript proof challenges with
their stated qualifications. The present review inherits those records;
it does not independently reread thousands of proof lines. External papers,
priority, the full Conway foundations, whole Lean developments, and reported
external source inspections remain outside this review.

## Retained issues and computational boundary

The immutable flow source still contains, at lines 166–167,

```text
Theorem~
ef{thm:timeoneexact}
```

The existing review identifies the intended `\ref{thm:timeoneexact}`.
The placement message acknowledges this editorial correction for later
integration; there is no manuscript edit here that repairs or deletes it.
The original clause and this locator remain on record.

The commit also records future handling of the support verifier's bare
assertions and the source's “not bundled” description of its predecessor.
Those are placement-author statements here, not newly executed validations.
Its listed further questions, sketches, action-definition issue and unchecked
citation likewise remain explicit pending integration decisions. The four
source ledgers' claims of complete written arguments or finite checks are
not elevated to Lean certification by copying the ledgers. No question is
silently deleted or newly declared proved by this review.

The supplied runs of 143, 5,372 and 669 finite checks, the support check
output, copied-suite replays, PDF inspections and shared-8-gram percentages
remain attributed claims. This metadata PASS does not reproduce them.

None of the four placements provides a complete paid ordinary-integer
Diophantine compiler, fixed finite witness interface, uniform input/history
loader, or gate saving. Borel selectors are not effective integer
algorithms; infinite certificates are not finite existential witnesses.
Finite jet or support-cutoff calculations require explicit effective
coefficient/support presentations and charged arithmetic before they can
be compared with the current finite Diophantine constructions. The prior
reviews already make these distinctions, and the ancillary placement does
not change them.

## Fresh metadata validation

Only the newly authored `review_borel_placement_54ece48ab.py` was executed.
It uses standard-library ZIP/hash/JSON operations and read-only Git calls;
it never imports or executes a delivered or predecessor program. No
repository file, Git reference, archive member, or prior review changed.
Fresh normal and optimized-Python exact receipt replays from `/` both
passed before freeze. These are metadata checks, not mathematical-suite
replays.

Helper SHA256:
`cf7394cb9ebbe5b3b149fd1b061df0cfbedb53a2ed034d3a43fdb4d9b292e96c`.

Receipt SHA256:
`4f570eceec8d8bb07d371b06589384f15c50cb54c52af54ef29110c0d4de6042`.
