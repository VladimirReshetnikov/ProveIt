# Root acceptance, retained corrections and rebuild for the horizons publication

The bounded publication review and the separate Part XVI correction review
are accepted at their stated scopes. Their immutable target is
`a21a42d8c27f62ac3443393f88adfeb3d5f6f265`. Corrections apply to the merged
host at `80afdf9fa` (unchanged in the intervening counter-certificate commit
`70af24030`), preserving the earlier R1–R3 metadata corrections. This is a
follow-up to the actual Part XVII write, not a repeat of the ancillary-only
placement review at `6571ee1af`.

## Claims corrected and retained

1. **Multiplication scope, H1.** The guide, notation table and Part XVII
   introduction extended multiplication to points of every fixed Ω^[B].
   With B=2 the point-cut Ω squares to the whole Ω², which cannot be a
   proper point-cut of itself. Both operations are stated on the hereditary
   order; only addition extends to all those powers. The printed arithmetic
   theorems and their proofs already had this scope.
2. **Set-likeness, H2.** The guide omitted A≥2 and nonempty B. The singleton
   power at A=1, B=Ord+1 refutes the first omission; A=Ord, B=0 refutes the
   second. Both hypotheses are restored. The source theorem is unchanged.
3. **Set-base collapse, H3.** The guide omitted the set-ordinal a≥2 premise.
   At a=1, B=1 its unrestricted statement would give 1≅Ord. The guide now
   repeats the printed corollary's premise.
4. **Digit/history invocation.** Remark XVI.5.29 formerly invoked a
   canonical history for every supplied exhausting tower. At W=1, Γ=0 the
   tower exists but the stated history definition excludes that schedule.
   The proof now handles this case directly as the unique isomorphism to
   P(0)=1, then invokes the history only for nonempty Γ. The old claim and
   counterexample remain within that numbered remark.
5. **Converse and tower-existence domains.** Source 33's Proposition XVI.5.30
   and Remark XVI.5.31 formerly asserted an exact tower for any W embedding
   into P(Γ). W=0, Γ=1 satisfies the embedding premise but is outside the
   printed tower definition. The proposition now restricts W to nonempty;
   the broader embedding/initial-embedding result separately handles empty
   W and then empty Γ before invoking the tower. Its formerly unrestricted
   history clause has the W=1, Γ=0 counterexample too. The adjacent Note
   XVI.5.32 now says all **nonempty** class well-orders and retains its old
   unrestricted wording with W=0. These are domain repairs, not changes
   to the endpoint embedding result or extra choice assumptions.
6. **Dependency-summary retention, H4.** The already corrected statement
   that source 35 used global choice only for one inference was too broad:
   its FPE corollary also cited a GBC equivalence. Item (4) of the old
   completion proof already replaced that dependency by its GB theorem.
   Its existing counterevidence now has an explicit numbered review-remark
   locator. Tm→T remains a recorded typographical correction, not an
   invented mathematical counterexample.
7. **Earlier review qualifications, H5.** The frozen `62b16914e` reviews
   and the separate unshipped working-note account missed the empty-domain
   cases in the tower/history and digit/converse chain. Their unqualified
   passes remain on record, now explicitly qualified by the counterexamples
   above. The nonempty arguments and GB completion proof remain valid in
   this bounded review. The guide and front matter point to that update.

No unproved source claim was promoted to a theorem or silently discarded.
Existing credited research questions remain in place. Review remarks use
explicit H1–H5 locators without advancing any theorem counter.

## Independent review and root checks

The publication reviewer read the full 557-line guide diff and 1,698
selected immutable article lines, with precise span hashes. Its fresh
metadata collector authenticated nine archive members, four internal
hashes, five exact ancillary placements and all 70 original source-label
routes. It checked 2,293 unique labels and 9,282 literal reference
occurrences at the immutable publication. These are the reviewer's
authenticated results; root did not replay that collector.

The separate Part XVI reviewer read 937 current and 316 parent article
lines plus 182 focused diff lines. The root read both complete review
notes and the current theorem/definition interfaces used by the corrections,
derived the positive/empty cases and edited the current host. A third
reviewer independently challenged the complete correction diff and its
retention record. Its exact text boundary and remaining build exclusion
are in `review_horizons_host_corrections.md`.

Root's fresh metadata record authenticates the delivered review files,
before/after host bytes, exact edit diffs, compiled labels and rendered
pages. It is separate from proof certification and does not execute,
import or evaluate any supplied/frozen helper or source array.

## Build and rendering

Root built the committed before-image and the corrected article directly
with TeX Live pdfLaTeX, shell escape disabled, in separate scratch
directories. Each final build used three passes. The before-image has
1,050 pages; the correction has **1,051 pages**. Both final logs have
37 underfull boxes and the expected shell-escape-disabled package warning,
with zero errors, unresolved references/citations, duplicate labels or
destinations, and overfull boxes. Historical MiKTeX diagnostics remain
labelled as historical in the guide.

All 2,293 literal labels keep their original order. All 4,586 ordinary and
cleveref auxiliary label entries keep their displayed numbers. The rebuilt
PDF is copied to the host byte for byte; no auxiliary build files are
committed. Root extracted the affected text and visually inspected final
PDF pages **25, 31, 780–782, 794, 848, 888 and 889**. After the final small
propagation edits, six rendered pages were byte-identical; pages 31, 782
and 794 were inspected again. This is bounded layout verification, not a
page-by-page review of the entire report.

## Arithmetic-complexity boundary

The selected arithmetic and initial-embedding leastness arguments pass
with their explicit class-order and ordinal-coefficient hypotheses. The
fixed-standard-complexity hierarchy is an effective syntax transformation,
not one unbounded semantic evaluator. No paid fixed-arity ordinary-integer
Diophantine computation history is supplied by these results.

The epsilon interpretation/calibrations, general transitive-model
spectrum, truth promotion, varying-G construction, admissible bounds and
unrolling proofs are not newly certified. External priority/attribution,
the whole manuscript and Lean/Rocq formalization are also outside this
review. The fully accounted universal construction remains at 84 operations.
