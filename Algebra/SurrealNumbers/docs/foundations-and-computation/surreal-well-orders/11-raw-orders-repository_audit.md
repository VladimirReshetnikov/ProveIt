# Targeted ProveIt repository audit

Audit target: `VladimirReshetnikov/ProveIt`.
Pinned revision: `ae7c1e6aae3dc58c9c638b35646865ad6c10387d`.
Commit date: 2026-10-03 01:03:53 UTC.
This SHA was verified both from recent-commit search and from the direct `branches/main` endpoint. Code-search results were indexed at the parent `63bb8b1d99359e7188abf0a33fb152e121858150`; every inspected source was fetched afresh at the pinned main SHA.

This is a targeted source audit, not an exhaustive audit or Lean build. No remote files were modified. No already-existing report specifically on lexicographic orders of all class well-orders of No was found in these focused searches.

## Direct precursor

Path: `SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/article.tex`.

This is a 54-page, 2 October 2026 merged report from three independently delivered manuscripts. The README explicitly calls it AI-assisted, unrefereed, and not formalized. None of its labels maps to a Lean theorem. Finite check scripts do not establish transfinite theorems.

Its genuinely general results already cover every infinite linearly ordered set X of cardinality λ:

- `lwo:lem:prefix-free`, lines 570ff: all exhaustive ordinal bijections onto the same X are prefix-free, hence comparison at the first unequal entry is a linear order.
- `lwo:lem:cylinder`, lines 600ff: prefix cylinders are convex and C_s is isomorphic to W(X minus ran(s)); the finite residual cylinder has m! points.
- `lwo:prop:cardinality`, lines 633ff: |W(X)| = |W_λ(X)| = 2^λ, with a lexicographic binary-cube embedding via disjoint pair swaps.
- `lwo:thm:no-long`, lines 837ff: W(X) contains neither λ^+ nor its reverse. The proof stabilizes common prefixes along a purported long monotone sequence, using exhaustion rather than assuming the enumeration lengths are bounded.
- `lwo:thm:ordinal-spectrum`, lines 880ff: every order of size ≤λ embeds into W_λ(X), and the exact ordinal and reverse-ordinal spectra are β<λ^+.

These generic claims apply directly to bounded surreal sign orders as alphabets. Such applications should be attributed as applications of existing repository results, not marketed as new general theorems. The inspected proofs of these core statements appear sound.

Real-specific results elsewhere in the report include fixed-stratum equimorphism to lexicographic cubes with finite tails, coding length c^+, power absorption, point and gap spectra, topology, and finite condensation. They should not be transported wholesale to surreal alphabets: in particular, arguments using that real well-ordered subsets are countable or that real cuts have countable witnesses require replacement.

Section 22, `lwo:sp:sec:surreal`, lines 2946–3004, is an explicit predecessor for bounded surreal orders. It defines S_{<θ} as sign sequences of length <θ, with - < termination < +. Its theorem `lwo:sp:thm:surreals` proves S_{<θ} embeds into W(ℝ) for θ<c^+, while S_{<c^+} does not, despite equal size 2^c. The obstruction is the embedded c^+ from all-plus signs. The proof gives no coherent family of bounded embeddings; indeed coherence would contradict the nonembedding result.

The report carefully distinguishes W(ℝ) from its minimal-type slice W_c(ℝ) and the actual Kanovei–Shelah ultrafilter-enumeration index. Any historical description saying that the latter is literally the order of all well-orders of ℝ should preserve this distinction.

## Foundational precursor

Path: `Algebra/SurrealNumbers/docs/foundations-and-computation/foundations/article.tex`.

Selected useful passages:

- Section 3, `found:prop:proper`: each surreal is a set-coded ordinal sign sequence; each fixed birthday fragment is a set; every set of surreals has bounded birthdays; full No is a proper class.
- `found:prop:allcuts`: unrestricted cut filling is inconsistent, by the cut (whole carrier, empty).
- Section 6, `found:sub:gbconvention`: GB means elementary class comprehension and class replacement with choices separately stated; GBC includes global choice.
- `found:rem:secondsort`: quantification over class maps does not make their totality a class with those maps as members.
- `found:prop:recursion`: local set-valued recursions on set dependency domains can assemble coherently into class functions; this is distinct from arbitrary ETR.
- `found:sub:km`: KM still has sets as class members and does not supply a hyperclass of all proper-class functions.
- Section 7: universe relativization preserves the distinction between small option sets and the larger carrier.
- Section 16: Lean universe polymorphism is a schema, not a term quantifying over every universe.

Do not repeat the article's historical proposal-era implementation status as the present repository status. Current source directories contain substantially more completed-looking arithmetic modules, including SignSequenceField, SignSequenceRealClosed, SignSequenceExpLog, and many others. No compilation was performed in this audit.

## Directly inspected Lean foundations

All paths below are relative to `Algebra/SurrealNumbers/Surreal/Foundations/`.

`SignSequence.lean`:
- `SignSequence : Type (u+1)`, with birthday in `Ordinal.{u}` and zero-extended signs.
- Numerical linear order uses -1 < 0 < 1 at the first difference.
- `ordinalOrderEmbedding`.
- `birthdays_bounded`, `small_strict_upper_bounds`, `not_small`, `small_bounded`.
- `IsPrefix`, `Simpler`, and `simpler_wellFounded`.

`SignSequenceSimplicity.lean`:
- `existsUnique_prefix_of_ordConnected`.
- `existsUnique_minimum_birthday_of_ordConnected`.
- `existsUnique_simplest_separator`, assuming a separator exists.

`SignSequenceCutOperation.lean`:
- actual `cut` from `SmallCutData.{u,u+1}`.
- `cut_realizes`, `cut_isPrefix`, `birthday_cut_le`, `birthday_cut_le_iSup`, `cut_congr`.
- `exists_separator_of_small_sets`.
- DenselyOrdered, NoMinOrder, NoMaxOrder instances.

`SignSequenceBounds.lean`:
- a small set with no greatest member has no least upper bound;
- finite ordinals are bounded without a supremum.

`SizeObstructions.lean`:
- `noUniversalStrictBound`, `noUnrestrictedStrictBounds`, `noUnrestrictedCuts`.
- `SmallCutData`, `HasSmallCutFillers`, `HasSmallStrictUpperBounds`.
- `not_small_of_small_cut_fillers`.

These inspected source declarations provide genuine reusable foundational code, but the new well-ordering-lexicographic claims are not thereby machine-verified.

## Other relevant existing work

`Algebra/SurrealNumbers/docs/surreal/real-vector-space-structure/article.tex`, lines 1392–1403: a class Hamel basis is built using a fixed set-like global well-order and set-initial-segment recursion. Lines 1417–1425 correct the unnecessarily strong assumption of GBC+ETR: GBC suffices for that specific set-valued recursion. This is a useful precedent for a carefully scoped enumeration construction.

`Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/article.tex` develops birthday-enriched structures, interpretations of hereditary-size universes H_κ, and forcing sensitivity. Its README warns that H_κ is not generally V_κ and that the pure-field and birthday-enriched structures have different model-theoretic behavior. This may inform future questions, but it is not needed to prove the order-theoretic core.

## Inspected source inventory and immutable URLs

Source-copy names below identify the audit inputs. The original repository sources are not bundled; use the immutable links to retrieve them.

- Audit input `reals_README.md`; Git blob `02791bdab5c33042588af539c581ca340a5ef6ef`; https://github.com/VladimirReshetnikov/ProveIt/blob/ae7c1e6aae3dc58c9c638b35646865ad6c10387d/SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/README.md
- Audit input `reals_article.tex`; Git blob `137c8601bba6d19cef5747ddc9ad099cbab2bff7`; https://github.com/VladimirReshetnikov/ProveIt/blob/ae7c1e6aae3dc58c9c638b35646865ad6c10387d/SetTheory/Cardinals/docs/reports/ordinals-and-order-types/lexicographic-well-orderings-of-reals/article.tex
- Audit input `surreal_foundations_article.tex`; Git blob `eb7f3e7d98b5ce159608b3097dffcfacd8d55e5e`; https://github.com/VladimirReshetnikov/ProveIt/blob/ae7c1e6aae3dc58c9c638b35646865ad6c10387d/Algebra/SurrealNumbers/docs/foundations-and-computation/foundations/article.tex
- Audit input `SignSequenceSimplicity.lean`; Git blob `3bf0fb22cb5a5c50b05360fd8e5dbeafb104e959`; https://github.com/VladimirReshetnikov/ProveIt/blob/ae7c1e6aae3dc58c9c638b35646865ad6c10387d/Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceSimplicity.lean
- Audit input `SignSequence.lean`; Git blob `e2c093860f29b0b9ea312d50099fc4aa89a76a99`; https://github.com/VladimirReshetnikov/ProveIt/blob/ae7c1e6aae3dc58c9c638b35646865ad6c10387d/Algebra/SurrealNumbers/Surreal/Foundations/SignSequence.lean
- Audit input `SignSequenceCutOperation.lean`; Git blob `478c1e7f603e44032ae180f38bb0601044a94bae`; https://github.com/VladimirReshetnikov/ProveIt/blob/ae7c1e6aae3dc58c9c638b35646865ad6c10387d/Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceCutOperation.lean
- Audit input `birthday_cutoffs_README.md`; Git blob `e2f956a6989efb74fc4d1d3e514bbb683134ca83`; https://github.com/VladimirReshetnikov/ProveIt/blob/ae7c1e6aae3dc58c9c638b35646865ad6c10387d/Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/README.md
- Audit input `birthday_cutoffs_article.tex`; Git blob `63c7ba4a0623d8487a7e2e51c7d9de10e5de4fff`; https://github.com/VladimirReshetnikov/ProveIt/blob/ae7c1e6aae3dc58c9c638b35646865ad6c10387d/Algebra/SurrealNumbers/docs/foundations-and-computation/birthday-cutoffs-and-hereditary-sets/article.tex
- Audit input `surreal_real_vector_space_article.tex`; Git blob `68aa74c57ab92b487188350d21deed7c029d770e`; https://github.com/VladimirReshetnikov/ProveIt/blob/ae7c1e6aae3dc58c9c638b35646865ad6c10387d/Algebra/SurrealNumbers/docs/surreal/real-vector-space-structure/article.tex
- Audit input `SignSequenceBounds.lean`; Git blob `978953964ba0520c96becc3de16932cda2c4c93c`; https://github.com/VladimirReshetnikov/ProveIt/blob/ae7c1e6aae3dc58c9c638b35646865ad6c10387d/Algebra/SurrealNumbers/Surreal/Foundations/SignSequenceBounds.lean
- Audit input `SizeObstructions.lean`; Git blob `02606e2b04ae42d19b723169d3e09f7c18b209ae`; https://github.com/VladimirReshetnikov/ProveIt/blob/ae7c1e6aae3dc58c9c638b35646865ad6c10387d/Algebra/SurrealNumbers/Surreal/Foundations/SizeObstructions.lean

The accompanying article provides full proofs of its stated extensions. The original source files remain available at the immutable URLs above.

