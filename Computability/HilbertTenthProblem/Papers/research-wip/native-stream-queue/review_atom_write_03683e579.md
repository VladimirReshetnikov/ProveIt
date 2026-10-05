# Atom actions and commuting injections: bounded Part III publication review

**One guide-provenance correction; the checked mathematical interfaces pass.** This review concerns immutable commit `03683e579fd54a681ad649bd659cc51b1f450829`, parent `a21208b3ff14a07a4c8318dbf916d543acbef043`. It changes exactly the README, article TeX and article PDF of `SetTheory/Cardinals/docs/reports/ordinals-and-order-types/naming-elementary-embeddings/`. Part III is now present in the article, unlike the earlier ancillary-only placement. This is a selected proof/interface review and a complete label/byte inventory, not certification of every merged proof or of the publisher's full union claim.

## 1. Retained finding and proposed correction

The immutable README, lines 438–439, says:

> No review of Part II's or Part III's manuscripts exists there.

This is false for Part III. At this very commit, `Computability/HilbertTenthProblem/Papers/research-wip/native-stream-queue/review_new_actions_26e036956.md` is already present. Its SHA256 is `55d864059205571c3eeab0d7522c72eaf7ea064c692fa9672dd10a7adc8b0a37`. It records a complete proof read of the commuting-injections manuscript and selected reads of the atom-actions manuscript. The separate `review_atom_injection_placement_27f200305.md`, SHA256 `b071eb84f7cf67c7ae508c591569637f3843f5c6cfc157e37821368a824047d5`, authenticates the seven ancillary placements. Neither is external review or formal verification, and neither gives a complete atom-actions proof certification.

**Review remark 1 (4 October 2026).** Retain the quoted incorrect sentence and identify those two existing reviews as its counterexample. Replace the active summary by: “No Part II manuscript review is identified here. Part III's sources were subsequently reviewed in `review_new_actions_26e036956.md`: the commuting-injections manuscript received a complete proof read, while atom-actions received the selected interface reads listed there. `review_atom_injection_placement_27f200305.md` separately authenticated the ancillary placement. These are scoped internal reviews, not formal or external certification.” This preserves the distinction between source mathematics and placement authentication.

No analogous “no review” claim was found in the article. Its line 237 accurately describes the earlier Part I review. The Part III provenance subsection is at lines 2643–2674; it credits source-internal reviews without making the false repository-wide absence claim. This finding calls for a guide correction, with no mathematical article or PDF correction. It is recorded against immutable bytes regardless of subsequent root-owned edits.

Subsequent repair: root's separate commit `6d06f8952c7a061bbab8612f7f67a2e6bf5080ad` corrects the guide and retains the old clause in numbered Review remark 1. Its short guide-only diff was read and matches the scope above; it makes no new Part II or whole-atom-review claim. This does not alter the receipt's immutable `03683e579` checkpoint.

The incoming standing rule was read at `docs/incoming/README.md`, lines 414–440: wrong claims remain with a numbered counterexample, and unproved claims remain as credited questions. The new article appropriately preserves the parameter-free-countability issue as prose plus Question 37.17 rather than silently deleting it. No applicable `AGENTS.md` exists on the destination's ancestor paths at this commit.

## 2. Source and placement authentication

The new files are:

| File | Git blob | SHA256 | Bytes |
|---|---|---|---:|
| README.md | `9934c736231bce1a4bb8de2e53462756ca086b4b` | `b23cc0e7136f59cbb4bdd7777354ad8e1800a7a1c6a186e5dd78348852b994b0` | 60,997 |
| article.tex | `41ce279212b15a0cd86ff8761c8041773b96b0c7` | `60db7b0c329105abdd6d092a7f326adb6f3b8815ac27db0f151f9be76077a153` | 451,431 |
| article.pdf | `79acc36e185b81ca89476b8ec64f68b575df291f` | `4c99795043a0aba980139b455b9dcf628a30de063543b2b86c35dfed37c4a8c7` | 1,249,345 |

The old three host files are byte-identical at the manuscript pin `715a716a3002b1e9f28daa2d81c009a392851b94`, placement `27f2003053ae8f4f6bbccdc70b9e2dcb70b40238` and this write's parent. Thus the before/after comparison uses the actual common Parts I–II source.

Both retired archives were recovered from arrival `26e036956381b07bb43de0187965f8dcdf9194fb` and matched to the placement's parent. Their unchanged hashes are:

- `atom_actions_research.zip`: `c7f96e8905fb0da490c3960b0afdb6bde92fcb96673782ebfc1a2c1a160ce264`;
- `commuting_injections_research.zip`: `15d35b3a01bddc25a3fc47f4f39b262789d5f91928a91a566987f198371b0433`.

Fresh metadata checks authenticate all 14 regular archive members and all eight atom-manifest entries. The seven code/data/figure placements remain exactly equal to their original members at placement, write parent and write commit, totalling 228,956 bytes. The receipt lists every mapping, byte count, blob and SHA256. No program in those files was executed or imported.

All 146 old labels remain. The article has 284 distinct labels: 73 new `nee:aa:` and 65 new `nee:ci:` labels. Every one of the sources' 45 and 51 labels has an existing target. The two source-04 equation labels `eq:necklace` and `eq:infinitecount` correctly route to the corresponding `nee:aa:` equations; the other source labels use their own prefix. These 96 routes establish locator availability, not whole-body or clause-by-clause equivalence. The receipt records their original and current line positions, all 60 literal source-credit lines, and the exact text-diff hunks.

All 782 parsed local reference commands, containing 839 targets, resolve. All 92 parsed citation commands, containing 111 keys, resolve to the 23 bibliography entries. These are source-text checks, not a TeX build or a guarantee about rendered numbering. Actual part commands occur at lines 185, 1129 and 2409. The PDF was authenticated as bytes only; its claimed page count, rendering and build warnings were not checked.

## 3. Mathematical and computational scope

The finite-path and rooted-code proofs checked here respect the internal/external boundary. A finite signed-word evaluation is a formula in the expanded language; it does not require the whole infinite component graph to be an internal set at the finite atom cutoff. Equality-diagram rooted codes are pure real parameters, and component-isomorphism arguments justify their use. A transitive-closure membership code used in the all-object theorem can be a large pure set: it is not asserted to be a finite integer or necessarily a real.

The atom-kernel theorem distinguishes atoms appearing in uniquely definable objects from individually definable atoms. The added notes retain the pure-real-parameter qualification and the finite-cutoff distinction between whole type blocks and centralizer orbits. The finite-cutoff all-object fixed-point theorem uses a specific membership-diagram construction; it is not an appeal to the invalid general principle that every automorphism-fixed object in an arbitrary structure is definable. The ordinary-definability and larger-cutoff questions remain explicitly open. The parameter-free-countability discussion correctly exposes its outer satisfaction/countability requirements.

The effective presentation theorem is a finite-input result: an integer relation matrix determines a rational nonnegative cone, its span, and unit certificates; rational linear algebra and finite support enumeration suffice. The nonnegative-relation/Farkas argument supplies integral positive relations after clearing denominators. This does not decide arbitrary cardinal/cofinality data of an action or compute arbitrary real rooted codes. The article retains the bit-complexity and verified-implementation problem as a question.

The checked fixed-action Replacement proof uses whole small type blocks and an internally definable type-selector. At the finite cutoff its additional finite-component premise is essential and is explicitly addressed. The universal theorem separates finite, countable and continuum supplies of types under a finitely generated commutative presentation. Its negative constructions retain the fixed-cutoff and ambient-Choice hypotheses. The forcing theorem distinguishes new types for a fixed presentation from the verdict for a fixed ground-model action; its finite-data argument for rank at most one and real-code argument for higher rank have no new gap in the selected read.

These results do not give a paid fixed-arity ordinary-integer Diophantine compiler, nor an operation-count improvement to the universal-polynomial frontier. A decision algorithm for finite monoid presentations, pure real/set parameters, and cardinal scheme criteria are different interfaces. The article says that the proposed formalization stages are not implemented. Author-reported program reruns, finite enumerations and PDF builds remain attributed claims here; they were not repeated.

## 4. Exact read scope and limits

The companion receipt hashes every declared span as exact source/diff bytes. New human reading covers:

- the complete 634-line guide diff and complete write commit message;
- article diff lines 1–127, covering preamble and earlier-Part editorial changes;
- article source lines 217–253, 2409–2810, 2874–3265, 3919–4087, 4628–4940, 5162–5384 and 5623–5674: 1,588 selected lines in total;
- both earlier bounded-review Markdown files in full;
- the incoming retention-rule span above.

The earlier intake's full commuting manuscript read and selected atom manuscript read are inherited with their exact original scope. In particular, that intake's unread atom monoid-classification/common-power proofs are not promoted to a full certification here. The current selected reads add focused scrutiny of merged kernel, effectivity, Replacement, forcing and trust-boundary interfaces. The intervening localization/type-enumeration proofs, full reflection/Collection developments, every Appendix item, all source-to-merged-body correspondences and external literature have not all been reread. No claim is made to independently certify the publisher's assertion that every source clause is preserved.

Fresh metadata code completed the writer and exact normal/optimized replays from `/` before freezing. All recorded inventories, pins, routes and local-reference checks passed. Only this newly authored read-only checker executed; there were no supplied, archived, committed, frozen or copied predecessor executions/imports, no builds, and no repository/Git mutations.

Helper SHA256: `7cdbf7d9b345ef2e65bf3443dd77caf72c37665f274a7833a72c032bf8f14307`.

Receipt SHA256: `2ef971e67211e1df3bbdc202ba293a1e5fd33cf9180b9111c9aa5e0bf84e85d9`.
