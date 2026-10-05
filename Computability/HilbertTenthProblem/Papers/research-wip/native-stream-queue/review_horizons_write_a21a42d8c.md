# Bounded horizons publication review at a21a42d8c

**Result: source/placement/locator authentication passes; the new arithmetic summaries need three narrow scope corrections.** The selected arithmetic and effective-interface proofs pass within their explicit hypotheses. The guide overextends multiplication to arbitrary finite-support powers and drops hypotheses from two other summaries; the multiplication overextension also appears in the article's notation table and PartXVII introduction. The printed theorem statements and proofs retain the relevant restrictions. This is not a certification of the whole new Part XVII.

The immutable publication is `a21a42d8c27f62ac3443393f88adfeb3d5f6f265`, parent `5a69916e8d753a2cbfab5afa9fa9c22cda0971bd`. Host: `Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/`. Root alone owns repository changes. This review describes the immutable publication before any later corrections.

## Retained arithmetic summary findings

1. **Multiplication scope.** Guide lines944–946 say “normal-form addition and multiplication of the points of the hereditary order `𝖤` (and of every `Ω^{[B]}`)”. Article1338–1341 similarly says “Normal-form addition and multiplication of points of `𝖤` or `Ω^{[B]}`”. Root also located the same overextension at article58919–58922: “multiplication of the points of `𝖤` and of every `Ω^{[B]}`”; I independently read and confirmed that immutable occurrence. Theorem XVII.5.1 extends **addition** to every such power; Theorem XVII.5.2 states **multiplication on the hereditary order `𝖤`**. For `B=2`, the point Ω belongs to `Ω^[2]`, but multiplying its predecessor order by itself gives the whole order `Ω²=Ω^[2]`. A well-order cannot be isomorphic to a proper initial point-cut of itself. Thus multiplication does not in general remain a point operation of that same fixed power. The correction is to state addition and multiplication on `𝖤`, then separately extend only addition to points of every `Ω^[B]`. This is a defect in three editorial summaries, not in the printed arithmetic proof.

2. **Set-likeness hypotheses.** Guide949–950 presents the criterion without the actual theorem's assumptions “A has at least two elements and B is nonempty” (article59604–59611). For `A=1`, `B=Ord+1`, the power is1 and is set-like, but neither listed alternative holds. Independently, `A=Ord`, `B=0` gives the set-like singleton `A^[0]`, again with neither alternative. Both omitted restrictions matter. The complete source theorem and its proof are correctly qualified.

3. **Set-base collapse.** Guide950–951 states `a^[Ord·B] ≅ Ord^[B]` without the corollary's assumption that a is a **set ordinal at least2** (article59645–59651). With `a=1`, `B=1` it would assert `1≅Ord`. Retain the actual corollary's premise. This is likewise a guide omission, not a source theorem counterexample.

These original clauses and counterexamples are retained under the incoming standing rule. `/tmp/horizons_a21_arithmetic_replacements.txt` gives exact replacement wording and proposed numbered review-remark content. The article's existing theorem numbers need not change. No assertion is silently deleted or promoted.

## What was newly read and challenged

The full **557-line raw guide diff** was read, including front matter, source routes, notation, claims/nonclaims, formalization status, execution disclosures and review provenance. The whole article diff was hashed, not read in full. The selected immutable article spans are:

| Inclusive article lines | Scope |
|---|---|
|1297–1401|Source36 notation dictionary and renamings; the multiplication-summary finding|
|2600–2685|Delivery/pin/status and editorial choices|
|58835–58898|PartXVI review/status text and new independent-check account|
|58906–58944|PartXVII introduction, including the third multiplication overextension|
|59198–59236|GB/class-order conventions and start of localization|
|59590–59690|Complete set-likeness criterion/proof and set-base collapse/proof; start of hereditary grammar|
|59702–59748|Finite shape versus ordinal labels; relative evaluation statement and start of its proof|
|59800–60185|Tower proof, full least-fixed-point proof and initial pre-fixed-point extension; complete addition/multiplication proofs; finite-support transfer definition/proof and its qualifications|
|60892–61282|Inaccessible-height model and correctness; horizon statement/proof with inherited epsilon premise; full partial-truth/filter, complexity hierarchy and no-uniform-evaluator arguments|
|61640–61860|Tail of unrolling discussion, formalization contracts, module-status and start of the notation demonstrator audit|
|62011–62140|New PartXVII answers/status, credited dependencies and review limits; surrounding source handoff|
|71092–71180|Source36 statement/question crosswalk and surrounding bibliography handoff|

This is a **1,698-line union**. Partial proof reads in the table are not counted as complete proof certification. Each span is hashed from immutable original bytes with original line terminators. Navigation searches add no proof coverage. Applicable `Algebra/SurrealNumbers/AGENTS.md` was read fully, and incoming retention rule426–439 was read at this publication commit.

The stronger leastness Note XVII.4.B passes: replacing the supplied fixed-point isomorphism by an **initial embedding** still maps the empty code to the least point, gives initial images of constants, and keeps every finite-height composite initial. Compatible finite-node evaluations give one elementary class map; no arbitrary class-recursion or comparison principle is introduced. This matches its explicit credit to source34 rather than creating a new unqualified comparison theorem.

The normal-form arithmetic proof remains relative to ordinal coefficient operations. Addition discards lower digits, adds the coefficient at the leading exponent by ordinary ordinal addition, and explicitly identifies its range with the final segment. Multiplication partitions coefficient-multiple intervals and uses successor-versus-limit behavior of an ordinal coefficient; it then combines the positive exponent terms in the hereditary grammar. These are isomorphisms of represented initial orders. They are not ordinary finite-integer evaluators for arbitrary ordinal labels, and they do not establish normalization of arbitrary powers.

The effective hierarchy is also correctly scoped in the body. The ambient model is `V_kappa` for strongly inaccessible kappa in external ZFC, with a named enumeration G. External countable sequences of its elements lie in the model, which makes the no-descending-sequence filter externally sound. Transitivity alone would not suffice. For each **fixed standard** complexity n, partial satisfaction and the validity test are formulas with the appropriate unbounded quantifiers. The map taking n to a formula is an effective syntax transformation, not a single semantic evaluator. The supremum defining h_n uses `alpha+1`, so the displayed strict complexity increase is justified. The no-uniform-evaluator argument then uses the stated horizon bound; the epsilon-term interpretation and general spectrum proof feeding that bound were not independently certified here.

The demonstrator remains a restricted natural-coefficient comparator/constructor interface, with no addition or multiplication API. Its reported successful runs, Windows encoding failure, time/size counts and build outputs remain attributed author evidence. No delivered program or build was run. The finite syntax still needs a representation/comparison interface for arbitrary ordinal labels, and no read passage supplies a fully paid fixed-arity ordinary-integer Diophantine compiler or an operation-count improvement.

## Immutable publication, archive and routes

Exactly three host files change. Their after-images are:

| File | Git blob | SHA-256 |
|---|---|---|
|README.md|`5f37bf69b60d85b282dd568bbadae43df1764e7d`|`1c53dedd147abd02d974265dc800f5f3d63eb62f6747f0ee7658f2d8b2dff7bc`|
|article.tex|`94dc646dac6942c82eb0f12f7a8ee75b8c8a011a`|`a5108202c9094a511f2e628318f8c5f54da9b3b116fe9e8c804fa0c16577d9c5`|
|article.pdf|`a369a06ac6dae3b9b3a019eefc5f3237f4c1be35`|`3d0ccbd8917985a74e159f05a4ac19599dac191d71ce4def17f28f97fb3c65aa`|

The receipt binds all six before/after blobs, both exact textual diffs and the selected spans. The PDF is hash-only; its reported1,049 pages and rendered correspondence were not checked. This commit genuinely adds PartXVII: there are17 ordinary part declarations rather than16. The earlier6571 placement had left the host guide/article/PDF unchanged; this new review does not conflate that placement with the present body publication.

The original ZIP at arrival `d7cf7d5547a50a6cf372f2cfaad96e950a68c03a` is `docs/incoming/Beyond_Ord_Research_Package.zip`,715,002 bytes, SHA-256 `a598178e496417cdaf982e387d72aad9ca954778296ea70c51e684f69d3acd12`. Fresh metadata code checks its nine distinct safe regular members, CRCs and all four `DOCUMENT_CHECKS.json` hashes. Every member has a byte length, SHA-256, Git-content hash and coverage description in the receipt. The five ancillary placements remain exactly equal to the original archive members and to their first-placement bytes:24,944 bytes total. Archive programs are treated only as bytes.

All70 original source36 labels have one uniquely prefixed host locator. The full host census changes from2,188 to2,293 unique literal labels, with no lost labels:81 new `swo:hn:` labels,23 `swo:xvii:` labels and the new Part label. All9,282 reference occurrences matched by the documented literal regex resolve to1,892 distinct targets; the101 bibliography keys cover the572 matched citation occurrences. These are source-level locator checks. They do not independently reproduce TeX counter expansion, unchanged rendered theorem numbers, complete body equivalence or the publisher's unshipped `coverage97.py` line comparison. The source's42 statement environments and10 question environments are consistent with the52 crosswalk entries, but the whole proof body is not recertified by that count.

## Prior reviews and new corrections

The complete prior intake and placement review notes were read as scope records. The source36 intake, SHA-256 `7880fae84e37d3b772b98941bf897787fb3994094ed3c3248d848f2d3fdf25b3`, records1,879 manuscript lines and explicitly excludes the full epsilon/spectrum/truth/variation/unrolling proofs. The new guide accurately preserves those main exclusions. The ancillary-placement review, SHA-256 `813394cedd7fa649ceef5ffa50b7f3a6f6328ddd86356a67b156e30857aa404e`, adds byte authentication and finite-interface reads, not a PartXVII publication audit. Claims about the placement author's hand recomputation are attributed to that author, not to this reviewer.

The earlier PartXVI GB review is pinned at `f79d9caf8a3d51c9b7850d8833b04650ea7f6d60dca26bf847bfa3f019c027e6`, and the publication review at `0c584cb04115c93ca476b1dc8f93a6f5551b23412597960105e34cdb6d21861c`. Both were read completely as inherited scope records. They are authenticated at root's context commit `45cb4552af638a55dc555e98bae284950c13befb`; the former and the6571 review are absent from the immutable incoming publication tree. Thus an incoming branch's omission of those citations is not itself evidence that its authors ignored files present there.

Three already recorded PartXVI editorial discrepancies survive from this incoming branch's parent: “2,468 manuscript lines” instead of1,665 manuscript plus803 other archive lines, Mathlibv4.31 instead of the pinnedv4.32, and the early guide's working-directory output sentence instead of the source35 script's beside-script path. They are inherited findings from the earlier review, not newly discovered mathematics or evidence that earlier corrections were never made elsewhere. Their old wording remains recoverable in both immutable publications and the prior review.

Pascal's separate frozen review is `/tmp/review_horizons_xvi_corrections_a21a42d8c.md`, SHA-256 `7060ea9d136a3623ae431083f84f07b844b4073b8774c14c4b173f8946d2d4ca`; its scope JSON is `730fd2fd8d61d9c92f4720c4cd729b702c70738001ec1de54057f85075f91216`. I authenticated both and read the full review. His937 current/316 parent article lines and182 focused diff lines are separate evidence, not added to my own coverage count.

It finds that the GB completion theorem remains sound after the Tm-to-T typo and dependency-summary correction. The nonempty-Gamma correction to XVI.5.24 is substantive: an empty schedule and singleton W give an exact tower but lie outside the printed canonical-history definition. Two later proofs still need explicit trivial branches before using the tower/history correspondence: XVI.5.29 must handle the empty schedule; XVI.5.31 must first handle empty W and then empty Gamma. The preceding source33 conditional-converse proposition likewise asserts a tower outside its printed domain at empty W; its statement needs the nonempty-W restriction, while the larger endpoint embedding assertion handles empty W trivially. The intended nonempty conclusions survive. These are attributed conclusions of his separate immutable-span audit, not a fresh complete dependency proof by this reviewer.

This new evidence explicitly qualifies our earlier broad PASS on the digit-map/converse chain; the frozen earlier notes remain unchanged historical evidence of the missed empty-domain cases. It does not refute the GB completion proof or justify declaring the whole report false. The updated incoming text's own unshipped independent-check account is an author report and cannot replace those remaining domain checks. No full review of PartXVI's truth/spectrum results or the present4,160-line article change is claimed here.

## Remaining limits

Unreviewed epsilon grammar/interpretation, exact external epsilon/zeta calibration, general transitive-model spectrum, truth promotion, varying-G construction, admissible bounds and full unrolling retain their source status. Selected downstream deductions above are conditional on those inherited results where used. No external bibliography, historical priority, Lean/Rocq declaration, PDF build or rendered page was certified. Research questions and the two marked conjectural commentary sentences remain credited questions.

Only the newly authored metadata collector ran. It reads immutable Git and ZIP objects and writes an exclusive `/tmp` receipt. No supplied, archived, committed, frozen or copied predecessor code was executed or imported; no repository or Git state was mutated.

## Final metadata validation

Fresh writer, normal Python and optimized Python exact-receipt checks from `/` passed before freeze. Use the new collector with `--repo` pointing to the checkout and `--expect` pointing to this receipt; it always reads the fixed commits above, not mutable host files.

* `review_horizons_write_a21a42d8c.py`: SHA-256 `55bd120fe386b0d74e059c643bb1fda7504c76edb08869471aa09a4b7616a810`.
* `review_horizons_write_a21a42d8c.json`: SHA-256 `754c241e8c2e1d177eddeee672ee0b993ecd1796d6af3d56dc2e3e1c9c8fd858`.
* `horizons_a21_arithmetic_replacements.txt`: SHA-256 `3f88896af016e3863d41ef2b02db76d24a5722a949d971fcdf8b59bea0e45003`.
