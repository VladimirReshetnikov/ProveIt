# Bounded publication review: definable surreals, Parts II and III

The publication integrates a substantial ambient-definability and enriched-language interpretation framework. The inspected interfaces do **not** supply an ordinary-integer evaluator, fixed-arity arithmetic certificate, or paid universal polynomial. I found two incomplete notation renames and one editorial proof-status inconsistency. These are recorded below without treating them as counterexamples to the underlying constructions.

This review covers immutable commit `c7d65e30b2935224e8ad7ff32a0aaf208d7d5e16`, parent `7389d7de4cec2bf27f0c882e00f26ecc7acc5c83`. The host is `Algebra/SurrealNumbers/docs/foundations-and-computation/definable-surreals-and-omnific-integers/`.

## Exact read and authentication scope

I read the **entire changed guide diff: 388 raw diff lines**. For the article, I read the first 191 raw diff lines, covering the small pre-Part-II editorial changes, and the following **21 exact after-source spans, totaling 3,138 lines**:

`1–265; 3220–3355; 3871–4250; 4252–4366; 5531–5665; 5731–5821; 5973–6081; 6611–6660; 7589–7670; 8134–8167; 8315–8596; 8995–9101; 9199–9258; 9523–9694; 9771–9948; 10029–10078; 10137–10590; 10701–10778; 10830–10990; 11310–11427; 11600–11680`.

These spans cover the publication provenance and notation; countable ordinal codes and their completion interface; the finite-ring retraction; the real decoder and its section criterion; the canonical-absoluteness statement; the set-sized certificate/Levy-hierarchy argument; native omnific arithmetic; selected support recovery; the complete powerset/graph-interpretation and Hahn-summation interfaces; coefficientwise operations; the finite-syntax/length and elementary-theory discussion; and the newly credited open proof obligations. They do **not** cover every proof in the newly inserted Parts. In particular, the detailed normal-form/sign-limit proof at 9259–9522, most forcing proofs, strong-stabilizer proofs and numerous parameter/field classification proofs were not reviewed here.

I read the earlier `review_definable_operations_de37a66d1.md` as context and a scope ledger. Its original manuscript-read coverage is **not** inherited as new coverage of this publication. The present JSON pins that earlier review and every current read span separately.

The full applicable `Algebra/SurrealNumbers/AGENTS.md` and incoming retention-rule context at `docs/incoming/README.md:420–445` were read; the read working bytes were verified equal to this immutable snapshot. Unproved claims must remain credited questions, and demonstrably wrong claims must remain with their failure or counterexample. This review preserves the exact problematic wording and distinguishes status corrections from mathematical refutations.

All three changed files have before/after Git blob IDs, byte sizes, SHA256 values and raw-diff pins in the receipt. The article's full 8,236-line raw diff is hashed, but only its stated initial 191 lines were read as a raw diff; the rest of the human article coverage is the source-span list above. The PDF is authenticated **as bytes only**. No build, rendering or 160-page claim was independently verified.

## Provenance and structural checks

The three original archives were read as inert Git ZIP bytes, with all 17 members CRC-checked and hashed:

| Source | Arrival archive | Members | Archive SHA256 |
|---|---|---:|---|
|02|`2faa3b37a:docs/incoming/definable_surreals.zip`|5|`7d6f05588441d0a164cec62c13233695f701af902dcb7bf904e89f4e8de7a4ab`|
|05|`2faa3b37a:docs/incoming/definable_surreals_real_parameters.zip`|8|`cdfb6d6b86e57119c7c1e095f10ae45340bd2433b621064ce79d02976e7e0238`|
|06|`de37a66d1:docs/incoming/definable_surreal_operations.zip`|4|`9c3fcd5b94b3c17234332dedd7e7075506ea988feb287117342e674daa0dfa9e`|

All seven retained ancillary files are **exact byte matches** to their archive members, both at placement `47a77daba` and at this publication: source 02's two programs; source 05's audit, Makefile, program and recorded JSON; and source 06's proof-status text. The source 05 delivered seven-entry checksum manifest also matches all seven named members. This authenticates the delivered recorded results; it does not independently reproduce the reported tests. No delivered program, script or build target was executed or imported.

The article has 346 distinct literal labels: all 139 earlier labels survive in their original order, plus three Part labels and 69 `dsn:rp:`, 53 `dsn:ca:` and 82 `dsn:op:` labels. These are source-label counts, not generated cleveref/auxiliary entries. All 820 parsed internal reference occurrences resolve, representing 249 distinct referenced labels.

The collector routes all 198 source-label occurrences. Source 02's 61 and source 06's 72 resolve through the stated prefix/old-prefix normalization. For source 05, 51 of 65 resolve directly; the remaining 14 are recorded as the publication's explicit editorial many-to-one/background routes, whose target labels exist. This is not a claim that every merged proof body is byte-identical or independently certified. A limited literal shared-counter simulation checks the claimed section offsets for all 80 labelled theorem-like statements from sources02 and06; it does not substitute for a TeX build or certify unlabelled numbering.

## Findings retained at the immutable publication

**D93-1 — the promised band-exponent rename is incomplete.** Article 4283 says source 05's `e_n(a)` becomes `b_n(a)`. README 595 and article 8329 repeat “here `b_n(a)`,” and the new completion proof at 6074 uses `omega^{b_n(alpha)}`. But the actual defining band equation at 5744, code 5749, bound 5768, proof 5774/5782 and finite example 5814–5815 still use `e_n` and `e_0,...,e_3`.

The original definition is

    e_n(a)=2^(-n-1)+2^(-n-2)*a/(1+a).

Thus the intended function is clear, but the new proof's symbol does not match the defining block. Complete the promised rename **only within source 05's band-code block**; keep the source-symbol column and historical audit quotation, unrelated formula codes `e_n`, and Part I's `e_beta` distinct. This is a notation/provenance correction, not a failure of the band inequalities or inverse formula.

**D93-2 — two Prikry exponent references retain the old name.** Article 6645 defines

    e_{kappa_n}=Omega(-(kappa_n+1)), y_n=Omega(e_{kappa_n}),

but6649 and6651 call the exponents `e_n`. Those two sentences should refer to `e_{kappa_n}`. The selected local summability and interval argument is unaffected once the symbol is made consistent; I did not independently certify the preceding forcing input.

**D93-3 — the new cost-status summary overstates its own recorded status.** The newly written Part I note at 3344–3349 lists answered syntactic-cost results “with an additive description-length bound.” The new Question 42.14 at 11337–11347 instead asks for the precompiled formulas, accounted constant and full proof of that bound, identifying missing variable-capture/constant-reference accounting. The inherited contribution ledger at 11405–11408 likewise combines level preservation and literal length under “Extension.”

For consistent status, distinguish the Levy-level preservation result from **source 06's proposed length bound and credited accounting question**. A dated clarification should retain the original phrase “with an additive description-length bound,” explain its scope and point to Question 42.14. This is not a proof that the bound is false or impossible. The publication's guide already labels these claims as unproved questions; the issue is its inconsistent new article summary.

## What the inspected interfaces establish, and what they do not

**Countable codes are semantic omnific objects.** The slot code in 5531–5665 and separated-band code in 5731–5821 put an arbitrary sequence of ordinals into the exponents of one countably supported omnific integer. Their elementary inequalities separate the bands, and the inverse `v/(1-v)` recovers each ordinal-valued coefficient parameter. Normal-form extraction and Replacement recover the whole sequence. These are not bounded ordinary integer encodings: an input entry can be an arbitrarily large ordinal, and the code uses an infinite support and the Conway omega map. The completion theorem explicitly requires ambient stability under fixed set-theoretic formulas; field arithmetic and countable sums alone are not asserted to generate it.

**Finite polynomial equations transfer only in the stated pure-equation language.** At 7589–7654, the constant-term map is a ring retraction to ordinary integers. Applying it coordinatewise transfers finite systems of polynomial equations with integer coefficients. Nonvanishing, order and positive-witness conditions do not transfer automatically. The text itself gives `X²=2Y²` with nonzero omnific solution `(sqrt(2)*omega,omega)` but no nonzero ordinary-integer solution. Likewise the native order formula at 9798–9803, `(b-a)q²=p²` with p,q nonzero, uses the real-closed omnific fraction field. It is not an unchanged ordinary-integer graph for order; `a=0,b=2` would fail there. The report also explicitly separates quotient/remainder definability from termination of repeated division.

**Set-sized certificates are not finite computation tables.** The canonical-operation graph discussion at 9523–9694 uses Collection to package a set-sized well-founded diagram and its local witnesses. A certificate can be infinite or transfinite. Its Delta1 classification is in the Levy hierarchy of set theory. The source expressly denies a resulting finite-description algorithm or optimal symbol/proof-length bound. The normal-form existence/sign-limit input remains a mathematical dependency; its detailed proof was outside this read scope.

**One omnific coordinate is not one finite integer witness.** The quotient interpretation at 10137–10421 uses exact coding of every subset and relation on a reverse-well-ordered support. Quantifying over these codes expresses actual well-foundedness, then a set-sized Mostowski collapse gives the represented set. The compressed single monomial has potentially transfinite information. Over ZFC the quotient covers all sets; the stated ZF reading covers hereditarily well-orderable sets. The syntax translation is effective for each fixed formula, but no truth evaluator or canonical global representative selector follows. The article correctly retains the missing bi-interpretation/comparison-map question.

**Hahn sums and Hadamard multiplication retain their extra semantics.** The summation interface requires the whole set-indexed family code, a reverse-well-ordered union support and finite coefficient fibres. Its fixed first-order formula represents partial-sum families; it is not a fixed list of paid ordinary scalar additions. The coefficientwise theorem separately defines Hadamard multiplication and contrasts it with ordinary convolution. No finite ordinary-integer implementation, variable-width representation guard or arithmetic ledger is supplied by these definability formulas. The earlier finite-integer implementation bottleneck therefore remains.

**The elementary-theory and diagonal scopes are properly separated.** The selected proof at 10875–10966 uses formula translations and absolute old graph codes; the new equal-height observation correctly explains why nested elementary inclusion then forces equality of the transitive models. This does not trivialize the different-height or elementary-equivalence statements. The diagonal argument at 10967–10990 excludes a total definable self-evaluator enumerating all definable total unary functions; it does not exclude ordinary partial universal computation.

The selected interface arguments preserve these domain distinctions. Apart from the three editorial findings, I found no concrete error in the elementary interfaces read. This is not a certification of the full manuscript, external set theory, transfinite normal-form machinery or every cross-report priority/dependency claim.

## Execution and final scope

Executed only fresh metadata code, immutable Git reads and inert text/ZIP processing. No archived, supplied, committed, frozen or copied predecessor helper was executed or imported; no TeX/Lean/PDF build ran; no repository or Git state was changed. The original scripts, recorded results and publisher build/test claims remain separately attributed evidence.

Collector: `/tmp/collect_definable_publication_c7d65e30b.py`, SHA256 `e4548fa1641ee7e58c083dd11fb2f0ac81ce048901862f26a7bbd0b494c88c41`.

Receipt: `/tmp/review_definable_publication_c7d65e30b.json`, SHA256 `47e29c2276d241a8dd7cc14b5ee2a0e53e0ac6e8f3881cadd3db3108143ab7a7`.
