# Bounded catalogue review at cd514f61b

**Review complete: four corrections recommended.** The catalogue preserves the major proof-status and arithmetic-interface boundaries, and every checked link resolves. Its collection count omits one completed report already in the same tree; three summaries also need more precise wording. No report program or supplied cross-reference checker was executed, and no repository file was changed.

Reviewed immutable commit `cd514f61bcefc92c2e30fb6325a595b2f94eb129` against parent `de37a66d1aa2cbb081de2c7e951fce9315054b41`. All changed text hunks in all 14 text files were read, including both manifest diffs, all README diffs and both FORMALIZATION inventory updates. The two changed PDFs were hashed only. The companion JSON lists all 16 changed paths, blob IDs, byte sizes, SHA-256 hashes and exact before/after hunk spans, plus separately hashed supporting-read spans.

The applicable `Algebra/SurrealNumbers/AGENTS.md` was read in full. The incoming catalogue procedure at the reviewed commit was read at420–480. The later standing rule at `5fefff6567ac7c727041bc3fb326967fc12e2182`, incoming README426–439, says unproved and wrong claims are never dropped. Accordingly the original wording and the reasons for correction are retained below. Proposed replacements repair the summaries and restore an omitted report; they do not erase source claims or silently promote open questions.

## Findings, with the old wording preserved

### C1. Different ant cost models described as a reduction

Collection `manifest.tex`4408–4411 says:

```tex
sentinel-decoded side words (Report~44, a recovered edition); its literal
source shrinks from 2{,}307{,}457 operations with prescribed coefficients
to 14{,}658{,}934 from the literals 1 and~3 (Reports 47 and~48), and
further in later programme packets.
```

The exact source line has `Reports 47 and~48` as printed; the surrounding paragraph explicitly specifies the two conventions. The defect is “shrinks from ... to”: 14,658,934 is larger than2,307,457, and the two counts charge different operations. The report's README103–117 instead records a literal-only dense-prefix cost554,386,261,710,212,588, reduced to31,388,831 and then14,658,934. State2,307,457 with prescribed coefficients separately, and describe the reduction within the literal-only grammar. The final ordinary-input warning in the catalogue is correct and must remain.

### C2. Replacement criterion and universal quantifier compressed away

Collection README793–797 says:

```text
(Yao's urelement kernel models after finitely many canonical elementary
atom lifts are named: Replacement holds exactly when the small component
types are few, one name is harmless iff `cf κ > ω` and two or more iff
`cf κ > 2^ℵ₀`, a CH characterization at `ℵ₂`, and exact Collection and
reflection criteria).
```

The report's stated criterion (README44–58) is the cardinality of the **union of small component-type blocks**, not merely the number of their types: for κ>ω this union has cardinality<κ; at κ=ω both that union and every component must be finite. Its cofinality thresholds quantify over **every** expansion with the indicated number of names.

The distinction is substantive. At κ=ω a bilateral shift on the atoms ℤ has no small type block but an infinite component; iterating the named shift on one atom over the pure set ω would require an infinite atom-supported image, excluded from the finite-kernel model. Thus “few small types” alone does not suffice. Conversely, naming the identity adds only a definable symbol and preserves Replacement even when cf κ=ω, so the individual-map interpretation of “one name is harmless iff” is false. Preserve the union bound, finite-component condition and universal quantifier. The manifest's longer entry already preserves the universal-expansion and κ=ω provisos.

### C3. Almost-sure and computability scope of hat surplus

Collection README809–813 says:

```text
(Eldredge's infinite binary hat game: a computable strategy with surplus
`log₂ n + O(1)` and, for every positive `g = o(n)`, one with surplus
eventually above any multiple of `g`, answering both questions of his
Remark 6.8; its finite corollary settles Part I's question Q9 for one
family).
```

The source README202–209 states both growth conclusions **almost surely**. For each arbitrary positive g=o(n), the guarantee is a continuous finite-information strategy, not necessarily a computable one (239–242). The catalogue should state both probability qualifiers and distinguish the two algorithmic claims. Its current use of “one” can incorrectly inherit “computable” from the first clause. The source also explicitly discusses exceptional outcomes: for the stated dominant-block schedules, a comeager set has liminf S_n/n=0 (215–216), so an unconditional all-outcomes reading is not available. The manifest already says “almost surely” for the first result and “continuous” for the second; repeating “almost surely” after the second limit removes any ambiguity.

### C4. An already written report is missing from the191 total

The immutable tree contains the completed batch91 report

`generating-functions-and-asymptotics/oeis-sequence-asymptotics/a196460-clipping-tables/`

with its README, article.tex and article.pdf, but no catalogue entry. Its README5–8 identifies the two-manuscript batch91O report; the accepted publication review `review_oeis_publication_9f924ac47.md` confirms the integration gap was resolved. This is not an incoming archive or an unfinished ancillary folder.

A fresh directory inventory gives **192** collection reports, against191 distinct existing catalogue entries. Every entry resolves; the single additional directory is exactly this report. The resulting category totals are73 generating-functions/asymptotics reports, including65 OEIS reports, instead of72 and64. The surreal inventory remains69 and agrees exactly with its catalogue.

The original191 claims occur at root README216; SetTheory README25; Cardinals README34,46; collection README5,12,33; manifest20,56,66,199. The generating category is collection README26; the OEIS subcategory is manifest170 and2138. The manifest's incoming contribution at69 becomes90 rather than89, because102+90=192, and the arrival accounting must include batch91. These old counts are preserved here as the omission record. The incoming procedure explicitly requires cataloguing every report without a row, not just the named batch.

The new entry must preserve the report's distinct scopes: zero versus one strictly positive auxiliary for **each fixed finite clipping table**, with table-dependent coefficients and degree; fixed-order forward/logarithmic/inverse expansions; and uniform truncation bounds for the **exact finite sector expansion**, not a growing-order inverse theorem. Neither the accepted review nor this addition supplies a uniform paid integer compiler.

## Proposed repairs

`/tmp/catalogue_cd514f61b_proposed_edits.md` supplies exact replacement paragraphs, the affected count table, and conservative README/TeX text for the missing report. Its proposed OEIS text follows the accepted bounded publication review, read in full here; it does not recertify all analytic inequalities or external dependencies. Root owns all repository changes and any direct TeX rebuild. Only the Cardinals manifest requires a content change; the surreal69 counts need none.

## Checks that passed and boundaries retained

Fresh metadata checks, using immutable Git bytes and new standard-library code, found:

- 69 unique surreal entries, matching the independently discovered69 report directories, all READMEs and all primary PDFs; family counts26+28+1+2+12.
- 191 unique collection entries, all resolving to report directories, READMEs and primary PDFs; the independent directory inventory exposes the single missing192nd report above.
- 1,708 local Markdown path occurrences outside code spans in the changed Markdown files, all resolving. This separately defined count is not a reproduction of the author's1,246-cross-reference claim. Anchors and external URLs were not checked.
- The new label namespaces `pma:atr:`, `pma:lgc:`, `pma:nsp:`, `pma:lcc:`, `pma:emb:`, `pma:gcm:` and `isg:ptg:` exist in the named immutable article sources; `pma:lc:lem:cooper` resolves exactly. Label existence is metadata, not theorem verification.

The new Polish summaries retain Part VIII's claimed, unreviewed ATR₀ status and Part XI's sketch status; the well-order summary retains its unreviewed countermodel interface. Standard-natural ListCoding and integer Presburger semantics are explicitly distinguished from internal nonstandard theorems. The ledger update leaves its63-text/4626-environment inventory unchanged and explicitly says six later texts are unindexed; it does not promote any new formalization.

The arithmetic summaries correctly distinguish the independent-gamma83 unresolved language from refuted free-coefficient83, auxiliary-product-only83, outer-slack83 and square/product82 variants. The actual fixed-polynomial candidate table and its status notes were read at article249–299, with selected detailed README caveats. The raw29/positive21 negative-index predicate remains undecided; the analytic existence claim is not silently certified. The older74 comparison-certificate bound is not substituted for a complete paid polynomial count. The ant's fixed U15 sentinel-pair language and external program-to-tape encoding are not presented as a free ordinary-input loader. The existing84 construction is not proved globally minimal by this catalogue.

## Exact scope and PDF authentication

Supporting reads are itemized with immutable hashes and line spans in JSON: the ant cost/interface guide; fixed-polynomial status/front-matter sections; named-embedding criteria; hat-surplus theorem-scope and review notes; the missing report's identity/status; and the full accepted OEIS publication review. The rest of the large manuscripts, their external mathematics, analytic appendices and proof dependencies were not re-audited. The catalogue diffs, not all unchanged catalogue prose, are the full human-read unit.

| PDF | Bytes | SHA-256 |
|---|---:|---|
| Surreal manifest |751129|`f3e6ecd4b23ea902966e60a693c2279444fb439abdc95b814dabdccd860885df`|
| Cardinals manifest |927867|`31e2e091f0749a27745b8863c14f99fca760ad224936471aec0ad0a72b5bf42a`|

PDF contents were not parsed, rendered or rebuilt. No supplied checker, archived/frozen/copied predecessor program, scientific evidence suite, Lean build or repository builder was run or imported. No changes to repository files or Git state were made. This is a bounded publication/interface review with the four explicit findings above, not certification of the report collection.
