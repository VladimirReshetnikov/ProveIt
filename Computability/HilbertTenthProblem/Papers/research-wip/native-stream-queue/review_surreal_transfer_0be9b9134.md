# Preservation audit of the assembled surreal well-orders report

**PASS for the bounded source-preservation and provenance checks below.** The
four original manuscripts are accounted for at write commits
`d51fafea806cbd48ba29be017eff85cdd9653b14` and
`0be9b913487fa2cc0e16cea6545c55f33b4446d8`. This is a thematic synthesis:
**124 original numbered statement bodies are normalized-exact, 41 are explicitly
rewritten as duplicate-result notes, and one original question remains verbatim
inside an augmented answered remark.** All 166 source occurrences have distinct,
correctly ordered crosswalk entries. This is not a claim that every original
proof or display is printed verbatim.

The separate [synthesis review](review_surreal_synthesis_0be9b9134.md) reads all
new notes and identifies the corrections needed in the added prose. Its patch
changes two unsupported uses of “coherent” to “uniform” and qualifies the largest
file statement as non-PDF. The underlying original choice proof and the copied
formal theorem bodies are unchanged. No additional mathematical transfer defect
was found by this census.

## Immutable inputs and transferred companions

I read `Algebra/SurrealNumbers/AGENTS.md` and the prior complete manuscript and
staging reviews. The target directory is
`Algebra/SurrealNumbers/docs/foundations-and-computation/surreal-well-orders/`.
The first write and final write are authenticated separately; the final article
is not silently substituted for the first write or the delivered manuscripts.

| Pinned presentation | SHA256 |
|---|---|
| First-write article | `8e40fe735efd3dfe3dc0b24a6c7cafb642203f43b7e8dc303804633fe7b99611` |
| First-write PDF | `d38c5cb93aa64098aa17a588de667a8ed0433a2faa37f6385d3070a01ef0de67` |
| Final article | `728573d68da543e25ee8d0f7d37f9d75410695ce5196702336e71e4a7928b503` |
| Final PDF | `4b228811c4719c063aad1932d540e7f0e531ff6a1ca082df014a6fce0d7a2cbf` |
| Final README | `8fc8b16c54a45cab946f383ee47b9f87b31b105939e0d65f681c88a1f1a6a568` |
| Final collection NOTATION | `1c6b246bfe5889177a7c9557b9c6d64d3654bfb099a12508ef3904a6c9f052e9` |

All four original archives are read from arrival
`4e270aa4648c5fd7e18626507531046715976535`:

| Source | Archive | SHA256 |
|---|---|---|
| 11 | `surreal_well_orders (1).zip` | `e48ab1b54681787324fd01953ba093d2b7abe546673ccd0f0a0bcb59e232e33a` |
| 12 | `surreal_well_orders.zip` | `1edf59eaa0febdc0b7c9da581d9a6a65cc2ae88b99c166756ffd58f8aa4d4d5d` |
| 09 | `Surreal_Well_Orders_Research.zip` | `8aebf0ab80207a4e2165be6f7a329eff18b90134128b02e65c4732c97c252ee9` |
| 08 | `Surreal_Well_Orders_Research (1).zip` | `36c7f6ac22cd2a665aa078eb99eeffef170cb2d6c0cadab31417562f147d8179` |

The helper pins every one of the 29 member hashes and sizes, rejects unsafe or
duplicate ZIP names and symlinks, and imports no archived program. All **14**
code/data/audit companions match their delivered bytes at the staging commit
`ccc046989e0d9c5556a8d2d8c1b81c3aa85e185d`, the first write, and the final write.
The final directory has exactly those 14 files plus the article, README and PDF.

The remaining 15 original presentation members are separately enumerated:
four TeX manuscripts, four delivery READMEs, four delivery PDFs and three
checksum manifests. They remain available at the arrival commit. This differs
from staging's 13 omissions because the original source-11 TeX and README were
then copied literally, while the final article and guide are synthesized.
There is no new missing executable or data file.

## Numbered formal statements and labels

The checker parses the original numbered theorem/lemma/proposition/corollary/
definition/example/remark/question environments with their section counters.
It independently checks Appendix D's entries against that sequence, preserving
both occurrence multiplicity and order for each source. It then locates the
corresponding target environment by its namespaced label and compares the bodies.
Optional statement titles are not part of this body comparison; the complete
crosswalk and source/target line maps are recorded in the receipt.

| Source | Original statements | Normalized-exact bodies | Duplicate notes | Original question retained in new remark |
|---|---:|---:|---:|---:|
| 11 |53|53|0|0|
| 12 |47|43|3|1|
| 09 |32|20|12|0|
| 08 |34|8|26|0|
| **Total** |**166**|**124**|**41**|**1**|

All 53 base-source statements also remain in their original order in the article
itself. The other three sources are intentionally reorganized; their global
article-order subsequence lengths (26, 30 and 29) are reported diagnostically,
not treated as omissions. Their crosswalks still preserve the full original
statement order.

All **198 original labels** occur exactly once with the documented prefixes:
60 source-11 labels under `swo:`, 39 source-12 labels under `swo:st:`, 46
source-09 labels under `swo:ec:`, and 53 source-08 labels under `swo:sk:`.
The final 272 labels are unique; all 830 internal reference occurrences resolve.
The additional 74 labels include originally unlabelled statements, merge prose
and the retained tagged equations. This checks label existence and occurrence,
not a Lean declaration or proof-assistant correspondence.

## Ordered displays and notation

The report marks **100 copied source ranges**. For each range the helper takes
the exact original line slice and the corresponding target chunk, normalizes
only the declared source-sensitive notation and label/citation changes, then
requires a strictly increasing one-to-one match of every displayed formula.
No sorting or unordered multiset comparison can hide a dropped duplicate or a
local reorder. The parser distinguishes `\[` from a `\\[spacing]` line break.

| Source | All original displays | Displays in copied chunks, all preserved in order | Outside copied chunks |
|---|---:|---:|---:|
| 11 |56|56|0|
| 12 |26|24|2|
| 09 |37|22|15|
| 08 |28|10|18|
| **Total** |**147**|**112**|**35**|

The 35 displays outside copied chunks belong to the material presented through
declared condensed notes/proof references. They are explicitly listed by source
line and are **not** certified as verbatim occurrence-preserved by this check.
A separate global ordered-subsequence diagnostic records exact matches without
promoting it to full coverage. The synthesis review assesses the new notes'
mathematical meaning. In particular source-08 equation (10) is explicitly
*described*, rather than displayed, in the orbit-interpolation note; tags
(S08.1)–(S08.9) and (S08.11)–(S08.13) remain displayed and labelled. Both that
exception and all 12 retained tags are checked.

Normalization is source-aware. It distinguishes source-12 binary coding rank
`rk` (renamed `bl`) from source-11 von Neumann rank; source-09 injective `Tree`
from source-11 arbitrary `WordsAll`; and source-08's core `Pset` from its
power-set uses. It checks the birthday-cutoff aliases, the two support-code
notations, the well-order/class-order names and source label namespaces.
Removing a redundant old cutoff alias from its defining equality is explicitly
limited to the delivered definitions. There is no algebraic, inequality,
quantifier, sign or arbitrary-prose simplification.

The receipt also records all **108 source macro declarations**, their mapped
target declarations and arities, including unchanged definitions and the
explicit glyph/notation differences. This makes the equivalence-symbol,
concatenation, embedding-arrow and script/caligraphic changes inspectable rather
than silently expanding colliding macro names in one global environment.

## Known correction, new prose and PDF boundary

The earlier source-08 fixed-relation correction is present exactly in its copied
foundation chunk. Under GBC, holding the sets and a fixed class relation fixed
holds its internal well-foundedness fixed between class expansions; available
relations and external well-foundedness are separate questions. The active
source chunk no longer contains the original misleading assertion. The nearby
editorial quotation of the old sentence is deliberately not mistaken for an
unapplied correction.

The added source-12 answer keeps the original weak-choice question verbatim,
then appends editorial prose. The synthesis reviewer found that this new prose
and one earlier comparison wrongly called the constructed rank orders
“coherent”; later orders need not extend earlier ones. That finding affects the
added answer, not the preserved original question or source-11 proof. The
separate private patch corrects both locations.

The authenticated inventory also proves the README's narrow size error:
**543,575 bytes** is the largest delivered member (source-11 PDF);
**126,780 bytes** is the largest delivered *non-PDF* member (source-11 TeX).
The separate patch adds that missing qualification. It is
`review_surreal_synthesis_0be9b9134.patch`, SHA256
`0004ce2f78d1ebd1f5986948077ca1a70488a1793bb4b9bf67cc088f639aa839`.
I read that companion review and agree with this separation of findings.

`pdfinfo` accepts the authenticated final PDF as an unencrypted 115-page PDF;
the originals have 35, 24, 24 and 26 pages for sources 11, 12, 09 and 08.
These are delivered-PDF checks, not a fresh typesetting run, a full visual audit,
or verification that a future patched article and the current PDF coincide.
The editorial patch requires a later PDF rebuild on application.

## Reproduce and limits

```sh
python3 review_surreal_transfer_0be9b9134.py \
  --repo /path/to/Proofs \
  --expect review_surreal_transfer_0be9b9134.json
```

The portable helper uses standard-library Python, read-only Git, and `pdfinfo`.
It reads immutable Git blobs, has no fixed worktree or `/tmp` dependency, and
writes only an explicitly requested `--output` receipt plus private temporary
PDF copies. Exact saved-receipt comparison is recursive and type-sensitive.
Normal Python is required. A fresh replay from a different working directory
matched the receipt.

No repository edits, Git mutations, unchanged author-suite reruns, TeX builds or
Lean/Rocq builds were performed. The earlier complete manuscript review remains
the source for the original proof assessment; the separate synthesis review
covers all 98 newly authored hand chunks and changed editorial passages. This
packet certifies the exact preservation inventory above, not every source word
or an independent re-proof of every transfinite theorem.

For the Diophantine goal these manuscripts supply order/size and uniformity
cautions. They do not furnish a Turing-complete substrate, a fixed-arity
Diophantine compiler, a paid ordinary-input representation, or an arithmetic
operation reduction.
