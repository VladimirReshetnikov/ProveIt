# Tree Calculus typesetting transfer at 954261e15

**PASS for the ordered preservation census, with five narrow editorial corrections supplied as a privately tested patch.** The original eager Tree Calculus theorem/source review is reused; this packet audits its transfer into Part XIX and the new editorial framing. It does not rerun unchanged author programs or claim a new full theorem, Lean/Rocq, or PDF-rendering audit.

The primary boundary is the complete commit `954261e15e38d84bdb2e1a97d93097a6b5551d5a`, parent `525b7795b0718a5506d2eccd243cd3f012791a8a`. The original archive is `docs/incoming/Eager_Tree_Calculus_Research_Package.zip` at arrival `aebfa386e44f232be06b546be9fc2f6138ad34f2`, SHA-256 `5c6c100296a58df366939febf2f7b6ca57616f17f77a71520f6f3a5e20204ab4`. Its companion placement was `a7ae02511c5584086ef9152f92d59ba77efa6148`.

## What the preservation check establishes

The helper authenticates the archive and all 56 individual members against embedded byte hashes, then independently checks its 55-entry `MANIFEST.sha256`. The manifest checker and author programs are not executed. ZIP paths are checked for traversal, absolute paths, duplicate members and symlinks; members are read in memory.

It compares the original manuscript body, from `\begin{document}` to the bibliography, with two nonoverlapping spans of the committed article:

- Manuscript21 introduction: lines3055–3137.
- PartXIX, including its two source appendices: lines30528–31602. Its endpoint is the anchored, actual `\appendix` command at line31603, never an occurrence inside a comment.

For each category, **one global increasing target-occurrence cursor** consumes the original occurrences in their original order. Repeated equal formulas require distinct later occurrences; the check is neither a set-membership test nor separate deques indexed only by formula value.

| Category | Original occurrences | Distinct ordered matches |
|---|---:|---:|
| Theorem, lemma, proposition, corollary, definition and proof environments |42|42|
| Display math, equation, align, gather and multline environments |83|83|
| Tabular, longtable and listing environments |12|12|
| Inline dollar-delimited math |806|806|

The JSON provides a source line, target line, target occurrence index and normalized SHA-256 for every match. The categories overlap: a displayed formula inside a proof contributes to both streams. The census is not a character-for-character claim about every prose paragraph or a general TeX semantic interpreter.

Only explicit presentation changes are normalized: comments and whitespace; balanced editorial `srcnote`, source attribution `srctag` and label commands; the `cdc:et:` prefix inside reference arguments; source `code/file/cl` versus target `tcode/code/clos`; the written-out upright `eqtag` rule labels; and the precise added cross-reference after `Appendix~A`. Source and target macros are interpreted separately, so mathematical `\code` in the source is not confused with filename `\code` in the assembled report. No algebra, commutative reordering, coefficient rewriting or mathematical hypothesis is normalized.

All 74 original labels occur exactly once with their target namespace. The 10 additional namespace labels are listed separately, and all 1,566 article labels are distinct. The helper compares 12 macro definitions exactly after whitespace removal: the eight Tree Calculus declarations/renames, the filename macro, and inherited `N`, `Z`, and `bits`.

Regression controls reject a missing duplicate, a reversed pair, a crossing repeated occurrence and a missing occurrence. Additional controls preserve the source/target macro distinction, refuse namespace removal outside references, distinguish `a+b` from `b+a` and `a+a` from `2a`, reject Boolean/float aliases in saved receipts, and check the actual-appendix boundary against comments.

## Original companions retained and excluded

All 51 retained companions are byte-identical to the original archive at both the placement commit and the reviewed integration commit. The helper derives their destination paths, cross-checks them against the separately pinned placement inventory, and checks that none changed between those commits. The JSON enumerates every source member, destination, byte count and digest.

The five excluded original files are explicit:

| Original member | Disposition at954261e15 |
|---|---|
|`README.md`|Original package guide not placed separately.|
|`eager-tree-certificates.tex`|Integrated into the assembled article.|
|`eager-tree-certificates.pdf`|Original standalone PDF not placed separately.|
|`MANIFEST.sha256`|Delivery checksum ledger retired after placement.|
|`verify_manifest.py`|Delivery manifest checker not placed separately.|

The integration commit modifies only the collection README, article source and article PDF. It imports no changed arithmetic code. The original `tree_kernel.py` boundary defect and the unapplied repair status were therefore accurately described **at this pinned commit**. A later corrected-package placement, `8a4e64732`, changes the live companions separately; this packet does not authenticate those corrected files as though they were the original bytes. When current working files have changed, the helper reads the immutable reviewed Git blobs instead.

## Editorial findings and minimal repair

The companion `review_tree_typesetting_954261e15.patch` changes five places in two text files. It leaves every source theorem and all companion code/data intact.

1. **README exact-size qualification** (`README.md:39–41`, following its broad uniqueness promise at21–24). Source21's one-witness claim concerns its canonical refinement at the exact number of distinct calls. The base family at an external upper bound is nonunique. The original source explicitly gives infinitely many unused-field choices for the one-row certificate `E(0,5,11)`. The patch states the distinction at the opening; later chapter and README qualifications already state it correctly.
2. **Growth threshold** (`article.tex:30530`). The PartXIX preface must say `D_n=64n+113` for `n≥2`, with `D_0=44`, `D_1=179`. The source theorem correctly preserves these base cases at31277; substituting0 and1 into the unrestricted affine expression would give113 and177.
3. **Single-fold input translation** (`article.tex:31441`). The new claim that a single-fold representation for the fixed universal tree would settle the general single-fold problem cites PartIX but omits an input-interface hypothesis. Tree universality supplies a computable many-one input translation; it explicitly does not supply a polynomial graph with unique auxiliary witnesses for that translation. PartIX's cited proof instead specializes a universal polynomial `H(e,x,w)` at `e_A`, retaining ordinary `x`. The patch adds “together with a fully charged single-fold input translation from universal halting.” This is a sufficient condition: a unique natural graph `(n,u)` of that translation composes with the tree polynomial by a sum of squares, preserving the unique accepting fiber. The finding is a missing obligation in the cited implication, not a proof that no other route could establish it.
4. **Provenance count** (`article.tex:31907`): twenty→twenty-one manuscripts.
5. **Bibliography count** (`article.tex:32018`): twenty→twenty-one manuscripts. The README's historical account of the prior twenty-manuscript write remains untouched.

The new no-computable-bound remark is sound: for a fixed `N`, memoized eager evaluation can stop on the `(N+1)`st distinct pair or a repeated active pair, so bounded-distinct-call acceptance is decidable. A total computable bound valid on the r.e.-complete halting domain would decide it. This does not rule out different fixed-arity MRDP constructions. The new formalization and older-SKI/DAG comparisons preserve their semantic distinctions and make no kernel-verification claim for the eager proofs.

A separate reviewer independently challenged the single-fold implication and read the complete five-edit patch, agreeing that the added translation hypothesis is sufficient and the other qualifications are correct. That bounded read did not repeat this census or the original source suites.

## Private application and pins

The helper reconstructs the exact intended patch from unique text contexts, compares its bytes with the supplied patch, and applies it in a temporary directory using `patch --batch --forward --fuzz=0 --no-backup-if-mismatch -p1`. It checks the complete resulting files and reruns all four ordered source-occurrence streams after repair. The archive and repository stay unchanged.

| File | Reviewed SHA-256 | Privately repaired SHA-256 |
|---|---|---|
|`README.md`|`6c5a1a81931914f9caaff22c3a02dcd2a5c45d28f279718d8e96b358ffb3df8d`|`27fadadfc18189b013cb47cd72e2c64917af32fba478ee116c7b8dea4a5ae1d4`|
|`article.tex`|`594e3da5caf4aac5228e594ed30feb506746c51d8d7896157934ed2566a38bb7`|`11e025e882c75616b216e5f1ce2aeb99e84dde01baa53b03405f9a439b20b60c`|
|`article.pdf`|`4ff74ee98f97c8a05046b8201e9bc2d6901d4798ad42985c15d8cca80fe18630`|Unchanged.|

Patch SHA-256: `9bdec9310f2f3f5dfa96d295e5fcb98d6fb78f0ea697144fc8cc25c46c04c344`.

A separately pinned **applicability-only** check also applies this same patch with zero fuzz at `bbc67d225e96a80a94b7d7a3c9a42f4c93e23cca`, which subsequently added the reciprocal Tree Calculus note. Its input and output hashes are separate fields in the receipt. This is not a preservation or theorem audit of that later revision and does not replace the primary954261e15 boundary.

The PDF is deliberately unchanged. Applying this text patch to a maintained report requires rebuilding its PDF; neither recorded PDF is represented as containing the corrected text. The collection's standard build command is `latexmk -pdf -interaction=nonstopmode -halt-on-error article.tex` in the report directory. No build was run in this transfer audit.

## Portable replay

The checker has no third-party Python dependency. It uses Python's standard library plus the usual `git` and `patch` command-line tools; it imports no archive program and needs no permanent `/tmp` source tree. Matching working bytes may be read directly; changed or retired files fall back to the pinned Git objects. An explicit `--archive` can provide the original ZIP; it must match the same archive hash. The JSON is deterministic and compared recursively with exact types by `--expect`.

From any working directory, with the four packet files together:

```sh
python /path/to/review_tree_typesetting_954261e15.py \
  --repo /path/to/Proofs \
  --expect /path/to/review_tree_typesetting_954261e15.json
```

To write a fresh receipt, add `--output /path/to/new-receipt.json`. The default patch is the sibling `.patch`, or supply `--patch`. The frozen receipt was reproduced in a fresh process from a different working directory. No author suites, compiler witnesses, code repairs, universal operation savings, future-revision correctness or PDF rendering claims are inferred from this source-preservation result.

## Root integration replay

Root read the complete portable checker, source-transfer note and patch, then
ran a fresh `--expect` replay with a new receipt. The complete receipt matches
byte for byte, including both private patch applications and the post-repair
ordered census. The separate [editorial read](review_tree_typesetting_editorial_954261e15.md)
and its [source pins](review_tree_typesetting_editorial_954261e15.json) preserve
the independent single-fold input-interface finding.
