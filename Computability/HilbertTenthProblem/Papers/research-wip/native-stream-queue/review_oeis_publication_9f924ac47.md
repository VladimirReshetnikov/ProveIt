# Bounded OEIS publication review at 9f924ac47

**The two-manuscript integration gap is resolved.** The new guide and article preserve the distinction between uniform finite-sector bounds and fixed-order logarithmic/inverse expansions. One minor Git-guidance error is recorded below; no mathematical integration correction was found within this review's scope.

Reviewed immutable commit `9f924ac472e22cd041b1c8949ac0b2c677e6a448`, against parent `8e9cd6f00e0ac79c4425ff6abdfa64b497cf3f41`. The host is `SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/oeis-sequence-asymptotics/a196460-clipping-tables/`. This checkpoint follows the bounded placement review at `ec8ae3dc7`; it does not retroactively enlarge that earlier read scope.

## Read and preservation evidence

The complete new 928-line README and the complete 2,169-line parent-to-publication raw article diff were read. The README raw diff has 1,046 lines. Together the two text changes contain 2,389 additions and 241 deletions. The 2,379-line article's unchanged portions outside diff context are not claimed newly read. The companion JSON records exact raw-diff and before/after hunk spans, byte lengths, Git blobs and raw/normalized SHA256 values. The new 637,646-byte PDF is authenticated only; it was not rendered or rebuilt.

The immutable incoming ZIPs at `0d7f51c442f5736f35d9de14d4c1b1f7cc1c2bbf` were read as data and authenticated against the previous placement pins:

| Original manuscript | Article member | SHA256 |
|---|---|---|
| Fixed-order, manuscript 21 | `ArityAsymptotics/article.tex` | `6569cdc99dc96bdf53c819d18ecfccad030771b5a1795b07c7deb02b3e7a901c` |
| Uniform-sector, manuscript 24 | `UniformSectors/article.tex` | `d0770c2f36b214204b13f7487f3d7299b2da96844de47f954cd717f5f78b3191` |

All 65 first-manuscript labels occur exactly once as `cta:` plus their original names. All 61 second-manuscript labels occur exactly once as `cta:us:` plus their original names. The three originally shared names are separated correctly. Exactly nine new labels complete the **135 unique labels**: the four front-matter sections and notation table, two Part headings, Part I's previously unlabelled introductory section, and the publication-provenance appendix. All 242 local `ref`/`eqref`-family reference occurrences resolve.

As a separate mechanical preservation check, each original main body through its evidence appendix survives as an ordered token subsequence after the declared label/reference prefixes and Part II citation-key changes. This checks 5,077 original fixed-order and 3,386 original uniform-sector nonwhitespace tokens; the added labels and appendix-title suffixes are disregarded for the comparison. Both original abstract inner texts occur literally in the new article. Token subsequence preservation is not byte identity or certification of every proof; together with reading the actual additions, it supports the declared integration rather than an unnoticed replacement of the mathematical text.

The publication changes only the README and article and adds the PDF. All **283 ancillary files** remain byte-identical to the previous placement pins. The guide's literal 286-file inventory matches the actual tree exactly: 26 root files, 33 under `code/`, and 227 under `data/`. Its complete 285-row original-to-shipped path map has 283 byte-identical destination files; the two explicit exceptions are the replaced main README/article. The new PDF is the remaining 286th file. Thus the guide now describes the actual flattened layout and identifies the delivered-layout instructions as historical, repairing the former path ambiguity.

The additional claim that manuscript 24 embeds manuscript 21 was also checked bytewise: its `inputs/predecessor-release/` contains all 176 first-archive files unchanged, and one source-seal ZIP equals the original first archive. No claim about file modes, timestamps, hostile-test results or historical tool correctness follows from these byte comparisons.

## Mathematical integration and compiler scope

The new front matter at article lines 74–316 distinguishes the two results and their notation. The first original manuscript is Part I (Sections 5–14, evidence Appendix A), and the second is now actually printed as Part II (Sections 15–22, evidence Appendix B), with publication provenance in Appendix C. This resolves the earlier observation that the second manuscript was only available as ancillary proof/evidence while Part I's main article still posed its question without an integrated answer.

Part I retains the exact zero-versus-one auxiliary classification for **each fixed finite clipping table**, interpreted on unbounded positive integer inputs through clipping. The strict positivity of the single witness remains essential. Coefficients and degree may depend on the entire table; no bound uniform in table size is supplied. The added note at 505–514 correctly identifies the construction as a product of nonnegative cell polynomials, rather than one residual square. This publication is not a new fixed-arity certificate for unrestricted histories or a complete arithmetic circuit with a smaller universal gate count.

Part II's theorem at 1398–1411 controls all truncations `0 ≤ M < 2n` for `n ≥ 32` of the **exact finite sector expansion**. The maximum relative excess remains

`3(3n²+n+1) / [n(13n²−15n+2)]`,

uniquely at `M = 2n−4`, with asymptotic constant `9/13`. Its merged terminal-sector convention for `C_n = a_n+1` gives maximum `1/n`, uniquely at `M = 2n−2`; the terminal denominator is doubled, and the unmerged endpoint has excess exactly 1. The publication preserves this endpoint distinction and does not claim that the convenient threshold 32 is minimal.

The new answer attached to Part I's “Growing truncation order” question at 1236–1248 is appropriately qualified. The full-range tail bound uses exact coefficients `P_k(n)`. Replacing a single coefficient by its leading monomial has the narrower condition `k²/n → 0`; the corrected estimate extends to `k=o(n^(2/3))`. Neither coefficientwise approximation licenses replacing every earlier retained sector at the first-omitted-sector error scale. The new front matter and Part II's retained scope section, 1937–1980, explicitly preserve this distinction.

The logarithmic and Laurent-inverse expansions remain **fixed-order** claims. No uniform growing-order logarithmic/inverse theorem, noninteger convergence assertion, or exact integer inverse obtained by flooring a truncated approximation is added. The exact threshold result still requires an exact comparison with the candidate sequence value, including the exceptional `C_0=2` endpoint. These qualifications agree with the earlier intake review and are now visible in the integrated article.

The new comparisons with the transseries volumes and Report 69 are read as scope/attribution notes. This checkpoint does not certify the cited external literature, priority, all neighboring theorem correspondences, or every analytic inequality in the imported manuscripts. The reported scientific reruns and PDF diagnostics remain the publication author's historical claims; none was repeated here.

## One minor guide finding

At **README lines 542–545**, the guide says the `.log` and `.fls` files match ignore rules and were initially added with `git add -f`, then concludes that a fresh `git add` of the directory will not pick up changes to them. That last clause is incorrect for already tracked files: ignore rules do not prevent ordinary `git add` from staging their modifications. Preserve the initial-force-add history, but limit the warning to newly created/untracked ignored paths. This is an operational documentation issue, not a mathematical or byte-preservation defect. The finding is pinned to the immutable reviewed commit even if a later correction is made.

## Execution and limits

No applicable ancestor `AGENTS.md` exists for this host at the reviewed commit. Only fresh standard-library metadata scripts and read-only Git/ZIP/text operations were executed. **No supplied, archived, frozen or copied predecessor program was run or imported; no build, scientific checker, Lean invocation or PDF renderer ran. No repository file or Git state was changed.**

The JSON is `/tmp/review_oeis_publication_9f924ac47.json`. It contains the full label mapping, path-map comparisons, immutable original/current hashes and exact human-read evidence. Fresh helper paths are recorded there. The five other new archives are outside this review. The outcome is completed local manuscript integration with the stated bounded review, not formal verification, external publication validation, or a new paid universal compiler.
