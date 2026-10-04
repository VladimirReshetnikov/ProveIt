# Bounded OEIS manuscript placement review at ec8ae3dc7

**Byte-placement PASS; main-manuscript integration is partial.** All285 files added in the new host match bytes from the two original arrival ZIPs. The host's `README.md` and `article.tex` are the first manuscript's unchanged release guide and1046-line article. The second manuscript's proof/evidence is placed as ancillary files; its own811-line article and172-line guide are not present as placed counterparts. This review finds no new fixed-cost universal Diophantine compiler in the inspected text.

This is a read-only review at immutable placement commit `ec8ae3dc7f6b422301cafda0f5870d73b642a6ca`, against arrival commit `0d7f51c442f5736f35d9de14d4c1b1f7cc1c2bbf`. The host is

    SetTheory/Cardinals/docs/reports/generating-functions-and-asymptotics/
      oeis-sequence-asymptotics/a196460-clipping-tables

No supplied/frozen program, copied predecessor, scientific checker, source interpreter, TeX/Lean build or PDF renderer ran. Fresh standard-library code only read Git blobs and ZIP members, hashed them, compared bytes and recorded text spans. No repository or Git mutation was made. No applicable ancestor `AGENTS.md` was found for this host.

## Exact placement evidence

The two arrival archives are:

| Archive under `docs/incoming/` | Bytes | File members | SHA256 |
|---|---:|---:|---|
| `A196460_asymptotics_and_inversion_sources.zip` |4,852,913|176|`821a1cfc1c00fd6d109ee2f6ff8007b4e8985f03d45f6f9a04d07aa8623fde27`|
| `A196460_sharp_uniform_truncations_sources.zip` |17,225,521|584|`9e223bb02aed17d87552925bd5019d8955da1ea8731883b94de8e7630c97b47e`|

The JSON inventories and hashes all760 nondirectory members. Nested archives and binaries are hashed as opaque bytes; their contents are not recursively audited. It also records the Git blob IDs, all285 host-file hashes and every matching archive member path.

The placement commit adds exactly285 files and deletes the two incoming ZIP paths. Of the host files,99 have the `21-fixed` prefix,184 have the `24-unif` prefix, and2 are the main guide/article. Every fixed-prefixed file has a byte-identical member in the first archive; every uniform-prefixed file has one in the second archive. The aggregate285/285 comparison has no mismatch. This authenticates the copied contents, not completeness of archive reproduction, permissions/mtime preservation, mathematical truth of retained receipts, or safety of supplied tools.

The primary manuscript comparison is decisive:

| Original object | Placed result |
|---|---|
| `ArityAsymptotics/README.md`,113 lines | Exact host `README.md`, SHA`dbdcc5fc5319dbd7b3b7ca6c82fa9b76fe7adb68ceea3465f04cffb128773d97` |
| `ArityAsymptotics/article.tex`,1046 lines | Exact host `article.tex`, SHA`6569cdc99dc96bdf53c819d18ecfccad030771b5a1795b07c7deb02b3e7a901c` |
| `UniformSectors/README.md`,172 lines | No identical host file; SHA`413a3942e3a0f14a3178fc0c31024d30e2d893338dac6a3178454b9f9c644d81` |
| `UniformSectors/article.tex`,811 lines | No identical host file; SHA`d0770c2f36b214204b13f7487f3d7299b2da96844de47f954cd717f5f78b3191` |
| Both original `article.pdf` files | No identical host file |

The host article retains65 distinct TeX labels; the unplaced uniform article has61. These are mechanical source censuses, not compilation results. Because the host article is byte-identical to the first delivery, it contains no newly assembled second part. In particular its lines889–895 still pose growing truncation order as a further question; the companion's later answer is available through the placed `24-unif-src-PROOF.md` and related evidence, not integrated into that main prose.

The host guide is likewise a historical release README, not an adapted host manifest. Its advertised `article.pdf`, `manuscript/article.tex`, `inputs/...`, `tools/` and `qa/` paths are absent under those names in the flattened host. Its exact locked-replay instructions and claims about release preparation describe the original package layout. This does not invalidate the copied mathematics, but the placement should not be reported as a completed two-manuscript publication or as a currently verified host build. No external publication status was checked.

## Mathematical and compiler scope of the inspected text

The main article explicitly fixes K and the Boolean table S as coefficient data (lines68–79). Its positive inputs A,B are **unbounded integers**, but their membership test depends only on the two clipped labels `min(A,K),min(B,K)`. Thus “finite table” must not be misreported as a theorem restricted to bounded A,B; it means that the entire accepted-pattern table is fixed in advance.

The read classification theorem and proof (lines133–232) give:

- Zero auxiliary variables exactly when each accepted tail cell includes its full coordinate-flat closure. The necessity argument restricts a polynomial to an infinite grid; the sufficiency polynomial is the product of squared-distance-to-flat factors.
- Every fixed table has a representation with one **strictly positive** existential witness. The factor for a cell uses `p_K(x)=product_(h=1)^(K−1)(x−h)^2` and requires the witness to equal the product of the designated tail factors. A zero witness would admit false tails. Empty/full tables and K=1 are handled separately.
- Consequently the exact auxiliary minimum is0 or1 for this particular class. The polynomial coefficients and degree may depend on the entire table; the article expressly imposes no degree bound. The proof makes no global auxiliary-minimum claim for a larger composed encoding.

No defect was found in this bounded read of the elementary classification proof. The count is stated as `C_n=1+a_n`, n=K−1, with the displayed double sum for a_n. The zero/one arity result and the asymptotic counts do not provide a complete arithmetic circuit of uniform size as K or the table grows. They do not turn finite-horizon tables into one fixed polynomial for unrestricted accepting histories, nor remove any paid loader, packing or finalizer costs from the current universal-polynomial constructions. This is a resource/scope distinction, not a denial of the explicit polynomial formulas for each fixed table.

The read main-article asymptotic statements are fixed-order claims: M is fixed before n grows, and constants/start thresholds may depend on M (lines356–442). The exact integer-threshold inverse still performs an exact comparison with a_m or C_m and handles C_0=2 separately (lines711–768). The further-questions section expressly leaves degree/coefficient/monomial-cost optimization separate from witness arity (lines920–925). I did not independently certify the unread logarithmic or inverse proof sections.

The second release's guide, principal statements and placed proof introduction say something stronger but different: for n>=32 they bound every **exact finite sector** truncation0<=M<2n simultaneously. The stated worst excess is

    3(3n²+n+1) / [n(13n²−15n+2)],

uniquely at M=2n−4, with sharp asymptotic constant9/13. For C_n=a_n+1, merging the extra term into the terminal sector gives excess at most1/n, uniquely maximal at M=2n−2; leaving that contribution unmerged has an endpoint excess exactly1. The text does not claim the threshold32 is minimal. Its scope section explicitly excludes growing-order logarithmic/inverse expansions and an exact integer inverse obtained by flooring an approximate real inverse. These are the authors' stated analytic theorems; this placement review does not certify their full proofs or rerun their recorded finite checks.

## Exact human-read scope

All listed line ranges are inclusive. The JSON stores the file SHA256 and the SHA256 of each UTF8 span with original line endings. Archive members with identical bytes inherit the same stated text coverage, not an additional independent proof audit.

| Location | Text read |
|---|---|
| Placed `README.md` |1–113, complete|
| Placed `article.tex` |1–234;356–443;711–768;887–974|
| Placed `21-fixed-src-README.md` |1–34, complete|
| Placed `24-unif-src-README.md` |1–33, complete|
| Placed `24-unif-src-PROOF.md` |1–78;347–370|
| Original second ZIP, `UniformSectors/README.md` |1–172, complete|
| Original second ZIP, `UniformSectors/article.tex` |35–235;630–786|

All other member contents have **hash-only** or byte-matching coverage. In particular there is no claimed full read of the two analytic manuscripts, audits, supplied code, build tools, numerical tables, logs or historical preservation ledgers. Supplied statements that earlier checks or visual reviews passed remain historical claims. OEIS/literature attributions were read locally but not independently checked online.

The complete manifest/read evidence is `review_oeis_placement_ec8ae3dc7.json`, SHA256 `c851783419859093c56200c5cf95cac20228e588482bac561edcd24884703500`. The new metadata helper was `/tmp/oeis_placement_inventory.py`; a separate fresh metadata-only script added read-span hashes. Neither invokes supplied scientific or presentation code. This checkpoint covers ec8ae3dc7 only, and does not duplicate the other placement commits or alter the scope of earlier arrival reviews.
