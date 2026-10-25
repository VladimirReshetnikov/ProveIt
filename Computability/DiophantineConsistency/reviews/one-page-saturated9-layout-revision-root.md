# Root static review of the tighter nine-point layout

The first released renderer correctly rejected the original layout: a
37.46252-point horizontal overflow, 31.1629-point vertical overflow and
two pages. Its remaining four commands were not run. Root separately
typeset the same frozen TeX in scratch and inspected both diagnostic
pages; the long D1 list crossed the column and part of the seed/footer
spilled onto page two. This was a fit failure, not an accepted PDF.

Reviewed the complete selected layout diff, revision/archival plan and all
changed proof, README, mapping and toolchain prose. The arithmetic stays
9-point and the seed 8-point. Header, leading and gaps are tighter; isolated
native prose is combined. The same 22 positive D1 powers with coefficient
two are partitioned into lists of 8/7/7. Every other formula, numeral and
literal seed character remains unchanged. The new actual TeX SHA-256 is
`c359081b6e1e610730a941185bf86bb12ca13a47ab94b98183a1a07141a314af`.

Both executable changes are exactly one font assertion, from leading 9.6
to 9.0. Reversing that single literal in each reproduces its previously
fully read executable byte for byte. All parsing, arithmetic, circuit,
constant-reconstruction, corruption-control and process algorithms are
unchanged. New auditor hash:
`059abfdb12f52ccc6cec23ca396424bc089cf9b21e3cf3b75509ee67812b79f5`;
renderer hash:
`e710f96fdddc1c994af56036c9651bb9dd1cc01af5d059f43bb1e6d0b8bf30ed`.

Independently authenticated all 56 external, 22 current/historical/option
and four tool-core whole hashes and byte counts, and all historical/current
preparation pins. The complete typed 13-member historical inventory is
exact at manifest `df194905…`; it preserves both original pin files, code,
TeX and failure transcript. The selected active TeX equals the proposed
option byte for byte. The entire polynomial and formula map equal commit
`0aad524696`. Current tool pins:
`739914e92fd8edd735f789bd857e19d325c2fe10bc4b88c7a34c41ca804cbb02`;
source pins:
`a7840536bdfb095c25306d26f7dc26af95a40f1ba2179e9f5efab0bda97f5134`.
Audit: `/tmp/proveit-root-nine-page-layout-revision-auth.json`.

Static result: PASS. No revised typesetting or module execution occurred
during this review. The independent delta review and explicit new root
release remain required; fit and visual inspection are still unresolved.
The canonical page and its constants are unchanged.
