# Transseries tutorials

Four independently written expository treatments of transseries, filed here on
2026-09-02 as standalone quick-gate receipts.  They arrived as bare directories
in direct-arrival commit `e23bad1bb0ab91fea6df5a1cfd2525eea28dcb16`; no
archive, checksum ledger, or provenance note was submitted.

These are *tutorials*: general introductions to the transseries field, its
motivation, and its machinery.  They are filed apart from
[`../polynomial-logarithmic-transseries/`](../polynomial-logarithmic-transseries/),
which treats one specific scale in operational depth, because the two have
different purposes and audiences even though their subjects overlap.

| Directory | Document | Source receipt | PDF receipt |
| --- | --- | --- | --- |
| `Transseries_Tutorial-1/` | *Transseries Tutorial* | 5,159 lines; 188,639 bytes; SHA-256 `75f427b8a8560cb1dbd0c5b85d2e66d8ff7c22260658fc3824d51d3fa0fcd324` | 143 Letter pages; 793,390 bytes; SHA-256 `81e6c8b020a7a6e87f1ce33810398dbe21a4a1e588be55aa2805038df10b841a` |
| `Transseries_Tutorial-2/` | *Transseries Tutorial* (second treatment) | 7,749 lines; 250,478 bytes; SHA-256 `50da089995e1132f3578919722662ae17f1013efb7f11d60d5b8f5568d95ffb2` | 164 Letter pages; 817,544 bytes; SHA-256 `4bc9941757997494d64e3b9115b49c56bfcb621d908890073a87649d39b26453` |
| `Transseries_Tutorial-3/` | *Transseries for Mere Mortals* | 4,410 lines; 134,470 bytes; SHA-256 `26fb3f4a30d85080ff84d154f41dea5c296397ecd2c997e6e38cce045412c348` | 121 Letter pages; 656,187 bytes; SHA-256 `8d34824a299cd9e732e22f2fa4e8c43813cba56624f861da0c22df8b5477bbf7` |
| `Transseries_Tutorial-4/` | *Transseries Tutorial* (fourth treatment) | 8,781 lines; 344,893 bytes; SHA-256 `f00fe3aa6c4e451c406a4d5f1ac8cc7684153cfe3b6dc8369f6184eb1c779105` | 217 custom 522-by-738-point pages; 893,129 bytes; SHA-256 `6e2065d45db6e63066c3fdf2b0d307f07772d7221e2e4915eb7a21401fe4ba0c` |

All four arrival PDFs are readable and unencrypted, and every font row is
embedded with no Type 3 font.  None uses Libertinus.  Three are Letter and one
is custom 522-by-738-point, so canonical A4/Libertinus restyling is explicit
post-publication debt for all four.

None of the four loads the shared notation file
`docs/fabius-notation.tex`; they use their own document-local notation and
predate the corpus notation migration.  Consequently they are free of the two
migration defect classes that had made every source in the neighbouring
subgroup fail to compile: a scan for fatal script collisions and for
macro-glued-to-letter tokens returns zero hits on all four.  Their sources have
not otherwise been build-verified here.

Similar titles and overlapping subject matter were noted at intake.  Claim
comparison, deduplication, canonical selection, consolidation, styling repair,
and Lean crosswalking are all deferred; nothing in this subgroup has been
merged or rewritten.

See [`../../MANIFEST.md`](../../MANIFEST.md) for the group record.
