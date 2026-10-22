Independent capture review passes. The root-created archive is
`920ba7ee18c35a92beed8be57f089d04ff622620fd58eff535c08ca9eea9e612`
(1,314,141 bytes); the exact index is `5348190a6f2e3e3d6472d9d13b5237d62cab4fb8b0b26446348ec51642b911dd`.
The independent actual receipt is `actual-review.json`, produced on the first
execution of `review_archive.py` without corrections or retries.

The auditor independently reconstructs the entire logical and source-alias index
from the approved config, raw plan and current source bytes. It verifies all 396
sorted regular blob members, their bytes and hashes, zero tar metadata and zero
gzip timestamp. The packet has 713 logical entries, 712 source aliases and 11
exact external phase18 boundaries. No previous packet internal aliases or object
files are copied.

Required coverage is exact: 452 checked workspace sources, 28 accepted fresh
source/log/record triples, two candidate audit triples, 20 runtime metadata files
and 133 context rows. All ten attempt triples and ten metadata files from the
failed old-baseline-v3 run are retained. The old producer ed95 snapshot resolves
the historical identity while the current producer4453 remains bound. All 44
current candidate pins and eight required absences pass.

The initial source review, final runtime review and ten-row runtime-v2 delta
review remain separate immutable receipts. Their earlier 703-entry estimate
applies to the first runtime bindings; v2 adds ten final static review contexts,
giving the verified 713 entries. The actual auditor reads tar member bytes into
memory only; it extracts no files, invokes no Lean or supplied/captured helper,
and changes no canonical or staging files.
