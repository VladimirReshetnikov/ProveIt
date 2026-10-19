# Complete coverage history

The [coverage result](../../../rotation240_coverage_complete.md) records all 565 successful modules. Its lossless history is preserved as four ordered parts of one gzip stream, each at most 32 MiB. Splitting changes no archive contents, source, audit, or proof record.

The [index](history-parts.json) records each part and the original archive identity. From this directory, reconstruct it with:

```sh
cat history.json.gz.part-00 history.json.gz.part-01 history.json.gz.part-02 history.json.gz.part-03 > /tmp/rotation240-coverage-history.json.gz
sha256sum /tmp/rotation240-coverage-history.json.gz
```

The resulting SHA-256 must be `35e19e6603b4cd37ebe4148d7ede59ae1c7388cb99d25b772751408215417097`; size is 129,525,059 bytes. Decompress as ordinary gzip JSON. Its `aliases` map gives the hash of each original path; `blobs` contains the exact UTF-8 text under that hash. The history includes raw proof records and logs, preparations, the generated family, publisher source, and independent reviews, including the two corrected reader attempts. Compiled objects are excluded.
