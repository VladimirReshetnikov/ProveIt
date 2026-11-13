# External MF source-port block-layout reconstruction

The read-only [checker](check.py) extracts ten representative little-endian
byte blocks from the pinned gzip/raw MF_source snapshot and reconstructs all
252 blocks using twelve runs. It independently reconstructs the proposed 2012
radix digits of `highPort + beta` and compares every representative block's
radix and byte decodings. It exited 0; [result.json](result.json) records the
segment counts and hashes. Checker SHA-256:
`d316191f784d0f36ef5f64a62c9b7f5383866a40a577cea7250fd3710bb3eee0`;
result SHA-256:
`31ed2aa6a062402179dfee6bcc203cec9d2cccf190f2e45d25a817acca93f5e4`.

This is external Python/filesystem evidence, not a Lean whole-port theorem,
file/gzip theorem or JSON/PDF binding. The [independent review](../../reviews/nine-sharing-sign17-mf-block-layout-independent/README.md) passed; the packet is frozen.
