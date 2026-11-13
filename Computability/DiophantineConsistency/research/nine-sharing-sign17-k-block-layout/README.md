# External K coefficient and byte-block decomposition

The read-only [checker](check.py) decodes the pinned K0 raw snapshot and builds
2021 little-endian radix-`2^47` digits from the frozen 3297-entry coefficient
array and the three sentinel powers. It checks each digit is below the radix,
then independently compares every group of eight radix digits with the
corresponding 47-byte block; the final group has five radix digits and 24
bytes. It exited 0. [result.json](result.json) records every block hash,
253 blocks in total, 126 distinct byte patterns and 128 all-zero full blocks.

Checker SHA-256:
`8ee7f7c0f32cb36bbe8f01d997faf7094c6aee0f0ef792621cb58bce76f43352`;
result SHA-256:
`390af8360b10c73cfa37584b4451f6b7f3b2becd40c6312321afde551706ea35`.
This is external Python/filesystem evidence about the frozen coefficient array
and raw snapshot. It does not prove in Lean that the coefficient array equals
the symbolic tile/rank sum, nor a Lean gzip/file/JSON/PDF binding. The [independent review](../../reviews/nine-sharing-sign17-k-block-layout-independent/README.md) passed; the packet is frozen.
