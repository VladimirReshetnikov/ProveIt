# Sign14 first shared-node byte chunk: failed guarded attempt

One stage proposes to check the 15-byte shared07 encoding and that the first
19 bytes of the included 689-byte row00 file are four operator bytes followed
by that encoding. It does not assert the other 670 bytes or the full row. Both
prior whole-row kernel-memory failures, the independently audited shared-code
provider, and original/source/scratch row00 bytes are pinned. The file-head proof exceeded the default recursion-depth limit; no module or
postflight was produced. Limits are
`-M3600`, 120 seconds per child, 4-GiB sampled RSS, 10-GiB host available-
memory floor and 5-GB disk precheck. Inherited provenance qualifications remain.

Author [no-Lean preflight](preflight.json) exited 0; [Independent prelaunch review](../../reviews/nine-sharing-sign14-prefix-chunk-prelaunch-independent/README.md) passed; the allocated Lean run failed with outer session 77800, numeric exit 1 ([receipt](attempt01/outer-result.json)); the [independent failure audit](../../reviews/nine-sharing-sign14-prefix-chunk-terminal-independent/README.md) passed.
