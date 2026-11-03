# Independent review: five corrected 80-growth receipts

All five corrected author checks report successful compilation and self-pin their actual executing runner before and after compilation. The separately captured `check.py` result verifies the current runners against the pinned receipt hashes, archived and current source hashes, bit-identical old/new output objects, logs and printed axiom reports, the Lean binary, selected predecessor hashes, direct import resolution, and sampled resource guards. It does not run Lean. See `observations/attempt01/stdout` for individual full hashes and selected paths.

| Module | Corrected observation | Output SHA-256 |
| --- | --- | --- |
| `Direct80GraphGrowth` | `attempt02` | `c8655a2059ba3e038f097637c6bf36aaa0f14551514c60aacf574b3ca04d0bb6` |
| `Direct80GraphIndex` | `graphindex-attempt02` | `e9a8f99e13f8929d4f63380ceed2deed49a8fd6e65f50ab2146add94b153deb2` |
| `Direct80CAboveX` | `cabovex-attempt02` | `b1f887f080fd28a6f205e7d63e198dd3f8d2669aaeabc79303eb8b74c62208ef` |
| `Direct80Kpos` | `kpos-attempt02` | `87d27abaaa5f411ef60b54d097d1aed03364fd284e5c1af8f4d6958fcb5f69c7` |
| `Direct80Size` | `size-attempt03` | `d062b0dce7109382a9e9fa8ccad456b1c66002de4e131dd1b0f13280bd102d79` |

`Direct80CAboveX` selects the corrected graph-index object in its direct import path, and `Direct80Kpos` selects the corrected c>X object; both pin the corrected graph-index object as a predecessor. The new and old corresponding object bytes are identical. The recorded failed `size-attempt01` remains a failure and is not promoted by these checks.

The previous receipts hashed sibling `run.py`, so they do not authenticate their actual executing variants; the new receipts do not retroactively repair that historical provenance. The corrected runners still pin selected inputs and one inherited provider, not the entire project/package/dynamic closure or historical source-to-object ancestry. Resource measurements are sampled; the author-produced receipts are not independent Lean replays. The recorded theorem assumptions and the remaining machine-soundness gap are unchanged by receipt repair; see the earlier [main/rank/growth review](../ten-positive-80-main-rank-growth-independent/README.md).
