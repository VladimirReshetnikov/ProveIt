# Review, execution release and exact author replay

The historical preparation was committed as
8fdb2df4e198783dd46e62cb58b0390f4e0a7260. Its HOLD_INVENTORY hash is
2c2a835e5b17937e07d43b00ec4cf8e95c2a0b10f3e9abd1bd17ace884d715d4.
Every historical core/input/pin byte is retained. The README and proof's
HOLD wording describe that preparation; these separate records document
the later authorized execution, without silently rewriting reviewed prose.

Both complete static reviews approved the exact checkpoint without a finding:

- reviews/ten-positive-doubled-product-square-static-root.md,
  SHA256 52e62c1dc911502c3e318983a251fc54b22dc31d96c107679bb198c59493a702;
- reviews/ten-positive-doubled-product-square-static-peer.md,
  SHA256 ef4b1da347694af9718a4b27fb19d2f5f5dbbc63fc2016b040a7e145fe6c698d.

Root then explicitly released only the four README commands: normal full
check, optimized full check, normal copy-only check, optimized copy-only
check, sequentially with stop on failure. All four exited zero on their
first invocation. Complete JSON and full stdout are retained; their exact
paths, byte lengths, commands and hashes are in AUTHOR_RUNS.json. No other
incoming program, parent/source compiler, generator, renderer, TeX or Lean
command ran. The full mode imported only the unchanged reviewed kernel.

The complete author outputs are:

| Receipt | SHA256 |
| --- | --- |
| CHECK.json | 8cca1fa15a5747727ac5b3edaea9a124f1b52dcdd62ccaad9e4e92ed9ba81dc5 |
| CHECK_OPTIMIZED.json | f98333b2998e5aaa8621986eba4a42550acf4e487474fa02b81a8effc21929b5 |
| COPY_CHECK.json | 60fbc156d363d5ae19343fb530e497b7a5b60b2cd817f3bb61f83b7033cc80f4 |
| COPY_CHECK_OPTIMIZED.json | c408963902c8571064acb1660c98d33c057e81e6f95d1356840187f34438866e |

Each corresponding verification/*.txt file is exactly the same whole byte
string as the JSON output. All controls and full certificates are retained.
There were no failures, patches, retries, substituted coefficients or hidden
layout/code fallbacks. Only these result/calibration/replay records and the
final actual inventory were added after the reviewed preparation. Root's
fresh independent scratch replays and final acceptance record remain outside
this author packet; no root receipt is copied here or treated as an author run.
