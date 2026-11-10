# External candidate K ranking witness

The [generator](build.py) loads the pinned external padding certificate and
frozen coefficient array, then writes [witness.json](witness.json). It
transcribes the Lean `recoveredIndex` and `selectorWeight` formulas in Python,
and checks that the 942 candidate indices form a permutation, Start maps to
index 0, each doubled candidate weight equals the corresponding coefficient,
and positions 1–941 have strictly decreasing weights. The author run exited
0. The witness gives explicit physical position, candidate original index,
tile coordinates and weight for each row.

Generator SHA-256:
`56bfcc1176973e6fade3630b2bd317c0c293aef7644c0c5e5a40a1b36d0e0daf`;
witness SHA-256:
`7f50654d30197158157533857892ddde91b7234bfdfe0cc6089282e5613b81a3`.
This is an untrusted external candidate generated using Python; it does not
prove the actual Lean tile/index/weight values, ranking, K coefficient sum,
or any file/gzip/JSON binding. The proof plan is in the separate
[ranking design](../nine-sharing-sign17-k-ranking-design/README.md).
The [independent review](../../reviews/nine-sharing-sign17-k-ranking-witness-independent/README.md) passed; the packet is frozen.
