# Representative activation: native review

These review drivers exercise the preserved selector in `reports/115` against
the maintained source geometry. They do not alter the default recognizer.
The mathematical review and its limitations are in
[`synthesis/representative_activation.tex`](../../synthesis/representative_activation.tex).

Run from any directory, passing an output filename:

```sh
python native_probe.py /tmp/activation-native.json
python relabel_probe.py /tmp/activation-relabel.json
```

`native_probe.py` authenticates all 126 cuts (120 existing plus the six signed
annulus fixtures), reconstructs exact unsigned counts, and tests three lower
policies: fixed source, fixed maximum passage, and all columns followed by
deferred forest discovery. It independently replays every proposed top
reduction and every rebuilt core certificate. It retains original row IDs,
repeated dual endpoints, input digests and exact local obstructions.

There are 378 trials: 366 successes and 12 independently checked local
obstructions. Every status agrees with the existing maximum-weight top
selector under the same lower policy. Only 28 of the 126 sources have interior
three-handles. The maximum exceptional boundary is 47; those examples succeed
on the incumbent path before the boundary cap. No uncapped search or general
negative recognition is claimed.

In particular, the full-column instances for
`nested_1_4_6/interior_links` and `interior_loop/interior_links` have respectively
seven mandatory source components versus graphic rank six, and two versus
rank one. No dual spanning tree can support private-column completion, even
before choosing a lower forest. This rules out every pair of forests for
this specific cancellation method, not handlebody structure or unknotting.

`relabel_probe.py` tests 30 relabellings of each of six named sources. All 180
maximum-passage and all 180 deferred trials already succeed; 178 source-forest
trials succeed and two have exact local obstructions. The selector finds no
new core positive. The search uses geometric preparation, and would perform
full source authentication for each new hit; there were no hits. These 180
sources are not counted among the 126 fully authenticated source packets.

Separately, the report's 71 tests and full algebra audit were rerun on a scratch
copy. The audit reproduced 8,061 exhaustive/random inputs, 300 planted inputs,
16,038 forced matroid queries, 2,369 closure comparisons, 1,951 sampled
independence checks, 255 projected-search comparisons and 503 exhaustive
small-field samples. Originals in `reports/115` remain unchanged. All retained
outputs are under `synthesis/data/activation-forest-*`.

The general selector is one-sided randomized and parameterized by the number
of rows incident to usable high-support columns. An unsuccessful capped or
randomized search is UNKNOWN. Native trials here use seed 11520261012,
eight rounds, boundary cap 20 and transition cap 100,000. None needed random
sampling or exhausted a cap. These are correctness experiments, not timing
benchmarks. No runtime integration or native performance improvement follows
from this review.
