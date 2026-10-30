# Direct-ordinate 86 early index and comparison: author replay

`AdaptiveDirectOrdinate86Comparison` proves the existing `EarlyIndex` and `Comparison` statements from an actual 86 literal zero in any model of IΣ₁, assuming a positive first port, positive witness coordinates and the two explicitly displayed port inequalities. It applies the separately checked 86 index and rank facts. The comparison includes the useful bounds `13≤n`, `14≤m`, and `2R<c`; it does not by itself prove `SignMod c |V| R`, 86/87 zero-set equivalence, or an HA proof-existence theorem.

The scoped author run `/tmp/adaptive-direct86-comparison-n59aave3` passed. It rebuilt post-merge `ArithmeticAdaptiveEarlyIndex2011`, then `ArithmeticAdaptiveIndexComparison2011`, then the 86 client over the refreshed rank chain. The parent rank provider is the author object, whose independent replay must be considered separately. Reproduce with `python3 Computability/DiophantineConsistency/research/wang-chunk-full/build_direct_ordinate_comparison.py`. Selected source/object/full-log records and graph guards are checked before and after; wider canonical and Foundation/Mathlib boundaries remain historical, not a complete source-current closure. State SHA-256 `358d7571151bc7132c076e4fa7990b36e6e694db602be314aaec2650eb542367`.

| Module | Source SHA-256 | Object SHA-256 |
|---|---|---|
| `ArithmeticAdaptiveEarlyIndex2011` | `3904ffe8c5c0730da601aa7ab0fb2db411064425c933067911e049a2835052c3` | `9bad3d79470db9486d333bb5b797cb8d5422dbe0c058eb23fae04318f00f12de` |
| `ArithmeticAdaptiveIndexComparison2011` | `a6f60fd74fbc8834232368c913015dd1c7a2e5f80b01ca6d958a74033dbfaa5a` | `d6ba58f47db9f2a0441f5d3558026c17d999b0e7f0f54a8eb75953b59a072a87` |
| `AdaptiveDirectOrdinate86Comparison` | `c83b46edbb48695bf53e5b517556c3fb7a2b18227f3873fded7e22519e30df59` | `f41c47f5bcc2054666ebfa4c5ed010fe2bfe033df258ebb680a2b6520e0e8d5b` |

All complete logs are empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). State, driver, source snapshots, full logs and timings are in `adaptive-direct86-comparison-author-evidence`; manifest SHA-256 `e5948c3c2868d904cc3e3b3a9772c2df86a8e82215c9a179d27af600d1f11626`.
