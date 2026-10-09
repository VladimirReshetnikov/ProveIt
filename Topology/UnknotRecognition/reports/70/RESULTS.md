# Completed results

The compiled article contains the proofs and tables. All measurements below
are supplied-model arithmetic/component kernels, not knot-recognition timings.

The final unit suite passes 34 tests on CPython 3.13.5. Inner loops include 816
exhaustive two-generator systems, 800 random multivertex inputs, 1,800 dynamic
updates, 930 full-map guard identities, and 30 sharp scalar support examples.
The separate recorded 2,000-model audit passes all 179,684 point-weight,
100,000 connectivity, 7,760 representative, and 2,000 certificate checks.

Five shuffled paired rounds gave the following median times (milliseconds):

| Task | Reference | Optimized | Median paired ratio |
|---|---:|---:|---:|
| W=256, static | 1.353 | 0.241 | 5.67 |
| W=1024, static | 6.048 | 0.320 | 19.50 |
| W=4096, static | 29.307 | 0.453 | 61.66 |
| W=16384, static | 166.322 | 0.548 | 319.50 |
| 96 sparse prefix queries | 146.742 | 9.208 | 17.59 |
| 200 monotone full-map updates | 202.847 | 21.202 | 9.65 |

Static reference is an explicit lifted-graph oracle. Other reference arms
rebuild the same supplied model and replay all current attachments. None is the
maintained recognizer or AHT. Identical-arm ratios span 0.68–1.20: substantial
noise, retained in full. The ratios are illustrative observations, not precise
or universal speed factors. No certificate cost is included in those rows.

The separate complete construction+certificate+checker medians were 6.293 ms
for W=2^1024, 12.790 ms for W=2^4096, and 51.229 ms for W=2^24000. Serialization
was excluded from time, but the last certificate's compact hexadecimal JSON
size was measured as 823,491 bytes, excluding the separately supplied source.

The sharp theorem gives 2K+3 values, attained for every K>=1 by the scalar
construction in the article. Sparse attachments extend the bound to 2K+3b+h.
The epoch experiment has exactly nine effective map insertions among 200
updates. These are exact structural counts, not fitted timing models.

`integration/status.json` records the native suite, native cover comparison,
real knot corpus, and general-AHT comparisons as NOT_RUN. Do not report their
status as passing. No native code was changed.
