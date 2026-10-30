# Generic 87→86 zero direction: author replay

`AdaptiveDirectOrdinate86Reverse.old_positive_zero_to_new_natural86` proves that any actual positive-coordinate 87 literal zero gives a positive-shifted 86 zero in every IΣ₁ model, under only a positive first port. It transfers the exact split equality to the maintained literal, obtains the old auxiliary norm and signed-ordinate representation, and derives the needed ordinate positivity; these are not assumed.

Scoped author run `/tmp/adaptive-direct86-reverse-rco9u5ze` passed after rebuilding current `ArithmeticAdaptiveAuxNorm2011` against the refreshed strong-norm chain, then the reverse client. State SHA-256 `d73c830bd28ef23e1da6a4f4551dfef1805b7fedf6a0f9e45e399fa832e270cf`. Reproduce with `python3 Computability/DiophantineConsistency/research/wang-chunk-full/build_direct_ordinate_reverse.py`. Selected source/object/full-log and narrow graph guards are rechecked; wider canonical and Foundation/Mathlib boundaries remain historical, not a complete source-current closure. This generic theorem is not the fixed-port combined equivalence or HA proof-existence.

| Module | Source SHA-256 | Object SHA-256 |
|---|---|---|
| `ArithmeticAdaptiveAuxNorm2011` | `479aa3e6a629acb624fed2070d56640ed7d5e4fd2b7316c81e8345fa254f0134` | `be85cbbb7f2ba9fa799cc864210ba6fc98a5638c95f42e5c04578593e2315d0e` |
| `AdaptiveDirectOrdinate86Reverse` | `b77ccd94d3b8262495023edf95913b5cf2541d39a3c6f175b0239304867a580a` | `fd4cc911fb1ebc21a9a5d18420a7156674608f576bf526e1dac9177a4502d5ad` |

Both complete logs are empty (SHA-256 `e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855`). State, driver, source snapshots, full logs and timings are in `adaptive-direct86-reverse-author-evidence`; manifest SHA-256 `ce534752026146177254fc5f17c97c648c681b71bbffb1b978d246212a13705f`.

The first attempt `/tmp/adaptive-direct86-reverse-ly436k27` recorded `FAILED` because the client did not open the `oldIndex` namespace; its successfully built AuxNorm object does not make the client successful. The failed state, source snapshots, logs and timing are separately preserved in `adaptive-direct86-reverse-failed-evidence`, manifest SHA-256 `d26460b609fd925a5bc37206a9fe2769347f0a7c34bbe071e4ff511835e4df35`; the corrected source was rebuilt from scratch for the successful run.
