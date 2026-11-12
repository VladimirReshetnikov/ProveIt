# Independent source review: model-natural eta exact-index draft

The generated `index_window` and `indices_ordinary` theorem headers match the pinned upstream statements exactly after removing only `(hη : 0 < η)`. Eta remains a model natural. The q³ scale, R>=26, first and main Pell coordinates, early congruence, rank window, strong norm, and auxiliary-offset hypotheses and all conclusions are retained. This does not show that any graph supplies those hypotheses.

The order changes are noncircular: the draft first derives `R+1<=2n<=k` and k>0, then obtains c>0 from Y*k>0 and eta>=0. With Y>=2 and k>0, its new `k<kY<=c` supplies the strict comparison needed for n<m. In the rank bound the strict step remains `2R<2(R+1)` and the last step is weakened to `kY<=c`; the `2<=c` step in `indices_ordinary` similarly uses non-strict `kY<=c`. These replacements remain valid at eta=0. The proposed source's arithmetic and binder order were independently checked, but its tactics have not been elaborated.

The local private `large_of_six` and local `index_close` bodies are byte-identical to the pinned upstream declarations; they are copied into a separate namespace. The draft imports the upstream `P72Exact` module for its transitive dependencies, which does not authenticate its provider ancestry or validate the new proofs. The generator receipt reproduces. No parity lemma, product-factor extraction, graph zero map, compact port binding, equation reduction or iPRA endpoint follows from this source review.

From `Computability/DiophantineConsistency`:

```sh
python3 -I -S -B reviews/ordinary13-eta-zero-p72-index-independent/check.py | cmp - reviews/ordinary13-eta-zero-p72-index-independent/result.json
python3 -I -S -B research/ordinary13-eta-zero-p72-index-draft/generate.py | cmp - research/ordinary13-eta-zero-p72-index-draft/result.json
```
