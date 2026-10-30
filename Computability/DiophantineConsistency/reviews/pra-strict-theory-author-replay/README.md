# Strict induction source-theory comparison

`PRAStrictTheoryComparison.comparison` transforms an actual proof over PA-minus plus induction for bounded predicates or syntactic existential-bounded predicates into a candidate-PRA proof of a universally closed open-existential goal, assuming the explicit equality identifying that goal with the language-mapped conclusion. Its source theory is shown included in Foundation IΣ₁. It does not establish the converse inclusion, arbitrary Σ₁ normalization or bounded-universal collection; it therefore does not establish full IΣ₁ conservation or the exact Con(ZFC) equivalence in PRA.

The author, private, and root independent runs passed at `/tmp/pra-strict-theory-author-n46om5sg`, `/tmp/pra-strict-theory-independent-4ivr2_eo`, and `/tmp/pra-strict-theory-independent-4m7t2sku`, respectively, against root's accepted parent `/tmp/pra-strict-sigma-certificate-independent-5p53_c4m/lib`. Manifest SHA-256: `0ecc08b43f054e93c80f5c2dafb30c25b96a86b713858a1459b98ade0893ada8`. The five listed direct parent source/object pairs and four output modules are authenticated; Foundation, Mathlib and the transitive parent graph are inherited. Author snapshots and full logs, and both independent states, snapshots and logs are retained. The author driver did not record a state file.

```sh
python Computability/DiophantineConsistency/reviews/pra-strict-theory-author-replay/replay.py --parent /tmp/pra-strict-sigma-certificate-independent-5p53_c4m/lib
```
