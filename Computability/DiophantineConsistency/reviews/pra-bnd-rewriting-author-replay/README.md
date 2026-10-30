# Bounding and rewriting

The new sources are `PRABndRewriting.lean` and `PRABndRewritingChecks.lean`. The author build passed against the root independently replayed post-five-induction provider, authenticating the one local source/object parent `StrictSigmaOneInduction`. Root replay `/tmp/pra-bnd-rewriting-independent-7n8kd56j` and private replay `/tmp/pra-bnd-rewriting-independent-08d63zgb` passed with matching source, object and complete-log hashes. Author/root sources, logs and all three terminal states are recorded; Foundation and Mathlib are inherited.

`natural` proves semantic commutation of `bnd` and an arbitrary rewriting of an arithmetic semisentence, for all valuations and the same distinguished bound in any ordered-ring structure on a type in `Type` (Lean universe zero). It includes arbitrary terms and nested quantifiers, without requiring a candidate-PRA model, collection or induction. It enables local bounded-witness proofs to be applied under the actual substitutions in larger formulas; it does not itself construct a witness majorant or prove the ZFC refutation bound certificate.

```sh
python3 Computability/DiophantineConsistency/reviews/pra-bnd-rewriting-author-replay/replay.py \
  --parent /tmp/pra-after-five-induction-independent-p0oew8oa/lib
```
