# Strict Σ₁ induction certificate

`strict_certificate` constructs the certificate required by the conditional normalization client for any arithmetic predicate syntactically `∃ D` with `D` bounded. It packs all finitely occurring free parameters, proves the original and packed predicates equivalent in arbitrary candidate-PRA models, and produces an actual proof of the mapped induction axiom from a strict bounded-matrix induction axiom. It does not normalize arbitrary `Hierarchy 𝚺 1` formulas: bounded-universal collection in particular remains open. It does not by itself prove the exact Con(ZFC) equivalence in PRA.

The author, private, and root independent builds passed at `/tmp/pra-strict-sigma-certificate-author-7_1isrec`, `/tmp/pra-strict-sigma-certificate-independent-psxq74ju`, and `/tmp/pra-strict-sigma-certificate-independent-5p53_c4m`, using root's accepted parent `/tmp/pra-conditional-normalization-independent-gxfv1eck/lib`. Manifest SHA-256: `9020c99e81ea8d8fc7b8a384a0b5b65c2390738b5effe8974e227a4d5a75bc31`. The seven listed direct parent source/object pairs and both output modules are authenticated; Foundation, Mathlib and the transitive parent graph are inherited. The author snapshots/full logs and both independent runs' states, snapshots and full logs are retained. The author driver did not record a state file.

```sh
python Computability/DiophantineConsistency/reviews/pra-strict-sigma-certificate-author-replay/replay.py --parent /tmp/pra-conditional-normalization-independent-gxfv1eck/lib
```
