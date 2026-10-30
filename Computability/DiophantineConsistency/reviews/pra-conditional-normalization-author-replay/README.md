# Conditional Σ₁ normalization client

`PRA_proves_goal_of_isigmaOne_certificates` combines a finite actual Foundation IΣ₁ proof with finite strict-induction elimination. It requires (1) a proof-producing normalization certificate for every Σ₁ induction formula and (2) an explicit equality identifying the mapped conclusion with the candidate-PRA open-existential goal. Neither premise is discharged here. In particular, this packet does not prove general Σ₁ normalization, bounded collection, conservation, or the exact PRA consistency equivalence.

The author, private, and root independent runs passed at `/tmp/pra-conditional-normalization-author-evlmkcu7`, `/tmp/pra-conditional-normalization-independent-2irxe1_7`, and `/tmp/pra-conditional-normalization-independent-gxfv1eck`, respectively, against root's accepted parent `/tmp/pra-multi-induction-independent-48aut06c/lib`. Manifest SHA-256: `a13a1dae5d5e7b85d132b4594785c4293e60c09a59e2a7424e28e1695a454943`. The two direct parent source/object pairs and two output modules are authenticated; Foundation, Mathlib and the transitive parent graph are inherited. Source snapshots, full logs and both independent state records are retained; the simple author driver did not write a state file.

```sh
python Computability/DiophantineConsistency/reviews/pra-conditional-normalization-author-replay/replay.py --parent /tmp/pra-multi-induction-independent-48aut06c/lib
```
