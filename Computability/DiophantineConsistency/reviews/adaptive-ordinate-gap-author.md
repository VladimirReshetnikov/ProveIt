# Conditional direct-ordinate offset recovery

`ArithmeticAdaptiveOrdinateGap2011` proves the following in every IΣ₁ model, with internal values and no standard-model or gcd assumption:

- `magnitude_ge_two`: if `2 ≤ R`, `2*R < c`, and `SignMod c z R` (`z % c = R % c` or `(z+R) % c = 0`), then `2 ≤ z`. This excludes both `z=0` and `z=1`.
- `ordinate_gt_magnitude`: if `2 ≤ I`, `2 ≤ z`, and `I²*z² + y² = 1 + I²*y²`, then `z < y`.
- `positive_offset_of_gap`: if `magnitude (L,M) < y`, there is `u > 0` with `L+u=M+y` and `magnitude (L+u,M)=y`. The final `positive_offset_of_norm_residue` combines these under the displayed norm and signed-residue hypotheses.

Author build `/tmp/adaptive-ordinate-gap-scoped-wus_o_2w` **PASS**, with empty log. It reauthenticated all 1,717 selected base object hashes and the 15 current guarded project sources reachable from its direct imports. Four named Foundation/Mathlib imports are inherited boundaries without current source guards. Full canonical preauthentication had failed before creating an overlay because the unrelated `ArithmeticAdaptivePopulation2011` guard changed from `368ff11b…` to `dd929829…`; the reachable source graph does not include that module. Consequently this result is qualified to the checked direct-import source slice and inherited boundaries, not the whole canonical provider.

The five-file `adaptive-ordinate-gap-author-evidence/FILES.json` manifest has SHA-256 `48b4e906cc9047544be6dacb1be222751b80f8a64e32e616ead05ab128c786b8`. Reproduce with `python3 Computability/DiophantineConsistency/research/wang-chunk-full/build_ordinate_gap_scoped.py`; the current source graph and base provider are recorded in the state. Independent replay matched source, object and complete log; see the companion receipt. This establishes only conditional arithmetic lemmas: binding their hypotheses to a changed literal equation, both natural zero-set directions, and an 86-gate reduction remain open.
