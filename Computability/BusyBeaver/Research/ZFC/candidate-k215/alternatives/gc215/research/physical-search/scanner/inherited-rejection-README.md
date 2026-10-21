# Rejected deletion of the return-scanner state 50

The proposed 214-state table removes native state 50 and redirects 34/0 from `0 L50` to`0 L75`. It is included strictly as a failed research experiment.

The shortened table reaches a calibrated blank prefix, but fails the primitive contract. For source ordinal 26, the zero case of CD1 at code `1101001001000000`, take all nine logical registers zero, gap zero, and spare list`[0]`. The accepted baseline reaches its first clean dispatcher frame after 588 steps, with code`110100100100001`. The altered table reaches a clean dispatcher frame after 662 steps whose code instead has a one at cell 12 rather than 14. All remaining one-cells agree.

Run:

```
python3 -B research/rejected-return214/check_counterexample.py
```

This independently replays both complete concrete traces and checks the expected register-machine successor. It establishes failure on a valid arbitrary primitive frame, not a conclusion about the modified machine's blank-run consistency equivalence.

The complete symbolic investigation proves 6,104 of 6,176 cases and leaves 72 cases unproved. The failures are concentrated at exactly 37 source addresses ending in six zeros. The concrete counterexample supplies stronger evidence for one of these cases; the other 71 are recorded as failures to prove, without claiming 71 additional semantic counterexamples.
