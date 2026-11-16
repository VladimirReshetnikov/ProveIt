# Repeatedly bound separation leaf with size discharged

For every model of PRA plus IΣ₁, every internally valid arity-one property φ, and every model-valued n (including nonstandard n), `modelClose_separation_leaf_unconditional_size` derives

```
Pr (imp (tr e (modelClose n (sepRoot φ))) 1)
```

from `SeedAdmission bound reserve e (axm s (modelClose n (sepRoot φ)))`. The earlier code-size premise is proved rather than assumed. The argument shows that reopening preserves formula complexity, every binding raises complexity by one, every valid formula's complexity is at most its numeric code, and a separation root has complexity greater than two. Model-internal induction proves these results for nonstandard codes and n. The earlier repeated-binding leaf and model-push resource bounds are imported.

This proves a compiler leaf for the n-fold bound formula. It does not show that a particular n eliminates all free variables, construct the complete parameterized sentence scheme, or produce a native iPRA derivation.

Replay from the repository root (use a fresh final output directory):

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-axioms/check-model-separation-full.sh "$PWD" \
  /dev/shm/pa194-model-separation-seeded-replay \
  /dev/shm/pa194-model-closure-definability-replay \
  /dev/shm/pa194-model-closure-replay \
  /dev/shm/pa194-general-separation-replay \
  /dev/shm/pa194-ranked-open-separation-replay-v3 \
  /dev/shm/pa194-unrestricted-all-replay \
  /dev/shm/pa194-full-one-level-audit \
  /dev/shm/pa194-model-separation-full-replay
```

The staged replay recompiles the pinned source against retained prerequisite objects, checks six axiom reports and rejects `sorryAx`; selected imported objects are hash-pinned. Log: `/tmp/pa194-model-separation-full-replay.log`.
