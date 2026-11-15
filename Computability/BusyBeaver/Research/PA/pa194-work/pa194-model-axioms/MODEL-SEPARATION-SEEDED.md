# Seeded model-length separation closure

In models of PRA plus IΣ₁, `modelPush_fields` gives the exact base and reserve after n model-valued pushes, and `modelPush_ranked` preserves the ranked environment at every model-valued n. The former is proved using model-internal Σ₁ induction, as is the latter.

`modelClose_separation_leaf_seeded` proves the target separation leaf for the n-fold closure code from `SeedAdmission` at that very axiom, assuming `n + 2 < modelClose n (sepRoot φ)`. It does not assume pushed-environment resources or the open leaf as independent hypotheses. The size bound remains an explicit premise, as does the well-formed arity-one property. This does not establish that n closures eliminate all free variables or produce a native iPRA derivation.

Replay, using a fresh final directory:

```sh
bash Computability/BusyBeaver/Research/PA/pa194-work/pa194-model-axioms/check-model-separation-seeded.sh "$PWD" \
  /dev/shm/pa194-model-closure-definability-replay \
  /dev/shm/pa194-model-closure-replay \
  /dev/shm/pa194-general-separation-replay \
  /dev/shm/pa194-ranked-open-separation-replay-v3 \
  /dev/shm/pa194-unrestricted-all-replay \
  /dev/shm/pa194-full-one-level-audit \
  /dev/shm/pa194-model-separation-seeded-replay
```

This is a staged replay with imported objects prebuilt. The source and two selected imported objects are hash-pinned before and after, four declarations are checked for axioms, and the log is `/tmp/pa194-model-separation-seeded-replay.log`.
