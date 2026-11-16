# Simulation with an existential physical clock

`simulateBeforeHalt` composes positive literal segments in candidate PRA models
with an IΣ₁ reduct. At each active source index, there exists an aligned physical
clock at least that index. Each verified instruction supplies its own clock.
The two witness transfers use a bounded first-hit supplier and, respectively,
halt persistence at active roots or a physical halt segment.

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194/ipra/machine-code/check-existential-model-length.sh \
  "$PWD" /dev/shm/pa194-existential-model-length-repo
```

The incremental replay checks all three declarations for `sorryAx` against
staged machine and Foundation objects. The concrete controller invariant and
all-site contract coverage remain separate premises.
