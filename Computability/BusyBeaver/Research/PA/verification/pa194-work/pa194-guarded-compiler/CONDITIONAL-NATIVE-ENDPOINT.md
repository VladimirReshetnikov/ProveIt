# Remaining premises of the native PA194 endpoint

The two checked modules assemble a derivation in `standardTheory` (iPRA),
using the pinned literal machine's `PA194ExplicitEndpoint.haltSentence` in
both directions. The Lean premises still to be supplied are:

- `ArithmeticCalibration`: source proofs of addition and multiplication
  coherence (`sA2`, `sM2`) and their fixed recursion clauses (`sA3`, `sM3`),
  in every covered candidate PRA model with an IΣ₁ arithmetic reduct.
- `SchedulerToPhysical`: a modeled scheduler halt implies a literal halt.
- `PhysicalToScheduler`: a literal halt implies a modeled scheduler halt.

`physical_nonhalt_implies_consistency` uses the first two. It combines the
ten already supplied source facts with the remaining coherence clauses,
translates an internal PA refutation, and uses the existing one-direction
transfer to iPRA. `consistency_implies_physical_nonhalt` uses only
`PhysicalToScheduler`, followed by the checked result that a modeled scheduler
halt yields an internal Foundation PA refutation. The two conclusions combine
in `consistency_iff_physical_nonhalt`. Neither implication for the literal
machine is established without its Lean premises.

From the repository root, with a fresh output:

```bash
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-guarded-compiler/check-conditional-native.sh \
  "$PWD" /dev/shm/pa194-conditional-native-repo
```

The two sources rebuild in one output, with five axiom reports checked for
`sorryAx`. The selected direct dependencies are hash-pinned; their further
transitive objects remain staged.
