# Shift invariance of separation roots

`sepRootPure_shift_fixed` proves for every ordered-ring model of IΣ₁ and every model element `p` satisfying `IsSemiformula SourceL 1 p` and `shift SourceL p = p` that `shift SourceL (sepRootPure p) = sepRootPure p`. The proof expands the coded separation constructor and uses the source syntax constructor equations, including internal negation and bound-variable shifts. The quantified model element may be nonstandard; the fixed-shift premise is explicit.

This is a constructor closure lemma. It does not construct `Theory.Δ₁`, show that arbitrary model codes are standard formulas, identify the classifier-defined theory with PA or all parameterized separation instances, establish proof compilation for PA, or prove a native iPRA theorem or a machine-halting equivalence. In particular the model assumptions are arithmetic IΣ₁, not native iPRA.

The incremental audit rebuilds `PA194ClosedSepTheory` and its axiom-report top in an independent output, using the separately checked uniform-classifier and standard-no-free overlays, compiler baselines, and prebuilt workspace dependencies. It is not a clean rebuild of those dependencies. The source's `PA194ModelStandardNoFree` import is retained for the prospective standard-theory correspondence, though the constructor theorem does not use its result.

Reproduce from the repo with an unused `NEW_EMPTY_OUTPUT`:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194-work/pa194-model-logic/check-sep-root-shift.sh "$PWD" NEW_EMPTY_OUTPUT \
  /dev/shm/pa194-uniform-sep-combined-replay /dev/shm/pa194-standard-no-free-replay \
  /dev/shm/pa194-closed-sep-classifier-replay /dev/shm/pa194-generic-sim-replay \
  /dev/shm/pa194-adjunctive-sim-v2-replay /dev/shm/pa194-shift-interface-replay \
  /dev/shm/pa194-unrestricted-existential-v2-replay /dev/shm/pa194-qf-ranked-existential-audit \
  /dev/shm/pa194-ranked-open-separation-replay-v2 /dev/shm/pa194-adjunctive-admission-audit \
  /dev/shm/pa194-general-shift-replay /dev/shm/pa194-general-reverse-shift-replay \
  /dev/shm/pa194-unrestricted-all-replay /dev/shm/pa194-general-freshness-audit \
  /dev/shm/pa194-observational-general-audit /dev/shm/pa194-full-one-level-audit
```
