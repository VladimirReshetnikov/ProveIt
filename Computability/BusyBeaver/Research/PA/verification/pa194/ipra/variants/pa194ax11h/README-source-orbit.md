# Candidate source/site-10 scheduler orbit

`PA194AX11HSourceOrbit.equivalent_site10` states, in every PRA model whose arithmetic reduct satisfies IΣ₁, that the generated AX11H source iterator reaches program counter 10 if and only if the supplied command scheduler reaches its halt flag. Its parameters are arbitrary scheduler step, halt-flag and source-frame codes. The theorem requires: the initial source state equals the supplied initial frame; every frame has source PC 25; every nonhalting scheduler command reaches the next frame in a positive model-valued number of candidate source steps; and every halting scheduler command reaches candidate source site 10. These are explicit hypotheses, not established command contracts.

The proof checks that candidate site 10 executes the halt row and the resulting sentinel is absorbing, then applies a model-valued synchronization argument. The public predicate is the source site-10 predicate; the sentinel is an internal proof device. This theorem alone does not identify a concrete scheduler, discharge any command contract, or connect the generated source to a literal Turing machine.

After building the candidate prerequisite, run:

```sh
bash Computability/BusyBeaver/Research/PA/verification/pa194/ipra/variants/pa194ax11h/check-source-orbit.sh \
  /path/to/fresh/output /path/to/candidate-output
```

The checker compiles both local sources from repository paths, snapshots and rechecks their hashes and the direct candidate-source object hash, and records the Lean search path. It retains the candidate output's documented prebuilt transitive baseline.
