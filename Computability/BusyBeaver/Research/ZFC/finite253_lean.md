`Table253.lean` imports the existing 253-state reduction attributed to mira-emmy in [public PR 20](https://github.com/jeff87654/busy-beaver/pull/20), pinned at `0d544f2a2e3c18f12278441a74b7879f31cbe856`. Mira-Cult designed the original 254-state machine and Jeff supplied its original verification. This work claims no authorship of that reduction.

The literal source is the retained `SetTheory/Cardinals/docs/reports/set-theory/zfc-closure-kernels/data/04-machine-machines-zfc_253.tm`, SHA-256 `84a21f714017c1d491008d86e9bd19c43cc6c5c9ae99a538b4f2314387827d95`, independently byte-matched to the pinned Git object. The Lean table has 253 operational states, 506 transitions, initial state 0 and separate halt target 253. Kernel `decide` checks its size, bounded targets, unique halt edge and initial action. The unique halt edge is state 102/read 1; the first blank action writes 1, moves right and enters state 1.

`Boot253.first1024` in `Table253.lean` checks an actual `BusyBeaver.Core.Machine.run` from the blank tape through 1,024 transitions. It reaches compact state 32, head −12 and the complete 14-one-cell tape given by `shortCheckpoint`. The original scoped check passed in 18.626 seconds; its finite table facts print no axioms, and `first1024` prints only `propext` and `Quot.sound`.

`Boot253.lean` extends the actual blank run through all **312,975 transitions** of the public startup. `fullBootstrap253` proves the state, absolute head and every tape read equal the explicit `bootTarget253` frame. Its state is compact 33, corresponding to old dispatch label 96, and its head is −17. `fullBootstrap253_tape` specifies the tape at every integer position, including its blank exterior. `fullBootstrap253_active_through` proves that no halt occurs at any elapsed time through this endpoint.

The target retains the complete public frame: a left marker followed by ten exterior blanks on the left half of the zipper; PC 000 plus 37 padding zeros and a header marker on the right; physical primary registers `[0,2,0,0,0,0,5,0,0]`; and all 158 spare blocks. Spare indices 2 and 8 have value 1 and the others have value 0. Each register value `v` occupies `false :: replicate (v+1) true`. The logical primary-register order is `[5,0,0,0,2,0,0,0,0]`. The finite zipper has left length 11, right length 385 and 178 true bits, each checked separately. Its lists describe tape contents; no equality with Core's internal sparse-list order or separate `Core.score` theorem is asserted.

`FiniteZipper.lean` supplies the generic proof interface. `ZipRep` relates a finite zero-exterior zipper to a Core configuration by state, head and all reads on both half-lines. `zipStep_sound` proves one-step preservation for every machine table. `zipBlock_sound` proves that a balanced block computes exactly `2^depth` Core steps. `read_eq_frameRead` exposes any integer tape position, and `active_through_of_endpoint` derives earlier activity from a nonhalting endpoint and Core's stationary halt convention.

The bootstrap proof uses a balanced, pretyped transition tree to make kernel reduction practical. `fast_transition_eq` checks all 506 actions against the unchanged literal table, with no axiom dependencies; `fastMachine_eq` proves exact equality of the two machine values. The three padding leaves outside the finite state domain introduce no operational states. This changes the evaluation representation, not the transition function or working-state count.

There are 83 kernel-checked computation blocks: 76 blocks of 4,096 steps, followed by 1,024, 512, 128, 8, 4, 2 and 1 steps. Each `bootChunk` proves a finite zipper equality with ordinary `by decide`; `advance_boot_checkpoint` then advances the actual literal `machine253.run`. Python generated expected checkpoint data only. The kernel checks every block and its final equality to the independently stated public boot frame. No trusted external trace checker, `native_decide`, custom axiom or admission is used.

The exact four-module scratch development passed before integration. Its full 83-block module took 272.11 seconds and peaked at 2,102,548 KiB; the separate lookup-equivalence module took 13.39 seconds. In a preliminary benchmark, one 4,096-step block through the original raw-array conversion took 46.33 seconds and 3.49 GB; the verified transition tree reduced early and late 4,096-step blocks together to 10.71 seconds. These are development measurements, not bounds on other hosts. The integrated modules are included in the opt-in umbrella and fresh serial source check. All 38 source modules passed in 340.606 seconds in a new scratch directory, with all recorded source hashes matched to the current files. [results/boot253-verification.json](results/boot253-verification.json) records the final verification status and source pins; [results/lean-verification.json](results/lean-verification.json) retains all module results and axiom audits.

This is an endpoint certificate, with no claim that 312,975 is the first dispatch arrival. The public argument's separate 330-step register prefix, arbitrary runtime invariant/site checker, instruction/compiler simulation, proof enumeration and arithmetic consistency export remain outside this Lean result. It supplies no new machine, state reduction or internal ZFC/PA consistency equivalence. It concerns the attributed public 253-state table, independently of the retired C/G compiler benchmarks.

Subsequent work now proves the separate [330-step register prefix](rm330_lean.md)
in Lean, using the exact 6,459-row public program and infinite-register path
semantics. Its primary register values match this boot frame. A representation
and arbitrary instruction-simulation theorem must still connect the two;
the extra spare tape blocks are not extra logical registers.

Rebuild its complete source closure, including the full finite startup computation, with:

```sh
uv run --no-project python Computability/BusyBeaver/Research/ZFC/check_lean.py
```
