# Arithmetic prefix removal for the exact 246-state machine

`ArithmeticMachinePrefixPrefix246` proves halting equivalence before and after any internal prefix of an exact246 arithmetic run, from any internal configuration code. The doubled word in the module name joins the operation name `ArithmeticMachinePrefix` with the candidate suffix `Prefix246`.

The proof commutes two blocks of iterations and uses complete-configuration halt absorption. It therefore also covers a halt that occurs inside the prefix, without assuming that the prefix continues or subtracting clock bounds. The concrete `boot_halts_iff` theorem specializes this result to the checked 410,735-step startup and its complete numeric tape code.

The [arbitrary-start run graph](arithmetic_machine_run_from_prefix246.md) and [arithmetic bootstrap](arithmetic_bootstrap_prefix246.md) are the exact 246-state parents. This unit does not identify the post-bootstrap run with the seeded scheduler or validator, and it adds no ZFC proof-code comparison or closed PA consistency statement. The first source/audit attempt passed at default proof limits; the earlier guard with a pending RunFrom parent remains preserved.

The [successful record](results/arithmetic-machine-prefix-prefix246-verification.json) has 4 named axiom probes and 6 typed callers, with no warnings. Source and audit took 1.784 and 1.830 seconds. The fresh source object was recorded before its audit and remained unchanged afterward. The [history](results/arithmetic-machine-prefix-prefix246-history.json) retains the original preparation where present, source generation, pending-parent evidence, exact proof snapshots, logs and reviews. Initial unbuilt reviews retain their original scope alongside the later [independent evidence review](results/arithmetic-machine-prefix-prefix246-review.json).

The guard selects exactly 43 prerequisite project modules and 4 direct Foundation/Mathlib boundaries, with 113 pinned inputs. The portable copy changes only source/audit/parent default paths. Successful records retain actual historical source and object paths. These cache-dependent prerequisites are not rebuilt or redistributed by the packet.

With the exact recorded provider bytes available, prepare from the repository root:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_machine_prefix_prefix246.py \
  --repo "$PWD" \
  --output /tmp/zfc-arithmetic-machine-prefix-prefix246-prepared \
  --prepare-only
```

Preparation performs no compiler or version query. Omitting `--prepare-only` checks only this source and audit with one thread, 4,096 MiB, a shared 120-second bound and default new-source proof limits. It performs no dependency build or download and does not claim a clean-checkout build. Attribution follows Mira-Cult's original machine/calculus, Jeff Ketchersid's verification, Andrew James Wade's compiler framework and source63's contextual reduction.
