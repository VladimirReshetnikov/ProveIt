# Weaken the terminal contract, without a reverse simulation

This is a small further API simplification of the new compiled positive-stuttering proof, not a new machine or a newly compiled theorem. The input is pinned in SOURCE_PIN.json. The derivative Lean file and patch are explicitly uncompiled; their original proof code is attributed to the source packet.

## Exact mathematical statement

Let A and B be deterministic partial transition systems: next maps a configuration to an optional successor, and terminal means next = none. Let R relate their configurations. Assume:

1. Every source transition from a related pair is simulated by a successful positive-length target run to another related pair.
2. If the source is terminal at a related pair, the target eventually halts.

Then related configurations are equihalting. Neither immediate terminal equality nor an independently supplied terminal-reflection obligation is required.

For preservation, induct on the finite source run. A terminal source uses assumption 2; a working source uses its target block and the induction hypothesis. For reflection, induct strongly on the length of a terminating target run. If the source is already terminal, finish. Otherwise its simulated positive block is a successful prefix of that deterministic terminating target run. Removing it leaves a strictly shorter terminating run, and induction supplies source termination. This argument uses assumption 1 alone. In the inspected source, Simulation.reflects_halts does not access the terminal field at all.

The original terminal equivalence implies the new terminal-drain premise by halt_now, so the existing strict interface can be retained with a compatibility constructor. The code-level change in the independent draft is only the terminal field and the preservation proof's base case, plus namespace/documentation changes. No existing production interface is overwritten.

## Why this is not just a weaker name

A terminal source can relate to a target that performs a short cleanup and then halts. This satisfies the new contract but not immediate terminal agreement. Such cleanup is a natural outcome of instruction fusion and local state-fold searches. For an executable certificate, supply a finite successful trace ending at a literal target halt for the terminal case. The abstract theorem must not turn arbitrary divergence into a terminal result.

This does not by itself simplify CM215's concrete marker invariant or yield 214 states. Its benefit is removing an unnecessary API obligation and permitting a broader class of future transport certificates. It may have negligible impact on current source-line counts.

## Critical boundary: partial versus absorbing semantics

The proof relies on successful target runs being unable to step past a terminal configuration. It must NOT be transferred unchanged to a total step function with an absorbing halt: a looping source could then be matched forever by positive absorbing steps at target halt. The previous report's total-step theorem therefore needed an explicit halt condition. Likewise, zero-length blocks are insufficient even for partial semantics.

## Independent finite corroboration

Run `python -I check_terminal_contract.py`. It enumerates all 36,864 combinations of two-state source systems, three-state target systems, and relations. It checks reflection whenever positive advance holds, and equivalence whenever advance and terminal drain both hold. It also exhibits terminal cleanup, and counterexamples to omitting positive progress or terminal drain. These finite tests corroborate the ordinary proof; they are not Lean/Rocq kernel validation. result.json records the exact counts. No imported executable is run.
