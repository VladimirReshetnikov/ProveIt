# Internal constructor template and the implication occurrence

`ArithmeticControlConstructor254` proves a reusable constructor contract and its actual implication occurrence at catalogue controls **195→222**. In an arbitrary internal model of IΣ₁, the input is a complete register file with both scratch coordinates zero. The theorem supplies a positive internal execution time and changes exactly:

- `TW := tagged(tag, first(oldWS), oldTW)`;
- `WS := second(oldWS)`.

Every other coordinate is preserved. The middle contract requires only `S2 = 0` and accepts arbitrary `S1`, constructing `tagged(tag, oldS1, oldTW)` while clearing `S1`.

The generic shape connects the checked WS-pop, pairing and fourfold-scale loops with literal control equalities. Its tag is in `Fin 4`; `TagChain` records a finite sequence of actual TW-increment instructions and targets. The chain proof uses structural induction on this finite syntax. Unbounded data and execution clocks range over the internal arithmetic model. The generic theorem does not assert that every tag already has a separately checked occurrence in the program.

`imp_constructor_run` instantiates tag zero at controls 195→222, producing `wim(first(oldWS), oldTW)`. The unchanged typed audit has seven named axiom probes and thirteen callers, including finite chain lengths 0, 1, 2 and 3, generic middle/full runs, coordinate preservation, and a concrete paired-WS client.

The selected root run passed source and audit with zero warnings under default Lean proof limits, one thread, a 4,096 MiB limit and a shared 120-second budget. The exact evidence and dependency pairs are in [the verification record](results/arithmetic-control-constructor254-verification.json); [the independent review](results/arithmetic-control-constructor254-review.json) checks the recorded current inputs, actual providers, raw output and pre-audit fresh-object capture. The imported closure has 100 project modules, six cached Foundation/Mathlib boundary pairs (five directly imported), and Init/Omega. The legacy MP parent recorded its source object before audit but lacked the later fresh-first-provider field. The guard resolves its recorded search path now and states that distinction explicitly.

The original source attempt failed before the audit: two uses of the reserved token `prefix` caused syntax errors, and 35 literal `resolveControl` reductions reached the recursion-depth limit. The repaired source renames those binders to `prior` and proves the same 35 targets through the exact finite tree walk, `resolve_source`, and `source_injective`. Independent parsing checks all 35 original target identities. No instruction, target proposition, arithmetic contract, audit caller or proof limit changed. [The exact history](results/arithmetic-control-constructor254-history.json) preserves the failed attempt, old source and guard, repair drafts and metadata failure, both preparations, successful raw logs and earlier source-only reviews with their original scope.

This unit does not complete the AX branch, the interpreter/Enum comparison, an internal binary-machine simulation, or the PA consistency equivalence.

The maintained [guard](check_arithmetic_control_constructor254.py) changes only the source, audit and provider-proposal default paths from the executed guard. Replay requires the exact historical dependency/cache providers in the verification record; this publication does not certify a clean-checkout dependency rebuild. A preparation-only run does not invoke Lean:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_constructor254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --mp-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-mp254-verification.json \
  --output /tmp/fresh-constructor-preparation \
  --prepare-only
```

The provider inventory and recorded dependency root must match the historical record exactly. After reviewing that preparation, omitting `--prepare-only` in a fresh output directory runs source and audit under the same bounds.
