# Internal AX prefix through its first implication

[ArithmeticControlAXFirstImp254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXFirstImp254.lean) composes checked register-program contracts at **136→222**, then extends that composition to the actual AX entry at **41→222**. Both the input file and the positive execution time are arbitrary internal values in a model of IΣ₁. Each execution contract assumes both scratch coordinates start at zero.

For the segment 136→222, the exact output `firstImpFile file` has `TW = wim(oldAC, first(oldPL))`, `WS = cantor(oldTW, oldWS)` and `PL = second(oldPL)`; all other coordinates retain their old values.

For the longer prefix 41→222, the exact output `axFirstImpFile file` has:

- `TW = wim(oldAC, first(second(oldPL)))`;
- `WS = cantor(wal(oldP1, oldCache), cantor(oldTW, oldWS))`;
- `cache = oldCache + first(oldPL)`;
- `PL = second(second(oldPL))`;
- every other coordinate unchanged, including AC, P1 and both scratch coordinates.

The proof composes the checked GEN/read prefix, argument and plain pushes, TW read, and implication constructor. Literal control equalities identify their common endpoints. Whole-file equalities discharge each next segment's scratch hypotheses, and `controlRun_add` combines their internal times. The theorem does not require an external bound on a register or runtime.

The [typed audit](arithmetic_control_ax_first_imp254_audit.lean) has 14 named axiom probes and 18 callers. It covers the three control joins, both whole-file results, both executions, a paired-parameter specialization and scratch preservation. The selected second run passed in 3.124 seconds for source and 2.398 seconds for audit, with zero warnings. The three control joins have no axioms; the eleven file/execution reports use only `propext`, `Classical.choice` and `Quot.sound`. The exact commands and outputs are retained in [the verification record](results/arithmetic-control-ax-first-imp254-verification.json).

The first source attempt failed before audit at a rewrite that expected the private `pushedFile` abbreviation while the preceding equality still displayed `pushFile (argumentPushFile acReg file)`. Three explicit `change` lines fold that same definition before composition. The theorem statements, audit and proof limits are unchanged. [The history](results/arithmetic-control-ax-first-imp254-history.json) preserves both sources and guards, the source failure, the exact repair, both preparations, the successful run, raw logs and all source/guard/evidence reviews. It also retains an earlier metadata-authoring rejection caused by a mistyped source hash; no guard or compiler ran in that rejected attempt.

The [independent actual-evidence review](results/arithmetic-control-ax-first-imp254-review.json) checks all 257 recorded inputs, the exact 109-project import closure, six cached Foundation/Mathlib pairs (five directly imported), Init/Omega, and the fresh object and first provider saved before audit. It is independent of source, guard, repair and execution authorship. All four immediate parents also record their source objects and fresh first providers before their audits; older ancestor provenance remains within its original scope.

The [provider proposal](results/arithmetic-control-ax-first-imp254-provider-proposal.json) is the preserved initial proposal. Its original source pin is historical; the repaired source, guard delta and successful record identify the selected successor. Replay requires the exact recorded cached providers. Compiled caches are excluded from publication, and this packet does not certify a clean-checkout dependency rebuild.

The maintained [guard](check_arithmetic_control_ax_first_imp254.py) changes only its source, audit and provider-proposal default paths. Preparation invokes no compiler or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_first_imp254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --gen-read-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-gen-read254-verification.json \
  --argument-push-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-argument-push254-verification.json \
  --read-tw-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-read-tw254-verification.json \
  --constructor-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-constructor254-verification.json \
  --output /tmp/fresh-ax-first-imp-preparation \
  --prepare-only
```

Omitting `--prepare-only` in a fresh output directory runs source and audit under default proof limits, one thread, 4,096 MiB and a shared 120-second budget. This completes the AX prefix through its first implication. The rest of the AX branch, interpreter/Enum comparison and internal binary consistency equivalence remain separate obligations.

The register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
