# Internal AX implication constructor at controls 248–275

[ArithmeticControlAXConstructor254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXConstructor254.lean) proves the implication-constructor contract for the actual register-program segment **248→275**. It applies to every internal register file in a model of IΣ₁, assumes both scratch coordinates are zero, and supplies a positive execution time in that same model.

The complete output file has:

- `TW := wim(first(oldWS), oldTW)`;
- `WS := second(oldWS)`;
- every other coordinate unchanged, including both scratch coordinates.

The finite occurrence instantiates the checked [generic constructor](arithmetic_control_constructor254.md). Its 27 executing instruction edges and 35 successor branches are bound to the literal control catalogue. The five shapes have the same structure as the earlier 195→222 occurrence, with control indices shifted by 53. Each target proof retains the exact tree path, consumed length and leaf instruction. The unbounded execution follows from the generic constructor theorem; no semantic run premise is assumed.

The [typed audit](arithmetic_control_ax_constructor254_audit.lean) contains three named axiom probes and four callers: entry and exit bindings, the arbitrary internal-file contract, and a specialization to `WS = cantor(left, rest)`. The first source/audit run passed in 57.985 and 1.665 seconds with zero warnings. The two control facts use `propext`; the execution theorem uses `propext`, `Classical.choice` and `Quot.sound`. The [verification record](results/arithmetic-control-ax-constructor254-verification.json) preserves the exact commands, logs, provider identities and fresh-object captures before audit.

The [independent source and evidence review](results/arithmetic-control-ax-constructor254-review.json) independently decoded all 28 control bindings, including the exit, and all 35 target paths from the complete literal tree. It checked all 229 recorded inputs, the exact 101-project import closure, six cached Foundation/Mathlib pairs (five direct imports), and Init/Omega. That reviewer subsequently authored the publication builder; root-owned execution, installation and maintained-default preparation remain separately recorded. [The history](results/arithmetic-control-ax-constructor254-history.json) retains the exact source, audit, guard, source-only inventory, preparation, raw actual logs and reviews. The selected source passed its first actual attempt.

The sole immediate proof parent is the checked generic Constructor run2. Its source object and first provider were captured before its audit, as were this unit's. The [provider proposal](results/arithmetic-control-ax-constructor254-provider-proposal.json) retains exact historical source/object pairs. Replay needs those cached providers; compiled caches are excluded from publication, and this packet does not certify a clean-checkout dependency rebuild.

The maintained [guard](check_arithmetic_control_ax_constructor254.py) changes only its source, audit and provider-proposal default paths. Preparation performs no compiler or version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_constructor254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --constructor-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-constructor254-verification.json \
  --output /tmp/fresh-ax-constructor-preparation \
  --prepare-only
```

Omitting `--prepare-only` in a fresh output directory runs the source and audit under default proof limits, one thread, 4,096 MiB and a shared 120-second budget. The contract covers this constructor occurrence. The full AX branch, interpreter/Enum comparison and internal binary consistency equivalence remain separate obligations.

The register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the source and attribution.
