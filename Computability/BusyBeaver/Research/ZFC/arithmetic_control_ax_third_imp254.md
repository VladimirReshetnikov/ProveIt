# Internal AX prefix through control 354

[ArithmeticControlAXThirdImp254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXThirdImp254.lean) composes the checked SecondImp41→275 and NextImp275→354 contracts. In every model of IΣ₁, for an arbitrary internal complete register file with S1=S2=0, it proves a positive internal execution time from the actual AX entry41 to control354, with these exact results:

- `TW = wim(oldP1, oldAC)`;
- `WS = cantor(wim(wim(oldAC, first(second(oldPL))), oldP1), cantor(wal(oldP1, oldcache), cantor(oldTW, oldWS)))`;
- `cache = oldcache + first(oldPL)`;
- `PL = second(second(oldPL))`;
- the other five coordinates are unchanged, including both scratch registers.

Thus the work stack retains the previous implication, GEN result and original TW/WS. The proof joins at actual control275 and adds arbitrary internal execution times with `controlRun_add`. It introduces no new induction or fixed-fuel restriction. This is the AX prefix41→354; the continuation after354 remains separate.

The [typed audit](arithmetic_control_ax_third_imp254_audit.lean) has seven named probes and ten callers. The first actual run passed in 2.242 seconds for source and 2.043 seconds for audit, with zero warnings. The control join reports no axioms; the six file/execution theorems report only `propext`, `Classical.choice` and `Quot.sound`. The [actual verification record](results/arithmetic-control-ax-third-imp254-verification.json) includes raw commands and outputs, source/audit snapshots, and the fresh object and actual first provider recorded before audit.

The [existing-evidence review](results/arithmetic-control-ax-third-imp254-review.json) checks all 267 current inputs, the exact 118-project import closure, six retained external source/object pairs (five directly imported), Init/Omega, and both immediate parent records. The two parents have 281 distinct input paths between them; that is separate from this unit's267-input count. The proof source was root-authored. The guard author performed this existing-evidence review and prepared the publication builder; separate peer source/API and guard reviews are preserved in [the history](results/arithmetic-control-ax-third-imp254-history.json). No independence from guard authorship is claimed.

The history preserves the original source-only freeze, whose then-pending NextImp status remains historical, preparation, the first actual source/audit PASS, raw logs, all available reviews and reviewer scripts. It also preserves two reviewer-only metadata corrections: an independent reader's tail-normalization assumption and this evidence reviewer's literal-AST handling of a set-difference boundary expression. Neither changed proof source, audit, guard, or actual execution evidence. There was no failed ThirdImp compilation.

The [provider proposal](results/arithmetic-control-ax-third-imp254-provider-proposal.json) pins actual SecondImp and NextImp records. Both immediate parents recorded source objects and first providers before audit; earlier ancestor provenance remains as originally recorded. The exact cached providers are prerequisites. Compiled caches are excluded from publication, and no clean-checkout dependency build is certified.

The maintained [guard](check_arithmetic_control_ax_third_imp254.py) differs from the executed guard only in its source, audit and proposal default paths. To prepare without invoking Lean or a version query:

```sh
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_third_imp254.py \
  --repo "$PWD" \
  --dependency-root /path/to/the/recorded/dependency-root \
  --second-imp-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-second-imp254-verification.json \
  --next-imp-evidence Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-next-imp254-verification.json \
  --output /tmp/fresh-ax-third-imp-preparation \
  --prepare-only
```

Omit `--prepare-only` in a fresh output directory for source/audit execution under default proof limits, one thread, 4,096 MiB and a shared120-second budget. The complete AX branch, validator/interpreter-to-Enum translation and the internal PA binary consistency equivalence are not supplied by this prefix theorem.

The literal register program is Mira-Cult's, imported from Jeff's verification; Wade authored the original TMBuilder framework. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) retains attribution and provenance.
