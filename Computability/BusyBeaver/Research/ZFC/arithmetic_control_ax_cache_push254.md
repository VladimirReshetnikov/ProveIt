# Internal AX cache/P2 push

[ArithmeticControlAXCachePush254](../../Lean/BusyBeaver/ZFC/ArithmeticControlAXCachePush254.lean) executes the actual second AX parameter push, from literal catalogue control 67 to 93. For any model of IΣ₁ and any internal nine-register file with zero scratch registers, it produces TW = old cache/P2 and WS = `cantor(old TW, old WS)`. Every other register is preserved. The cache-copy tail needs only scratch1 = 0 and has the exact internal clock `7 * cache + 2`.

The module also composes this result with the checked first AX push. Starting at control 41, the resulting TW is the old cache and WS is `cantor(old P1, cantor(old TW, old WS))`. These indices name source-program instructions, not binary states. Runtime witnesses and input values may be nonstandard. Existing generic Push, Copy, Move and Pair contracts supply the loop arguments; no new induction or larger proof limit was introduced.

The [guarded second attempt](results/arithmetic-control-ax-cache-push254-verification.json) passed the source and [audit](arithmetic_control_ax_cache_push254_audit.lean): 8 named axiom probes, 12 typed callers, and zero warnings. The [independent review](results/arithmetic-control-ax-cache-push254-review.json) checks the source, provider bindings and existing evidence. The first attempt failed because two `simpa` calls did not normalize three literal control aliases. Its source, audit, executed guard, log and result are retained in the [history](results/arithmetic-control-ax-cache-push254-history.json), alongside the three explicit `rfl` equalities used for the successful repair. The earlier final-newline normalization and original uncompiled draft are also preserved. Publication packaging performed no proof replay.

The [guard](check_arithmetic_control_ax_cache_push254.py) reuses the exact [AXPrefix PASS record](results/arithmetic-control-ax-prefix254-verification.json) and its 99 imported project providers. Five external boundaries are directly imported; the separately retained `Foundation.FirstOrder.Arithmetic.HFS.Seq` gives six verified external providers in total, alongside two toolchain boundaries. The guard builds only this source and its audit with a shared 120-second deadline, `-j1 -M4096`, and default proof limits. Its inherited arithmetic binary transport remains the Perm252 transport. This result advances the register interpreter shared with the 246-state target; it does not establish an internal 246 binary transport, the GEN constructor, the remaining AX suffix, or the full PA consistency endpoint.

Preparation and replay require the exact historical cached project and dependency objects, source files and compiler recorded in the evidence. This packet contains source and evidence; it does not distribute those object caches or provide a clean-checkout dependency build. Existing cache identities are checked, and the external dependency closures are not rebuilt.

The shared register program is Mira-Cult's, imported from Jeff's verification; the original TMBuilder framework is Wade's. [Prog254.lean](../../Lean/BusyBeaver/ZFC/Prog254.lean) records the original source and attribution.

After installing the packet, prepare the exact maintained defaults without compiling:

```bash
python3 -B Computability/BusyBeaver/Research/ZFC/check_arithmetic_control_ax_cache_push254.py \
  --repo "$PWD" \
  --dependency-root /home/codex/src/Proofs \
  --ax-prefix-evidence "$PWD/Computability/BusyBeaver/Research/ZFC/results/arithmetic-control-ax-prefix254-verification.json" \
  --output /tmp/zfc-ax-cache-push-maintained-prepared \
  --prepare-only
```

A proof replay uses the same command with a fresh empty output directory and without `--prepare-only`. Preparation retains the required parent and dependency arguments, uses installed source/audit defaults, and performs no compiler or compiler-version query. Installed-default preparation is recorded separately after placement; it is not claimed by the original successful proof record.
