# Reuse the existing strict Pell index bound

**Optional local source cleanup, not new Pell theory. Uncompiled.**

At frozen source `7ba7d102822df1eff376cbca913727d9d588ab4e`, the local `hKr` proof in `NativeOuterSeedConstruction.exists_outer_seed` expands a lower power bound, compares the literal base through `Q` and `X`, and finishes by linear arithmetic. The repository already provides exactly `n < yn a1 n` when `1 < a` and `2 <= n` in `Diophantine.Common.PellMod.lt_yn_of_two_le`.

The replacement is:

```lean
  have hKr : r+1 < K := lt_yn_of_two_le hP (by omega)
```

Here `K := yn hP (r+1)`, `hP : 1 < P`, and `population_sizes` supplies `hr : 4 <= r`; hence the helper's `2 <= r+1` condition follows. The following `hkR` and positive quotient construction are unchanged. The entire theorem statement, all definitions, imports, witnesses and other source bytes remain identical. The prior `hRX` binding is deliberately left untouched to keep this patch limited to one proof.

The named local fragment falls from 11 physical lines to 1; the whole module falls from 279 to 269. No new helper, import, mathematical theorem, or general proof API is proposed. Reusing the repository lemma removes the stronger intermediate lower-bound calculations, so maintainers lose those visible calculations but gain a proof at the exact required abstraction. It also makes this client depend visibly on the existing helper's name and statement. No performance or axiom-footprint change is claimed.

## Strict novelty boundary

The prior two-base Pell comparison and fixed-index anchor mechanisms are assumed applied, but neither is used here. In particular, replacing the neighboring `hcX` proof by a fixed index-two anchor is excluded as the earlier fixed-anchor mechanism with a new numeral. Rewriting new consistency endpoints via `not_congr` is likewise excluded by the earlier systematic contraposition direction. See `../../baseline_audit/` for exact prior evidence and the one bounded closing screen.

## Replay

Run `python3 research/outer_seed/check_candidate.py` from the packet root. It checks source Git blob/SHA256, one exact replacement and its patch, full-file and fragment line counts, surrounding source facts, and the helper signature. It also checks 1,953 finite Pell recurrence samples and three negative controls showing that index zero, index one and base one do not satisfy the strict inequality. Normal and optimized Python executions agree.

These checks are **not Lean elaboration or kernel verification**. In an authorized complete checkout, compile the changed module and its Checks file and affected reverse dependencies, then compare endpoint axiom reports. The selected snapshot is not a complete Lake project. The TeX/build and byte-verification scaffolding is reused from round 6 and receives no research credit.
