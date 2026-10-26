# Three local machine-proof reductions

**Pin:** `22e020937caa81d0cb72a4f63071d6c0bcc1eba9`.
**Status:** complete **uncompiled** candidates. No Lean/Lake runtime is available and none was installed. Static theorem-header preservation and patch applicability checks pass; elaboration, axiom output, and runtime are unmeasured.

## Result first

| ID | Existing theorem | Nonblank declaration lines | Proof-body lines |
|---|---|---:|---:|
| M1 | `WangMachineAction.act_next_none_iff` | 10 → 3 | 8 → 1 |
| M2 | `WangMachineStep.color_action` | 15 → 11 | 8 → 4 |
| M3 | `WangMachineTraceBounds.run_read_of_abs_ge` | 8 → 3 | 6 → 1 |
| Total | Three independent replacements | **33 → 17** | **22 → 6** |

The savings are 16 nonblank source lines, not 16 kernel-proof lines. All existing declaration headers are retained byte for byte; no new helper overhead, definitions, axioms, or imports are introduced. The same 16-line delta survives the counterfactual baseline in which all previously proposed families have already been applied. These are intentionally modest local wins; the existing trace induction and exact decimal calibration should remain intact.

## M1. Reflect halt equality through the already injective encoding

[Exact source, lines 60–69](https://github.com/VladimirReshetnikov/ProveIt/blob/22e020937caa81d0cb72a4f63071d6c0bcc1eba9/Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineAction.lean#L60-L69).

The existing proof manually transports the equality through `stateNumber` in both directions. But `stateNumber_injective.eq_iff` is precisely that equivalence. After reflecting equality, the previously established `act_stateNumber` and `stateNumber_none` identify both sides:

```lean
  rw [← stateNumber_injective.eq_iff, act_stateNumber a ha, stateNumber_none]
```

The premise `ha : a.2.2 < 216` remains essential. The raw action adapter sends an invalid target 216 to `none` too, so a theorem without the bound would be false. The cache-to-decoder theorem, direction-specific target sets, target215 convention, all 430 actions and the concrete decimal machine are unchanged. This proves a property of the actual adapter; it does not postulate a replacement transition relation.

**Virtual baseline and novelty:** consumes existing `stateNumber_injective` and `act_stateNumber`; it neither recreates generic scanner semiconjugacy nor proposes finite controller invariants. The audit of eleven prior packets found no advertised machine-action invariant-equality client. This theorem is new in the reviewed interval and remains a two-direction transport proof after all prior proposals are assumed applied. In particular, fresh family NF004 (virtual baseline V12) uses finite injective dynamics and a forward-invariant predicate to derive invariant predecessors. M1 is pointwise equality cancellation: it uses no dynamics, invariant predicate, finite surjectivity, or periodicity. The baseline auditor explicitly confirmed this distinction.

## M2. Split on the sole write location, not on the color destination

[Exact source, lines 62–76](https://github.com/VladimirReshetnikov/ProveIt/blob/22e020937caa81d0cb72a4f63071d6c0bcc1eba9/Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineStep.lean#L62-L76).

The result has three cases (moved head, old head, other cell), but its proof does not need three branches. A write affects exactly one cell. At the old head, movement guarantees it is not the new head. Away from the old head, the tape-read frame rule applies uniformly whether or not the cell is the new head. Leave that new-head `if` symbolic on both sides:

```lean
  by_cases ho : x = cfg.head
  · subst x
    simp [color, (moved_head_ne a.move cfg.head).symm]
  · simp [color, ho, Tape.read_write_of_ne cfg.tape ho a.write]
```

This removes one decision and one leaf: two `by_cases` / three leaves become one `by_cases` / two leaves. No combined action structure or global simp rule is added. The **three-way theorem statement is not weakened**. `a.next = none` still writes and moves; the destination reads its old bit, and the final head remains encoded by 432/433. The proof permits duplicate entries in the tape representation because it only uses tape reads, never normalized list equality.

**Virtual baseline and novelty:** consumes existing `Tape.read_write_of_ne`, `Tape.read_write_same` (a simp theorem), `moved_head_ne`, and `color`. The prior syntax-tag dispatch and constructor-view proposals do not normalize tape-write support at this client. The incoming audit approved this exact case-order reduction, not merely the broad idea of using `simp`.

## M3. The sharp exterior condition is already `le_abs'`

[Exact source, lines 89–96](https://github.com/VladimirReshetnikov/ProveIt/blob/22e020937caa81d0cb72a4f63071d6c0bcc1eba9/Computability/DiophantineConsistency/Lean/DiophantineConsistency/WangMachineTraceBounds.lean#L89-L96).

The existing proof splits on the sign of `x`, rewrites its absolute value, and proves the left/right exterior disjunction. The module already imports the exact library equivalence:

```lean
le_abs' : a ≤ |b| ↔ b ≤ -a ∨ a ≤ b
```

Therefore its complete proof is:

```lean
  exact run_read_outside M t x (le_abs'.mp hx)
```

The theorem is generated by `@[to_additive]` from `le_mabs'` in pinned Mathlib [`Algebra/Order/Group/Abs.lean`, lines 66–67](https://github.com/leanprover-community/mathlib4/blob/81a5d257c8e410db227a6665ed08f64fea08e997/Mathlib/Algebra/Order/Group/Abs.lean#L66-L67). The complete source and Git-blob-verified metadata are supplied under `evidence/`. This is source verification, not compilation.

The inclusive threshold `|x| ≥ t` remains exact, including `t = 0` and `x = 0`. No positivity premise on `n`, `t`, or the initial tape is added. The underlying write-before-move support theorem and stationary-halted semantics are untouched.

**Virtual baseline and novelty:** the earlier packet's general library-reuse recommendations do not claim every possible library application. No prior packet addressed this newly introduced sharp trace-support conversion. This local replacement is independent of scanner iteration/fixed-point abstractions and of finite-cycle closure.

## Artifacts and reproduction

- `MachineCandidates.lean`: all three source-exact statements in an isolated namespace, plus target215/invalid216, old/new-head, and time-zero checks. The replacements never call the original target theorem.
- `M1-*.patch`, `M2-*.patch`, `M3-*.patch`: independent proof-body-only patches.
- `patched/`: complete candidate versions of the three source modules, with unchanged public names and statements.
- `build_candidates.py`, `metrics.json`: deterministic source extraction, statement-identity check and line counts; runs without Lean and does not alter upstream sources.
- `evidence/MathlibAbs.lean`, `evidence/MathlibAbs-source.json`: exact library source and verified identity.
- `validation.json`: evidence of static checks and precise not-run stages.

In a **complete** checkout of the pinned repository with its existing Lean 4.32.0 toolchain, first re-run `git apply --check` on each patch, apply them in a throwaway worktree, then compile the changed modules and `WangMachineActionChecks`, `WangMachineStepChecks`, `WangMachineTraceBoundsChecks`; rebuild affected row-step and construction consumers. Compile `MachineCandidates.lean` separately and inspect its supplied `#print axioms` output against the original declarations. None of those Lean checks has run here.

## Deliberately not expanded

`step_head_ne` could also be derived directly by `rw [step_eq M cfg q hq]; exact moved_head_ne _ _`, avoiding another `omega` elimination. This is a small clarity-only variant (one more source line), not included in savings or patches. A new generic trace-envelope record, combined head/support induction, or halted-time clipping API would add abstraction to already short proofs without a demonstrated current consumer saving, so none is proposed as a net reduction.
