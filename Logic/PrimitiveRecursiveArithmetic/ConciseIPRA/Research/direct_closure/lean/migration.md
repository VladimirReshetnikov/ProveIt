# Direct closure induction: uncompiled Lean migration sketch

**Status:** proposed source patch, not compiled or kernel checked in this task.
The patch applies cleanly by `git apply --check` to the three pinned input
files. That checks patch context and syntax only; it does not check Lean
syntax, elaboration, theorem correctness, or downstream builds. No repository
files were changed.

**Baseline:** `b17dd5487f34adea473a0204c5320fb3eeb8910e` of
[VladimirReshetnikov/ProveIt](https://github.com/VladimirReshetnikov/ProveIt/tree/b17dd5487f34adea473a0204c5320fb3eeb8910e/Logic/PrimitiveRecursiveArithmetic/ConciseIPRA).

The proposed patch is `closure_progress.patch`. Paths in its headers are
relative to the ProveIt repository root. It changes three source files:
`Native.lean`, `NativeStruct.lean`, and `NativeEq.lean` under
`Logic/PrimitiveRecursiveArithmetic/ConciseIPRA/Lean/ConciseIPRA/`.

## 1. Primitive constructor

The old constructor introduces a witnessed D formula from an equation's
progression. Its two matrix terms are scoped over `n + 2` variables and it
also takes a witness term scoped over `n` variables.

The replacement makes direct equation-closure induction primitive:

```lean
  /-- Direct Q induction: from `E(z) ⊢ E(S z)` with `z` fresh infer
  `Q_y E`, for a literal equation `E` only. -/
  | qIInd {n : ℕ} {Γ : List (NFm n)} (s₁ s₂ : Tm (n + 1))
      (h : NPrf (NFm.eq s₁ s₂ :: Γ.map NFm.shift)
        ((NFm.eq s₁ s₂).subst (repl (succ (var 0))))) :
      NPrf Γ (.Q (.eq s₁ s₂))
```

`qIInd` avoids a name collision with the existing derived theorem
`NPrf.qIProg`. Numerical terms, native formulas, and their ordinary reading
remain identical. In particular, Q still means conditional universal
closure, not progressiveness.

### Constructor comparison

| Coordinate | Old `dIProg` | New `qIInd` |
| --- | ---: | ---: |
| Explicit term inputs | 3 | 2 |
| Matrix's extra bound numerical variables | 2 | 1 |
| Explicit existential witness input | 1 | 0 |
| Derivation premises | 1 | 1 |
| Explicit witness-instantiation expressions in constructor | 2 | 0 |
| UTF-8 bytes of constructor code, excluding doc comment | 270 | 214 |
| Primitive constructors in `NPrf` | 8 | 8 |

These are local constructor measurements, not a complete-checker comparison.
The byte counts preserve the shown formatting and existing Unicode names;
no Lean parser AST measurement was performed. The count and reproducibility
metadata are in `constructor_metrics.json`.

## 2. Changed soundness case

The new constructor's soundness proof temporarily assumes the zero instance,
uses `Teq.eqInd`, and discharges that zero-instance assumption. It no longer
introduces an existential witness or rewrites a witness instantiation.

```lean
  | qIInd s₁ s₂ _ ih =>
    simp only [List.map_cons, NFm.map_toFm_shift,
      NFm.toFm_subst, NFm.toFm_eq] at ih
    rw [NFm.toFm_Q, NFm.toFm_eq]
    exact .impI (Teq.eqInd s₁ s₂ Prf.hyp0
      (ih.weaken (List.cons_subset_cons _
        (List.subset_cons_self _ _))))
```

The weakening inserts the assumed base equation immediately after the
induction hypothesis in the step context. The equation matrix stays literal,
so no induction beyond the existing `Teq.eqInd` is invoked.

## 3. Structural inductions

`NativeStruct.lean` performs induction on `NPrf` in three places. The patch
changes each corresponding constructor case.

| Lemma | Required change |
| --- | --- |
| `NPrf.weaken` | Replace the old `dIProg` case by `qIInd`, retaining the same context inclusion under its one fresh variable. |
| `NPrf.subst` | Apply the induction hypothesis with `up σ`; translate the two equation terms with `Syn.subst (up σ)`. No witness substitution and no `NFm.subst_up_inst` rewrite are needed in this case. |
| `NPrf.cut` | Replace the old case by `qIInd` with the same `cutLift` construction. |

All three proofs preserve their public statement. The existing formula
substitution lemmas remain available because D-case still uses two binders.
They should not be deleted merely because this progression case no longer
needs them.

## 4. Compatibility bridge: recover witnessed D progression

The patch keeps the former constructor's public type as a theorem
`NPrf.dIProg` in `NativeEq.lean`.

Let

```lean
  B := (NFm.eq s₁ s₂).subst (up (inst t))
```

be the equation matrix after its witness has been instantiated.
The given progression proof supplies `qIInd`, producing `Q B`.
For D-case at witness `t`, weaken this closure into the local context with
`B(0)`. QE at the fresh successor gives `B(S z)` and D-case closes the
construction.

The proposed Lean proof uses two already available substitution lemmas from
the start of `NativeEq.lean`:

- `NFm.subst_dummy_up_inst` identifies opening a weakened one-variable
  matrix with replacing its existing bound variable.
- `NFm.shift_subst_inst_zero` identifies the shifted zero instance with
  replacement by zero.

The retained compatibility theorem occurs after those lemmas, so it creates
no import cycle. It uses `NPrf.shift` and `NPrf.wk`, already proved in
`NativeStruct.lean`. The patch includes the proposed full tactic body, but
it is an uncompiled elaboration sketch.

The existing `NPrf.qIProg` then becomes the one-line alias

```lean
  .qIInd s t h
```

with exactly its previous public type.

## 5. Bridge in the other direction

The pinned baseline already formalizes new-to-old admissibility as
`NPrf.qIProg` in `NativeEq.lean`: introduce
`D_{u,y} E(y)` with unused `u` and witness zero; eliminate it and return its
local Q hypothesis. That proof is evidence for the mathematical validity of
the replacement rule.

It is not, by itself, a compiled equivalence theorem between two separately
represented Lean derivability types. This patch edits `NPrf` in place and
retains the old API as a derived theorem; it does not declare both inductive
types side by side. A formal equivalence artifact would preserve the old
inductive type under a separate namespace and define the two proof
translations by induction, using these two bridges.

## 6. Downstream impact

The pinned repository's exact-name search found `dIProg` references in the
three patched Lean files. The following public interfaces are preserved:

- `NPrf.qIProg` and `NPrf.eqInd` keep their existing statements.
- `NPrf.sound`, `NPrf.weaken`, `NPrf.subst`, and `NPrf.cut` keep their
  existing statements.
- `NFm`, `NFm.toFm`, native logical macros, and ordinary arithmetic axioms
  are unchanged.

`NativeGate.lean` uses `qIProg`, and `NativeTranslate.lean` uses it for the
ordinary induction axiom. Those call sites should remain unchanged. The
native round-trip theorem and `NPrf.iff_teq` in `NativeComposite.lean` should
also retain their statements; their dependencies need rebuilding.

The generated eliminators `NPrf.rec`, `NPrf.recOn`, and `NPrf.casesOn` have a
changed constructor signature. External code that pattern-matches directly
on the old constructor must be updated. External code importing only
`Native.lean` and calling `dIProg` would need the compatibility theorem's
module; in the inspected pinned sources, the known references are covered
by the patch.

## 7. Independent proof-tree node audit

Count each primitive Hyp, computation, Tr, QE, DE, D-case, and progression
occurrence as one node. Weakening and renaming preserve the count because
they relabel an existing derivation rather than add primitive nodes.

### New Q progression to old calculus

For a premise subtree of size `p`, the replacement contains:

1. The same premise subtree: `p` nodes.
2. Old D progression with dummy witness: 1 node.
3. Hyp returning the opened Q closure: 1 node.
4. DE: 1 node.

The original new inference contained `p + 1` nodes; the replacement contains
`p + 3`. Thus the local increase is exactly 2.

### Old D progression to new calculus

For a premise subtree of size `p`, the replacement contains:

1. The same premise subtree, weakened by the case assumption: `p` nodes.
2. New Q progression: 1 node.
3. Hyp supplying the case's zero instance: 1 node.
4. QE at the fresh successor: 1 node.
5. D-case: 1 node.

The original old inference contained `p + 1` nodes; the replacement contains
`p + 4`. Thus the local increase is exactly 3.

Consequently new-to-old translation has `N + 2r` nodes and old-to-new
translation has `N + 3r` nodes, where `r` counts the replaced progression
occurrences of the source derivation. These are bounds on inference trees,
not serialized certificate size, term length, kernel term size, or checker
runtime.

## 8. Validation still required

Apply the patch to an isolated checkout of the pinned commit, compile the
three changed modules and the downstream native round-trip module using the
repository's existing Lean toolchain, and inspect the final theorem's axiom
dependencies. Tactic elaboration around the compatibility theorem's shifted
matrix is the most likely place to require a local syntactic adjustment.
The file currently provides no compilation result and must remain labeled
an uncompiled migration sketch until that work is done.
