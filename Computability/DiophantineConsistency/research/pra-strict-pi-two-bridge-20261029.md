# Strict Σ₁ normalization and the strict Π₂ bridge (2026-10-29)

This note records plan step 2 of [PRA_PROVABILITY_PLAN.md](../PRA_PROVABILITY_PLAN.md)
("the exact equivalence is in the Π₂ fragment accepted by the conservation
theorem") and the "Σ₁ normalization gap" named in that plan's opening section.
All modules are new; none of the existing PRA, Herbrand or Parsons modules is
changed.

## 1. Strict induction suffices for IΣ₁

[`StrictSigmaOneInduction`](../Lean/DiophantineConsistency/StrictSigmaOneInduction.lean)
imports only Foundation and proves

```lean
theory_le : 𝗜𝚺₁ ⪯ 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma
isigma1_provable : 𝗜𝚺₁ ⊢ σ → 𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma ⊢ σ
```

`StrictSigma φ` means `φ = ∃⁰^[n] D` with `Hierarchy 𝚺 0 D`. This is
definitionally `ParsonsStrictInvariant.Strict`
(`StrictPiTwoParsons2011.strict_eq : StrictSigma = Strict := rfl`). So every
`𝗜𝚺₁` theorem has an actual proof whose induction predicates are all strict,
which is exactly the hypothesis of `ParsonsStrictInitial.strict_fragment`.

The proof is semantic, with no rewriting of proof objects. In a model of `𝗣𝗔⁻`
plus strict induction:

1. `bnd φ` replaces each unbounded `∃⁰ ψ` of `φ` by `∃⁰[x < w] ψ`, where `w` is
   one new last bound variable. This is a structural recursion on formulas.
   Putting `w` last means no variable swaps are needed under binders.
   * `eval_bnd_imp`: `bnd φ → φ` holds in every structure.
   * `eval_bnd_mono`: `bnd φ` is monotone in `w`.
   * `hierarchy_bnd`: `bnd φ` is `Σ₀` for `Σ₁` φ.
2. `strict_induction`: induction for `∃ȳ D(ȳ, x)` with model-element
   parameters, through Foundation's `rewriteMap`/`enumarateFVar` conversion.
3. `collection`: `∀x<T ∃b R x b → ∃b ∀x<T R x b` for monotone `Σ₀` relations
   `R`. It is proved by strict induction on `∃b ∀x<a (x<T → R x b)`.
4. `eval_bnd_of`: every `Σ₁` φ implies `bnd φ` at some `w`. Collection is needed
   only at bounded-universal nodes.
5. `models_isigma1`, then completeness, gives `theory_le`.

Axioms of all six main theorems: `propext`, `Classical.choice`, `Quot.sound`
(`StrictSigmaOneInductionChecks`).

## 2. A strict Π₂ normal form for `(∀x̄ θ) ↔ ¬π`

[`StrictPiTwoBridge`](../Lean/DiophantineConsistency/StrictPiTwoBridge.lean)
is generic. Take an open (`Σ₀`) matrix `θ` in `k` variables and a `Σ₁` sentence
`π`, and set `β := bnd π`. The normal form is

```
normalForm θ π := ∀ w ∀ x̄, ∃ v ∃ ȳ, (¬θ ȳ ∨ ¬β w) ∧ (β v ∨ θ x̄)
               = ∀⁰* (∃⁰^[k+1] matrix θ π),   matrix Σ₀ (matrix_sigma0)
```

* `isigma1_normalForm`: `𝗜𝚺₁ ⊢ (∀⁰* θ) ↔ ∼π` implies `𝗜𝚺₁ ⊢ normalForm θ π`.
* `normalForm_valid`: `𝗘𝗤 ℒₒᵣ ⊢ normalForm θ π → ((∀⁰* θ) ↔ conB π)`. This is pure
  equality logic and the "transport back" of plan step 2.
* `isigma1_conB`: `𝗜𝚺₁ ⊢ ∼π ↔ conB π`, where `conB π := ∀ w, ¬β w` is the
  strict `Π₁` form of `¬π`.

## 3. The current equation

[`StrictPiTwoCurrent2011`](../Lean/DiophantineConsistency/StrictPiTwoCurrent2011.lean)
sets `θ := body`, the open matrix of `classicalSentence` (`classicalSentence = ∀⁰* body`
by `rfl`), and `π := provSentence = ∼(𝗭𝗙𝗖).consistent`. It exports:

| theorem | statement |
| --- | --- |
| `nf_shape` | `nf = ∀⁰* (∃⁰^[15] D)` with `D` `Σ₀` |
| `isigma1_nf` | endpoint `𝗜𝚺₁ ⊢ classicalSentence ↔ conSentence` ⟹ `𝗜𝚺₁ ⊢ nf` |
| `strict_nf` | same hypothesis ⟹ `𝗣𝗔⁻ ∪ InductionScheme ℒₒᵣ StrictSigma ⊢ nf` |
| `nf_valid` | `𝗘𝗤 ℒₒᵣ ⊢ nf → (classicalSentence ↔ strictCon)` |
| `isigma1_strictCon` | `𝗜𝚺₁ ⊢ conSentence ↔ strictCon` |

`strictCon` is Foundation's own ZFC proof predicate with all of its unbounded
witnesses bounded by one `w`: the same Gödel coding and the same theory, in
strict `Π₁` form.

[`StrictPiTwoParsons2011`](../Lean/DiophantineConsistency/StrictPiTwoParsons2011.lean)
connects this to the Codex rule calculus:

* `rule_proof_of_isigma1`: every `𝗜𝚺₁` theorem `∀⁰* (∃⁰^[k] D)` with `D` `Σ₀` has a
  `ParsonsRule.Proof 𝗣𝗔⁻`;
* `nf_rule_proof`: the same for `nf`, given the endpoint.

The endpoint hypothesis is discharged by
`HACurrentEquation2011.isigma1_proves_current_iff_consistency`; since
`FoundationZFCConsistencyNat.sourceSentence = conSentence` holds by `rfl`, the
composition is

```lean
theorem isigma1_current : 𝗜𝚺₁ ⊢ classicalSentence 🡘 conSentence :=
  (rfl : FoundationZFCConsistencyNat.sourceSentence = conSentence) ▸
    HACurrentEquation2011.isigma1_proves_current_iff_consistency
theorem strict_nf_current := strict_nf isigma1_current
theorem nf_rule_proof_current := StrictPiTwoParsons2011.nf_rule_proof isigma1_current
```

## 4. Why the PRA statement should use `strictCon`

The planned end statement has the form "PRA proves the equation's
unsolvability ↔ Con(ZFC)". Its PRA-level consistency sentence should be
`strictCon`, not Foundation's `consistent` itself, for two reasons:

* The direction `consistent → strictCon` is pure logic, since bounded witnesses
  imply unbounded ones.
* The converse direction needs collection for `Σ₁` formulas with inner bounded
  universals. That is a Π₃-type principle, and PRA does not prove it in general.

`strictCon` is the standard PRA formalization of Con(ZFC): a universal sentence
over a bounded matrix of the same proof predicate. Its equivalence with
Foundation's sentence is recorded at the IΣ₁ level (`isigma1_strictCon`).

## 5. Status and what remains

| module | status |
| --- | --- |
| `StrictSigmaOneInduction`, `StrictPiTwoBridge`, `StrictPiTwoCurrent2011`, `StrictPiTwoParsons2011` | built and audited (`StrictSigmaOneInductionChecks`, `StrictPiTwoChecks`: `propext`, `Classical.choice`, `Quot.sound` only) |
| endpoint composition above | not yet a module: it imports the 230-module HA endpoint closure, about 140 of whose modules were stale on 2026-10-29; deferred to the source-current HA replay |

All builds ran serially (`LAKE_JOBS=1`, `LEAN_NUM_THREADS=0`) under a 6.5 GB
process-tree cap. Peaks were 3.2–3.6 GB, except 5.8 GB while rebuilding
`WangTiles942Data`.

Still open, all in the Codex lanes:

* the global cut-free recursion of the Parsons translation;
* the passage from the rule calculus to candidate PRA;
* the candidate-to-standard PRA comparison.

The contract this note provides is a strict-induction proof (or rule proof) of
`nf`, plus the logical transport back.
