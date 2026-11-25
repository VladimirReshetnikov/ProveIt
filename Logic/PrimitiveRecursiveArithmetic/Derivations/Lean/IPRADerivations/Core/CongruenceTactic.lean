import IPRADerivations.Core.Basic

/-!
# Congruence of a term in all its arguments

`Prf.eqCongr t h` derives `t[σ] ≐ t[σ']` from derivations `h i : Γ ⊢ σ i ≐ σ' i`. In use, the two substitutions
are written out, the derivations are matched to the variables by a case split, and the substitutions are pushed
back through the term. `ipra_congr` does this from the template and the list of derivations alone:

    theorem f_congr (ha : Γ ⊢ a ≐ a') (hb : Γ ⊢ b ≐ b') : Γ ⊢ f a b ≐ f a' b' := by
      ipra_congr (f (var 0) (var 1) : PTm 2) with [ha, hb]

* `EqPair Γ` packs a derived equation with its two sides, so that a vector of derivations determines both
  substitutions;
* `eqCongrPairs t v` is `Prf.eqCongr` for such a vector;
* `ipra_congr t with [h₀, …, h_{k−1}]` closes a goal `Γ ⊢ s ≐ s'` whose sides are `t` at the left and right sides
  of the `hᵢ`, up to `simp` (the lemmas `subst_f` that push substitutions through defined terms are simp
  lemmas); `ipra_congr t with [h₀, …] using [l₁, …]` adds simp lemmas, for definitions to be unfolded.
  A derivation whose statement is not literally the one meant is given as `(show Γ ⊢ a ≐ b from h)`;
* `vec6_5`, …: the entries of a vector literal beyond the fifth, for templates with six to twelve variables.
-/

namespace LeanProofs.IPRA

open LeanProofs.ConciseIPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- A derived equation with its sides. -/
structure EqPair (Γ : List (Fm PTm n)) where
  /-- The left side. -/
  lhs : PTm n
  /-- The right side. -/
  rhs : PTm n
  /-- The derivation. -/
  eq : Γ ⊢[PRAAx] lhs ≐ rhs

/-- Congruence of a term in all its variables, for a vector of derived equations. -/
theorem eqCongrPairs {k : ℕ} (t : PTm k) (v : Fin k → EqPair Γ) :
    Γ ⊢[PRAAx] Syn.subst (fun i => (v i).lhs) t ≐ Syn.subst (fun i => (v i).rhs) t :=
  Prf.eqCongr t fun i => (v i).eq

/-! Entries of a vector literal beyond the fifth, which `simp` does not look up by itself. -/

theorem vec6_5 {α : Type*} (a b c d e f : α) : (![a, b, c, d, e, f] : Fin 6 → α) 5 = f := rfl
theorem vec7_5 {α : Type*} (a b c d e f g : α) : (![a, b, c, d, e, f, g] : Fin 7 → α) 5 = f := rfl
theorem vec7_6 {α : Type*} (a b c d e f g : α) : (![a, b, c, d, e, f, g] : Fin 7 → α) 6 = g := rfl
theorem vec8_5 {α : Type*} (a b c d e f g h : α) : (![a, b, c, d, e, f, g, h] : Fin 8 → α) 5 = f := rfl
theorem vec8_6 {α : Type*} (a b c d e f g h : α) : (![a, b, c, d, e, f, g, h] : Fin 8 → α) 6 = g := rfl
theorem vec8_7 {α : Type*} (a b c d e f g h : α) : (![a, b, c, d, e, f, g, h] : Fin 8 → α) 7 = h := rfl
theorem vec9_5 {α : Type*} (a b c d e f g h i : α) : (![a, b, c, d, e, f, g, h, i] : Fin 9 → α) 5 = f := rfl
theorem vec9_6 {α : Type*} (a b c d e f g h i : α) : (![a, b, c, d, e, f, g, h, i] : Fin 9 → α) 6 = g := rfl
theorem vec9_7 {α : Type*} (a b c d e f g h i : α) : (![a, b, c, d, e, f, g, h, i] : Fin 9 → α) 7 = h := rfl
theorem vec9_8 {α : Type*} (a b c d e f g h i : α) : (![a, b, c, d, e, f, g, h, i] : Fin 9 → α) 8 = i := rfl
theorem vec10_5 {α : Type*} (a b c d e f g h i j : α) : (![a, b, c, d, e, f, g, h, i, j] : Fin 10 → α) 5 = f := rfl
theorem vec10_6 {α : Type*} (a b c d e f g h i j : α) : (![a, b, c, d, e, f, g, h, i, j] : Fin 10 → α) 6 = g := rfl
theorem vec10_7 {α : Type*} (a b c d e f g h i j : α) : (![a, b, c, d, e, f, g, h, i, j] : Fin 10 → α) 7 = h := rfl
theorem vec10_8 {α : Type*} (a b c d e f g h i j : α) : (![a, b, c, d, e, f, g, h, i, j] : Fin 10 → α) 8 = i := rfl
theorem vec10_9 {α : Type*} (a b c d e f g h i j : α) : (![a, b, c, d, e, f, g, h, i, j] : Fin 10 → α) 9 = j := rfl
theorem vec11_5 {α : Type*} (a b c d e f g h i j k : α) : (![a, b, c, d, e, f, g, h, i, j, k] : Fin 11 → α) 5 = f := rfl
theorem vec11_6 {α : Type*} (a b c d e f g h i j k : α) : (![a, b, c, d, e, f, g, h, i, j, k] : Fin 11 → α) 6 = g := rfl
theorem vec11_7 {α : Type*} (a b c d e f g h i j k : α) : (![a, b, c, d, e, f, g, h, i, j, k] : Fin 11 → α) 7 = h := rfl
theorem vec11_8 {α : Type*} (a b c d e f g h i j k : α) : (![a, b, c, d, e, f, g, h, i, j, k] : Fin 11 → α) 8 = i := rfl
theorem vec11_9 {α : Type*} (a b c d e f g h i j k : α) : (![a, b, c, d, e, f, g, h, i, j, k] : Fin 11 → α) 9 = j := rfl
theorem vec11_10 {α : Type*} (a b c d e f g h i j k : α) : (![a, b, c, d, e, f, g, h, i, j, k] : Fin 11 → α) 10 = k := rfl
theorem vec12_5 {α : Type*} (a b c d e f g h i j k l : α) : (![a, b, c, d, e, f, g, h, i, j, k, l] : Fin 12 → α) 5 = f := rfl
theorem vec12_6 {α : Type*} (a b c d e f g h i j k l : α) : (![a, b, c, d, e, f, g, h, i, j, k, l] : Fin 12 → α) 6 = g := rfl
theorem vec12_7 {α : Type*} (a b c d e f g h i j k l : α) : (![a, b, c, d, e, f, g, h, i, j, k, l] : Fin 12 → α) 7 = h := rfl
theorem vec12_8 {α : Type*} (a b c d e f g h i j k l : α) : (![a, b, c, d, e, f, g, h, i, j, k, l] : Fin 12 → α) 8 = i := rfl
theorem vec12_9 {α : Type*} (a b c d e f g h i j k l : α) : (![a, b, c, d, e, f, g, h, i, j, k, l] : Fin 12 → α) 9 = j := rfl
theorem vec12_10 {α : Type*} (a b c d e f g h i j k l : α) : (![a, b, c, d, e, f, g, h, i, j, k, l] : Fin 12 → α) 10 = k := rfl
theorem vec12_11 {α : Type*} (a b c d e f g h i j k l : α) : (![a, b, c, d, e, f, g, h, i, j, k, l] : Fin 12 → α) 11 = l := rfl

end LeanProofs.IPRA

/-- `ipra_congr t with [h₀, …, h_{k−1}]` derives `t[a₀, …] ≐ t[b₀, …]` from `hᵢ : Γ ⊢ aᵢ ≐ bᵢ`, for a template
`t : PTm k` written with `var 0, …, var (k − 1)`. -/
syntax "ipra_congr " term " with " "[" term,* "]" (" using " "[" Lean.Parser.Tactic.simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| ipra_congr $t with [$hs,*]) => do
      let ps ← hs.getElems.mapM fun h => `((⟨_, _, $h⟩ : LeanProofs.IPRA.EqPair _))
      `(tactic| simpa [LeanProofs.IPRA.vec6_5, LeanProofs.IPRA.vec7_5, LeanProofs.IPRA.vec7_6,
          LeanProofs.IPRA.vec8_5, LeanProofs.IPRA.vec8_6, LeanProofs.IPRA.vec8_7, LeanProofs.IPRA.vec9_5,
          LeanProofs.IPRA.vec9_6, LeanProofs.IPRA.vec9_7, LeanProofs.IPRA.vec9_8, LeanProofs.IPRA.vec10_5,
          LeanProofs.IPRA.vec10_6, LeanProofs.IPRA.vec10_7, LeanProofs.IPRA.vec10_8, LeanProofs.IPRA.vec10_9,
          LeanProofs.IPRA.vec11_5, LeanProofs.IPRA.vec11_6, LeanProofs.IPRA.vec11_7, LeanProofs.IPRA.vec11_8,
          LeanProofs.IPRA.vec11_9, LeanProofs.IPRA.vec11_10, LeanProofs.IPRA.vec12_5, LeanProofs.IPRA.vec12_6,
          LeanProofs.IPRA.vec12_7, LeanProofs.IPRA.vec12_8, LeanProofs.IPRA.vec12_9, LeanProofs.IPRA.vec12_10,
          LeanProofs.IPRA.vec12_11] using
          LeanProofs.IPRA.eqCongrPairs $t ![$ps,*])
  | `(tactic| ipra_congr $t with [$hs,*] using [$ls,*]) => do
      let ps ← hs.getElems.mapM fun h => `((⟨_, _, $h⟩ : LeanProofs.IPRA.EqPair _))
      `(tactic| simpa [$ls,*, LeanProofs.IPRA.vec6_5, LeanProofs.IPRA.vec7_5, LeanProofs.IPRA.vec7_6,
          LeanProofs.IPRA.vec8_5, LeanProofs.IPRA.vec8_6, LeanProofs.IPRA.vec8_7, LeanProofs.IPRA.vec9_5,
          LeanProofs.IPRA.vec9_6, LeanProofs.IPRA.vec9_7, LeanProofs.IPRA.vec9_8, LeanProofs.IPRA.vec10_5,
          LeanProofs.IPRA.vec10_6, LeanProofs.IPRA.vec10_7, LeanProofs.IPRA.vec10_8, LeanProofs.IPRA.vec10_9,
          LeanProofs.IPRA.vec11_5, LeanProofs.IPRA.vec11_6, LeanProofs.IPRA.vec11_7, LeanProofs.IPRA.vec11_8,
          LeanProofs.IPRA.vec11_9, LeanProofs.IPRA.vec11_10, LeanProofs.IPRA.vec12_5, LeanProofs.IPRA.vec12_6,
          LeanProofs.IPRA.vec12_7, LeanProofs.IPRA.vec12_8, LeanProofs.IPRA.vec12_9, LeanProofs.IPRA.vec12_10,
          LeanProofs.IPRA.vec12_11] using
          LeanProofs.IPRA.eqCongrPairs $t ![$ps,*])
