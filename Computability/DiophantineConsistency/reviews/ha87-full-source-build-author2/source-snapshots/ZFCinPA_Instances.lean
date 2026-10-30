import Foundation.FirstOrder.SetTheory.Basic.Axioms
import Foundation.FirstOrder.Bootstrapping.Syntax

/-!
# Arithmetical definability of the set-theoretic language `ℒₛₑₜ`

Foundation's arithmetized syntax (`LO.FirstOrder.Arithmetic.Bootstrapping`) is
generic over a language `L` carrying two instances: `L.Encodable`, fixing Gödel
codes for the symbols, and `L.LORDefinable`, providing `𝚺₀` formulas that
recognize the codes of function and relation symbols of each arity.  `ℒₛₑₜ`
already ships an `Encodable` instance (`eq ↦ 0`, `mem ↦ 1`, no function
symbols); this module supplies the missing `LORDefinable` instance, together
with `Language.Finite ℒₛₑₜ` (needed to see that the equality axioms `𝗘𝗤 ℒₛₑₜ`
form a finite theory).

With these instances the whole coded-syntax layer — `IsFormula`, Gödel
quotation `⌜·⌝`, internal substitution, and internal provability — becomes
available for `ℒₛₑₜ` in any model of `𝗜𝚺₁`.
-/

namespace LeanProofs.ZFCinPA

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping

/-! ## Symbol-code ranges of `ℒₛₑₜ`

`ℒₛₑₜ` has no function symbols (`Func k = Empty` for every arity), and exactly
two relation symbols, both binary, with `encode eq = 0` and `encode mem = 1`. -/

/-- No natural number codes a function symbol of `ℒₛₑₜ`. -/
lemma set_mem_range_encode_func {k f : ℕ} :
    f ∈ Set.range (Encodable.encode : (ℒₛₑₜ).Func k → ℕ) ↔ False := by
  simp only [iff_false]
  rintro ⟨x, -⟩
  exact x.elim

/-- The relation-symbol codes of `ℒₛₑₜ`: arity `2` with code `0` (`=`) or `1` (`∈`). -/
lemma set_mem_range_encode_rel {k r : ℕ} :
    r ∈ Set.range (Encodable.encode : (ℒₛₑₜ).Rel k → ℕ) ↔
    (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1) := by
  constructor
  · rintro ⟨R, rfl⟩
    match k, R with
    | 2, Language.Set.Rel.eq => exact Or.inl ⟨rfl, rfl⟩
    | 2, Language.Set.Rel.mem => exact Or.inr ⟨rfl, rfl⟩
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact ⟨Language.Set.Rel.eq, rfl⟩
    · exact ⟨Language.Set.Rel.mem, rfl⟩

/-- The symbol recognizers of `ℒₛₑₜ`: no function symbols; a relation symbol is
an arity-`2` code equal to `0` or `1`. -/
instance instLORDefinableSet : (ℒₛₑₜ).LORDefinable where
  func := .mkSigma “k f. ⊥”
  rel := .mkSigma “k r. (k = 2 ∧ r = 0) ∨ (k = 2 ∧ r = 1)”
  func_iff {k c} :=
    Iff.trans (set_mem_range_encode_func (k := k) (f := c)) (by simp)
  rel_iff {k c} :=
    Iff.trans (set_mem_range_encode_rel (k := k) (r := c)) (by simp; omega)

/-! ## Finiteness of `ℒₛₑₜ` -/

instance : IsEmpty ((k : ℕ) × (ℒₛₑₜ).Func k) := ⟨fun ⟨_, f⟩ => f.elim⟩

/-- The arity-indexed relation symbols of `ℒₛₑₜ` are exactly `⟨2, =⟩` and `⟨2, ∈⟩`. -/
def setRelEquivFinTwo : ((k : ℕ) × (ℒₛₑₜ).Rel k) ≃ Fin 2 where
  toFun := fun ⟨_, R⟩ =>
    match R with
    | Language.Set.Rel.eq => 0
    | Language.Set.Rel.mem => 1
  invFun := ![⟨2, Language.Set.Rel.eq⟩, ⟨2, Language.Set.Rel.mem⟩]
  left_inv := fun ⟨_, R⟩ => by cases R <;> rfl
  right_inv := fun i =>
    match i with
    | 0 => rfl
    | 1 => rfl

instance instFiniteSet : (ℒₛₑₜ).Finite where
  func := Fintype.ofIsEmpty
  rel := Fintype.ofEquiv (Fin 2) setRelEquivFinTwo.symm

/-! ## Smoke tests

The generic coded-syntax layer now fires for `ℒₛₑₜ`: the internal
formulahood predicate elaborates, and sentences of set theory receive
Gödel codes in `ℕ`. -/

#check (Bootstrapping.IsFormula (V := ℕ) ℒₛₑₜ)

#check (⌜SetTheory.Axiom.empty⌝ : ℕ)

#check fun (φ : SetTheorySemiproposition 1) => (⌜φ⌝ : ℕ)

end LeanProofs.ZFCinPA
