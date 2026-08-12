import PolynomialFormulas.LazardInvariantModularCyclicAction
import PolynomialFormulas.LazardInvariantModularProductBridgeCore
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

/-!
# Lightweight degree semantics for the modular cyclic action

This module isolates the characteristic-free, non-certificate facts shared
by the generic cyclic-invariant reconstruction and the degree-seven
enumeration.  In particular, importing it does not force evaluation of the
large degree-seven separation certificates.
-/

namespace LeanProofs.PolynomialFormulas.LazardInvariantModularCyclicInvariants

open scoped BigOperators
open Finset
open LazardInvariantModularCounterexample

set_option autoImplicit false

noncomputable section

/-- The executable weak-composition recursion has exactly its advertised
semantics. -/
theorem mem_weakCompositions_iff (slots total : ℕ) (values : List ℕ) :
    values ∈ weakCompositions slots total ↔
      values.length = slots ∧ values.sum = total := by
  induction slots generalizing total values with
  | zero =>
      cases total <;> cases values <;> simp [weakCompositions]
  | succ slots ih =>
      cases values with
      | nil => simp [weakCompositions]
      | cons first rest =>
          simp [weakCompositions, ih]
          omega

abbrev ExplicitDegreeExponent (d : ℕ) :=
  {a : Exponent // a ∈ (degreeExponents d).toFinset}

/-- Any finite-support exponent of degree `d ≤ 7` occurs in the executable
degree list. -/
theorem exponentFunction_mem_degreeExponents
    (d : Fin 8) (m : Fin 6 →₀ ℕ) (hm : m.degree = d.1) :
    Finsupp.equivFunOnFinite m ∈ (degreeExponents d.1).toFinset := by
  let values : List ℕ :=
    [m 0, m 1, m 2, m 3, m 4, m 5]
  have hm' : (∑ i : Fin 6, m i) = d.1 := by
    simpa [Finsupp.degree_eq_sum] using hm
  have hsum : values.sum = d.1 := by
    simpa [values, Fin.sum_univ_succ] using hm'
  have hweak : values ∈ weakCompositions 6 d.1 :=
    (mem_weakCompositions_iff 6 d.1 values).mpr
      ⟨by simp [values], hsum⟩
  have hexponent :
      exponentOfList values = Finsupp.equivFunOnFinite m := by
    funext i
    fin_cases i <;> rfl
  have hlist :
      Finsupp.equivFunOnFinite m ∈ degreeExponents d.1 := by
    rw [degreeExponents]
    exact List.mem_map.mpr ⟨values, hweak, hexponent⟩
  simpa using hlist

/-- Rotation by one of the six relevant shifts preserves total degree. -/
theorem sum_rotateExponent_of_lt_six (a : Exponent) (k : ℕ) (hk : k < 6) :
    ∑ i : Fin 6, rotateExponent a k i = ∑ i : Fin 6, a i := by
  interval_cases k <;>
    simp [rotateExponent, Fin.sum_univ_succ] <;> omega

end

end LeanProofs.PolynomialFormulas.LazardInvariantModularCyclicInvariants
