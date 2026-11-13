import DiophantineConsistency.Compact44.P64Norm

/-! P64's residual split with an arbitrary first residual. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace P64NormFirstReplacement
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing ArithmeticSignedPairs
open ArithmeticAdaptiveQuotients2011 P64Graph P64Root P64Norm
open ArithmeticAdaptiveFactorUnits2011 (residue residue_add residue_mul residue_nat)
open P72Root (ι_tsub)
open P72Aux (ι_absdiff_sq)
open DiophantineConsistency.ArithmeticPellHalfIndex (absdiff)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem residuals (p : Fin 4 → ℕ) (v : Fin 14 → V) (hv : ∀ j, 0 < v j)
    (first : DiffRing V)
    (hs : first*first +
      (graph (fun j => (p j : ℤ))).M.evalRing (fun j => ι (v j)) * (graph (fun j => (p j : ℤ))).M.evalRing (fun j => ι (v j)) +
      (graph (fun j => (p j : ℤ))).W.evalRing (fun j => ι (v j)) * (graph (fun j => (p j : ℤ))).W.evalRing (fun j => ι (v j)) +
      (graph (fun j => (p j : ℤ))).Na.evalRing (fun j => ι (v j)) * (graph (fun j => (p j : ℤ))).Na.evalRing (fun j => ι (v j)) +
      (graph (fun j => (p j : ℤ))).Lt.evalRing (fun j => ι (v j)) * (graph (fun j => (p j : ℤ))).Lt.evalRing (fun j => ι (v j)) = 1) :
    first=0 ∧ InternalZero (graph (fun j => (p j : ℤ))).M v ∧
      InternalZero (graph (fun j => (p j : ℤ))).W v ∧
      (graph (fun j => (p j : ℤ))).Na.evalRing (fun j => ι (v j)) = 1 ∧
      InternalZero (graph (fun j => (p j : ℤ))).Lt v := by
  set q : V := (p 0 : V) * v 0 + 1 with hq
  set cV : V := (v 10 + v 11) * v 7 + v 10 with hcV
  set aV : V := (v 8 * q) * v 7 + v 7 with haV
  set ΔV : V := aV * aV + (4 * aV + 3) with hΔV
  have hf1 : 1 ≤ v 4 * v 4 := one_le_mul_of_one_le_of_one_le (pos_iff_one_le.mp (hv 4)) (pos_iff_one_le.mp (hv 4))
  set A : V := ΔV * (v 4 * v 4 - 1) with hA
  have cA : (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).Aaux = ι A := by
    rw [c_Aaux, c_Delta, hA, map_mul, ι_tsub hf1, map_mul, map_one]
  obtain ⟨P0, N0, hPN⟩ := exists_mk (vals (fun j => (p j : ℤ)) (fun j => ι (v j))).V
  rw [mk_eq_sub] at hPN
  set x : V := absdiff P0 N0 with hx
  set y : V := absdiff (P0 + v 12) N0 with hy
  have hna : (graph (fun j => (p j : ℤ))).Na.evalRing (fun j => ι (v j)) =
      ι A * (ι x * ι x - ι y * ι y) + ι y * ι y := by
    rw [Na_eval, c_y, cA, hPN, hx, hy, ι_absdiff_sq, ι_absdiff_sq, map_add]; ring
  -- Na ≠ 0
  have hn : (graph (fun j => (p j : ℤ))).Na.evalRing (fun j => ι (v j)) ≠ 0 := by
    intro h0
    rcases (pos_iff_one_le.mp (hv 4)).lt_or_eq with hf2 | hf1'
    · -- f ≥ 2: A ≥ 2
      have hA2 : 2 ≤ A := by
        have hΔ3 : 3 ≤ ΔV := le_add_self.trans' (le_add_self)
        have hff : 4 ≤ v 4 * v 4 := by
          have h2 : 2 ≤ v 4 := by simpa [one_add_one_eq_two] using lt_iff_succ_le.mp hf2
          calc (4 : V) = 2 * 2 := by norm_num
            _ ≤ v 4 * v 4 := mul_le_mul h2 h2 (by norm_num) (Arithmetic.zero_le _)
        have hf3 : 3 ≤ v 4 * v 4 - 1 := by
          apply (add_le_add_iff_right (1 : V)).mp
          rw [tsub_add_cancel_of_le hf1]
          calc (3 : V) + 1 = 4 := by norm_num
            _ ≤ v 4 * v 4 := hff
        calc (2 : V) ≤ 3 * 3 := by norm_num
          _ ≤ ΔV * (v 4 * v 4 - 1) := mul_le_mul hΔ3 hf3 (by norm_num) (Arithmetic.zero_le _)
      apply na_ne_zero A P0 N0 (v 12) hA2 (hv 12)
      apply ι_injective
      simp only [map_add, map_mul]
      rw [hna] at h0
      linear_combination h0
    · -- f = 1: W is too large
      have hA0 : A = 0 := by rw [hA, ← hf1', mul_one, tsub_self, mul_zero]
      have hc3 : (3 : V) ≤ cV := by
        have hk2 : 2 ≤ v 10 + v 11 := by
          simpa [one_add_one_eq_two] using add_le_add (pos_iff_one_le.mp (hv 10)) (pos_iff_one_le.mp (hv 11))
        calc (3 : V) = 2 * 1 + 1 := by norm_num
          _ ≤ (v 10 + v 11) * v 7 + v 10 := add_le_add (mul_le_mul hk2 (pos_iff_one_le.mp (hv 7))
              (by norm_num) (Arithmetic.zero_le _)) (pos_iff_one_le.mp (hv 10))
      have hI : (9 : V) ≤ v 5 * (cV * cV) := by
        calc (9 : V) = 1 * (3 * 3) := by norm_num
          _ ≤ v 5 * (cV * cV) := mul_le_mul (pos_iff_one_le.mp (hv 5))
              (mul_le_mul hc3 hc3 (by norm_num) (Arithmetic.zero_le _)) (by norm_num) (Arithmetic.zero_le _)
      have hW : (graph (fun j => (p j : ℤ))).W.evalRing (fun j => ι (v j)) =
          ι (v 5 * (cV * cV)) * ι (v 5 * (cV * cV)) := by
        rw [W_eval, cA, hA0, map_zero, _root_.sub_zero, c_c]; simp only [map_mul]; rfl
      have hI' : (9 : DiffRing V) ≤ ι (v 5 * (cV * cV)) := by
        have h := (ι_le_ι (V := V)).mpr hI; rwa [map_ofNat] at h
      rw [hW, h0] at hs
      set I : DiffRing V := ι (v 5 * (cV * cV)) with hIdef
      have hII : (81 : DiffRing V) ≤ I * I := by nlinarith
      have hIIII : (6561 : DiffRing V) ≤ I * I * (I * I) := by nlinarith
      have := mul_self_nonneg first
      have := mul_self_nonneg ((graph (fun j => (p j : ℤ))).M.evalRing (fun j => ι (v j)))
      have := mul_self_nonneg ((graph (fun j => (p j : ℤ))).Lt.evalRing (fun j => ι (v j)))
      linarith
  obtain ⟨h0, hm, hw, hn1, hl⟩ := sq_split hs hn
  refine ⟨h0, (internalZero_iff _ _).mpr hm, (internalZero_iff _ _).mpr hw,
    ?_, (internalZero_iff _ _).mpr hl⟩
  rcases hn1 with h1 | hneg
  · exact h1
  · exfalso
    apply na_ne_neg aV (v 4) x y hf1
    rw [← hΔV, ← hA]
    apply ι_injective
    rw [hna] at hneg
    simp only [map_add, map_mul, map_one]
    linear_combination hneg

end P64NormFirstReplacement

#print axioms P64NormFirstReplacement.residuals
