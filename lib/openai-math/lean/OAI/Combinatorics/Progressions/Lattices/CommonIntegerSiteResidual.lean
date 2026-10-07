/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Estimates.ScaledLinearResidual
import OAI.Combinatorics.Progressions.Fourier.CommonCoveredSiteCharacter

namespace OAI

section

namespace Erdos3

open scoped BigOperators Matrix Classical

theorem clearedMatrix_real {I S : Type*} [Fintype I] [Fintype S]
    (T : Matrix I S ℚ) (i : I) (s : S) :
    (clearedMatrix T i s : ℝ) = (matrixDenominator T : ℝ) * (T i s : ℝ) := by
  have h := congrFun (congrFun (clearedMatrix_cast T) i) s
  change (clearedMatrix T i s : ℚ) = (matrixDenominator T : ℚ) * T i s at h
  exact_mod_cast h

theorem matrixModuleAction_cleared {I S W : Type*} [Fintype I] [Fintype S]
    [AddCommGroup W] [Module ℝ W] (T : Matrix I S ℚ) (x : S → W) :
    matrixModuleAction (fun i s => (clearedMatrix T i s : ℝ)) x =
      (matrixDenominator T : ℝ) • matrixModuleAction (fun i s => (T i s : ℝ)) x := by
  funext i
  change (∑ s, (clearedMatrix T i s : ℝ) • x s) =
    (matrixDenominator T : ℝ) • ∑ s, (T i s : ℝ) • x s
  simp only [clearedMatrix_real, mul_smul, Finset.smul_sum]

theorem exists_integer_site_residual {I S : Type*} [Fintype I] [Fintype S]
    (E : Matrix S I ℤ) {H : ℕ} (hH : 1 ≤ H)
    (hE : ∀ s i, RationalHeightLE (E s i : ℚ) H) :
    ∃ (q : ℕ) (T : Matrix I S ℤ), 0 < q ∧
      (∀ {W : Type*} [AddCommGroup W] [Module ℝ W] (x : I → W),
        matrixModuleAction (fun s i => (E s i : ℝ))
          (matrixModuleAction (fun i s => (T i s : ℝ))
            (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
          (q : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x) ∧
      (∀ {P : ℝ}, 0 ≤ P → (Fintype.card I : ℝ) ≤ P → (Fintype.card S : ℝ) ≤ P →
        (H : ℝ) ≤ Real.exp P → (q : ℝ) ≤ Real.exp ((P + 2) ^ 36)) := by
  obtain ⟨T, hT, hTH⟩ := exists_bounded_rational_image_section (fun s i => (E s i : ℚ)) hH hE
  refine ⟨matrixDenominator T, clearedMatrix T, matrixDenominator_pos T, ?_, ?_⟩
  · intro W _ _ x
    rw [matrixModuleAction_cleared, map_smul]
    congr 1
    have he := matrixModuleAction_image_section
      (Matrix.of (fun s i => ((E s i : ℚ) : ℝ)))
      (Matrix.of (fun i s => (T i s : ℝ)))
      (real_matrix_image_section _ T hT) x
    have he' := congrFun he
    funext s
    have hs := he' s
    simpa only [matrixModuleAction, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.of_apply, Rat.cast_intCast] using hs
  · intro P hP hI hS hHP
    simpa only [Nat.mul_one] using real_image_section_denominator_bound T H 1 hTH hP hS hI hHP
      (by simpa using Real.one_le_exp hP)

theorem scaledSiteResidual_preserves_lattice {I S J : Type*} [Fintype I] [Fintype S]
    (U : Submodule ℝ (J → ℝ)) (E : Matrix S I ℤ) (T : Matrix I S ℤ) (q : ℕ)
    (x : I → U) (hx : x ∈ subspaceArrayIntegerLattice I U) :
    scaledLinearResidual (matrixModuleAction (fun s i => (E s i : ℝ)))
      (matrixModuleAction (fun i s => (T i s : ℝ))) (q : ℝ) x ∈ subspaceArrayIntegerLattice I U := by
  apply (subspaceArrayIntegerLattice I U).sub_mem ?_
    (integerMatrix_preserves_array_lattice U T _ (integerMatrix_preserves_array_lattice U E x hx))
  intro i a
  obtain ⟨z, hz⟩ := hx i a
  refine ⟨(q : ℤ) * z, ?_⟩
  change (q : ℝ) * (x i).val a = _
  rw [hz, Int.cast_mul, Int.cast_natCast]

end Erdos3

end

section

namespace Erdos3

open scoped Matrix Classical

theorem cleared_image_section_entry_bound {I S : Type*} [Fintype I] [Fintype S]
    (T : Matrix I S ℚ) (H : ℕ)
    (hT : ∀ i s, RationalHeightLE (T i s) (rationalKernelHeight (Fintype.card S) H))
    {P : ℝ} (hP : 0 ≤ P) (hI : (Fintype.card I : ℝ) ≤ P)
    (hS : (Fintype.card S : ℝ) ≤ P) (hH : (H : ℝ) ≤ Real.exp P) (i : I) (s : S) :
    |(clearedMatrix T i s : ℝ)| ≤ Real.exp (2 * (P + 2) ^ 36) := by
  have hden : (matrixDenominator T : ℝ) ≤ Real.exp ((P + 2) ^ 36) := by
    simpa only [Nat.mul_one] using real_image_section_denominator_bound T H 1 hT hP hS hI hH
      (by simpa using Real.one_le_exp hP)
  have hentry := (hT i s).abs_real_le.trans
    (rationalKernelHeight_le_budget (Fintype.card S) H hP hS hH)
  have hpow : (P + 2) ^ 7 ≤ (P + 2) ^ 36 :=
    pow_le_pow_right₀ (by linarith) (by decide)
  rw [clearedMatrix_real, abs_mul, abs_of_nonneg (Nat.cast_nonneg _)]
  calc
    _ ≤ Real.exp ((P + 2) ^ 36) * Real.exp ((P + 2) ^ 7) :=
      mul_le_mul hden hentry (abs_nonneg _) (Real.exp_pos _).le
    _ = Real.exp ((P + 2) ^ 36 + (P + 2) ^ 7) := (Real.exp_add _ _).symm
    _ ≤ Real.exp (2 * (P + 2) ^ 36) := Real.exp_le_exp.mpr (by linarith)

theorem exists_bounded_integer_site_residual {I S : Type*} [Fintype I] [Fintype S]
    (E : Matrix S I ℤ) {H : ℕ} (hH : 1 ≤ H)
    (hE : ∀ s i, RationalHeightLE (E s i : ℚ) H) :
    ∃ (d : ℕ) (T : Matrix I S ℤ), 0 < d ∧
      (∀ {W : Type*} [AddCommGroup W] [Module ℝ W] (x : I → W),
        matrixModuleAction (fun s i => (E s i : ℝ))
          (matrixModuleAction (fun i s => (T i s : ℝ))
            (matrixModuleAction (fun s i => (E s i : ℝ)) x)) =
          (d : ℝ) • matrixModuleAction (fun s i => (E s i : ℝ)) x) ∧
      (∀ {P : ℝ}, 0 ≤ P → (Fintype.card I : ℝ) ≤ P → (Fintype.card S : ℝ) ≤ P →
        (H : ℝ) ≤ Real.exp P →
        (d : ℝ) ≤ Real.exp ((P + 2) ^ 36) ∧
          ∀ i s, |(T i s : ℝ)| ≤ Real.exp (2 * (P + 2) ^ 36)) := by
  obtain ⟨T, hT, hTH⟩ := exists_bounded_rational_image_section (fun s i => (E s i : ℚ)) hH hE
  refine ⟨matrixDenominator T, clearedMatrix T, matrixDenominator_pos T, ?_, ?_⟩
  · intro W _ _ x
    rw [matrixModuleAction_cleared, map_smul]
    congr 1
    have he := matrixModuleAction_image_section
      (Matrix.of (fun s i => ((E s i : ℚ) : ℝ)))
      (Matrix.of (fun i s => (T i s : ℝ))) (real_matrix_image_section _ T hT) x
    funext s
    simpa only [matrixModuleAction, LinearMap.coe_mk, AddHom.coe_mk,
      Matrix.of_apply, Rat.cast_intCast] using congrFun he s
  · intro P hP hI hS hHP
    refine ⟨?_, cleared_image_section_entry_bound T H hTH hP hI hS hHP⟩
    simpa only [Nat.mul_one] using real_image_section_denominator_bound T H 1 hTH hP hS hI hHP
      (by simpa using Real.one_le_exp hP)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators Classical

theorem matrixModuleAction_int_smul {I S W : Type*} [Fintype S]
    [AddCommGroup W] [Module ℝ W] (T : Matrix I S ℤ) (d : ℕ) (x : S → W) :
    matrixModuleAction (fun i s => (((d : ℤ) * T i s : ℤ) : ℝ)) x =
      (d : ℝ) • matrixModuleAction (fun i s => (T i s : ℝ)) x := by
  funext i
  change (∑ s, (((d : ℤ) * T i s : ℤ) : ℝ) • x s) =
    (d : ℝ) • ∑ s, (T i s : ℝ) • x s
  simp only [Int.cast_mul, Int.cast_natCast, mul_smul, Finset.smul_sum]

theorem exists_common_integer_site_residual {J S : Type*} [Fintype J] [Fintype S]
    {I : J → Type*} [∀ j, Fintype (I j)] (E : ∀ j, Matrix S (I j) ℤ)
    (H : J → ℕ) (hH : ∀ j, 1 ≤ H j)
    (hE : ∀ j s i, RationalHeightLE (E j s i : ℚ) (H j)) :
    ∃ (q : ℕ) (T : ∀ j, Matrix (I j) S ℤ), 0 < q ∧
      (∀ j {W : Type*} [AddCommGroup W] [Module ℝ W] (x : I j → W),
        matrixModuleAction (fun s i => (E j s i : ℝ))
          (matrixModuleAction (fun i s => (T j i s : ℝ))
            (matrixModuleAction (fun s i => (E j s i : ℝ)) x)) =
          (q : ℝ) • matrixModuleAction (fun s i => (E j s i : ℝ)) x) ∧
      (∀ {P : ℝ}, 0 ≤ P → (∀ j, (Fintype.card (I j) : ℝ) ≤ P) →
        (Fintype.card S : ℝ) ≤ P → (∀ j, (H j : ℝ) ≤ Real.exp P) →
        (q : ℝ) ≤ Real.exp (Fintype.card J * (P + 2) ^ 36)) := by
  choose d T hd hT hbound using fun j => exists_integer_site_residual (E j) (hH j) (hE j)
  let q := ∏ j, d j
  let c := fun j => ∏ i ∈ Finset.univ.erase j, d i
  have hc (j) : c j * d j = q := by
    exact (Finset.prod_erase_mul _ _ (Finset.mem_univ j)).trans rfl
  refine ⟨q, fun j i s => (c j : ℤ) * T j i s, Finset.prod_pos (fun j _ => hd j), ?_, ?_⟩
  · intro j W _ _ x
    rw [matrixModuleAction_int_smul, map_smul, hT j, smul_smul]
    congr 1
    exact_mod_cast hc j
  · intro P hP hI hS hHP
    calc
      (q : ℝ) = ∏ j, (d j : ℝ) := Nat.cast_prod _ _
      _ ≤ ∏ _j : J, Real.exp ((P + 2) ^ 36) :=
        Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => hbound j hP (hI j) hS (hHP j))
      _ = Real.exp (Fintype.card J * (P + 2) ^ 36) := by
        rw [Finset.prod_const, Finset.card_univ, ← Real.exp_nat_mul]

end Erdos3

end

end OAI
