import GowersSzemeredi.Proofs16ModelEliminationStep

/-! Iterate model elimination while retaining both quantitative bounds. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem modelTestDensity_le_quarter (g d : Nat) {r : Real} (hr : 0 < r) :
    modelTestDensity g d r ≤ 1/4 := by
  have hQ : (1 : Real) ≤ refinementCells (r/2) := by
    exact_mod_cast (show 0 < refinementCells (r/2) from Nat.ceil_pos.mpr (by positivity))
  have hp : (1 : Real) ≤ (refinementCells (r/2) : Real)^(g+d) := one_le_pow₀ hQ
  unfold modelTestDensity
  apply (div_le_iff₀ (by positivity : (0 : Real) < 4*(refinementCells (r/2) : Real)^(g+d))).mpr
  nlinarith

theorem column_model_elimination_iterate {J : Type*} {N g d : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N)) (I : Finset J) (Gamma : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (f : J → ZMod N → ZMod N) {rho r s : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hA : A.Nonempty) (hGamma : Gamma.card ≤ g)
    (hT : ∀ x ∈ A, (T x).card ≤ d)
    (hf : ∀ j ∈ I, IsFreimanLinearOn (bohr Gamma rho) (f j))
    (hf0 : ∀ j ∈ I, f j 0 = 0)
    (hne : ∀ j ∈ I, ∃ y ∈ bohr Gamma (refinementKernelRadius g d rho (r/2)), f j y ≠ 0)
    (hN : refinementKernelCap g d rho (r/2) < N) (h7 : 7 ≤ N)
    (hcover : ColumnQuadModelAlternatives A Gamma T L s r I f) (t : Nat) :
    ∃ P ⊆ A, ∃ I' ⊆ I,
      (modelTestDensity g d r/10)^t*A.card ≤ (P.card : Real) ∧
      (I'.card : Real) ≤ (1-modelTestDensity g d r)^t*I.card ∧
      ColumnQuadModelAlternatives P Gamma T L s r I' f := by
  let beta := modelTestDensity g d r
  have hb : 0 < beta := modelTestDensity_pos g d hr
  have hb1 : beta ≤ 1/4 := modelTestDensity_le_quarter g d hr
  have hb10 : 0 ≤ beta/10 := by positivity
  have hc : 0 ≤ 1-beta := by linarith
  induction t with
  | zero => exact ⟨A,Finset.Subset.refl _,I,Finset.Subset.refl _,by simp,by simp,hcover⟩
  | succ t ih =>
    obtain ⟨P,hPA,I',hI'I,hP,hI',hcov⟩ := ih
    have hPne : P.Nonempty := by
      apply Finset.card_pos.mp
      have hpos : (0 : Real) < P.card :=
        (mul_pos (pow_pos (by positivity : 0 < beta/10) t)
          (by exact_mod_cast Finset.card_pos.mpr hA)).trans_le hP
      exact_mod_cast hpos
    by_cases hIe : I'.Nonempty
    · obtain ⟨Q,hQP,I'',hII',hQ,hI'',hcov'⟩ :=
        column_model_elimination_step P I' Gamma T L f hrho hr hrle hPne hIe hGamma
          (fun x hx => hT x (hPA hx)) (fun j hj => hf j (hI'I hj))
          (fun j hj => hf0 j (hI'I hj)) (fun j hj => hne j (hI'I hj)) hN h7 hcov
      refine ⟨Q,hQP.trans hPA,I'',hII'.trans hI'I,?_,?_,hcov'⟩
      · calc _ = (beta/10)*((beta/10)^t*A.card) := by dsimp only [beta]; rw [pow_succ]; ring
          _ ≤ (beta/10)*P.card := mul_le_mul_of_nonneg_left hP hb10
          _ ≤ _ := hQ
      · calc (I''.card : Real) ≤ (1-beta)*I'.card := hI''
          _ ≤ (1-beta)*((1-beta)^t*I.card) := mul_le_mul_of_nonneg_left hI' hc
          _ = _ := by dsimp only [beta]; rw [pow_succ]; ring
    · have hIe' : I' = ∅ := Finset.not_nonempty_iff_eq_empty.mp hIe
      refine ⟨P,hPA,I',hI'I,?_,?_,hcov⟩
      · calc _ = (beta/10)*((beta/10)^t*A.card) := by dsimp only [beta]; rw [pow_succ]; ring
          _ ≤ 1*((beta/10)^t*A.card) := mul_le_mul_of_nonneg_right (by linarith) (by positivity)
          _ ≤ _ := by simpa only [one_mul] using hP
      · rw [hIe']; simp only [Finset.card_empty,Nat.cast_zero]
        exact mul_nonneg (pow_nonneg hc _) (Nat.cast_nonneg _)

end LeanProofs.GowersSzemeredi
