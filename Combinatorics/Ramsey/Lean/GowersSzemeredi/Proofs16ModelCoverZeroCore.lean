import GowersSzemeredi.Proofs16ModelInitialization

/-! A uniform zero-relation core from a complete finite model cover. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem modelEliminationRounds_mono {beta : Real} (hb : 0 < beta)
    {m M : Nat} (hm : m ≤ M) : modelEliminationRounds beta m ≤ modelEliminationRounds beta M := by
  apply Nat.ceil_le_ceil
  apply div_le_div_of_nonneg_right _ hb.le
  exact Real.log_le_log (by positivity) (by exact_mod_cast Nat.add_le_add_right hm 1)

/-- Eliminate precisely the models which do not already vanish, with a
retention bound depending only on an upper bound for the full model count. -/
theorem column_model_cover_zero_core {J : Type*} {N g d M : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N)) (I : Finset J) (Gamma : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (f : J → ZMod N → ZMod N) {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hA : A.Nonempty) (hGamma : Gamma.card ≤ g) (hI : I.card ≤ M)
    (hT : ∀ x ∈ A, (T x).card ≤ d)
    (hf : ∀ j ∈ I, IsFreimanLinearOn (bohr Gamma rho) (f j))
    (hf0 : ∀ j ∈ I, f j 0 = 0)
    (hN : refinementKernelCap g d rho (r/2) < N) (h7 : 7 ≤ N)
    (hcover : ∀ a ∈ columnAnchorFibre A 3 0, ∃ j ∈ I,
      ∀ y ∈ bohr Gamma r, (∀ x ∈ columnAnchorList a, y ∈ bohr (T x) r) →
        columnAnchorEval (fun x => L x y) (columnAnchorList a) = f j y) :
    let beta := modelTestDensity g d r
    let t := modelEliminationRounds beta M
    let s := min r (refinementKernelRadius g d rho (r/2))
    ∃ P ⊆ A, P.Nonempty ∧ (beta/10)^t*A.card ≤ (P.card : Real) ∧
      ∀ q : Fin 4 → ZMod N, (∀ i, q i ∈ P) → q 0-q 1+q 2-q 3 = 0 →
        ∀ y ∈ bohr Gamma s, (∀ i, y ∈ bohr (T (q i)) s) → columnQuadValue L q y = 0 := by
  let u := refinementKernelRadius g d rho (r/2)
  let I' := I.filter (fun j => ∃ y ∈ bohr Gamma u, f j y ≠ 0)
  have hsub : I' ⊆ I := Finset.filter_subset _ _
  obtain ⟨P,hPA,hPne,hP,hzero⟩ := column_model_elimination_zero_core A I' Gamma T L f
    hrho hr hrle hA hGamma hT (fun j hj => hf j (hsub hj))
    (fun j hj => hf0 j (hsub hj)) (fun j hj => (Finset.mem_filter.mp hj).2) hN h7
    (column_models_initialize A Gamma T L I f r u hcover)
  refine ⟨P,hPA,hPne,?_,hzero⟩
  have hb := modelTestDensity_pos g d hr
  have hb1 := modelTestDensity_le_quarter g d hr
  have ht := modelEliminationRounds_mono hb ((Finset.card_le_card hsub).trans hI)
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (by positivity) (by linarith : modelTestDensity g d r/10 ≤ 1) ht)
    (Nat.cast_nonneg A.card)).trans hP

end LeanProofs.GowersSzemeredi
