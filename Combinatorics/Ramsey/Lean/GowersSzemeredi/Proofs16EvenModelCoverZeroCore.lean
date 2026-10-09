import GowersSzemeredi.Proofs16EvenModelInitialization

/-! A zero-relation core for all alternating lists of a fixed even length,
with a retention bound depending only on the full model-count cap. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Eliminate precisely the models which do not already vanish, with a
retention bound depending only on an upper bound for the full model count. -/
theorem even_model_cover_zero_core {J : Type*} {N g d M k : Nat} [NeZero N] [Fact N.Prime] [NeZero k]
    (A : Finset (ZMod N)) (I : Finset J) (Gamma : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (f : J → ZMod N → ZMod N) {rho r : Real}
    (hrho : 0 < rho) (hr : 0 < r) (hrle : r ≤ rho)
    (hA : A.Nonempty) (hGamma : Gamma.card ≤ g) (hI : I.card ≤ M)
    (hT : ∀ x ∈ A, (T x).card ≤ d)
    (hf : ∀ j ∈ I, IsFreimanLinearOn (bohr Gamma rho) (f j))
    (hf0 : ∀ j ∈ I, f j 0 = 0)
    (hN : refinementKernelCap g d rho (r/2) < N) (h7 : 7 ≤ N)
    (hcover : ∀ a ∈ columnAnchorFibre A (2*k-1) 0, ∃ j ∈ I,
      ∀ y ∈ bohr Gamma r, (∀ x ∈ columnAnchorList a, y ∈ bohr (T x) r) →
        columnAnchorEval (fun x => L x y) (columnAnchorList a) = f j y) :
    let beta := modelTestDensity g d r
    let t := modelEliminationRounds beta M
    let s := min r (refinementKernelRadius g d rho (r/2))
    ∃ P ⊆ A, P.Nonempty ∧ (beta/(5*k))^t*A.card ≤ (P.card : Real) ∧
      ∀ as : List (ZMod N), as.length = 2*k → (∀ x ∈ as, x ∈ P) → columnAnchorEval id as = 0 →
        ∀ y ∈ bohr Gamma s, (∀ x ∈ as, y ∈ bohr (T x) s) → columnAnchorEval (fun x => L x y) as = 0 := by
  let u := refinementKernelRadius g d rho (r/2)
  let I' := I.filter (fun j => ∃ y ∈ bohr Gamma u, f j y ≠ 0)
  have hsub : I' ⊆ I := Finset.filter_subset _ _
  obtain ⟨P,hPA,hPne,hP,hzero⟩ := even_model_elimination_zero_core (k := k) A I' Gamma T L f
    hrho hr hrle hA hGamma hT (fun j hj => hf j (hsub hj))
    (fun j hj => hf0 j (hsub hj)) (fun j hj => (Finset.mem_filter.mp hj).2) hN h7
    (even_models_initialize (k := k) A Gamma T L I f r u hcover)
  refine ⟨P,hPA,hPne,?_,hzero⟩
  have hk : (1 : Real) ≤ k := by exact_mod_cast NeZero.pos k
  have hb := modelTestDensity_pos g d hr
  have hb1 := modelTestDensity_le_quarter g d hr
  have ht := modelEliminationRounds_mono hb ((Finset.card_le_card hsub).trans hI)
  exact (mul_le_mul_of_nonneg_right
    (pow_le_pow_of_le_one (by positivity) ((div_le_iff₀ (by positivity)).mpr (by nlinarith) : modelTestDensity g d r/(5*k) ≤ 1) ht)
    (Nat.cast_nonneg A.card)).trans hP

end LeanProofs.GowersSzemeredi
