import GowersSzemeredi.Proofs16JointRowEightRefinement

/-! The Bogolyubov--Freiman spectrum depends on the dense set alone.
Every order-eight map on that set uses the same constant-radius Bohr
neighborhood, without paying a spectrum-rank cost for each map. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

theorem dense_eight_shared_bohr_spectrum {N : Nat} [NeZero N]
    (A : Finset (ZMod N)) {kappa : Real} (hk : 0 < kappa) (hA : kappa*N ≤ (A.card : Real)) :
    ∃ S : Finset (ZMod N), (S.card : Real) ≤ 16*kappa^(-(2 : Real)) ∧
      ∀ f : ZMod N → ZMod N, FreimanHom 8 A f →
        IsBHomomorphism A (bohr S (1/(8*Real.pi))) f := by
  have hn : (0 : Real) < N := by exact_mod_cast NeZero.pos N
  let alpha : Real := (A.card : Real)/N
  have hka : kappa ≤ alpha := (le_div_iff₀ hn).mpr hA
  have ha : 0 < alpha := hk.trans_le hka
  have hcard : (A.card : Real) = alpha*N := (div_mul_cancel₀ _ hn.ne').symm
  have hid : FreimanHom 8 A id := isAddFreimanHom_id (Set.subset_univ _)
  have hS := (lemma_7_8_constant_radius N A id alpha ha hcard hid).1
  refine ⟨section7Spectrum A alpha,hS.trans ?_,fun f hf => ?_⟩
  · exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_nonpos hk hka (by norm_num)) (by norm_num)
  · exact (lemma_7_8_constant_radius N A f alpha ha hcard hf).2

end LeanProofs.GowersSzemeredi
