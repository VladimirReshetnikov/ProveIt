import GowersSzemeredi.Proofs16ClassStepDegrees
import GowersSzemeredi.Proofs16IntegerClassStepCover
import GowersSzemeredi.Proofs16ClassStepDegreesSide

/-! The same uniform-class successor also has genuine integer covers,
provided its predecessor does. The existing degree budgets are unchanged. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

theorem powerUniformClass_succ_integer {k : Nat} (hk : 1 ≤ k) {V : Real} (hV : 1 ≤ V) {D : Nat}
    (hD : 1 ≤ D) (C : PowerUniformClass k V D D D) (hC : C.IntegerCover) {K p : Nat} (hK : 1 ≤ K) (hp : 0 < p)
    (hlemma6 : AbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor K) (familyWidthDivisor k p)))
    (hIntegerLemma6 : IntegerAbstractFamilyLemma166At k
      (section16PowerWidth (familyWidthPrefactor K) (familyWidthDivisor k p)))
    {V' : Real} (hVV : V ≤ V') (hKV : (K : Real) ≤ V') (hpV : (p : Real) ≤ V') :
    ∃ C' : PowerUniformClass (k + 1) V' (stepCountDeg k D) (stepExpDeg k D) (stepThrDeg k D),
      C'.IntegerCover := by
  classical
  refine ⟨{
    U := fun N _ theta gamma Gamma =>
      ∃ P : Fin (classPieces gamma theta k) → StepPiece C N theta gamma,
        Gamma ⊆ stepPieceGraphs C P
    mono := fun N _ theta gamma Gamma Gamma' hsub ⟨P, hP⟩ => ⟨P, hsub.trans hP⟩
    empty := fun N _ theta gamma =>
      ⟨fun _ => ClassPiece.empty C _ _ _ _ _ _, Finset.empty_subset _⟩
    decomp := ?_
    cover := ?_ }, ?_⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ hN Gamma hsize hprod
    have hN' : classStepThreshold V D theta gamma k ≤ N :=
      (step_thr_le hk hV hVV hg hg1 ht ht1).trans hN
    obtain ⟨J, hJ, P, hP⟩ := class_step_decomp C hk ht ht1 hg hg1 hN' Gamma hsize hprod
    exact ⟨J, hJ, P, hP⟩
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have h := class_step_cover C hk hV (familyWidthPrefactor_pos hK) (familyWidthDivisor_pos hp)
      hlemma6 ht ht1 hg hg1 Gamma P hP
    refine h.weaken ?_ ?_ ?_
    · intro rho hr hr1
      exact step_count_le hD hV hVV hg hg1 ht ht1 hr hr1 n
    · intro rho hr hr1
      have h2 := uniformBase_two_le (hV.trans hVV) n ht ht1 hg hg1 hr hr1
      positivity
    · intro rho hr hr1
      obtain ⟨he0, hei⟩ := step_exp_inv_le hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n
      have := inv_anti₀ (inv_pos.mpr he0) hei
      rwa [inv_inv] at this
  · intro theta gamma ht ht1 hg hg1 N _ _ n Gamma hU
    choose P hP using hU
    have h := integer_class_step_cover C hC hk hV (familyWidthPrefactor_pos hK)
      (familyWidthDivisor_pos hp) hIntegerLemma6 ht ht1 hg hg1 Gamma P hP
    refine h.weaken ?_ ?_ ?_
    · intro rho hr hr1
      exact step_count_le hD hV hVV hg hg1 ht ht1 hr hr1 n
    · intro rho hr hr1
      have h2 := uniformBase_two_le (hV.trans hVV) n ht ht1 hg hg1 hr hr1
      positivity
    · intro rho hr hr1
      obtain ⟨he0, hei⟩ := step_exp_inv_le hD hV hVV hK hp hKV hpV hg hg1 ht ht1 hr hr1 n
      have h := inv_anti₀ (inv_pos.mpr he0) hei
      rwa [inv_inv] at h
end LeanProofs.GowersSzemeredi
