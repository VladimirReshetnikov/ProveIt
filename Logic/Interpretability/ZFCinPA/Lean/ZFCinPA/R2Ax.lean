import ZFCinPA.R2Gic
import ZFCinPA.NativePeel
import ZFCinPA.NativeTheory

set_option autoImplicit false
noncomputable section

/-!
# R2: the axioms of the native theory are validator theorems

* `gic_body`: the encoded GIC body at every odd environment and even stream,
  from `R2Gic.gic_bridge_core` at the odd stream `lu F` and Codex's stream
  alpha transport `encode_formula_relabel`;
* `closure`: the encoded universal closure `qqAlls b m` of a body whose opened
  instances are validator theorems at every odd environment, by `Π₂` induction
  over the (possibly nonstandard) binder count, one `R2Quant.all_step` per
  binder;
* `gic_axiom`: every internal code recognized by `GicR`.
-/

namespace LeanProofs.ZFCinPA.R2Ax

open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open LeanProofs.ZFCinPA.ValidatorProvability254 LeanProofs.ZFCinPA.ValidatorQuantifierCore254
open LeanProofs.ZFCinPA.ValidatorEnvironmentLabels254 LeanProofs.ZFCinPA.ValidatorEnvironmentVacuity254
open LeanProofs.ZFCinPA.ValidatorEnvironmentOpening254 LeanProofs.ZFCinPA.ValidatorEnvironmentStreams254
open LeanProofs.ZFCinPA.ValidatorEnvironmentAlpha254 LeanProofs.ZFCinPA.ValidatorNativeGicSlots254
open LeanProofs.ZFCinPA.R2Ctx LeanProofs.ZFCinPA.R2Neg LeanProofs.ZFCinPA.R2Quant LeanProofs.ZFCinPA.R2Gic
open scoped LO.FirstOrder.Arithmetic

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺 2]

/-- **The encoded GIC body** at every odd environment and even stream. -/
theorem gic_body (K : SF (V := V) 2) {F s : V} (hF : OddEnv F) (hs : s % 2 = 0) :
    CProv (encode F 0 s (gicBody K).val) := by
  set t := lu F
  have ot : t % 2 = 1 := lu_odd F
  have hb := gic_bridge_core K hF (lx_odd F) (lw_odd F) ot (odd_add_two ot)
    (odd_add_two (odd_add_two ot)) (odd_add_two (odd_add_two (odd_add_two ot)))
    (odd_add_two (odd_add_two (odd_add_two (odd_add_two ot))))
    (lx_gt F) (one_lt_lx F) (lx_lt_lw F) (lw_lt_lu F) (lt_add_two _) (lt_add_two _)
    (lt_add_two _) (lt_add_two _)
  have ht : CProv (encode F 0 t (gicBody K).val) := by
    rw [encode_gicBody, SUPc_eq, COVc_eq]; exact hb
  have hFt : F < t := (lx_gt F).trans ((lx_lt_lw F).trans (lw_lt_lu F))
  have h1t : 1 < t := (one_lt_lx F).trans ((lx_lt_lw F).trans (lw_lt_lu F))
  have hp : IsFormula ℒₛₑₜ (gicBody K).val := (gicBody K).isSemiformula
  exact cProv_mp (encode_formula_relabel hp F t s (streamFree_big hFt h1t)
    (streamFree_even hs hF)).1 ht


/-! ## Universal closure -/

/-- The opened closure code peeled to `i` binders. -/
noncomputable def pc (s m b F i : V) : V := encode F 0 s (subst ℒₛₑₜ (fvarVec (m - i)) (qqAlls b i))

private instance cProv_pi2 : 𝚷-[2]-Predicate[V] CProv := sigma1_to_pi2 cProv_definable
private instance oddEnv_pi2 : 𝚷-[2]-Predicate[V] OddEnv := R2Main.oddEnv_definable.of_deltaOne

/-- **The universal closure**: if every opened instance of a shift-fixed body with
`m` bound variables is a validator theorem at every odd environment, so is its
closure `qqAlls b m`. -/
theorem closure {m b s : V} (hb : IsSemiformula ℒₛₑₜ m b) (hbs : shift ℒₛₑₜ b = b) (hs : s % 2 = 0)
    (base : ∀ F : V, OddEnv F → CProv (encode F 0 s (subst ℒₛₑₜ (fvarVec m) b))) :
    ∀ F : V, OddEnv F → CProv (encode F 0 s (qqAlls b m)) := by
  have hpc1 : 𝚺₁-Function₂[V] (fun F i ↦ pc s m b F i) := by unfold pc; definability
  haveI : 𝚺-[2]-Function₂[V] (fun F i ↦ pc s m b F i) := hpc1.of_sigmaOne
  have key : ∀ i : V, i ≤ m → ∀ F : V, OddEnv F → CProv (pc s m b F i) := by
    apply InductionOnHierarchy.order_induction_sigma 𝚷 2
      (P := fun i => i ≤ m → ∀ F : V, OddEnv F → CProv (pc s m b F i))
    · definability
    intro i ih hi F hF
    rcases zero_or_succ i with (rfl | ⟨j, rfl⟩)
    · simpa [pc] using base F hF
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + (j + 1) := ⟨m - (j + 1), (tsub_add_cancel_of_le hi).symm⟩
      have e1 : k + (j + 1) - j = k + 1 := by
        rw [add_comm j 1, ← add_assoc, add_tsub_cancel_right]
      have hB : IsSemiformula ℒₛₑₜ (k + 1) (qqAlls b j) :=
        IsSemiformula.qqAlls (by rwa [add_assoc, add_comm 1 j])
      have hBs : shift ℒₛₑₜ (qqAlls b j) = qqAlls b j := by
        rw [NativePeel.shift_qqAlls hb.isUFormula, hbs]
      have hf := ModelCodedBindFree.fvarVec_isTermVec (L := ℒₛₑₜ) (V := V) k
      have hw : IsSemitermVec ℒₛₑₜ (k + 1) 1 (qVec ℒₛₑₜ (fvarVec k)) := by simpa using hf.qVec
      have hq : IsSemiformula ℒₛₑₜ 1 (subst ℒₛₑₜ (qVec ℒₛₑₜ (fvarVec k)) (qqAlls b j)) := hB.subst hw
      have ih' := ih j (by simp) (le_trans (by simp) hi) (lx F ∷ F) (R2Main.oddEnv_cons (lx_odd F) hF)
      simp only [pc, e1] at ih'
      rw [← NativePeel.free_subst_qVec_fvarVec hB hBs, encode_free hq F (lx F) s] at ih'
      simp only [pc, add_tsub_cancel_right]
      rw [qqAlls_succ, substs_all hB.isUFormula]
      exact cProv_mp (all_step hq hF hs).1 (cProv_gen (lx F) ih')
  intro F hF
  have h := key m le_rfl F hF
  simp only [pc, tsub_self] at h
  have hc : IsSemiformula ℒₛₑₜ 0 (qqAlls b m) := IsSemiformula.qqAlls (by simpa using hb)
  rwa [subst_eq_self hc (ModelCodedBindFree.fvarVec_isTermVec (L := ℒₛₑₜ) 0) (by simp)] at h

/-- **Every internal GIC axiom code is a validator theorem**, at every odd
environment and even stream. -/
theorem gic_axiom {p : V} (hp : GicR p) {F s : V} (hF : OddEnv F) (hs : s % 2 = 0) :
    CProv (encode F 0 s p) := by
  obtain ⟨m, -, b, -, rfl, hbU, hbs, hbv, K, -, hK, hKb⟩ := hp
  have hb : IsSemiformula ℒₛₑₜ m b := by simpa [hbv] using hbU.isSemiformula
  let Kt : SF (V := V) 2 := ⟨K, by simpa using hK⟩
  exact closure hb hbs hs (fun F' hF' ↦ by
    rw [hKb, show K = Kt.val from rfl, gicBodyVal_eq Kt]; exact gic_body Kt hF' hs) F hF

end LeanProofs.ZFCinPA.R2Ax
