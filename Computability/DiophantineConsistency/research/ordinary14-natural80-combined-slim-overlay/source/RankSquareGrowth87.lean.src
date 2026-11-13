import PowerRecovery87
import GuardGap87

/-! Source-only model rank-square and own-zero X>q² bounds. No Mersenne
condition, q|X, Lean elaboration or endpoint is assumed. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.RankSquareGrowth87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing NaturalRank84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The positive scalar gap alone forces q² below the natural rank. -/
theorem scalar_rank_square (q beta J F alpha MC MF : V)
    (hJ : 0<J) (hF : 0<F) (ha : 0<alpha)
    (hq : q=1+J*beta) (hgap : F+alpha<q) :
    q*q≤(alpha+(q-F)*(J*beta))*(q*q-1)+J*(MC+MF*q) := by
  have hf1 : 1≤F := pos_iff_one_le.mp hF
  have ha1 : 1≤alpha := pos_iff_one_le.mp ha
  have hgap1 : F+alpha+1≤q := lt_iff_succ_le.mp hgap
  have hq3 : 3≤q := by nlinarith
  have hq1 : 1≤q := by nlinarith
  have hFq : F≤q := le_of_lt (lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le alpha)) hgap)
  have heF : q-F+F=q := tsub_add_cancel_of_le hFq
  have he1 : q-1+1=q := tsub_add_cancel_of_le hq1
  have hqm : 2≤q-1 := by nlinarith
  have hqF : 2≤q-F := by nlinarith
  have hmult : 4≤(q-F)*(q-1) := by
    have h := mul_le_mul hqF hqm (by norm_num : (0:V)≤2) (Arithmetic.zero_le (q-F))
    norm_num at h ⊢
    exact h
  have hG : 5≤alpha+(q-F)*(J*beta) := by
    have he : q-1=J*beta := by rw [hq]; simp [add_comm]
    rw [←he]
    nlinarith
  have hq2 : 9≤q*q := by
    have h := mul_le_mul hq3 hq3 (by norm_num : (0:V)≤3) (Arithmetic.zero_le q)
    norm_num at h ⊢
    exact h
  have hq2one : 1≤q*q := by nlinarith
  have hesq : q*q-1+1=q*q := tsub_add_cancel_of_le hq2one
  have hG2 : 2≤alpha+(q-F)*(J*beta) := le_trans (by norm_num : (2:V)≤5) hG
  have hmul : 2*(q*q-1)≤(alpha+(q-F)*(J*beta))*(q*q-1) :=
    mul_le_mul_of_nonneg_right hG2 (Arithmetic.zero_le _)
  have hsq : q*q≤2*(q*q-1) := by nlinarith
  exact le_trans (le_trans hsq hmul) (le_add_of_nonneg_right (Arithmetic.zero_le _))

/-- At an 87 own-zero the direct power-recovery source yields X>q². -/
theorem X_gt_q_square (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hbeta46 : 46≤beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    FirstFields86Draft.q beta v*FirstFields86Draft.q beta v<v 6 := by
  let q := AuxGraphNormClientDraft.q beta v
  let R := naturalRank beta MC MF v
  have hgap : v 1+v 2<q := GuardGap87Draft.gap_of_87_zero p beta K v hport hK (hv 1) (hv 6) hz
  have hsq : q*q≤R := by
    simpa only [R,naturalRank,q,AuxGraphNormClientDraft.q] using
      scalar_rank_square q beta (v 0) (v 1) (v 2) MC MF (hv 0) (hv 1) (hv 2) rfl hgap
  have hX : v 6=Exp.exp R := by
    simpa only [R,MainBalance87Draft.X] using
      PowerRecovery87Draft.power p beta K MC MF v hbeta hbeta46 hport hK hMCcast hMFcast hMC hMF hv hz
  have hlt : q*q<Exp.exp R := lt_of_le_of_lt hsq (lt_exp R)
  simpa only [q,AuxGraphNormClientDraft.q,FirstFields86Draft.q,←hX] using hlt

end DiophantineConsistency.RankSquareGrowth87Draft

#print axioms DiophantineConsistency.RankSquareGrowth87Draft.X_gt_q_square
