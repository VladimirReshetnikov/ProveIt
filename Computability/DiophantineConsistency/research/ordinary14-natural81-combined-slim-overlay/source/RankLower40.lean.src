import NaturalRank

/-! Source-only elementary lower bound for the 84 natural rank. It assumes
no mask upper bounds; all graph imports remain unelaborated drafts. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.RankLower4084Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing GuardGap84Draft NaturalRank84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A positive scalar gap forces rank at least 40; mask values need only be
natural. This is a fact-level inequality, not a graph or endpoint statement. -/
theorem scalar_lower40 (q beta J F alpha MC MF : V)
    (hbeta : 0<beta) (hJ : 0<J) (hF : 0<F) (ha : 0<alpha)
    (hq : q=1+J*beta) (hgap : F+alpha<q) :
    40≤(alpha+(q-F)*(J*beta))*(q*q-1)+J*(MC+MF*q) := by
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
  have hsq : 8≤q*q-1 := by nlinarith
  have hR : 40≤(alpha+(q-F)*(J*beta))*(q*q-1) := by
    have h := mul_le_mul hG hsq (by norm_num : (0:V)≤8)
      (Arithmetic.zero_le (alpha+(q-F)*(J*beta)))
    norm_num at h ⊢
    exact h
  exact le_trans hR (le_add_of_nonneg_right (Arithmetic.zero_le (J*(MC+MF*q))))

/-- Apply the lower bound to the 84 graph's own zero via its guard gap. -/
theorem rank_lower40 (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    40≤naturalRank beta MC MF v := by
  let q := AuxGraphNormClientDraft.q beta v
  have hgap : v 1+v 2<q := gap_of_84_zero p beta K v hport hK (hv 1) (hv 6) hz
  have hq : q=1+v 0*beta := rfl
  simpa only [naturalRank,q,AuxGraphNormClientDraft.q] using
    scalar_lower40 q beta (v 0) (v 1) (v 2) MC MF hbeta (hv 0) (hv 1) (hv 2) hq hgap

end DiophantineConsistency.RankLower4084Draft

#print axioms DiophantineConsistency.RankLower4084Draft.rank_lower40
