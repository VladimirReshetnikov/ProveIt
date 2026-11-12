import RankSquareGrowth87
import PositiveMap86To87

/-! Source-only 87 own-zero omega>F calibration. Uses no Mersenne or q|X
hypothesis; transitive model drafts are unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.OmegaGtF87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PositiveMap86To87Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed F<omega from the 87 own zero, with explicit model port, size
and mask assumptions. No sign assumption, Mersenne condition, or q|X. -/
theorem omega_gt_F (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hbeta46 : 46≤beta) (hport : (p 0 : DiffRing V)=ι beta)
    (hK : (p 1 : DiffRing V)=ι K) (hMCcast : (p 2 : DiffRing V)=ι MC)
    (hMFcast : (p 3 : DiffRing V)=ι MF) (hMC : MC<beta) (hMF : MF<2*beta)
    (hv : ∀ j, 0<v j) (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    v 1<v 13 := by
  let qq := q beta v
  let bb : V := v 0*beta
  let cc := C beta v
  have hb : 0<bb := by dsimp [bb]; exact mul_pos (hv 0) hbeta
  have hq : 0<qq := by dsimp [qq,q]; simp
  have hgap : v 1+v 2<qq := by
    simpa only [qq,q,AuxGraphNormClientDraft.q] using
      GuardGap87Draft.gap_of_87_zero p beta K v hport hK (hv 1) (hv 6) hz
  have hF : v 1<qq := lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le (v 2))) hgap
  have hFle : v 1≤qq := le_of_lt hF
  have he : qq-v 1+v 1=qq := tsub_add_cancel_of_le hFle
  have ha : v 2<qq-v 1 := by
    apply (add_lt_add_iff_right (v 1)).mp
    rw [he]
    simpa only [add_comm] using hgap
  have hC : 0<cc := by dsimp [cc,C,qq]; exact tsub_pos_of_lt ha
  have hC1 : 1≤cc := pos_iff_one_le.mp hC
  have hX : qq*qq<v 6 := by
    simpa only [qq,q,FirstFields86Draft.q] using
      RankSquareGrowth87Draft.X_gt_q_square p beta K MC MF v hbeta hbeta46 hport hK hMCcast hMFcast hMC hMF hv hz
  have hqF : qq*(v 1)<qq*qq := mul_lt_mul_of_pos_left hF hq
  have hbound : qq*(v 1)<cc*(v 6+K*qq) :=
    lt_of_lt_of_le (lt_trans hqF hX)
      (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le (K*qq)))
        (le_mul_of_one_le_left (Arithmetic.zero_le _) hC1))
  have hCcast : ι cc=ι qq-ι (v 1)-ι (v 2) := cast_C beta v hgap
  have hg := GuardGap87Draft.guard_of_zero p v hz
  rw [GuardGap87Draft.guard_eval p beta K v hport hK] at hg
  have hnat : bb*v 13+v 1=cc*(v 6+K*qq) := by
    apply ι_injective
    simp only [map_add,map_mul]
    rw [hCcast]
    change (ι bb*ι (v 13)+ι (v 1))=(ι qq-ι (v 1)-ι (v 2))*(ι (v 6)+ι K*ι qq)
    change (ι qq-ι (v 1)-ι (v 2))*(ι (v 6)+ι K*ι qq)-ι (v 1)-ι bb*ι (v 13)=0 at hg
    nlinarith
  have hmul : bb*(v 1)<bb*(v 13) := by
    apply (add_lt_add_iff_right (v 1)).mp
    calc
      bb*(v 1)+v 1=qq*(v 1) := by dsimp [qq,q,bb]; ring
      _<cc*(v 6+K*qq) := hbound
      _=bb*(v 13)+v 1 := hnat.symm
  exact (mul_lt_mul_left hb).mp hmul

end DiophantineConsistency.OmegaGtF87Draft

#print axioms DiophantineConsistency.OmegaGtF87Draft.omega_gt_F
