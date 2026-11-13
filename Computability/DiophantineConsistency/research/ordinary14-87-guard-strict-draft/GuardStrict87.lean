import GuardGap87
import PositiveMap86To87

/-! Source-only strict 87 guard bound conditional on X≥q². The growth
premise is not inferred from the graph zero here. No Lean result. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.GuardStrict87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing PositiveMap86To87Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Under an explicit X≥q² bound, a positive 87 own-zero has C*K<omega.
All involved subtractions in C are justified using the own-zero guard gap. -/
theorem strict_of_large_X (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hbeta : 0<beta) (hport : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hv : ∀ j, 0<v j) (hX : q beta v*q beta v≤v 6)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    C beta v*K<v 13 := by
  let qq := q beta v
  let bb : V := v 0*beta
  let cc := C beta v
  have hb : 0<bb := by dsimp [bb]; exact mul_pos (hv 0) hbeta
  have hq0 : 0<qq := by dsimp [qq,q]; simp
  have hq1 : 1≤qq := pos_iff_one_le.mp hq0
  have hgap : v 1+v 2<qq := by
    simpa only [qq,q,AuxGraphNormClientDraft.q] using
      GuardGap87Draft.gap_of_87_zero p beta K v hport hK (hv 1) (hv 6) hz
  have hF : v 1<qq := lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le (v 2))) hgap
  have hFle : v 1≤qq := le_of_lt hF
  have he : qq-v 1+v 1=qq := tsub_add_cancel_of_le hFle
  have halpha : v 2<qq-v 1 := by
    apply (add_lt_add_iff_right (v 1)).mp
    rw [he]
    simpa only [add_comm] using hgap
  have hC : 0<cc := by dsimp [cc,C,qq]; exact tsub_pos_of_lt halpha
  have hC1 : 1≤cc := pos_iff_one_le.mp hC
  have hqq : qq≤qq*qq := le_mul_of_one_le_right (Arithmetic.zero_le qq) hq1
  have hFX : v 1<v 6 := lt_of_lt_of_le hF (le_trans hqq hX)
  have hbound : v 1<cc*(v 6+K) := lt_of_lt_of_le hFX
    (le_trans (le_add_of_nonneg_right (Arithmetic.zero_le K))
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
  have hless : bb*(cc*K)+v 1<bb*v 13+v 1 := calc
    _<bb*(cc*K)+cc*(v 6+K) := add_lt_add_left hbound _
    _=cc*(v 6+K*qq) := by dsimp [qq,q,bb]; ring
    _=bb*v 13+v 1 := hnat.symm
  have hmul : bb*(cc*K)<bb*v 13 := (add_lt_add_iff_right (v 1)).mp hless
  exact (mul_lt_mul_left hb).mp hmul

end DiophantineConsistency.GuardStrict87Draft

#print axioms DiophantineConsistency.GuardStrict87Draft.strict_of_large_X
