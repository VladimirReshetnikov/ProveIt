import GuardGap87
import NaturalRank

/-! Source-only natural rank from the 87 own-zero gap. The rank fields are
shared, but no 85/86 graph zero is assumed. No Lean elaboration is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.NaturalRank87Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The 87 own-zero scalar gap makes the existing natural rank cast valid. -/
theorem rank_of_87_zero (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)
    (hFpos : 0<v 1) (hX : 0<v 6)
    (hz : InternalZero (P87ShiftedGuard.graph p).output v) :
    AuxGraphNormClientDraft.rank p beta v=ι (NaturalRank84Draft.naturalRank beta MC MF v) := by
  let q := AuxGraphNormClientDraft.q beta v
  have hgap : v 1+v 2<q := GuardGap87Draft.gap_of_87_zero p beta K v hbeta hK hFpos hX hz
  have hF : v 1≤q := le_of_lt (lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le (v 2))) hgap)
  have hq0 : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hq : 1≤q := pos_iff_one_le.mp hq0
  have hq2 : 1≤q*q := le_trans hq (le_mul_of_one_le_right (Arithmetic.zero_le q) hq)
  exact NaturalRank84Draft.rank_repr p beta MC MF v hMC hMF hF hq2

end DiophantineConsistency.NaturalRank87Draft

#print axioms DiophantineConsistency.NaturalRank87Draft.rank_of_87_zero
