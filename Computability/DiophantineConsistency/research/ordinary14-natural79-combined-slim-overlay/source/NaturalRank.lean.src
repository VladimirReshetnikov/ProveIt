import GuardGap

/-! Source-only natural rank representation. Port casts and the required
natural subtraction bounds are explicit; no rank window is asserted. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.NaturalRank84Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing GuardGap84Draft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def naturalRank (beta MC MF : V) (v : Fin 14 → V) : V :=
  let q := AuxGraphNormClientDraft.q beta v
  (v 2+(q-v 1)*(v 0*beta))*(q*q-1)+v 0*(MC+MF*q)

/-- Natural rank cast under both subtraction bounds and explicit mask casts. -/
theorem rank_repr (p : Fin 4 → ℤ) (beta MC MF : V) (v : Fin 14 → V)
    (hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)
    (hF : v 1≤AuxGraphNormClientDraft.q beta v)
    (hq2 : 1≤AuxGraphNormClientDraft.q beta v*AuxGraphNormClientDraft.q beta v) :
    AuxGraphNormClientDraft.rank p beta v=ι (naturalRank beta MC MF v) := by
  have hsub := P72Root.ι_tsub hF
  have hsq := P72Root.ι_tsub hq2
  simp only [AuxGraphNormClientDraft.rank,naturalRank,map_add,map_mul,map_one,
    hsub,hsq,hMC,hMF]

/-- An own-zero 84 guard supplies the F-bound; q≥1 supplies the square bound.
All four port representations used here are explicit. -/
theorem rank_of_84_zero (p : Fin 4 → ℤ) (beta K MC MF : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hMC : (p 2 : DiffRing V)=ι MC) (hMF : (p 3 : DiffRing V)=ι MF)
    (hFpos : 0<v 1) (hw : 0<v 6)
    (hz : InternalZero (P84QcubeGraph.graph p).output v) :
    AuxGraphNormClientDraft.rank p beta v=ι (naturalRank beta MC MF v) := by
  let q := AuxGraphNormClientDraft.q beta v
  have hgap : v 1+v 2<q := gap_of_84_zero p beta K v hbeta hK hFpos hw hz
  have hF : v 1≤q := le_of_lt (lt_of_le_of_lt (le_add_of_nonneg_right (Arithmetic.zero_le (v 2))) hgap)
  have hq0 : 0<q := by dsimp [q,AuxGraphNormClientDraft.q]; simp
  have hq : 1≤q := pos_iff_one_le.mp hq0
  have hq2 : 1≤q*q := le_trans hq (le_mul_of_one_le_right (Arithmetic.zero_le q) hq)
  exact rank_repr p beta MC MF v hMC hMF hF hq2

end DiophantineConsistency.NaturalRank84Draft

#print axioms DiophantineConsistency.NaturalRank84Draft.rank_of_84_zero
