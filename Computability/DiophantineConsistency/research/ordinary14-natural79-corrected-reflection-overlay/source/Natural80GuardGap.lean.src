import Natural80OwnZeroNorm
import OwnZeroGuardStrict74

/-! Source-only guard-gap proposal from an 80 own zero. All graph/model
dependencies and tactics remain unelaborated. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace DiophantineConsistency.Natural80GuardGapDraft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ModelDifferenceRing
open FirstFactor74Draft OwnZeroUnits74Draft OwnZeroGuardStrict74Draft
open Natural80Partial74Draft Natural80JPosDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Proposed `F+alpha<q` with represented positive beta and K0. The proof
uses no positivity hypothesis on gamma, f, r or y. -/
theorem gap_of_80_zero (p : Fin 4 → ℤ) (beta K : V) (v : Fin 14 → V)
    (hbeta : (p 0 : DiffRing V)=ι beta) (hK : (p 1 : DiffRing V)=ι K)
    (hb : 0<beta) (hKpos : 0<K)
    (hz : InternalZero (P80NaturalForcedGamma.graph p).output v) :
    let u := partial74 v
    u 1+u 2 < q beta u := by
  let u := partial74 v
  have hJ0 := Natural80JPosDraft.J_pos_of_zero p K v hK hKpos hz
  have hJ : 0<u 0 := by simpa [u,partial74] using hJ0
  have hF : 0<u 1 := by simp [u,partial74]
  have hw : 0<u 6 := by simp [u,partial74]
  have hs : 0<u 7 := by simp [u,partial74]
  have hh : 0<u 13 := by simp [u,partial74]
  have hz74 : InternalZero (P74PositiveGuard.graph p).output u :=
    (internalZero_iff_partial p v).mp hz
  have hg := guard_factor_one p beta u hbeta hb hJ hw hs hz74
  rw [guard_eval p beta K u hbeta hK] at hg
  have hf1 : (1:DiffRing V)≤ι (u 1) := by
    rw [←map_one ι]
    exact ι_le_ι.mpr (pos_iff_one_le.mp hF)
  have hh1 : (1:DiffRing V)≤ι (u 13) := by
    rw [←map_one ι]
    exact ι_le_ι.mpr (pos_iff_one_le.mp hh)
  have hqcast : ι (q beta u)=(1:DiffRing V)+ι (u 0*beta) := by
    simp [q,map_add,map_one]
  have hbh : ι (u 0*beta)≤ι (u 0*beta)*ι (u 13) := by
    have h := mul_nonneg (ι_nonneg (u 0*beta)) (sub_nonneg.mpr hh1)
    nlinarith
  have hc : (0:DiffRing V)<ι (q beta u)-ι (u 1)-ι (u 2) := by
    by_contra hn
    have hc0 : ι (q beta u)-ι (u 1)-ι (u 2)≤0 := le_of_not_gt hn
    have hmul := mul_nonpos_of_nonpos_of_nonneg hc0
      (add_nonneg (ι_nonneg (X beta u)) (ι_nonneg K))
    rw [hqcast] at hg
    linarith
  have hsum : ι (u 1+u 2)<ι (q beta u) := by
    rw [map_add]
    linarith
  exact ι_lt_ι.mp hsum

end DiophantineConsistency.Natural80GuardGapDraft

#print axioms DiophantineConsistency.Natural80GuardGapDraft.gap_of_80_zero
