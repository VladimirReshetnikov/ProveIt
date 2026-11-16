import PA194SourceMulCoherence
import PA194SourceAddComm
set_option autoImplicit false
set_option maxHeartbeats 400000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
/-!
# The four fixed source proofs from the ten

For the adjunctive source theory with full separation, in a model `V` of `IΣ₁`:
`calibration_of_ten` derives internal proofs of coherence of addition and multiplication
(`sA2`, `sM2`) and of the two successor facts (`sA3`, `sM3`) from `TenFacts`, the ten
members of `SourceFacts` other than `sA2` and `sM2`. `sourceFacts_of_ten` assembles
`SourceFacts` from `TenFacts`, `sA2` and `sM2` for an arbitrary theory.
-/
namespace PA194SourceModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194ModelLogic PA194BindSource PA194Schematic PA194GuardedCompiler

section generic
variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem sourceFacts_of_ten {T : Theory SourceL} [T.Δ₁] (K : TenFacts (V := V) T)
    (a2 : T.internalize V ⊢ (tHyp sA2 : Bootstrapping.Semiformula V SourceL 0))
    (m2 : T.internalize V ⊢ (tHyp sM2 : Bootstrapping.Semiformula V SourceL 0)) :
    SourceFacts (V := V) T where
  e1 := K.e1
  ei := K.ei
  is := K.is
  it := K.it
  z1 := K.z1
  z2 := K.z2
  s1 := K.s1
  s2 := K.s2
  a1 := K.a1
  a2 := a2
  m1 := K.m1
  m2 := m2

attribute [local instance] adjunctiveFullSepTheoryDelta

/-- All twelve source facts for the adjunctive source theory with full separation. -/
theorem sourceFacts_full (K : TenFacts (V := V) adjunctiveFullSepTheory) :
    SourceFacts (V := V) adjunctiveFullSepTheory :=
  sourceFacts_of_ten K (a2_supply K) (m2_supply K (a2_supply K))

/-- Coherence of addition and multiplication and the two successor facts. -/
theorem calibration_of_ten (K : TenFacts (V := V) adjunctiveFullSepTheory) :
    (adjunctiveFullSepTheory.internalize V ⊢ (tHyp sA2 : Bootstrapping.Semiformula V SourceL 0)) ∧
    (adjunctiveFullSepTheory.internalize V ⊢ (tHyp sM2 : Bootstrapping.Semiformula V SourceL 0)) ∧
    (adjunctiveFullSepTheory.internalize V ⊢ (tHyp sA3 : Bootstrapping.Semiformula V SourceL 0)) ∧
    (adjunctiveFullSepTheory.internalize V ⊢ (tHyp sM3 : Bootstrapping.Semiformula V SourceL 0)) :=
  ⟨a2_supply K, m2_supply K (a2_supply K),
    a3_of_predecessor (sourceFacts_full K) sAP_supply,
    m3_of_predecessor (sourceFacts_full K) sMP_supply (ac_supply K)⟩

#print axioms sourceFacts_of_ten
#print axioms sourceFacts_full
#print axioms calibration_of_ten
end generic
end PA194SourceModel
