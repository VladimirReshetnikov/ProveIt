module
public import M6PA.Theory
public import M6PA.Calibration.ActualCertificateSeparationPointed
@[expose] public section

/-! Numeric nonextensional separation at an explicit formula-code witness.
Padding equivalence is paid by actual vacuity/forall-strip certificates.
The chosen output label is not yet relocated to a source allocator name. -/
namespace M6.PA.ActualCertificateEquivalence
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCheckerBlueprint
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def separationValue (a b c property : V) : V :=
  wex c (wal b (wa (wim (wel c b) (wa (wel a b) property))
    (wim (wa (wel a b) property) (wel c b))))

noncomputable def separationAtEquivalentCode (a b property c : V)
    (ha : c≠a) (hb : c≠b) (he : BiWitness (wa (wel a b) property) c) :
    Certificate (separationValue a b c property) := by
  let prop := wa (wel a b) property
  let mc := wel c b
  let clause := wa (wim (wel a b) (wim prop mc)) (wim mc prop)
  let first : Context [prop,clause] prop := .assumption (by simp)
  let hcl : Context [prop,clause] clause := .assumption (by simp)
  let forward : Context [clause] (wim prop mc) :=
    (Context.mp first (.mp first.andLeft hcl.andLeft)).deduction
  let reverse : Context [clause] (wim mc prop) :=
    (Context.assumption (by simp) : Context [clause] clause).andRight
  let pointwise : Certificate (wim clause (wa (wim mc prop) (wim prop mc))) :=
    (Context.andIntro reverse forward).deduction.empty
  let frame : Context [wa (wal b clause) (wim prop mc)]
      (wa (wal b clause) (wim prop mc)) := .assumption (by simp)
  let project : Certificate (wim (wa (wal b clause) (wim prop mc))
      (wal b (wa (wim mc prop) (wim prop mc)))) :=
    (frame.andLeft.forallMP b (.closed (.all b pointwise))).deduction.empty
  exact (pointedAtEquivalentCode a b prop c ha hb he).mp (existentialMonotonicity c project)

/-- The padding label may be any model value with the displayed actual
vacuity certificate. Its freshness is not inferred from host Named syntax. -/
noncomputable def paddedSeparation (a b property x : V)
    (ha : wal x (wa (wel a b) property)≠a)
    (hb : wal x (wa (wel a b) property)≠b)
    (hv : Certificate (wim (wa (wel a b) property) (wal x (wa (wel a b) property)))) :
    Certificate (separationValue a b (wal x (wa (wel a b) property)) property) :=
  separationAtEquivalentCode a b property _ ha hb ⟨hv,forallStrip x _ hv⟩

theorem padding_code_above (x property : V) : x<wal x property := by
  have hp := (SourceCantorInternal.pairValue_bounds x property).1
  have hm : SourceCantorInternal.pairValue x property≤4*SourceCantorInternal.pairValue x property := by
    exact le_mul_of_one_le_left (by simp) (by norm_num)
  have hh := lt_of_le_of_lt (le_trans hp hm)
    (show 4*SourceCantorInternal.pairValue x property<4*SourceCantorInternal.pairValue x property+2 by simp)
  simpa [wal,universalValue,ActualHeadGraphs.universalExpr,ActualHeadGraphs.al,
    ActualHeadGraphs.im,ActualArithmeticGraph.eval] using hh

noncomputable def paddedSeparationAbove (a b property x : V) (ha : a≤x) (hb : b≤x)
    (hv : Certificate (wim (wa (wel a b) property) (wal x (wa (wel a b) property)))) :
    Certificate (separationValue a b (wal x (wa (wel a b) property)) property) :=
  paddedSeparation a b property x
    (Ne.symm (ne_of_lt (lt_of_le_of_lt ha (padding_code_above x _))))
    (Ne.symm (ne_of_lt (lt_of_le_of_lt hb (padding_code_above x _)))) hv

#print axioms padding_code_above
#print axioms paddedSeparationAbove
#print axioms separationAtEquivalentCode
#print axioms paddedSeparation
end M6.PA.ActualCertificateEquivalence

