module
public import M6PA.Theory
public import M6PA.Calibration.FoundationRelationalSequentConditional
public import M6PA.Calibration.ActualCertificateNeighborhoodCongruence
@[expose] public section

/-! Finite conditional native atom-renaming certificates, over arbitrary PA
models, using the exact neighborhood replacement and guarded membership rules. -/
namespace M6.PA.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open ActualCertificateConstructors ActualCertificateConstructors.Dominated
open ActualCertificateEquivalence ActualCheckerBlueprint

universe u
variable {V : Type u} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable abbrev neighborhoodValue (a b z : V) : V := ActualArithmeticGraph.eval neighborhoodExpr a b z 0

noncomputable def contextRelSymm {Γ : List V} {a b z : V}
    (p : Context Γ (neighborhoodValue a b z)) : Context Γ (neighborhoodValue b a z) :=
  .mp p (.closed (neighborhoodSymmetry a b z))

noncomputable def contextRelTrans {Γ : List V} {a b c z : V}
    (p : Context Γ (neighborhoodValue a b z)) (q : Context Γ (neighborhoodValue b c z)) :
    Context Γ (neighborhoodValue a c z) :=
  .mp q (.mp p (.closed (neighborhoodTransitivity a b c z)))

noncomputable def contextRelCongruence {Γ : List V} {a b c d z : V}
    (p : Context Γ (neighborhoodValue a c z)) (q : Context Γ (neighborhoodValue b d z))
    (h : Context Γ (neighborhoodValue a b z)) : Context Γ (neighborhoodValue c d z) :=
  contextRelTrans (contextRelTrans (contextRelSymm p) h) q

noncomputable def contextMembershipCongruence {Γ : List V} {a b c d z : V}
    (ha : z≠a) (hb : z≠b) (hc : z≠c) (hd : z≠d)
    (p : Context Γ (neighborhoodValue a c z)) (q : Context Γ (neighborhoodValue b d z))
    (h : Context Γ (wel a b)) : Context Γ (wel c d) :=
  .mp (.mp h (.mp p (.closed (neighborhoodRightCongruence a c z b ha hc hb))))
    (.mp q (.closed (neighborhoodLeftCongruence b d z c hb hd hc)))

noncomputable def contextRenameRel {Γ : List V} (x y a z : V)
    (h : Context Γ (neighborhoodValue x y z)) :
    Context Γ (neighborhoodValue a (renameLabelValue x y a) z) := by
  classical
  by_cases ha : a=x
  · subst a
    simpa only [renameLabel_self] using h
  · simpa only [renameLabel_other ha] using
      (Context.closed (Γ:=Γ) (neighborhoodReflexivity a z))

noncomputable def renameMembership (z x y a b : V)
    (hza : z≠a) (hzb : z≠b) (hzy : z≠y) :
    ConditionalBiWitness (neighborhoodValue x y z) (wel a b)
      (wel (renameLabelValue x y a) (renameLabelValue x y b)) := by
  have ha' := renameLabel_reserved (x:=x) hza hzy
  have hb' := renameLabel_reserved (x:=x) hzb hzy
  constructor
  · let he : Context [wel a b,neighborhoodValue x y z] (neighborhoodValue x y z) := .assumption (by simp)
    let hm : Context [wel a b,neighborhoodValue x y z] (wel a b) := .assumption (by simp)
    exact (contextMembershipCongruence hza hzb ha' hb' (contextRenameRel x y a z he)
      (contextRenameRel x y b z he) hm).deduction.deduction.empty
  · let m := wel (renameLabelValue x y a) (renameLabelValue x y b)
    let he : Context [m,neighborhoodValue x y z] (neighborhoodValue x y z) := .assumption (by simp)
    let hm : Context [m,neighborhoodValue x y z] m := .assumption (by simp)
    exact (contextMembershipCongruence ha' hb' hza hzb (contextRelSymm (contextRenameRel x y a z he))
      (contextRelSymm (contextRenameRel x y b z he)) hm).deduction.deduction.empty

noncomputable def renameNeighborhood (z x y a b : V) :
    ConditionalBiWitness (neighborhoodValue x y z) (neighborhoodValue a b z)
      (neighborhoodValue (renameLabelValue x y a) (renameLabelValue x y b) z) := by
  constructor
  · let he : Context [neighborhoodValue a b z,neighborhoodValue x y z]
      (neighborhoodValue x y z) := .assumption (by simp)
    let hm : Context [neighborhoodValue a b z,neighborhoodValue x y z]
      (neighborhoodValue a b z) := .assumption (by simp)
    exact (contextRelCongruence (contextRenameRel x y a z he)
      (contextRenameRel x y b z he) hm).deduction.deduction.empty
  · let m := neighborhoodValue (renameLabelValue x y a) (renameLabelValue x y b) z
    let he : Context [m,neighborhoodValue x y z] (neighborhoodValue x y z) := .assumption (by simp)
    let hm : Context [m,neighborhoodValue x y z] m := .assumption (by simp)
    exact (contextRelCongruence (contextRelSymm (contextRenameRel x y a z he))
      (contextRelSymm (contextRenameRel x y b z he)) hm).deduction.deduction.empty

#print axioms contextRelSymm
#print axioms contextRelTrans
#print axioms contextRelCongruence
#print axioms contextMembershipCongruence
#print axioms contextRenameRel
#print axioms renameMembership
#print axioms renameNeighborhood
end M6.PA.RelationalSource.Numeric
