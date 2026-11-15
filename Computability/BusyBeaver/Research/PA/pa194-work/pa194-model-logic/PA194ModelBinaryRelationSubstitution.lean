import PA194ModelNeighborhoodSpecialization

/-! Target-calculus relation congruence for two translated equality atoms. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance binarySubstitutionZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance binarySubstitutionOne : One M := ⟨F oneCode Fin.elim0⟩
local instance binarySubstitutionAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance binarySubstitutionMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance binarySubstitutionLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance binarySubstitutionIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Simultaneous rewriting in both membership arguments. -/
theorem neighborhoodBothCongruence_target (a b c d z : M)
    (ha : z ≠ a) (hb : z ≠ b) (hc : z ≠ c) (hd : z ≠ d) :
    TargetProvable (impValue (neighborhoodValue a b z)
      (impValue (neighborhoodValue c d z) (impValue (memValue c a) (memValue d b)))) := by
  let he : Ctx [memValue c a,neighborhoodValue c d z,neighborhoodValue a b z]
      (neighborhoodValue a b z) := .assumption (by simp)
  let hf : Ctx [memValue c a,neighborhoodValue c d z,neighborhoodValue a b z]
      (neighborhoodValue c d z) := .assumption (by simp)
  let hm : Ctx [memValue c a,neighborhoodValue c d z,neighborhoodValue a b z]
      (memValue c a) := .assumption (by simp)
  let hmid := Ctx.mp hm (.mp he (.closed (neighborhoodLeftCongruence_target a b z c ha hb hc)))
  exact (Ctx.mp hmid (.mp hf (.closed
    (neighborhoodRightCongruence_target c d z b hc hd hb)))).deduction.deduction.deduction.empty

/-- Source equality and membership atom decoders satisfy the simultaneous
binary relation congruence pattern, under decoded-label freshness. -/
theorem sourceAtom_binaryRelationSubstitution (a b c d bound free z : M)
    (ha : z ≠ F termLabelCode ![a,bound,free])
    (hb : z ≠ F termLabelCode ![b,bound,free])
    (hc : z ≠ F termLabelCode ![c,bound,free])
    (hd : z ≠ F termLabelCode ![d,bound,free]) :
    TargetProvable (impValue
      (F equalityAtomCode ![^rel (2 : M) (0 : M) (pair a (pair b 0+1)+1),bound,free,z])
      (impValue
        (F equalityAtomCode ![^rel (2 : M) (0 : M) (pair c (pair d 0+1)+1),bound,free,z])
        (impValue
          (F membershipAtomCode ![^rel (2 : M) (1 : M) (pair a (pair c 0+1)+1),bound,free,z])
          (F membershipAtomCode ![^rel (2 : M) (1 : M) (pair b (pair d 0+1)+1),bound,free,z])))) := by
  rw [equalityAtom_model,equalityAtom_model,membershipAtom_model,membershipAtom_model]
  exact neighborhoodBothCongruence_target _ _ _ _ z ha hb hc hd

/-- Explicit universal closure of the direct implication form. -/
theorem binaryRelationSubstitution_supplier (a b c d z : M)
    (ha : z ≠ a) (hb : z ≠ b) (hc : z ≠ c) (hd : z ≠ d) :
    TargetProvable (allValue a (allValue b (allValue c (allValue d
      (impValue (neighborhoodValue a b z)
        (impValue (neighborhoodValue c d z) (impValue (memValue c a) (memValue d b)))))))) :=
  tp_gen a (tp_gen b (tp_gen c (tp_gen d (neighborhoodBothCongruence_target a b c d z ha hb hc hd))))

/-- The exact negation-normal propositional shape produced by Foundation's
binary relation-extensionality axiom, before its four universal binders. -/
theorem relExtNNFBody_target (a b c d z : M)
    (ha : z ≠ a) (hb : z ≠ b) (hc : z ≠ c) (hd : z ≠ d) :
    let e₁ := neighborhoodValue a b z
    let e₂ := neighborhoodValue c d z
    let old := memValue c a
    let new := memValue d b
    let antecedent := negValue (impValue (negValue (negValue e₁))
      (impValue (negValue (negValue e₂)) (memValue 0 0)))
    TargetProvable (impValue antecedent (impValue (negValue (negValue old)) new)) := by
  dsimp only
  let e₁ := neighborhoodValue a b z
  let e₂ := neighborhoodValue c d z
  let old := memValue c a
  let new := memValue d b
  let S := negValue (impValue (negValue (negValue e₁))
    (impValue (negValue (negValue e₂)) (memValue 0 0)))
  let T := negValue (negValue old)
  let hs : Ctx [T,S] S := .assumption (by simp)
  let ht : Ctx [T,S] T := .assumption (by simp)
  let he₁ : Ctx [T,S] e₁ := hs.negImpLeft.dne
  let he₂ : Ctx [T,S] e₂ := hs.negImpRight.negImpLeft.dne
  let hold : Ctx [T,S] old := ht.dne
  let hnew : Ctx [T,S] new :=
    .mp hold (.mp he₂ (.mp he₁ (.closed (neighborhoodBothCongruence_target a b c d z ha hb hc hd))))
  exact hnew.deduction.deduction.empty

/-- Four-universal closure at consecutive allocation labels; the freshness
hypotheses are stated individually and no proof-valued assumptions remain. -/
theorem relExtNNF_supplier (lo z : M)
    (h0 : z ≠ lo) (h1 : z ≠ lo+1) (h2 : z ≠ (lo+1)+1) (h3 : z ≠ ((lo+1)+1)+1) :
    let x₀ := lo
    let x₁ := lo+1
    let x₂ := (lo+1)+1
    let x₃ := ((lo+1)+1)+1
    let e₁ := neighborhoodValue x₃ x₁ z
    let e₂ := neighborhoodValue x₂ x₀ z
    let old := memValue x₂ x₃
    let new := memValue x₀ x₁
    let antecedent := negValue (impValue (negValue (negValue e₁))
      (impValue (negValue (negValue e₂)) (memValue 0 0)))
    TargetProvable (allValue x₀ (allValue x₁ (allValue x₂ (allValue x₃
      (impValue antecedent (impValue (negValue (negValue old)) new)))))) := by
  dsimp only
  exact tp_gen lo (tp_gen (lo+1) (tp_gen ((lo+1)+1) (tp_gen (((lo+1)+1)+1)
    (relExtNNFBody_target (((lo+1)+1)+1) (lo+1) ((lo+1)+1) lo z h3 h1 h2 h0))))

#print axioms relExtNNFBody_target
#print axioms relExtNNF_supplier
#print axioms neighborhoodBothCongruence_target
#print axioms sourceAtom_binaryRelationSubstitution
#print axioms binaryRelationSubstitution_supplier
end models
end PA194ModelLogic
