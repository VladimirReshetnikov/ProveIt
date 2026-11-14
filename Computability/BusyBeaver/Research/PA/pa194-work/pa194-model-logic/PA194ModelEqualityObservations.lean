import PA194ModelSourceAtomCode

/-! Fixed-size target-calculus derivations exposing the observational content
of the internally translated source equality atom. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance equalityObservationsZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance equalityObservationsOne : One M := ⟨F oneCode Fin.elim0⟩
local instance equalityObservationsAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance equalityObservationsMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance equalityObservationsLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance equalityObservationsIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem iff_forward_target (a b : M) : TargetProvable (impValue (iffValue a b) (impValue a b)) := by
  let h : Ctx [iffValue a b] (conjValue (impValue a b) (impValue b a)) := .assumption (by simp [iffValue])
  exact h.andLeft.deduction.empty

theorem iff_reverse_target (a b : M) : TargetProvable (impValue (iffValue a b) (impValue b a)) := by
  let h : Ctx [iffValue a b] (conjValue (impValue a b) (impValue b a)) := .assumption (by simp [iffValue])
  exact h.andRight.deduction.empty

/-- The first half of translated equality supplies the universally quantified
forward neighborhood implication in the target numerical calculus. -/
theorem neighborhood_observe_right_forward (a b z : M) :
    TargetProvable (impValue (neighborhoodValue a b z)
      (allValue z (impValue (memValue a z) (memValue b z)))) := by
  let h : Ctx [neighborhoodValue a b z] (neighborhoodValue a b z) := .assumption (by simp)
  let q := h.andLeft.forallMP z (.closed (tp_gen z (iff_forward_target (memValue a z) (memValue b z))))
  exact q.deduction.empty

theorem neighborhood_observe_right_reverse (a b z : M) :
    TargetProvable (impValue (neighborhoodValue a b z)
      (allValue z (impValue (memValue b z) (memValue a z)))) := by
  let h : Ctx [neighborhoodValue a b z] (neighborhoodValue a b z) := .assumption (by simp)
  let q := h.andLeft.forallMP z (.closed (tp_gen z (iff_reverse_target (memValue a z) (memValue b z))))
  exact q.deduction.empty

theorem neighborhood_observe_left_forward (a b z : M) :
    TargetProvable (impValue (neighborhoodValue a b z)
      (allValue z (impValue (memValue z a) (memValue z b)))) := by
  let h : Ctx [neighborhoodValue a b z] (neighborhoodValue a b z) := .assumption (by simp)
  let q := h.andRight.forallMP z (.closed (tp_gen z (iff_forward_target (memValue z a) (memValue z b))))
  exact q.deduction.empty

theorem neighborhood_observe_left_reverse (a b z : M) :
    TargetProvable (impValue (neighborhoodValue a b z)
      (allValue z (impValue (memValue z b) (memValue z a)))) := by
  let h : Ctx [neighborhoodValue a b z] (neighborhoodValue a b z) := .assumption (by simp)
  let q := h.andRight.forallMP z (.closed (tp_gen z (iff_reverse_target (memValue z a) (memValue z b))))
  exact q.deduction.empty

/-- The source equality decoder produces a target formula proving this
observation for every internally valid arity-two source term vector. -/
theorem equalityAtom_valid_observe_right {v : M}
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) (bound free z : M) :
    ∃ a b, IsUTerm M6.PA.RelationalSource.language a ∧
      IsUTerm M6.PA.RelationalSource.language b ∧
      TargetProvable (impValue (F equalityAtomCode ![^rel (2 : M) (0 : M) v,bound,free,z])
        (allValue z (impValue (memValue (F termLabelCode ![a,bound,free]) z)
          (memValue (F termLabelCode ![b,bound,free]) z)))) := by
  obtain ⟨a,b,ha,hb,heq⟩ := equalityAtom_complete hv bound free z
  refine ⟨a,b,ha,hb,?_⟩
  rw [heq]
  exact neighborhood_observe_right_forward _ _ _

/-- All four observational directions are derivable for an internally valid
translated equality atom; the source terms and labels may be nonstandard. -/
theorem equalityAtom_valid_observe_all {v : M}
    (hv : IsUTermVec M6.PA.RelationalSource.language 2 v) (bound free z : M) :
    ∃ a b, IsUTerm M6.PA.RelationalSource.language a ∧
      IsUTerm M6.PA.RelationalSource.language b ∧
      let e := F equalityAtomCode ![^rel (2 : M) (0 : M) v,bound,free,z]
      let x := F termLabelCode ![a,bound,free]
      let y := F termLabelCode ![b,bound,free]
      TargetProvable (impValue e (allValue z (impValue (memValue x z) (memValue y z)))) ∧
      TargetProvable (impValue e (allValue z (impValue (memValue y z) (memValue x z)))) ∧
      TargetProvable (impValue e (allValue z (impValue (memValue z x) (memValue z y)))) ∧
      TargetProvable (impValue e (allValue z (impValue (memValue z y) (memValue z x)))) := by
  obtain ⟨a,b,ha,hb,heq⟩ := equalityAtom_complete hv bound free z
  refine ⟨a,b,ha,hb,?_⟩
  dsimp only
  rw [heq]
  exact ⟨neighborhood_observe_right_forward _ _ _,neighborhood_observe_right_reverse _ _ _,
    neighborhood_observe_left_forward _ _ _,neighborhood_observe_left_reverse _ _ _⟩

#print axioms equalityAtom_valid_observe_all
#print axioms iff_forward_target
#print axioms iff_reverse_target
#print axioms neighborhood_observe_right_forward
#print axioms neighborhood_observe_right_reverse
#print axioms neighborhood_observe_left_forward
#print axioms neighborhood_observe_left_reverse
#print axioms equalityAtom_valid_observe_right
end models
end PA194ModelLogic
