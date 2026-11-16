import PA194ModelContext

/-! Uniform fixed-size numerical-calculus derivations for neighborhood equality.
The labels may be nonstandard. These results do not internalize induction on proofs. -/
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
local instance : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨F oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def iffValue (a b : M) := conjValue (impValue a b) (impValue b a)
noncomputable def neighborhoodValue (a b z : M) :=
  conjValue (allValue z (iffValue (memValue a z) (memValue b z)))
    (allValue z (iffValue (memValue z a) (memValue z b)))

theorem iff_refl (a : M) : TargetProvable (iffValue a a) :=
  (Ctx.andIntro (.closed (imp_refl a)) (.closed (imp_refl a))).empty

theorem iff_symm (a b : M) : TargetProvable (impValue (iffValue a b) (iffValue b a)) := by
  let h : Ctx [iffValue a b] (conjValue (impValue a b) (impValue b a)) := .assumption (by simp [iffValue])
  exact (Ctx.andIntro h.andRight h.andLeft).deduction.empty

theorem iff_trans (a b c : M) :
    TargetProvable (impValue (iffValue a b) (impValue (iffValue b c) (iffValue a c))) := by
  let p : Ctx [iffValue b c,iffValue a b] (conjValue (impValue a b) (impValue b a)) :=
    .assumption (by simp [iffValue])
  let q : Ctx [iffValue b c,iffValue a b] (conjValue (impValue b c) (impValue c b)) :=
    .assumption (by simp [iffValue])
  exact (Ctx.andIntro (p.andLeft.arrowCompose q.andLeft)
    (q.andRight.arrowCompose p.andRight)).deduction.deduction.empty

theorem neighborhood_refl (a z : M) : TargetProvable (neighborhoodValue a a z) :=
  (Ctx.andIntro (.closed (tp_gen z (iff_refl (memValue a z))))
    (.closed (tp_gen z (iff_refl (memValue z a))))).empty

theorem neighborhood_symm (a b z : M) :
    TargetProvable (impValue (neighborhoodValue a b z) (neighborhoodValue b a z)) := by
  let h : Ctx [neighborhoodValue a b z] (neighborhoodValue a b z) := .assumption (by simp)
  let l := h.andLeft.forallMP z (.closed (tp_gen z (iff_symm (memValue a z) (memValue b z))))
  let r := h.andRight.forallMP z (.closed (tp_gen z (iff_symm (memValue z a) (memValue z b))))
  exact (Ctx.andIntro l r).deduction.empty

theorem neighborhood_trans (a b c z : M) :
    TargetProvable (impValue (neighborhoodValue a b z)
      (impValue (neighborhoodValue b c z) (neighborhoodValue a c z))) := by
  let p : Ctx [neighborhoodValue b c z,neighborhoodValue a b z]
      (neighborhoodValue a b z) := .assumption (by simp)
  let q : Ctx [neighborhoodValue b c z,neighborhoodValue a b z]
      (neighborhoodValue b c z) := .assumption (by simp)
  let l := q.andLeft.forallMP z (p.andLeft.forallMP z
    (.closed (tp_gen z (iff_trans (memValue a z) (memValue b z) (memValue c z)))))
  let r := q.andRight.forallMP z (p.andRight.forallMP z
    (.closed (tp_gen z (iff_trans (memValue z a) (memValue z b) (memValue z c)))))
  exact (Ctx.andIntro l r).deduction.deduction.empty

/-- The universally closed reflexivity supplier at the given labels. -/
theorem equality_reflexivity_supplier (lo z : M) :
    TargetProvable (allValue lo (neighborhoodValue lo lo z)) :=
  tp_gen lo (neighborhood_refl lo z)

/-- The universally closed symmetry supplier, using the source disjunction encoding. -/
theorem equality_symmetry_supplier (lo z : M) :
    let a := neighborhoodValue lo (lo+1) z
    let b := neighborhoodValue (lo+1) lo z
    TargetProvable (allValue lo (allValue (lo+1)
      (impValue (negValue (negValue a)) b))) := by
  dsimp only
  exact tp_gen lo (tp_gen (lo+1)
    (imp_trans (doubleNegationElimination _) (neighborhood_symm lo (lo+1) z)))

/-- The universally closed transitivity supplier, with source disjunctions encoded by implication. -/
theorem equality_transitivity_supplier (lo z : M) :
    let a := neighborhoodValue lo (lo+1) z
    let b := neighborhoodValue (lo+1) ((lo+1)+1) z
    let c := neighborhoodValue lo ((lo+1)+1) z
    TargetProvable (allValue lo (allValue (lo+1) (allValue ((lo+1)+1)
      (impValue (negValue (negValue a)) (impValue (negValue (negValue b)) c))))) := by
  dsimp only
  let a := neighborhoodValue lo (lo+1) z
  let b := neighborhoodValue (lo+1) ((lo+1)+1) z
  let c := neighborhoodValue lo ((lo+1)+1) z
  let ha : Ctx [negValue (negValue b),negValue (negValue a)] (negValue (negValue a)) := .assumption (by simp)
  let hb : Ctx [negValue (negValue b),negValue (negValue a)] (negValue (negValue b)) := .assumption (by simp)
  have h : TargetProvable (impValue (negValue (negValue a)) (impValue (negValue (negValue b)) c)) :=
    (Ctx.mp hb.dne (.mp ha.dne (.closed (neighborhood_trans lo (lo+1) ((lo+1)+1) z)))).deduction.deduction.empty
  exact tp_gen lo (tp_gen (lo+1) (tp_gen ((lo+1)+1) h))

#print axioms equality_reflexivity_supplier
#print axioms equality_symmetry_supplier
#print axioms equality_transitivity_supplier
#print axioms iff_refl
#print axioms iff_symm
#print axioms iff_trans
#print axioms neighborhood_refl
#print axioms neighborhood_symm
#print axioms neighborhood_trans
end models
end PA194ModelLogic
