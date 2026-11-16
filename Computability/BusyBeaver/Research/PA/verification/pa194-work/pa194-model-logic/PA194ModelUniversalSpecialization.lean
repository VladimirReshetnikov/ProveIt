import PA194ModelEqualityObservations

/-! Guarded membership vacuity and conditional universal specialization in the
actual target numerical calculus, uniformly in nonstandard model parameters. -/
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
local instance universalSpecializationZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance universalSpecializationOne : One M := ⟨F oneCode Fin.elim0⟩
local instance universalSpecializationAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance universalSpecializationMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance universalSpecializationLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance universalSpecializationIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Extract the membership-vacuity component of the actual guarded seed. -/
theorem membershipVacuity_target (a b c : M) (hca : c ≠ a) (hcb : c ≠ b) :
    TargetProvable (impValue (memValue a b) (allValue c (memValue a b))) := by
  have h := gate_provable a b c hca hcb
  change TargetProvable (negValue (impValue (memVacValue a b c) (separationTailValue a b c))) at h
  change TargetProvable (memVacValue a b c)
  exact negImpLeft h

/-- Universal specialization with mirrored primitive equality. The exact two
provability premises are explicit; no general substitution theorem is assumed. -/
theorem specializeWithMirroredEquality_target (z c atom target : M)
    (hv : TargetProvable (impValue target (allValue z target)))
    (hr : TargetProvable (impValue (eqValue c z) (impValue atom target))) :
    TargetProvable (impValue (allValue z atom) target) := by
  have hs : TargetProvable (impValue atom (impValue (eqValue c z) target)) :=
    tp_mp hr (imp_exchange (eqValue c z) atom target)
  let hu : Ctx [allValue z atom] (allValue z atom) := .assumption (by simp)
  let ht : Ctx [allValue z atom] (allValue z (impValue (eqValue c z) target)) :=
    hu.forallMP z (.closed (tp_gen z hs))
  exact (Ctx.existsElim z hv ht (.closed (r1 z c))).deduction.empty

/-- A negative membership specialization from direct primitive-equality
rewriting and target-formula vacuity, with all remaining premises explicit. -/
theorem negativeSpecialization_target (y v c p q : M) (hcy : y ≠ c) (hvy : y ≠ v)
    (hr : TargetProvable (impValue (eqValue v y) (impValue q p)))
    (hv : TargetProvable (impValue q (allValue y q))) :
    TargetProvable (impValue (allValue y (impValue (memValue c y) (negValue p)))
      (impValue (memValue c v) (negValue q))) := by
  let e := eqValue v y
  let py := impValue (memValue c y) (negValue p)
  let he : Ctx [q,memValue c v,py,e] e := .assumption (by simp)
  let hq : Ctx [q,memValue c v,py,e] q := .assumption (by simp)
  let hm : Ctx [q,memValue c v,py,e] (memValue c v) := .assumption (by simp)
  let hy : Ctx [q,memValue c v,py,e] py := .assumption (by simp)
  let hmy := Ctx.mp hm (.mp he (.closed (memRight v y c)))
  let hp := Ctx.mp hq (.mp he (.closed hr))
  let contra := Ctx.mp hp (.mp hmy hy)
  have hh : TargetProvable (impValue e (impValue py (impValue (memValue c v) (negValue q)))) :=
    contra.deduction.deduction.deduction.deduction.empty
  exact specializeWithMirroredEquality_target y v py (impValue (memValue c v) (negValue q))
    (implicationVacuity y _ _ (membershipVacuity_target c v y hcy hvy)
      (negationVacuity y q hv)) hh

#print axioms membershipVacuity_target
#print axioms specializeWithMirroredEquality_target
#print axioms negativeSpecialization_target
end models
end PA194ModelLogic
