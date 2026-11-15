import PA194ModelAlignedAtoms
import PA194ModelSafeQF
import PA194ModelExMembership
import PA194ModelSeedEnvironment
import PA194ModelDescendantComplexity
import PA194ModelRankedEnvironment
import PA194ModelDualInduction
import PA194ModelAtomicFreshness
import PA194RelExtTypedTranslation

/-! Internal structural induction for arbitrary-label vacuity. -/
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option linter.unusedSectionVars false
namespace PA194ModelLogic
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAModelIOpenPairing
 PRASubAddition PRAHistoryPairCode PRAExhaustion PRAHerbrandSelection PRAEqualityCode PRASelectCode
 PA194TargetCantor PA194TargetProofLeaf PA194TargetLeaves PA194TargetGate
 PA194PathIterator PA194BranchSeed PA194TermShiftCodeModel PA194TargetStep PA194StackCode PA194StackHistory
 PA194FormulaUpdate PA194ParamHistory PA194SourceSearchCoding PA194CloseVariable
open SetTheory.BusyBeaver.ZFC.ArithmeticCantor
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local notation "F" => Structure.func (L := language) (M := M)
local instance obsAlignedZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance obsAlignedOne : One M := ⟨F oneCode Fin.elim0⟩
local instance obsAlignedAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance obsAlignedMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance obsAlignedLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance obsAlignedIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]






/-- An arbitrary premise which is vacuous at the binder can be carried through
universal quantification. -/
theorem targetPremiseRewrite_all (E w A B : M)
    (hv : TargetProvable (impValue E (allValue w E)))
    (h : TargetPremiseRewrite E A B) :
    TargetPremiseRewrite E (allValue w A) (allValue w B) := by
  constructor
  · let he : Ctx [allValue w A,E] E := .assumption (by simp)
    let ha : Ctx [allValue w A,E] (allValue w A) := .assumption (by simp)
    let hea : Ctx [allValue w A,E] (allValue w E) := .mp he (.closed hv)
    let hab : Ctx [allValue w A,E] (allValue w (impValue A B)) :=
      hea.forallMP w (.closed (tp_gen w h.1))
    exact (ha.forallMP w hab).deduction.deduction.empty
  · let he : Ctx [allValue w B,E] E := .assumption (by simp)
    let hb : Ctx [allValue w B,E] (allValue w B) := .assumption (by simp)
    let hea : Ctx [allValue w B,E] (allValue w E) := .mp he (.closed hv)
    let hba : Ctx [allValue w B,E] (allValue w (impValue B A)) :=
      hea.forallMP w (.closed (tp_gen w h.2))
    exact (hb.forallMP w hba).deduction.deduction.empty

theorem targetPremiseRewrite_ex (E w A B : M)
    (hv : TargetProvable (impValue E (allValue w E)))
    (h : TargetPremiseRewrite E A B) :
    TargetPremiseRewrite E (exValue w A) (exValue w B) := by
  exact targetPremiseRewrite_neg E _ _
    (targetPremiseRewrite_all E w _ _ hv (targetPremiseRewrite_neg E A B h))

theorem neighborhoodPremiseRewrite_all (x y z w A B : M)
    (hwy : w ≠ y) (hwx : w ≠ x) (hwz : w ≠ z)
    (h : TargetPremiseRewrite (neighborhoodValue y x z) A B) :
    TargetPremiseRewrite (neighborhoodValue y x z) (allValue w A) (allValue w B) :=
  targetPremiseRewrite_all _ w A B (neighborhoodVacuity_target w y x z hwy hwx hwz) h

theorem neighborhoodPremiseRewrite_ex (x y z w A B : M)
    (hwy : w ≠ y) (hwx : w ≠ x) (hwz : w ≠ z)
    (h : TargetPremiseRewrite (neighborhoodValue y x z) A B) :
    TargetPremiseRewrite (neighborhoodValue y x z) (exValue w A) (exValue w B) :=
  targetPremiseRewrite_ex _ w A B (neighborhoodVacuity_target w y x z hwy hwx hwz) h

theorem observationalMembershipFirst (x y a b c z : M) (h : LabelAligned x y a b)
    (hzy : z ≠ y) (hzx : z ≠ x) (hzc : z ≠ c) :
    TargetPremiseRewrite (neighborhoodValue y x z) (memValue a c) (memValue b c) := by
  rcases h with hab | ⟨hax,hby⟩
  · subst b; exact targetPremiseRewrite_refl _ _
  · subst a; subst b
    let N := neighborhoodValue y x z
    constructor
    · let hn : Ctx [memValue x c,N] N := .assumption (by simp)
      let hm : Ctx [memValue x c,N] (memValue x c) := .assumption (by simp)
      let hnr : Ctx [memValue x c,N] (neighborhoodValue x y z) := .mp hn (.closed (neighborhood_symm y x z))
      exact (Ctx.mp hm (.mp hnr (.closed (neighborhoodRightCongruence_target x y z c hzx hzy hzc)))).deduction.deduction.empty
    · exact neighborhoodRightCongruence_target y x z c hzy hzx hzc

theorem observationalMembershipSecond (x y a b c z : M) (h : LabelAligned x y a b)
    (hzy : z ≠ y) (hzx : z ≠ x) (hzc : z ≠ c) :
    TargetPremiseRewrite (neighborhoodValue y x z) (memValue c a) (memValue c b) := by
  rcases h with hab | ⟨hax,hby⟩
  · subst b; exact targetPremiseRewrite_refl _ _
  · subst a; subst b
    let N := neighborhoodValue y x z
    constructor
    · let hn : Ctx [memValue c x,N] N := .assumption (by simp)
      let hm : Ctx [memValue c x,N] (memValue c x) := .assumption (by simp)
      let hnr : Ctx [memValue c x,N] (neighborhoodValue x y z) := .mp hn (.closed (neighborhood_symm y x z))
      exact (Ctx.mp hm (.mp hnr (.closed (neighborhoodLeftCongruence_target x y z c hzx hzy hzc)))).deduction.deduction.empty
    · exact neighborhoodLeftCongruence_target y x z c hzy hzx hzc

theorem observationalMembership (x y a b c d z : M) (ha : LabelAligned x y a b)
    (hc : LabelAligned x y c d) (hzy : z ≠ y) (hzx : z ≠ x) (hzc : z ≠ c) (hzb : z ≠ b) :
    TargetPremiseRewrite (neighborhoodValue y x z) (memValue a c) (memValue b d) :=
  targetPremiseRewrite_trans _ _ _ _ (observationalMembershipFirst x y a b c z ha hzy hzx hzc)
    (observationalMembershipSecond x y c d b z hc hzy hzx hzb)

theorem observationalNeighborhoodFirst (x y a b c z : M) (h : LabelAligned x y a b) :
    TargetPremiseRewrite (neighborhoodValue y x z) (neighborhoodValue a c z) (neighborhoodValue b c z) := by
  rcases h with hab | ⟨hax,hby⟩
  · subst b; exact targetPremiseRewrite_refl _ _
  · subst a; subst b
    let N := neighborhoodValue y x z
    constructor
    · let hn : Ctx [neighborhoodValue x c z,N] N := .assumption (by simp)
      let hm : Ctx [neighborhoodValue x c z,N] (neighborhoodValue x c z) := .assumption (by simp)
      exact (Ctx.mp hm (.mp hn (.closed (neighborhood_trans y x c z)))).deduction.deduction.empty
    · let hn : Ctx [neighborhoodValue y c z,N] N := .assumption (by simp)
      let hm : Ctx [neighborhoodValue y c z,N] (neighborhoodValue y c z) := .assumption (by simp)
      let hnr : Ctx [neighborhoodValue y c z,N] (neighborhoodValue x y z) := .mp hn (.closed (neighborhood_symm y x z))
      exact (Ctx.mp hm (.mp hnr (.closed (neighborhood_trans x y c z)))).deduction.deduction.empty

theorem observationalNeighborhoodSecond (x y a b c z : M) (h : LabelAligned x y a b) :
    TargetPremiseRewrite (neighborhoodValue y x z) (neighborhoodValue c a z) (neighborhoodValue c b z) := by
  rcases h with hab | ⟨hax,hby⟩
  · subst b; exact targetPremiseRewrite_refl _ _
  · subst a; subst b
    let N := neighborhoodValue y x z
    constructor
    · let hn : Ctx [neighborhoodValue c x z,N] N := .assumption (by simp)
      let hm : Ctx [neighborhoodValue c x z,N] (neighborhoodValue c x z) := .assumption (by simp)
      let hnr : Ctx [neighborhoodValue c x z,N] (neighborhoodValue x y z) := .mp hn (.closed (neighborhood_symm y x z))
      exact (Ctx.mp hnr (.mp hm (.closed (neighborhood_trans c x y z)))).deduction.deduction.empty
    · let hn : Ctx [neighborhoodValue c y z,N] N := .assumption (by simp)
      let hm : Ctx [neighborhoodValue c y z,N] (neighborhoodValue c y z) := .assumption (by simp)
      exact (Ctx.mp hn (.mp hm (.closed (neighborhood_trans c y x z)))).deduction.deduction.empty

theorem observationalNeighborhood (x y a b c d z : M) (ha : LabelAligned x y a b)
    (hc : LabelAligned x y c d) :
    TargetPremiseRewrite (neighborhoodValue y x z) (neighborhoodValue a c z) (neighborhoodValue b d z) :=
  targetPremiseRewrite_trans _ _ _ _ (observationalNeighborhoodFirst x y a b c z ha)
    (observationalNeighborhoodSecond x y c d b z hc)

#print axioms observationalMembership
#print axioms observationalNeighborhood
#print axioms targetPremiseRewrite_all
#print axioms targetPremiseRewrite_ex
#print axioms neighborhoodPremiseRewrite_all
#print axioms neighborhoodPremiseRewrite_ex
end models
end PA194ModelLogic
