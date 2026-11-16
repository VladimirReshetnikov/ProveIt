import PA194ModelExEqualityDiagonal

/-!
# Primitive equality gives observational equality, without a vacuity premise

In a candidate-PRA model `M` whose arithmetic reduct satisfies `𝗜𝚺₁`, for the numerical
calculus of PA194 (`TargetProvable`).

`pa194-model-logic` proves `targetEq_to_neighborhood_of_vacuity`: the primitive equality
`eqValue a b` entails the observational equality `neighborhoodValue a b z` if that primitive
equality is vacuous at the label `z`. The calculus has no vacuity axiom for primitive
equality, so the premise cannot be discharged for an arbitrary `z`. It can be discharged at
one label: the code of the equality itself, by the diagonal axiom `c → ∀c c`. This file ports
the remaining step of the standard development (`pa194-neighborhood`,
`PA194NeighborhoodTransport`): the bound label of each half of the neighborhood formula is
moved from that code to an arbitrary `z ≠ a, b` by specialization with mirrored equality.

* `primitiveToSelfNeighborhood_target`: `a = b → a ≈ b` with the equality's own code as the
  bound label.
* `transferBinder_target`: `∀z₀ atom → ∀z target` from a rewrite `z = z₀ → atom → target`.
* `primitiveToNeighborhood_target`: `a = b → a ≈ b` at every label `z ≠ a, b`.
* `neighborhoodWitness_target`: `∃x x ≈ c` for `z ≠ x, c`.
* `universalInstance_target`: `∀x P → r` from `x ≈ y → P → r` and vacuity of `r` at `x`. This
  is the skeleton of universal instantiation and of the renaming of a bound label.
* `targetExistsNeighborhoodLeft`, `targetExistsNegNeighborhoodLeft`,
  `targetExistsNeighborhoodRight`, `targetExistsNegNeighborhoodRight`: the four existential
  introductions for observational equality of `pa194-model-logic`
  (`…_of_eqVacuity`), with the vacuity premise replaced by `z ≠ c` and `z ≠ x`.

Nothing here concerns a source formula translation, a simulation, or a consistency
implication.
-/
set_option autoImplicit false
set_option maxHeartbeats 3000000
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
local instance nbWitnessZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance nbWitnessOne : One M := ⟨F oneCode Fin.elim0⟩
local instance nbWitnessAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance nbWitnessMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance nbWitnessLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance nbWitnessIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Primitive equality entails observational equality whose bound label is the code of the
equality itself: the diagonal axiom supplies the vacuity. -/
theorem primitiveToSelfNeighborhood_target (a b : M) :
    TargetProvable (impValue (eqValue a b) (neighborhoodValue a b (eqValue a b))) :=
  targetEq_to_neighborhood_of_vacuity a b (eqValue a b) (diagonal_provable (eqValue a b))

theorem iffTransport_target (e a0 a1 b0 b1 : M)
    (ha : TargetProvable (impValue e (iffValue a1 a0)))
    (hb : TargetProvable (impValue e (iffValue b1 b0))) :
    TargetProvable (impValue e (impValue (iffValue a0 b0) (iffValue a1 b1))) := by
  unfold iffValue at ha hb ⊢
  let he : Ctx [conjValue (impValue a0 b0) (impValue b0 a0),e] e := .assumption (by simp)
  let hp : Ctx [conjValue (impValue a0 b0) (impValue b0 a0),e]
      (conjValue (impValue a0 b0) (impValue b0 a0)) := .assumption (by simp)
  let hA : Ctx [conjValue (impValue a0 b0) (impValue b0 a0),e]
      (conjValue (impValue a1 a0) (impValue a0 a1)) := .mp he (.closed ha)
  let hB : Ctx [conjValue (impValue a0 b0) (impValue b0 a0),e]
      (conjValue (impValue b1 b0) (impValue b0 b1)) := .mp he (.closed hb)
  let forward : Ctx [conjValue (impValue a0 b0) (impValue b0 a0),e] (impValue a1 b1) :=
    (hA.andLeft.arrowCompose hp.andLeft).arrowCompose hB.andRight
  let backward : Ctx [conjValue (impValue a0 b0) (impValue b0 a0),e] (impValue b1 a1) :=
    (hB.andLeft.arrowCompose hp.andRight).arrowCompose hA.andRight
  exact (Ctx.andIntro forward backward).deduction.deduction.empty

/-- Rewriting the second argument of a membership atom along primitive equality, as an
equivalence. -/
theorem membershipRightIff_target (z z0 a : M) :
    TargetProvable (impValue (eqValue z z0) (iffValue (memValue a z) (memValue a z0))) := by
  unfold iffValue
  let he : Ctx [eqValue z z0] (eqValue z z0) := .assumption (by simp)
  let hf : Ctx [eqValue z z0] (impValue (memValue a z) (memValue a z0)) :=
    .mp he (.closed (memRight z z0 a))
  let hr : Ctx [eqValue z z0] (impValue (memValue a z0) (memValue a z)) :=
    .mp he (.closed (reverseRight_target z z0 a))
  exact (Ctx.andIntro hf hr).deduction.empty

/-- Rewriting the first argument of a membership atom along primitive equality, as an
equivalence. -/
theorem membershipLeftIff_target (z z0 a : M) :
    TargetProvable (impValue (eqValue z z0) (iffValue (memValue z a) (memValue z0 a))) := by
  unfold iffValue
  let he : Ctx [eqValue z z0] (eqValue z z0) := .assumption (by simp)
  let hf : Ctx [eqValue z z0] (impValue (memValue z a) (memValue z0 a)) :=
    .mp he (.closed (memLeft z z0 a))
  let hr : Ctx [eqValue z z0] (impValue (memValue z0 a) (memValue z a)) :=
    .mp he (.closed (reverseLeft_target z z0 a))
  exact (Ctx.andIntro hf hr).deduction.empty

/-- Transfer a universally quantified formula along an explicitly proved rewrite of its
bound label. -/
theorem transferBinder_target (z0 z atom target : M)
    (hvTarget : TargetProvable (impValue target (allValue z0 target)))
    (hvAntecedent : TargetProvable (impValue (allValue z0 atom) (allValue z (allValue z0 atom))))
    (hr : TargetProvable (impValue (eqValue z z0) (impValue atom target))) :
    TargetProvable (impValue (allValue z0 atom) (allValue z target)) := by
  have hs := specializeWithMirroredEquality_target z0 z atom target hvTarget hr
  have hu : TargetProvable (impValue (allValue z (allValue z0 atom)) (allValue z target)) :=
    tp_mp (tp_gen z hs) (r2 z (allValue z0 atom) target)
  exact imp_trans hvAntecedent hu

/-- **Primitive equality entails observational equality at every label other than the two
compared ones.** -/
theorem primitiveToNeighborhood_target (a b z : M) (hza : z ≠ a) (hzb : z ≠ b) :
    TargetProvable (impValue (eqValue a b) (neighborhoodValue a b z)) := by
  by_cases hz : z = eqValue a b
  · subst hz
    exact primitiveToSelfNeighborhood_target a b
  · let z0 : M := eqValue a b
    have h0a : z0 ≠ a := ne_of_gt (label_lt_eqValue_left a b)
    have h0b : z0 ≠ b := ne_of_gt (label_lt_eqValue_right a b)
    have h0z : z0 ≠ z := fun h => hz h.symm
    have hLtarget : TargetProvable (impValue (iffValue (memValue a z) (memValue b z))
        (allValue z0 (iffValue (memValue a z) (memValue b z)))) :=
      iffVacuity_target z0 _ _ (membershipVacuity_target a z z0 h0a h0z)
        (membershipVacuity_target b z z0 h0b h0z)
    have hRtarget : TargetProvable (impValue (iffValue (memValue z a) (memValue z b))
        (allValue z0 (iffValue (memValue z a) (memValue z b)))) :=
      iffVacuity_target z0 _ _ (membershipVacuity_target z a z0 h0z h0a)
        (membershipVacuity_target z b z0 h0z h0b)
    have hLsource : TargetProvable (impValue (iffValue (memValue a z0) (memValue b z0))
        (allValue z (iffValue (memValue a z0) (memValue b z0)))) :=
      iffVacuity_target z _ _ (membershipVacuity_target a z0 z hza hz)
        (membershipVacuity_target b z0 z hzb hz)
    have hRsource : TargetProvable (impValue (iffValue (memValue z0 a) (memValue z0 b))
        (allValue z (iffValue (memValue z0 a) (memValue z0 b)))) :=
      iffVacuity_target z _ _ (membershipVacuity_target z0 a z hz hza)
        (membershipVacuity_target z0 b z hz hzb)
    have hL := transferBinder_target z0 z (iffValue (memValue a z0) (memValue b z0))
      (iffValue (memValue a z) (memValue b z)) hLtarget (universalVacuity z z0 _ hLsource)
      (iffTransport_target _ _ _ _ _ (membershipRightIff_target z z0 a)
        (membershipRightIff_target z z0 b))
    have hR := transferBinder_target z0 z (iffValue (memValue z0 a) (memValue z0 b))
      (iffValue (memValue z a) (memValue z b)) hRtarget (universalVacuity z z0 _ hRsource)
      (iffTransport_target _ _ _ _ _ (membershipLeftIff_target z z0 a)
        (membershipLeftIff_target z z0 b))
    have hself := primitiveToSelfNeighborhood_target a b
    unfold neighborhoodValue at hself ⊢
    let he : Ctx [eqValue a b] (eqValue a b) := .assumption (by simp)
    let hs : Ctx [eqValue a b]
        (conjValue (allValue z0 (iffValue (memValue a z0) (memValue b z0)))
          (allValue z0 (iffValue (memValue z0 a) (memValue z0 b)))) := .mp he (.closed hself)
    let hl : Ctx [eqValue a b] (allValue z (iffValue (memValue a z) (memValue b z))) :=
      .mp hs.andLeft (.closed hL)
    let hr : Ctx [eqValue a b] (allValue z (iffValue (memValue z a) (memValue z b))) :=
      .mp hs.andRight (.closed hR)
    exact (Ctx.andIntro hl hr).deduction.empty

/-- **Every label has an observationally equal copy under a bound label.** -/
theorem neighborhoodWitness_target (x c z : M) (hzx : z ≠ x) (hzc : z ≠ c) :
    TargetProvable (exValue x (neighborhoodValue x c z)) :=
  tp_mp (tp_mp (r1 x c) (existentialMonotonicity x (primitiveToNeighborhood_target c x z hzc hzx)))
    (existentialMonotonicity x (neighborhood_symm c x z))

/-- Universal instantiation from a substitution along observational equality: if `P` with
`x` observationally equal to `y` gives `r`, and `r` does not depend on `x`, then `∀x P`
gives `r`. -/
theorem universalInstance_target (x y z P r : M) (hzx : z ≠ x) (hzy : z ≠ y)
    (hv : TargetProvable (impValue r (allValue x r)))
    (hsub : TargetProvable (impValue (neighborhoodValue x y z) (impValue P r))) :
    TargetProvable (impValue (allValue x P) r) := by
  have hperm : TargetProvable (impValue P (impValue (neighborhoodValue x y z) r)) :=
    tp_mp hsub (imp_exchange (neighborhoodValue x y z) P r)
  let hall : Ctx [allValue x P] (allValue x P) := .assumption (by simp)
  let hrel : Ctx [allValue x P] (allValue x (impValue (neighborhoodValue x y z) r)) :=
    hall.forallMP x (.closed (tp_gen x hperm))
  exact (Ctx.existsElim x hv hrel (.closed (neighborhoodWitness_target x y z hzx hzy))).deduction.empty

/-! ## Existential introduction for observational equality, without a vacuity premise -/

theorem targetExistsNeighborhoodLeft (x c a z : M)
    (hxc : x ≠ c) (hxa : x ≠ a) (hxz : x ≠ z) (hzc : z ≠ c) :
    TargetProvable (impValue (neighborhoodValue c a z) (exValue x (neighborhoodValue x a z))) := by
  let P := neighborhoodValue x a z
  let Q := neighborhoodValue c a z
  let E := eqValue c x
  have hv : TargetProvable (impValue (negValue Q) (allValue x (negValue Q))) :=
    negationVacuity x Q (neighborhoodVacuity_target x c a z hxc hxa hxz)
  have hr : TargetProvable (impValue E (impValue (negValue P) (negValue Q))) := by
    let he : Ctx [Q,negValue P,E] E := .assumption (by simp)
    let hp : Ctx [Q,negValue P,E] (negValue P) := .assumption (by simp)
    let hq : Ctx [Q,negValue P,E] Q := .assumption (by simp)
    let hcx : Ctx [Q,negValue P,E] (neighborhoodValue c x z) :=
      .mp he (.closed (primitiveToNeighborhood_target c x z hzc (Ne.symm hxz)))
    let hxc' : Ctx [Q,negValue P,E] (neighborhoodValue x c z) :=
      .mp hcx (.closed (neighborhood_symm c x z))
    let hp' : Ctx [Q,negValue P,E] P :=
      .mp hq (.mp hxc' (.closed (neighborhood_trans x c a z)))
    exact (Ctx.mp hp' hp).deduction.deduction.deduction.empty
  have hs := specializeWithMirroredEquality_target x c (negValue P) (negValue Q) hv hr
  let hq : Ctx [allValue x (negValue P),Q] Q := .assumption (by simp)
  let hall : Ctx [allValue x (negValue P),Q] (allValue x (negValue P)) := .assumption (by simp)
  let hn : Ctx [allValue x (negValue P),Q] (negValue Q) := .mp hall (.closed hs)
  exact (Ctx.mp hq hn).deduction.deduction.empty

theorem targetExistsNegNeighborhoodLeft (x c a z : M)
    (hxc : x ≠ c) (hxa : x ≠ a) (hxz : x ≠ z) (hzc : z ≠ c) :
    TargetProvable (impValue (negValue (neighborhoodValue c a z))
      (exValue x (negValue (neighborhoodValue x a z)))) := by
  let P := neighborhoodValue x a z
  let Q := neighborhoodValue c a z
  let E := eqValue c x
  have hv : TargetProvable (impValue Q (allValue x Q)) := neighborhoodVacuity_target x c a z hxc hxa hxz
  have hr : TargetProvable (impValue E (impValue P Q)) := by
    let he : Ctx [P,E] E := .assumption (by simp)
    let hp : Ctx [P,E] P := .assumption (by simp)
    let hcx : Ctx [P,E] (neighborhoodValue c x z) :=
      .mp he (.closed (primitiveToNeighborhood_target c x z hzc (Ne.symm hxz)))
    let hq : Ctx [P,E] Q := .mp hp (.mp hcx (.closed (neighborhood_trans c x a z)))
    exact hq.deduction.deduction.empty
  have hs := specializeWithMirroredEquality_target x c P Q hv hr
  exact targetExistsNeg_of_specialize x P Q hs

theorem targetExistsNeighborhoodRight (x c a z : M)
    (hxc : x ≠ c) (hxa : x ≠ a) (hxz : x ≠ z) (hzc : z ≠ c) :
    TargetProvable (impValue (neighborhoodValue a c z) (exValue x (neighborhoodValue a x z))) :=
  imp_trans (neighborhood_symm a c z)
    (imp_trans (targetExistsNeighborhoodLeft x c a z hxc hxa hxz hzc)
      (existentialMonotonicity x (neighborhood_symm x a z)))

theorem targetExistsNegNeighborhoodRight (x c a z : M)
    (hxc : x ≠ c) (hxa : x ≠ a) (hxz : x ≠ z) (hzc : z ≠ c) :
    TargetProvable (impValue (negValue (neighborhoodValue a c z))
      (exValue x (negValue (neighborhoodValue a x z)))) :=
  imp_trans (contrapose (neighborhood_symm c a z))
    (imp_trans (targetExistsNegNeighborhoodLeft x c a z hxc hxa hxz hzc)
      (existentialMonotonicity x (contrapose (neighborhood_symm a x z))))

#print axioms primitiveToSelfNeighborhood_target
#print axioms transferBinder_target
#print axioms primitiveToNeighborhood_target
#print axioms neighborhoodWitness_target
#print axioms universalInstance_target
#print axioms targetExistsNeighborhoodLeft
#print axioms targetExistsNegNeighborhoodLeft
#print axioms targetExistsNeighborhoodRight
#print axioms targetExistsNegNeighborhoodRight
end models
end PA194ModelLogic
