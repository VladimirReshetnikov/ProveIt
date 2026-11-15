import PA194ModelWeakAdjunction

/-!
# Separation in the numerical calculus, at model level

In a candidate-PRA model `M` whose arithmetic reduct satisfies `𝗜𝚺₁`, the numerical calculus
of PA194 proves separation for an arbitrary property value `P` of `M` and arbitrary labels:

  `∃c ∀b (b ∈ c ↔ (b ∈ a ∧ P))`,

written with `memValue x y` for "`y` is a member of `x`". The property is a value of the
model, not a syntactic object, so the side conditions of the standard derivation
(`separationAtName` of `pa194-source-separation`: the output label and the reserved label do
not occur in the property) are replaced by target-provable vacuity of `P` at three labels.

* `universalSelf_target`: `∀q X → X` when `X` is vacuous at `q`.
* `rawSeparation_target`: the gate at `(a, b, d)` with `d` the code of `∀q (b ∈ a ∧ P)`. As a
  formula `d` is equivalent to `b ∈ a ∧ P`, and the gate makes `b ∈ d` equivalent to `d`.
* `separationBodySubst_target`, `separationRenameOutput_target`: the output label is renamed
  from `d` to `c` along observational equality.
* `separationAtName_target`: the statement above, for `c ≠ a, b`, a reserved label
  `z ≠ b, c`, and a label `q` above `a, b, c, z`, when `P` is vacuous at `c`, at `q` and at
  the code of `∀q (b ∈ a ∧ P)`.

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
local instance separationZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance separationOne : One M := ⟨F oneCode Fin.elim0⟩
local instance separationAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance separationMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance separationLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance separationIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The body of separation at the output label `y`: the members of `y` are the members `b`
of `a` with the property `P`. -/
noncomputable def separationBody (a b P y : M) : M :=
  allValue b (iffValue (memValue y b) (conjValue (memValue a b) P))

/-- A universal quantifier over a label at which the formula is vacuous can be dropped. -/
theorem universalSelf_target (q X : M) (hv : TargetProvable (impValue X (allValue q X))) :
    TargetProvable (impValue (allValue q X) X) :=
  specializeWithMirroredEquality_target q q X X hv
    (tp_mp (imp_refl X) (imp_k (impValue X X) (eqValue q q)))

/-- The gate at the code of the padded property: the separated set has the output label
`d`, the code of `∀q (b ∈ a ∧ P)`. -/
theorem rawSeparation_target (a b P q : M)
    (ha : allValue q (conjValue (memValue a b) P) ≠ a)
    (hb : allValue q (conjValue (memValue a b) P) ≠ b)
    (hv : TargetProvable (impValue (conjValue (memValue a b) P)
      (allValue q (conjValue (memValue a b) P)))) :
    TargetProvable (exValue (allValue q (conjValue (memValue a b) P))
      (separationBody a b P (allValue q (conjValue (memValue a b) P)))) := by
  let ma : M := memValue a b
  let X : M := conjValue ma P
  let d : M := allValue q X
  have hdX : TargetProvable (impValue d X) := universalSelf_target q X hv
  let md : M := memValue d b
  let clause : M := conjValue (impValue ma (impValue d md)) (impValue md d)
  let sep : M := allValue b clause
  let point : M := impValue d md
  have hn : TargetProvable (negValue (allValue d (impValue sep (negValue point)))) :=
    notSeparationTail_target a b d ha hb
  have hall : TargetProvable
      (impValue (allValue d (negValue (negValue (impValue sep (negValue point)))))
        (allValue d (impValue sep (negValue point)))) :=
    liftImp d (doubleNegationElimination (impValue sep (negValue point)))
  have hex : TargetProvable (exValue d (conjValue sep point)) := tp_mp hn (contrapose hall)
  have pointwise : TargetProvable (impValue clause (iffValue md X)) := by
    let hcl1 : Ctx [md,clause] (conjValue (impValue ma (impValue d md)) (impValue md d)) :=
      .assumption (by simp [clause])
    let hmd : Ctx [md,clause] md := .assumption (by simp)
    let hd1 : Ctx [md,clause] d := .mp hmd hcl1.andRight
    let fwd : Ctx [clause] (impValue md X) := (Ctx.mp hd1 (.closed hdX)).deduction
    let hcl2 : Ctx [X,clause] (conjValue (impValue ma (impValue d md)) (impValue md d)) :=
      .assumption (by simp [clause])
    let hX : Ctx [X,clause] (conjValue ma P) := .assumption (by simp [X])
    let hXX : Ctx [X,clause] X := .assumption (by simp)
    let hd2 : Ctx [X,clause] d := .mp hXX (.closed hv)
    let bwd : Ctx [clause] (impValue X md) :=
      (Ctx.mp hd2 (.mp hX.andLeft hcl2.andLeft)).deduction
    exact (Ctx.andIntro fwd bwd).deduction.empty
  have out : TargetProvable (impValue (conjValue sep point) (separationBody a b P d)) := by
    let frame : Ctx [conjValue sep point] (conjValue sep point) := .assumption (by simp)
    let hs : Ctx [conjValue sep point] (allValue b clause) := frame.andLeft
    exact (hs.forallMP b (.closed (tp_gen b pointwise))).deduction.empty
  exact tp_mp hex (existentialMonotonicity d out)

/-- Substitution of the output label of the body along observational equality. -/
theorem separationBodySubst_target (a b P d c z : M)
    (hzd : z ≠ d) (hzc : z ≠ c) (hzb : z ≠ b) (hbd : b ≠ d) (hbc : b ≠ c) :
    TargetProvable (impValue (neighborhoodValue d c z)
      (impValue (separationBody a b P d) (separationBody a b P c))) := by
  let N : M := neighborhoodValue d c z
  let X : M := conjValue (memValue a b) P
  let I1 : M := iffValue (memValue d b) X
  let I2 : M := iffValue (memValue c b) X
  have hdc := neighborhoodRightCongruence_target d c z b hzd hzc hzb
  have hcd := neighborhoodRightCongruence_target c d z b hzc hzd hzb
  have hsym := neighborhood_symm d c z
  have hstep : TargetProvable (impValue N (impValue I1 I2)) := by
    let fN : Ctx [memValue c b,I1,N] N := .assumption (by simp)
    let fI : Ctx [memValue c b,I1,N]
        (conjValue (impValue (memValue d b) X) (impValue X (memValue d b))) :=
      .assumption (by simp [I1,iffValue])
    let fm : Ctx [memValue c b,I1,N] (memValue c b) := .assumption (by simp)
    let fN' : Ctx [memValue c b,I1,N] (neighborhoodValue c d z) := .mp fN (.closed hsym)
    let fdm : Ctx [memValue c b,I1,N] (memValue d b) := .mp fm (.mp fN' (.closed hcd))
    let fwd : Ctx [I1,N] (impValue (memValue c b) X) := (Ctx.mp fdm fI.andLeft).deduction
    let bN : Ctx [X,I1,N] N := .assumption (by simp)
    let bI : Ctx [X,I1,N]
        (conjValue (impValue (memValue d b) X) (impValue X (memValue d b))) :=
      .assumption (by simp [I1,iffValue])
    let bX : Ctx [X,I1,N] X := .assumption (by simp)
    let bdm : Ctx [X,I1,N] (memValue d b) := .mp bX bI.andRight
    let bcm : Ctx [X,I1,N] (memValue c b) := .mp bdm (.mp bN (.closed hdc))
    let bwd : Ctx [I1,N] (impValue X (memValue c b)) := bcm.deduction
    exact (Ctx.andIntro fwd bwd).deduction.deduction.empty
  have hNvac : TargetProvable (impValue N (allValue b N)) :=
    neighborhoodVacuity_target b d c z hbd hbc (Ne.symm hzb)
  have hgen : TargetProvable (impValue N (allValue b (impValue I1 I2))) := by
    let h : Ctx [N] (impValue I1 I2) := .mp (.assumption (by simp)) (.closed hstep)
    exact (h.generalize b (fun x hx => by
      have hxe : x = N := by simpa using hx
      rw [hxe]
      exact hNvac)).deduction.empty
  unfold separationBody
  let hN : Ctx [allValue b I1,N] N := .assumption (by simp)
  let hB : Ctx [allValue b I1,N] (allValue b I1) := .assumption (by simp)
  exact (hB.forallMP b (.mp hN (.closed hgen))).deduction.deduction.empty

/-- The body is vacuous at every label that differs from its labels and at which the
property is vacuous. -/
theorem separationBodyVacuity_target (a b P x y : M)
    (hP : TargetProvable (impValue P (allValue y P)))
    (hya : y ≠ a) (hyb : y ≠ b) (hyx : y ≠ x) :
    TargetProvable (impValue (separationBody a b P x) (allValue y (separationBody a b P x))) := by
  unfold separationBody
  exact universalVacuity y b _ (iffVacuity_target y _ _ (membershipVacuity_target x b y hyx hyb)
    (conjunctionVacuity y _ _ (membershipVacuity_target a b y hya hyb) hP))

/-- Renaming of the existentially bound output label. -/
theorem separationRenameOutput_target (a b P d c z : M)
    (hzd : z ≠ d) (hzc : z ≠ c) (hzb : z ≠ b) (hbd : b ≠ d) (hbc : b ≠ c)
    (hca : c ≠ a) (hcd : c ≠ d) (hda : d ≠ a)
    (hPc : TargetProvable (impValue P (allValue c P)))
    (hPd : TargetProvable (impValue P (allValue d P))) :
    TargetProvable (impValue (exValue d (separationBody a b P d))
      (exValue c (separationBody a b P c))) := by
  let Bd : M := separationBody a b P d
  let Bc : M := separationBody a b P c
  have hsub : TargetProvable (impValue (neighborhoodValue c d z)
      (impValue (negValue Bc) (negValue Bd))) := by
    let hN : Ctx [Bd,negValue Bc,neighborhoodValue c d z] (neighborhoodValue c d z) :=
      .assumption (by simp)
    let hn : Ctx [Bd,negValue Bc,neighborhoodValue c d z] (negValue Bc) := .assumption (by simp)
    let hb : Ctx [Bd,negValue Bc,neighborhoodValue c d z] Bd := .assumption (by simp)
    let hN' : Ctx [Bd,negValue Bc,neighborhoodValue c d z] (neighborhoodValue d c z) :=
      .mp hN (.closed (neighborhood_symm c d z))
    let hbc' : Ctx [Bd,negValue Bc,neighborhoodValue c d z] Bc :=
      .mp hb (.mp hN' (.closed (separationBodySubst_target a b P d c z hzd hzc hzb hbd hbc)))
    exact (Ctx.mp hbc' hn).deduction.deduction.deduction.empty
  have hvBd : TargetProvable (impValue Bd (allValue c Bd)) :=
    separationBodyVacuity_target a b P d c hPc hca (Ne.symm hbc) hcd
  have hinst : TargetProvable (impValue (allValue c (negValue Bc)) (negValue Bd)) :=
    universalInstance_target c d z (negValue Bc) (negValue Bd) hzc hzd
      (negationVacuity c Bd hvBd) hsub
  have hvBc : TargetProvable (impValue Bc (allValue d Bc)) :=
    separationBodyVacuity_target a b P c d hPd hda (Ne.symm hbd) (Ne.symm hcd)
  have hvall : TargetProvable (impValue (allValue c (negValue Bc))
      (allValue d (allValue c (negValue Bc)))) :=
    universalVacuity d c _ (negationVacuity d Bc hvBc)
  let h : Ctx [allValue c (negValue Bc)] (negValue Bd) :=
    .mp (.assumption (by simp)) (.closed hinst)
  have hall : TargetProvable (impValue (allValue c (negValue Bc)) (allValue d (negValue Bd))) :=
    (h.generalize d (fun x hx => by
      have hxe : x = allValue c (negValue Bc) := by simpa using hx
      rw [hxe]
      exact hvall)).deduction.empty
  exact contrapose hall

/-- **Separation for arbitrary labels and an arbitrary property value**: some `c` has as
members the members `b` of `a` with the property `P`. The property has to be vacuous at the
output label `c`, at a label `q` above `a, b, c, z`, and at the code of `∀q (b ∈ a ∧ P)`. -/
theorem separationAtName_target (a b c z P q : M)
    (haq : a < q) (hbq : b < q) (hcq : c < q) (hzq : z < q)
    (hca : c ≠ a) (hcb : c ≠ b) (hzb : z ≠ b) (hzc : z ≠ c)
    (hPc : TargetProvable (impValue P (allValue c P)))
    (hPq : TargetProvable (impValue P (allValue q P)))
    (hPd : TargetProvable (impValue P
      (allValue (allValue q (conjValue (memValue a b) P)) P))) :
    TargetProvable (exValue c (separationBody a b P c)) := by
  let X : M := conjValue (memValue a b) P
  let d : M := allValue q X
  have hq : q < d := label_lt_allValue q X
  have hda : d ≠ a := ne_of_gt (lt_trans haq hq)
  have hdb : d ≠ b := ne_of_gt (lt_trans hbq hq)
  have hdc : d ≠ c := ne_of_gt (lt_trans hcq hq)
  have hdz : d ≠ z := ne_of_gt (lt_trans hzq hq)
  have hXq : TargetProvable (impValue X (allValue q X)) :=
    conjunctionVacuity q _ _ (membershipVacuity_target a b q (ne_of_gt haq) (ne_of_gt hbq)) hPq
  have h1 : TargetProvable (exValue d (separationBody a b P d)) :=
    rawSeparation_target a b P q hda hdb hXq
  exact tp_mp h1 (separationRenameOutput_target a b P d c z (Ne.symm hdz) hzc hzb
    (Ne.symm hdb) (Ne.symm hcb) hca (Ne.symm hdc) hda hPc hPd)

#print axioms universalSelf_target
#print axioms rawSeparation_target
#print axioms separationBodySubst_target
#print axioms separationRenameOutput_target
#print axioms separationAtName_target
end models
end PA194ModelLogic
