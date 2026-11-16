import PA194ModelNeighborhoodWitness

/-!
# Weak adjunction in the numerical calculus, at model level

In a candidate-PRA model `M` whose arithmetic reduct satisfies `𝗜𝚺₁`, the numerical calculus
of PA194 proves weak adjunction for arbitrary labels of `M`:

  `∃c ((∀m (m ∈ a → m ∈ c)) ∧ b ∈ c)`,

written with `memValue x y` for "`y` is a member of `x`". This is the model-level port of the
standard derivation `weakAdjunctionAtName` of `pa194-source-separation`.

* `rawWeakAdjunction_target`: the gate at `(a, b, d)` with `d` the code of `∀q ⊤`, which is a
  theorem, gives `∃d ((∀b (b ∈ a → b ∈ d)) ∧ b ∈ d)`. The output label is the code of the
  defining property and the bound member label is the point `b`.
* `subsetClauseRename_target`: the bound member label is renamed from `b` to `m`, by
  specialization with mirrored primitive equality and reverse rewriting.
* `weakAdjunctionRenameOutput_target`: the output label is renamed from `d` to `c`, by
  instantiation along observational equality (`universalInstance_target`).
* `weakAdjunctionAtName_target`: the statement above, for pairwise distinct `a, b, c, m` and
  a reserved label `z` different from `b`, `c`, `m`.
* `weakAdjunction_supplier`: the universally closed form with the consecutive labels
  `lo, lo+1, lo+2, lo+3` and the source encoding of the implication.

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
local instance weakAdjZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance weakAdjOne : One M := ⟨F oneCode Fin.elim0⟩
local instance weakAdjAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance weakAdjMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance weakAdjLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance weakAdjIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The body of weak adjunction at the output label `x`: every member of `a` is a member of
`x`, and `b` is a member of `x`. The bound member label is `m`. -/
noncomputable def weakAdjunctionBody (a b m x : M) : M :=
  conjValue (allValue m (impValue (memValue a m) (memValue x m))) (memValue x b)

theorem label_lt_allValue (q h : M) : q < allValue q h := by
  have h1 : q ≤ impValue h q := le_impValue_right h (le_refl q)
  have h2 : impValue h q < impValue h q + 2 := lt_add_of_pos_right _ (by norm_num)
  exact lt_of_le_of_lt h1 h2

/-- The gate at the code of a provable formula: the separated set contains every member of
`a` and the point `b`. -/
theorem rawWeakAdjunction_target (a b q : M)
    (ha : allValue q 0 ≠ a) (hb : allValue q 0 ≠ b) :
    TargetProvable (exValue (allValue q 0)
      (conjValue (allValue b (impValue (memValue a b) (memValue (allValue q 0) b)))
        (memValue (allValue q 0) b))) := by
  let d : M := allValue q 0
  have hd : TargetProvable d := tp_gen q sequentTruth_zero
  let ma : M := memValue a b
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
  have proj : TargetProvable (impValue clause (impValue ma md)) := by
    let hma : Ctx [ma,clause] ma := .assumption (by simp)
    let hcl : Ctx [ma,clause] (conjValue (impValue ma (impValue d md)) (impValue md d)) :=
      .assumption (by simp [clause])
    exact (Ctx.mp (.closed hd) (.mp hma hcl.andLeft)).deduction.deduction.empty
  have out : TargetProvable (impValue (conjValue sep point)
      (conjValue (allValue b (impValue ma md)) md)) := by
    let frame : Ctx [conjValue sep point] (conjValue sep point) := .assumption (by simp)
    let hs : Ctx [conjValue sep point] (allValue b clause) := frame.andLeft
    let hpt : Ctx [conjValue sep point] (impValue d md) := frame.andRight
    let hp : Ctx [conjValue sep point] md := .mp (.closed hd) hpt
    let hi : Ctx [conjValue sep point] (allValue b (impValue ma md)) :=
      hs.forallMP b (.closed (tp_gen b proj))
    exact (Ctx.andIntro hi hp).deduction.empty
  exact tp_mp hex (existentialMonotonicity d out)

/-- Renaming of the bound member label of the inclusion clause. -/
theorem subsetClauseRename_target (a d b m : M)
    (hba : b ≠ a) (hbm : b ≠ m) (hbd : b ≠ d) (hma : m ≠ a) (hmd : m ≠ d) :
    TargetProvable (impValue (allValue b (impValue (memValue a b) (memValue d b)))
      (allValue m (impValue (memValue a m) (memValue d m)))) := by
  let atom : M := impValue (memValue a b) (memValue d b)
  let target : M := impValue (memValue a m) (memValue d m)
  have hv : TargetProvable (impValue target (allValue b target)) :=
    implicationVacuity b _ _ (membershipVacuity_target a m b hba hbm)
      (membershipVacuity_target d m b hbd hbm)
  have hr : TargetProvable (impValue (eqValue m b) (impValue atom target)) := by
    let he : Ctx [memValue a m,atom,eqValue m b] (eqValue m b) := .assumption (by simp)
    let hat : Ctx [memValue a m,atom,eqValue m b] (impValue (memValue a b) (memValue d b)) :=
      .assumption (by simp [atom])
    let hm : Ctx [memValue a m,atom,eqValue m b] (memValue a m) := .assumption (by simp)
    let hab : Ctx [memValue a m,atom,eqValue m b] (memValue a b) :=
      .mp hm (.mp he (.closed (memRight m b a)))
    let hdb : Ctx [memValue a m,atom,eqValue m b] (memValue d b) := .mp hab hat
    let hdm : Ctx [memValue a m,atom,eqValue m b] (memValue d m) :=
      .mp hdb (.mp he (.closed (reverseRight_target m b d)))
    exact hdm.deduction.deduction.deduction.empty
  have hinst : TargetProvable (impValue (allValue b atom) target) :=
    specializeWithMirroredEquality_target b m atom target hv hr
  have hvac : TargetProvable (impValue (allValue b atom) (allValue m (allValue b atom))) :=
    universalVacuity m b atom (implicationVacuity m _ _
      (membershipVacuity_target a b m hma (Ne.symm hbm))
      (membershipVacuity_target d b m hmd (Ne.symm hbm)))
  let h : Ctx [allValue b atom] target := .mp (.assumption (by simp)) (.closed hinst)
  exact (h.generalize m (fun x hx => by
    have hxe : x = allValue b atom := by simpa using hx
    rw [hxe]
    exact hvac)).deduction.empty

/-- Substitution of the output label of the body along observational equality. -/
theorem weakAdjunctionBodySubst_target (a b m d c z : M)
    (hzd : z ≠ d) (hzc : z ≠ c) (hzb : z ≠ b) (hzm : z ≠ m) (hmd : m ≠ d) (hmc : m ≠ c) :
    TargetProvable (impValue (neighborhoodValue d c z)
      (impValue (weakAdjunctionBody a b m d) (weakAdjunctionBody a b m c))) := by
  let N : M := neighborhoodValue d c z
  let P1 : M := impValue (memValue a m) (memValue d m)
  let P2 : M := impValue (memValue a m) (memValue c m)
  have hstep : TargetProvable (impValue N (impValue P1 P2)) := by
    let hN : Ctx [memValue a m,P1,N] N := .assumption (by simp)
    let hP : Ctx [memValue a m,P1,N] (impValue (memValue a m) (memValue d m)) :=
      .assumption (by simp [P1])
    let hm : Ctx [memValue a m,P1,N] (memValue a m) := .assumption (by simp)
    let hdm : Ctx [memValue a m,P1,N] (memValue d m) := .mp hm hP
    let hcm : Ctx [memValue a m,P1,N] (memValue c m) :=
      .mp hdm (.mp hN (.closed (neighborhoodRightCongruence_target d c z m hzd hzc hzm)))
    exact hcm.deduction.deduction.deduction.empty
  have hNvac : TargetProvable (impValue N (allValue m N)) :=
    neighborhoodVacuity_target m d c z hmd hmc (Ne.symm hzm)
  have hgen : TargetProvable (impValue N (allValue m (impValue P1 P2))) := by
    let h : Ctx [N] (impValue P1 P2) := .mp (.assumption (by simp)) (.closed hstep)
    exact (h.generalize m (fun x hx => by
      have hxe : x = N := by simpa using hx
      rw [hxe]
      exact hNvac)).deduction.empty
  unfold weakAdjunctionBody
  let B : M := conjValue (allValue m P1) (memValue d b)
  let hN : Ctx [B,N] N := .assumption (by simp)
  let hB : Ctx [B,N] (conjValue (allValue m P1) (memValue d b)) := .assumption (by simp [B])
  let hall : Ctx [B,N] (allValue m P2) := hB.andLeft.forallMP m (.mp hN (.closed hgen))
  let hcb : Ctx [B,N] (memValue c b) :=
    .mp hB.andRight (.mp hN (.closed (neighborhoodRightCongruence_target d c z b hzd hzc hzb)))
  exact (Ctx.andIntro hall hcb).deduction.deduction.empty

theorem weakAdjunctionBodyVacuity_target (a b m x y : M)
    (hya : y ≠ a) (hym : y ≠ m) (hyx : y ≠ x) (hyb : y ≠ b) :
    TargetProvable (impValue (weakAdjunctionBody a b m x)
      (allValue y (weakAdjunctionBody a b m x))) := by
  unfold weakAdjunctionBody
  exact conjunctionVacuity y _ _
    (universalVacuity y m _ (implicationVacuity y _ _
      (membershipVacuity_target a m y hya hym) (membershipVacuity_target x m y hyx hym)))
    (membershipVacuity_target x b y hyx hyb)

/-- Renaming of the existentially bound output label. -/
theorem weakAdjunctionRenameOutput_target (a b m d c z : M)
    (hzd : z ≠ d) (hzc : z ≠ c) (hzb : z ≠ b) (hzm : z ≠ m)
    (hmd : m ≠ d) (hmc : m ≠ c) (hca : c ≠ a) (hcb : c ≠ b) (hcd : c ≠ d)
    (hda : d ≠ a) (hdb : d ≠ b) :
    TargetProvable (impValue (exValue d (weakAdjunctionBody a b m d))
      (exValue c (weakAdjunctionBody a b m c))) := by
  let Bd : M := weakAdjunctionBody a b m d
  let Bc : M := weakAdjunctionBody a b m c
  have hsub : TargetProvable (impValue (neighborhoodValue c d z)
      (impValue (negValue Bc) (negValue Bd))) := by
    let hN : Ctx [Bd,negValue Bc,neighborhoodValue c d z] (neighborhoodValue c d z) :=
      .assumption (by simp)
    let hn : Ctx [Bd,negValue Bc,neighborhoodValue c d z] (negValue Bc) := .assumption (by simp)
    let hb : Ctx [Bd,negValue Bc,neighborhoodValue c d z] Bd := .assumption (by simp)
    let hN' : Ctx [Bd,negValue Bc,neighborhoodValue c d z] (neighborhoodValue d c z) :=
      .mp hN (.closed (neighborhood_symm c d z))
    let hbc : Ctx [Bd,negValue Bc,neighborhoodValue c d z] Bc :=
      .mp hb (.mp hN' (.closed (weakAdjunctionBodySubst_target a b m d c z hzd hzc hzb hzm hmd hmc)))
    exact (Ctx.mp hbc hn).deduction.deduction.deduction.empty
  have hvBd : TargetProvable (impValue Bd (allValue c Bd)) :=
    weakAdjunctionBodyVacuity_target a b m d c hca (Ne.symm hmc) hcd hcb
  have hinst : TargetProvable (impValue (allValue c (negValue Bc)) (negValue Bd)) :=
    universalInstance_target c d z (negValue Bc) (negValue Bd) hzc hzd
      (negationVacuity c Bd hvBd) hsub
  have hvBc : TargetProvable (impValue Bc (allValue d Bc)) :=
    weakAdjunctionBodyVacuity_target a b m c d hda (Ne.symm hmd) (Ne.symm hcd) hdb
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

/-- **Weak adjunction for arbitrary labels**: some `c` contains every member of `a` and
contains `b`. -/
theorem weakAdjunctionAtName_target (a b c m z : M)
    (hab : a ≠ b) (ham : a ≠ m) (hbm : b ≠ m) (hca : c ≠ a) (hcb : c ≠ b) (hcm : c ≠ m)
    (hzb : z ≠ b) (hzc : z ≠ c) (hzm : z ≠ m) :
    TargetProvable (exValue c (weakAdjunctionBody a b m c)) := by
  let q : M := a + b + c + m + z
  let d : M := allValue q 0
  have hq : q < d := label_lt_allValue q 0
  have haq : a ≤ q := le_trans (le_trans (le_trans le_self_add le_self_add) le_self_add) le_self_add
  have hbq : b ≤ q := le_trans (le_trans (le_trans le_add_self le_self_add) le_self_add) le_self_add
  have hcq : c ≤ q := le_trans (le_trans le_add_self le_self_add) le_self_add
  have hmq : m ≤ q := le_trans le_add_self le_self_add
  have hzq : z ≤ q := le_add_self
  have hda : d ≠ a := ne_of_gt (lt_of_le_of_lt haq hq)
  have hdb : d ≠ b := ne_of_gt (lt_of_le_of_lt hbq hq)
  have hdc : d ≠ c := ne_of_gt (lt_of_le_of_lt hcq hq)
  have hdm : d ≠ m := ne_of_gt (lt_of_le_of_lt hmq hq)
  have hdz : d ≠ z := ne_of_gt (lt_of_le_of_lt hzq hq)
  have h1 := rawWeakAdjunction_target a b q hda hdb
  have h2 := subsetClauseRename_target a d b m (Ne.symm hab) hbm (Ne.symm hdb) (Ne.symm ham)
    (Ne.symm hdm)
  have hmono : TargetProvable (impValue
      (conjValue (allValue b (impValue (memValue a b) (memValue d b))) (memValue d b))
      (weakAdjunctionBody a b m d)) := by
    unfold weakAdjunctionBody
    let h : Ctx [conjValue (allValue b (impValue (memValue a b) (memValue d b))) (memValue d b)]
        (conjValue (allValue b (impValue (memValue a b) (memValue d b))) (memValue d b)) :=
      .assumption (by simp)
    exact (Ctx.andIntro (.mp h.andLeft (.closed h2)) h.andRight).deduction.empty
  have h3 : TargetProvable (exValue d (weakAdjunctionBody a b m d)) :=
    tp_mp h1 (existentialMonotonicity d hmono)
  exact tp_mp h3 (weakAdjunctionRenameOutput_target a b m d c z (Ne.symm hdz) hzc hzb hzm
    (Ne.symm hdm) (Ne.symm hcm) hca hcb (Ne.symm hdc) hda hdb)

/-- **The universally closed weak-adjunction supplier**, with consecutive labels and the
source encoding `¬¬p → q` of the implication `p → q`. -/
theorem weakAdjunction_supplier (lo z : M)
    (h1 : z ≠ lo+1) (h2 : z ≠ (lo+1)+1) (h3 : z ≠ ((lo+1)+1)+1) :
    TargetProvable (allValue lo (allValue (lo+1) (exValue ((lo+1)+1)
      (conjValue
        (allValue (((lo+1)+1)+1)
          (impValue (negValue (negValue (memValue lo (((lo+1)+1)+1))))
            (memValue ((lo+1)+1) (((lo+1)+1)+1))))
        (memValue ((lo+1)+1) (lo+1)))))) := by
  let a : M := lo
  let b : M := lo+1
  let c : M := (lo+1)+1
  let m : M := ((lo+1)+1)+1
  have lab : a < b := lt_add_one lo
  have lbc : b < c := lt_add_one (lo+1)
  have lcm : c < m := lt_add_one ((lo+1)+1)
  have hraw := weakAdjunctionAtName_target a b c m z (ne_of_lt lab)
    (ne_of_lt (lt_trans lab (lt_trans lbc lcm))) (ne_of_lt (lt_trans lbc lcm))
    (ne_of_gt (lt_trans lab lbc)) (ne_of_gt lbc) (ne_of_lt lcm) h1 h2 h3
  have hdn : TargetProvable (impValue (weakAdjunctionBody a b m c)
      (conjValue (allValue m (impValue (negValue (negValue (memValue a m))) (memValue c m)))
        (memValue c b))) := by
    unfold weakAdjunctionBody
    have hinner : TargetProvable (impValue (impValue (memValue a m) (memValue c m))
        (impValue (negValue (negValue (memValue a m))) (memValue c m))) := by
      let hnn : Ctx [negValue (negValue (memValue a m)),impValue (memValue a m) (memValue c m)]
          (negValue (negValue (memValue a m))) := .assumption (by simp)
      let hi : Ctx [negValue (negValue (memValue a m)),impValue (memValue a m) (memValue c m)]
          (impValue (memValue a m) (memValue c m)) := .assumption (by simp)
      exact (Ctx.mp hnn.dne hi).deduction.deduction.empty
    let h : Ctx [conjValue (allValue m (impValue (memValue a m) (memValue c m))) (memValue c b)]
        (conjValue (allValue m (impValue (memValue a m) (memValue c m))) (memValue c b)) :=
      .assumption (by simp)
    exact (Ctx.andIntro (.mp h.andLeft (.closed (liftImp m hinner))) h.andRight).deduction.empty
  exact tp_gen a (tp_gen b (tp_mp hraw (existentialMonotonicity c hdn)))

#print axioms rawWeakAdjunction_target
#print axioms subsetClauseRename_target
#print axioms weakAdjunctionRenameOutput_target
#print axioms weakAdjunctionAtName_target
#print axioms weakAdjunction_supplier
end models
end PA194ModelLogic
