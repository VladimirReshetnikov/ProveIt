import PA194ModelUniversalSpecialization

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
local instance reverseEqualityZero : Zero M := ⟨F (Code.zero 0) Fin.elim0⟩
local instance reverseEqualityOne : One M := ⟨F oneCode Fin.elim0⟩
local instance reverseEqualityAdd : Add M := ⟨fun x y => F addCode ![x,y]⟩
local instance reverseEqualityMul : Mul M := ⟨fun x y => F mulCode ![x,y]⟩
local instance reverseEqualityLT : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local instance reverseEqualityIOpen : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
variable [M↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

inductive MembershipSlot where
  | first | second | diagonal
  deriving DecidableEq

noncomputable def chiValue : MembershipSlot → M → M → M
  | .first,d,t => memValue t d
  | .second,d,t => memValue d t
  | .diagonal,_,t => memValue t t

theorem impValue_le_negValue (a : M) : a < negValue a := by
  have hp : (0 : M) < cantor a 1 :=
    lt_of_lt_of_le (by simp) (components_le a 1).2
  have hm : (1 : M) * cantor a 1 < 4 * cantor a 1 :=
    mul_lt_mul_of_pos_right (by norm_num) hp
  have h := lt_of_le_of_lt (components_le a 1).1 (by simpa only [one_mul] using hm)
  exact h

theorem label_lt_eqValue_left (a b : M) : a < eqValue a b := by
  have h : a ≤ impValue a b := le_impValue_left b (le_refl a)
  have h3 : impValue a b < impValue a b + 3 := by
    have hp : (0 : M) < 3 := by norm_num
    exact lt_add_of_pos_right _ hp
  exact lt_of_le_of_lt h h3

theorem label_lt_eqValue_right (a b : M) : b < eqValue a b := by
  have h : b ≤ impValue a b := le_impValue_right a (le_refl b)
  have h3 : impValue a b < impValue a b + 3 := by
    have hp : (0 : M) < 3 := by norm_num
    exact lt_add_of_pos_right _ hp
  exact lt_of_le_of_lt h h3

theorem separator_fresh_model (e q p a b : M) (ha : a ≤ e) (hb : b ≤ e) :
    a < negValue (impValue e (impValue q p)) ∧ b < negValue (impValue e (impValue q p)) := by
  have he : e ≤ impValue e (impValue q p) := le_impValue_left _ (le_refl e)
  exact ⟨lt_of_le_of_lt (le_trans ha he) (impValue_le_negValue _),
    lt_of_le_of_lt (le_trans hb he) (impValue_le_negValue _)⟩

theorem notSeparationTail_target (a b c : M) (ha : c ≠ a) (hb : c ≠ b) :
    TargetProvable (negValue (separationTailValue a b c)) := by
  have h := gate_provable a b c ha hb
  change TargetProvable (negValue (impValue (memVacValue a b c) (separationTailValue a b c))) at h
  exact negImpRight h

theorem chiDirect_target (k : MembershipSlot) (d a b : M) :
    TargetProvable (impValue (eqValue a b) (impValue (chiValue k d a) (chiValue k d b))) := by
  cases k with
  | first => exact memLeft a b d
  | second => exact memRight a b d
  | diagonal =>
    let he : Ctx [memValue a a,eqValue a b] (eqValue a b) := .assumption (by simp)
    let hm : Ctx [memValue a a,eqValue a b] (memValue a a) := .assumption (by simp)
    let hm' := Ctx.mp hm (.mp he (.closed (memLeft a b a)))
    exact (Ctx.mp hm' (.mp he (.closed (memRight a b b)))).deduction.deduction.empty

theorem chiVacuity_target (k : MembershipSlot) (d t y : M)
    (hyt : y ≠ t) (hyd : k = .diagonal ∨ y ≠ d) :
    TargetProvable (impValue (chiValue k d t) (allValue y (chiValue k d t))) := by
  cases k with
  | first => exact membershipVacuity_target t d y hyt (hyd.resolve_left (by decide))
  | second => exact membershipVacuity_target d t y (hyd.resolve_left (by decide)) hyt
  | diagonal => exact membershipVacuity_target t t y hyt hyt

noncomputable def Ctx.negImpLeft {Γ : List M} {a b : M}
    (p : Ctx Γ (negValue (impValue a b))) : Ctx Γ a := by
  let ha : Ctx (a :: negValue a :: Γ) a := .assumption (by simp)
  let hn : Ctx (a :: negValue a :: Γ) (negValue a) := .assumption (by simp)
  let hi : Ctx (negValue a :: Γ) (impValue a b) := ((Ctx.mp ha hn).explosion b).deduction
  exact (Ctx.mp hi (p.up (negValue a))).deduction.dne

noncomputable def Ctx.negImpRight {Γ : List M} {a b : M}
    (p : Ctx Γ (negValue (impValue a b))) : Ctx Γ (negValue b) := by
  let hb : Ctx (b :: Γ) b := .assumption (by simp)
  exact (Ctx.mp (hb.lift a) (p.up b)).deduction

theorem phiToEquality_target (e q p : M) :
    TargetProvable (impValue (negValue (impValue e (impValue q p))) e) := by
  let h : Ctx [negValue (impValue e (impValue q p))] (negValue (impValue e (impValue q p))) := .assumption (by simp)
  exact h.negImpLeft.deduction.empty

theorem phiToQ_target (e q p : M) :
    TargetProvable (impValue (negValue (impValue e (impValue q p))) q) := by
  let h : Ctx [negValue (impValue e (impValue q p))] (negValue (impValue e (impValue q p))) := .assumption (by simp)
  exact h.negImpRight.negImpLeft.deduction.empty

theorem phiToNotP_target (e q p : M) :
    TargetProvable (impValue (negValue (impValue e (impValue q p))) (negValue p)) := by
  let h : Ctx [negValue (impValue e (impValue q p))] (negValue (impValue e (impValue q p))) := .assumption (by simp)
  exact h.negImpRight.negImpRight.deduction.empty

/-- Reverse primitive-equality membership rewriting when the variable labels
are distinct and the fixed parameter is fresh (unless using the diagonal slot). -/
theorem reverseDistinct_target (k : MembershipSlot) (d a b : M)
    (hab : a ≠ b) (had : k = .diagonal ∨ a ≠ d) :
    TargetProvable (impValue (eqValue a b) (impValue (chiValue k d b) (chiValue k d a))) := by
  let e := eqValue a b
  let p := chiValue k d a
  let q := chiValue k d b
  let C := impValue e (impValue q p)
  let φ := negValue C
  let P := pointValue a φ
  let A := impValue (memValue a a) P
  let B := impValue (memValue φ a) φ
  let S := allValue a (conjValue A B)
  have hφa : φ ≠ a := by
    have hf := (separator_fresh_model e q p a b
      (le_of_lt (label_lt_eqValue_left a b)) (le_of_lt (label_lt_eqValue_right a b))).1
    change a < φ at hf
    exact ne_of_gt hf
  have hca : a ≠ φ := Ne.symm hφa
  have hp : TargetProvable (impValue φ (negValue p)) := phiToNotP_target e q p
  let hconj : Ctx [conjValue A B] (conjValue A B) := .assumption (by simp)
  have hproj : TargetProvable (impValue (conjValue A B) B) := hconj.andRight.deduction.empty
  have hS : TargetProvable (impValue S (allValue a (impValue (memValue φ a) (negValue p)))) :=
    imp_trans (liftImp a hproj) (liftImp a (imp_lift hp (memValue φ a)))
  have hspec : TargetProvable (impValue (allValue a (impValue (memValue φ a) (negValue p)))
      (impValue (memValue φ b) (negValue q))) :=
    negativeSpecialization_target a b φ p q hca hab (chiDirect_target k d b a) (chiVacuity_target k d b a hab had)
  have hSQ : TargetProvable (impValue S (impValue (memValue φ b) (negValue q))) := imp_trans hS hspec
  let hpCtx : Ctx [P,S,φ] P := .assumption (by simp)
  let hsCtx : Ctx [P,S,φ] S := .assumption (by simp)
  let hφCtx : Ctx [P,S,φ] φ := .assumption (by simp)
  let heCtx : Ctx [P,S,φ] e := .mp hφCtx (.closed (phiToEquality_target e q p))
  let hqCtx : Ctx [P,S,φ] q := .mp hφCtx (.closed (phiToQ_target e q p))
  let hMa : Ctx [P,S,φ] (memValue φ a) := .mp hφCtx hpCtx
  let hMb : Ctx [P,S,φ] (memValue φ b) := .mp hMa (.mp heCtx (.closed (memRight a b φ)))
  let hnq : Ctx [P,S,φ] (negValue q) := .mp hMb (.mp hsCtx (.closed hSQ))
  have himp : TargetProvable (impValue φ (impValue S (negValue P))) :=
    (Ctx.mp hqCtx hnq).deduction.deduction.deduction.empty
  have hAll : TargetProvable (impValue (allValue φ φ) (allValue φ (impValue S (negValue P)))) :=
    tp_mp (tp_gen φ himp) (r2 φ φ (impValue S (negValue P)))
  have hdiag : TargetProvable (impValue φ (allValue φ φ)) := diagonal_provable φ
  have hφQ : TargetProvable (impValue φ (separationTailValue a a φ)) := by
    change TargetProvable (impValue φ (allValue φ (impValue S (negValue P))))
    exact imp_trans hdiag hAll
  have hnQ : TargetProvable (negValue (separationTailValue a a φ)) := notSeparationTail_target a a φ hφa hφa
  have hnnC : TargetProvable (negValue (negValue C)) := imp_trans hφQ hnQ
  exact tp_mp hnnC (doubleNegationElimination C)

/-- Reverse primitive-equality membership rewriting for all label collisions,
proved uniformly for arbitrary elements of every candidate-PRA model. -/
theorem reverseAll_target (k : MembershipSlot) (d a b : M) :
    TargetProvable (impValue (eqValue a b) (impValue (chiValue k d b) (chiValue k d a))) := by
  by_cases hab : a = b
  · subst b
    let atom := chiValue k d a
    exact tp_mp (imp_refl atom) (imp_k (impValue atom atom) (eqValue a a))
  · by_cases had : a = d
    · subst d
      cases k with
      | diagonal => exact reverseDistinct_target .diagonal a a b hab (Or.inl rfl)
      | first =>
        let he : Ctx [memValue b a,eqValue a b] (eqValue a b) := .assumption (by simp)
        let hm : Ctx [memValue b a,eqValue a b] (memValue b a) := .assumption (by simp)
        let hbb : Ctx [memValue b a,eqValue a b] (memValue b b) :=
          .mp hm (.mp he (.closed (memRight a b b)))
        let haa : Ctx [memValue b a,eqValue a b] (memValue a a) :=
          .mp hbb (.mp he (.closed (reverseDistinct_target .diagonal a a b hab (Or.inl rfl))))
        exact haa.deduction.deduction.empty
      | second =>
        let he : Ctx [memValue a b,eqValue a b] (eqValue a b) := .assumption (by simp)
        let hm : Ctx [memValue a b,eqValue a b] (memValue a b) := .assumption (by simp)
        let hbb : Ctx [memValue a b,eqValue a b] (memValue b b) :=
          .mp hm (.mp he (.closed (memLeft a b b)))
        let haa : Ctx [memValue a b,eqValue a b] (memValue a a) :=
          .mp hbb (.mp he (.closed (reverseDistinct_target .diagonal a a b hab (Or.inl rfl))))
        exact haa.deduction.deduction.empty
    · exact reverseDistinct_target k d a b hab (Or.inr had)

theorem reverseRight_target (a b d : M) :
    TargetProvable (impValue (eqValue a b) (impValue (memValue d b) (memValue d a))) :=
  reverseAll_target .second d a b

theorem reverseLeft_target (a b d : M) :
    TargetProvable (impValue (eqValue a b) (impValue (memValue b d) (memValue a d))) :=
  reverseAll_target .first d a b

#print axioms reverseAll_target
#print axioms reverseRight_target
#print axioms reverseLeft_target
#print axioms reverseDistinct_target
#print axioms phiToEquality_target
#print axioms phiToQ_target
#print axioms phiToNotP_target
#print axioms impValue_le_negValue
#print axioms separator_fresh_model
#print axioms notSeparationTail_target
#print axioms chiDirect_target
#print axioms chiVacuity_target
end models
end PA194ModelLogic
