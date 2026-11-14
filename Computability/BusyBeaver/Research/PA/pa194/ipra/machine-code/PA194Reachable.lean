import PA194HalfDiv
import PA194Stepper
/-! The packed PA194 clock only reaches controls at most 194, at every model time, by open induction inside candidate PRA models. -/
set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
namespace PA194Reachable
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PRAModelIOpenPairing PA194BinaryDouble TableDispatch
open PRAOpenInduction PackedDecoderModel PA194HalfDiv PA194FiniteControls ConfigurationStep PackedIterationModel PackedClock PackedRootModel TableModelSemantics PRAQOrder

theorem targetBound (n : Nat) (hn : n < 388) :
    (PA194Rows.rows.getD n (0,0,194)).2.2 ≤ 194 := by
  have h : ∀ i : Fin 388, (PA194Rows.rows.getD i.val (0,0,194)).2.2 ≤ 194 := by decide +kernel
  exact h ⟨n,hn⟩
def boundBody : Semiformula language Nat 1 :=
  .nrel Language.ORing.Rel.lt ![.func (constantCode 194) ![.bvar 0], .func clockState ![.bvar 0]]
theorem boundBody_open : boundBody.Open := by simp [boundBody, Semiformula.Open, Semiformula.qr]
section model
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
theorem stepBound (x : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    pi₁ x ≤ (194 : M) → pi₁ (F encodedStep (fun _ => x)) ≤ (194 : M) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  intro hx
  rw [modelEncodedStepAny]
  simp only [modelPairCode, pi₁_pair]
  let q := pi₁ x
  let l := pi₁ (pi₂ x)
  let r := pi₂ (pi₂ x)
  change (stepSem q l r).1 ≤ (194 : M)
  by_cases hq : q < modelNumeral M 194
  · obtain ⟨i,b,hi,hb,hw,hd,ht⟩ := modelWorkingRow q r hq
    have hbound := targetBound (2*i.val+b.val) (by have := i.isLt; have := b.isLt; omega)
    simp only [targetCode, modelLookupAll] at ht
    unfold stepSem
    dsimp only
    split_ifs with ha hd'
    · exact False.elim ((modelLtZero q (modelNumeral M 194)).mp ha hq)
    all_goals
      change lookupSem 194 targets (q+q+F parityCode (fun _ => r)) ≤ (194 : M)
      rw [ht, modelNumeralCast]
      exact_mod_cast hbound
  · unfold stepSem
    dsimp only
    have ha := (modelLtZero q (modelNumeral M 194)).mpr hq
    change F ltBitCode ![q, modelNumeral M 194] = F (Code.zero 0) Fin.elim0 at ha
    simp only [ha, if_true]
    exact hx
theorem boundBody_eval (t : M) (e : Nat → M) : boundBody.Eval ![t] e ↔
    ¬modelNumeral M 194 < F clockState (fun _ => t) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![t] boundBody ↔ _
  simp only [boundBody, Semiformula.EvalAux]
  have hv (a b : Semiterm language Nat 1) :
      (fun i => Semiterm.val ![t] e (![a,b] i)) = ![Semiterm.val ![t] e a,Semiterm.val ![t] e b] := by
    exact val_pair ![t] e a b
  rw [hv]
  have hx (f : Code 1) : Semiterm.val ![t] e ((.func f ![.bvar 0]) : Semiterm language Nat 1) = F f (fun _ => t) := by
    simp only [Semiterm.val_func]
    congr 1
    funext i
    refine Fin.cases ?_ (fun j => Fin.elim0 j) i
    simp [Semiterm.val_bvar]
  rw [hx, hx, modelConstant]
  rfl
theorem clockStateEval (t : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    F clockState (fun _ => t) = pi₁ (F clock (fun _ => t)) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  simp only [clockState, PackedRootModel.modelUnary, modelDecodeLeft]

/-- The bound holds at every model time, including nonstandard times. -/
theorem clockBound (t : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    pi₁ (F clock (fun _ => t)) ≤ (194 : M) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hc : modelNumeral M 194 = (194 : M) := by rw [modelNumeralCast]; norm_num
  let e : Nat → M := fun _ => t
  have h : boundBody.Eval ![t] e := by
    apply modelOpenInduction (M := M) boundBody boundBody_open e
    · apply (boundBody_eval (0 : M) e).mpr
      rw [clockStateEval]
      change ¬modelNumeral M 194 < pi₁ (F clock (fun _ => F (Code.zero 0) Fin.elim0))
      rw [modelClockZero, hc]
      change ¬ (194 : M) < pi₁ (0 : M)
      have hp : pair (0 : M) 0 = 0 := by simp [pair]
      have hz : pi₁ (0 : M) = 0 := by simpa [hp] using pi₁_pair (0 : M) 0
      rw [hz]
      intro h; exact not_lt_zero h
    · intro k hk
      apply (boundBody_eval (F Code.succ (fun _ => k)) e).mpr
      have hi := (boundBody_eval k e).mp hk
      rw [clockStateEval, hc] at hi
      have hi' : pi₁ (F clock (fun _ => k)) ≤ (194 : M) := le_of_not_gt hi
      rw [clockStateEval, modelClockSucc, hc]
      exact not_lt_of_ge (stepBound _ hi')
  have ht := (boundBody_eval t e).mp h
  rw [clockStateEval, hc] at ht
  exact le_of_not_gt ht
/-- The existing packed halting indicator is one precisely at the designated terminal control. -/
theorem haltIndicatorIffState (t : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    F haltIndicator (fun _ => t) = (1 : M) ↔ pi₁ (F clock (fun _ => t)) = (194 : M) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have hc : modelNumeral M 194 = (194 : M) := by rw [modelNumeralCast]; norm_num
  rw [modelHaltIndicator, hc]
  constructor
  · intro h
    exact le_antisymm (clockBound t) (le_of_not_gt h)
  · intro h
    rw [h]
    exact _root_.lt_irrefl _
#print axioms haltIndicatorIffState
#print axioms clockBound
#print axioms boundBody_eval
#print axioms stepBound
end model
#print axioms targetBound
end PA194Reachable
