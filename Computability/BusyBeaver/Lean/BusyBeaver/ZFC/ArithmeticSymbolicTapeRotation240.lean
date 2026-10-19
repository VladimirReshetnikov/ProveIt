import BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252
import BusyBeaver.ZFC.SymbolicRotation240

set_option autoImplicit false

/-!
Numeric interpretation of the actual Rotation240 symbolic tape syntax.
The existing internal bit-prefix and affine algebra is reused without any
Perm252 machine execution or spare-file interpretation. Each gap and numeric
suffix is an arbitrary IΣ1 model element; boxes are pure prefix parameters.
Normalization preserves arbitrary suffixes. Dropping the left exterior is
proved only at suffix zero. This is tape algebra, with no box/step execution,
first-exit, complete simulation or internal PA consistency endpoint claim.
The source follows the checked ArithmeticSymbolicTapePerm252 proof structure;
Mira-Cult, Jeff Ketchersid, Andrew James Wade and ProveIt retain attribution.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineUniformScansPerm252
open ArithmeticSymbolicTapePerm252
  (affine affine_add bitPrefix_add bitPrefix_one bitPrefix_false_zero)
open SymbolicRotation240 (Segment Token Box SConfig)

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def segmentPrefix (gap : V) (boxes : Box → V → V) : Segment → V → V
  | .bit b, suffix => 2*suffix+digit b
  | .run b a c, suffix => bitPrefix b (affine gap a c) suffix
  | .box x, suffix => boxes x suffix

noncomputable def tapePrefix (gap : V) (boxes : Box → V → V) : List Segment → V → V
  | [], suffix => suffix
  | x :: xs, suffix => segmentPrefix gap boxes x (tapePrefix gap boxes xs suffix)

noncomputable def tokenPrefix (gap : V) (boxes : Box → V → V) : Token → V → V
  | .run b a c, suffix => bitPrefix b (affine gap a c) suffix
  | .box x, suffix => boxes x suffix

noncomputable def tokensPrefix (gap : V) (boxes : Box → V → V) : List Token → V → V
  | [], suffix => suffix
  | x :: xs, suffix => tokenPrefix gap boxes x (tokensPrefix gap boxes xs suffix)

lemma tapePrefix_append (gap : V) (boxes : Box → V → V)
    (xs ys : List Segment) (suffix : V) :
    tapePrefix gap boxes (xs++ys) suffix =
      tapePrefix gap boxes xs (tapePrefix gap boxes ys suffix) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,tapePrefix,ih]

lemma tokensPrefix_append (gap : V) (boxes : Box → V → V)
    (xs ys : List Token) (suffix : V) :
    tokensPrefix gap boxes (xs++ys) suffix =
      tokensPrefix gap boxes xs (tokensPrefix gap boxes ys suffix) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.cons_append,tokensPrefix,ih]

lemma tokenOf_prefix (gap : V) (boxes : Box → V → V) (x : Segment) (suffix : V) :
    tokenPrefix gap boxes (SymbolicRotation240.tokenOf x) suffix =
      segmentPrefix gap boxes x suffix := by
  cases x <;> simp [SymbolicRotation240.tokenOf,tokenPrefix,segmentPrefix,affine]

lemma push_prefix (gap : V) (boxes : Box → V → V) (x : Token)
    (xs : List Token) (suffix : V) :
    tokensPrefix gap boxes (SymbolicRotation240.push x xs) suffix =
      tokenPrefix gap boxes x (tokensPrefix gap boxes xs suffix) := by
  cases x with
  | box x => rfl
  | run b a c =>
    simp only [SymbolicRotation240.push]
    split
    next hz =>
      rcases hz with ⟨rfl,rfl⟩
      simp [tokenPrefix,affine]
    next _ =>
      cases xs with
      | nil => rfl
      | cons x xs =>
        cases x with
        | box x => rfl
        | run b' a' c' =>
          by_cases hb : b = b'
          · subst b'
            simp only [if_true,tokensPrefix,tokenPrefix,affine_add,bitPrefix_add]
          · simp only [if_neg hb]
            rfl

theorem norm_prefix (gap : V) (boxes : Box → V → V)
    (xs : List Segment) (suffix : V) :
    tokensPrefix gap boxes (SymbolicRotation240.norm xs) suffix =
      tapePrefix gap boxes xs suffix := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change tokensPrefix gap boxes
      (SymbolicRotation240.push (SymbolicRotation240.tokenOf x) (SymbolicRotation240.norm xs)) suffix = _
    rw [push_prefix,ih,tokenOf_prefix]
    rfl

/-- Only exterior zeros are removed, so this theorem fixes the exterior to zero. -/
theorem dropExterior_zero (gap : V) (boxes : Box → V → V) (xs : List Token) :
    tokensPrefix gap boxes (SymbolicRotation240.dropExterior xs) 0 =
      tokensPrefix gap boxes xs 0 := by
  cases he : xs.reverse with
  | nil => simp [SymbolicRotation240.dropExterior,he]
  | cons x tail =>
    cases x with
    | box x => simp [SymbolicRotation240.dropExterior,he]
    | run b a c =>
      cases b with
      | true => simp [SymbolicRotation240.dropExterior,he]
      | false =>
        have hx : xs = tail.reverse ++ [.run false a c] := by
          simpa only [List.reverse_reverse,List.reverse_cons] using congrArg List.reverse he
        simp only [SymbolicRotation240.dropExterior,he]
        rw [hx,tokensPrefix_append]
        simp [tokensPrefix,tokenPrefix]

theorem normL_zero (gap : V) (boxes : Box → V → V) (xs : List Segment) :
    tokensPrefix gap boxes (SymbolicRotation240.normL xs) 0 = tapePrefix gap boxes xs 0 := by
  rw [SymbolicRotation240.normL,dropExterior_zero,norm_prefix]

/-- A numeric frame for the existing standard finite symbolic configuration.
The gap and values supplied by concrete box prefixes may be nonstandard. -/
noncomputable def configValue (gap : V) (boxes : Box → V → V) (s : SConfig) : V :=
  let q : V := (ArithmeticMachinePerm252.stateCode s.state : Nat)
  let left := tapePrefix gap boxes s.left 0
  let right := tapePrefix gap boxes s.right 0
  if s.onLeft then leftFrame q left right else frame q left right

@[simp] theorem configValue_right (gap : V) (boxes : Box → V → V)
    (q : Option (Fin 240)) (l r : List Segment) :
    configValue gap boxes ⟨q, false, l, r⟩ =
      frame (ArithmeticMachinePerm252.stateCode q : V)
        (tapePrefix gap boxes l 0) (tapePrefix gap boxes r 0) := rfl

@[simp] theorem configValue_left (gap : V) (boxes : Box → V → V)
    (q : Option (Fin 240)) (l r : List Segment) :
    configValue gap boxes ⟨q, true, l, r⟩ =
      leftFrame (ArithmeticMachinePerm252.stateCode q : V)
        (tapePrefix gap boxes l 0) (tapePrefix gap boxes r 0) := rfl

/-- Reuses the literal existing comparison, with exact whole numeric halves. -/
theorem isMatch_value (gap : V) (boxes : Box → V → V) (s t : SConfig)
    (h : SymbolicRotation240.isMatch s t = true) : configValue gap boxes s = configValue gap boxes t := by
  have he : s.state = t.state ∧ s.onLeft = t.onLeft ∧
      SymbolicRotation240.norm s.right = SymbolicRotation240.norm t.right ∧
      SymbolicRotation240.normL s.left = SymbolicRotation240.normL t.left := of_decide_eq_true h
  have hr : tapePrefix gap boxes s.right 0 = tapePrefix gap boxes t.right 0 := by
    rw [←norm_prefix,←norm_prefix,he.2.2.1]
  have hl : tapePrefix gap boxes s.left 0 = tapePrefix gap boxes t.left 0 := by
    rw [←normL_zero,←normL_zero,he.2.2.2]
  simp only [configValue,he.1,he.2.1,hr,hl]

end SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapeRotation240
