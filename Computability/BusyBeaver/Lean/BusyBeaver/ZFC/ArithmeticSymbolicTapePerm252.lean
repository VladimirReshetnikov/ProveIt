import BusyBeaver.ZFC.ArithmeticMachineUniformScansPerm252
import BusyBeaver.ZFC.SymbolicPerm252

/-!
Numeric interpretation of the existing finite symbolic tape syntax.
Run lengths may contain an arbitrary internal gap. Box prefixes are parameters
to this tape-algebra layer; no box execution or arbitrary-box soundness is
assumed or concluded. The actual existing normalization/checker data are reused.
Equality accepted by isMatch preserves the complete numeric configuration,
including the blank exterior removed by normL. Concrete boxes and symbolic
step soundness are subsequent obligations.
-/
namespace SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticMachineUniformScansPerm252
open SymbolicPerm252 (Segment Token Box SConfig)
set_option maxRecDepth 8192
set_option maxHeartbeats 4000000
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private instance bitPrefix_delta (b : Bool) : 𝚫₁-Function₂[V] (bitPrefix b) :=
  (bitPrefix_defined b).graph_delta.to_definable

theorem bitPrefix_add (b : Bool) (n m suffix : V) :
    bitPrefix b (n+m) suffix = bitPrefix b n (bitPrefix b m suffix) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [show ((n+1)+m : V) = (n+m)+1 by ring, bitPrefix_succ,
      bitPrefix_succ, ih]

@[simp] theorem bitPrefix_one (b : Bool) (suffix : V) :
    bitPrefix b 1 suffix = 2*suffix+digit b := by
  simpa using bitPrefix_succ b (0 : V) suffix

@[simp] theorem bitPrefix_false_zero (n : V) : bitPrefix false n (0 : V) = 0 := by
  simp [bitPrefix, zerosPrefix]

def affine (gap : V) (a c : Nat) : V := (a : V)*gap+(c : V)

lemma affine_add (gap : V) (a c a' c' : Nat) :
    affine gap (a+a') (c+c') = affine gap a c+affine gap a' c' := by
  simp only [affine, Nat.cast_add]
  ring

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
    tokenPrefix gap boxes (SymbolicPerm252.tokenOf x) suffix =
      segmentPrefix gap boxes x suffix := by
  cases x <;> simp [SymbolicPerm252.tokenOf,tokenPrefix,segmentPrefix,affine]

lemma push_prefix (gap : V) (boxes : Box → V → V) (x : Token)
    (xs : List Token) (suffix : V) :
    tokensPrefix gap boxes (SymbolicPerm252.push x xs) suffix =
      tokenPrefix gap boxes x (tokensPrefix gap boxes xs suffix) := by
  cases x with
  | box x => rfl
  | run b a c =>
    simp only [SymbolicPerm252.push]
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
    tokensPrefix gap boxes (SymbolicPerm252.norm xs) suffix =
      tapePrefix gap boxes xs suffix := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change tokensPrefix gap boxes
      (SymbolicPerm252.push (SymbolicPerm252.tokenOf x) (SymbolicPerm252.norm xs)) suffix = _
    rw [push_prefix,ih,tokenOf_prefix]
    rfl

/-- Only exterior zeros are removed, so this theorem fixes the exterior to zero. -/
theorem dropExterior_zero (gap : V) (boxes : Box → V → V) (xs : List Token) :
    tokensPrefix gap boxes (SymbolicPerm252.dropExterior xs) 0 =
      tokensPrefix gap boxes xs 0 := by
  cases he : xs.reverse with
  | nil => simp [SymbolicPerm252.dropExterior,he]
  | cons x tail =>
    cases x with
    | box x => simp [SymbolicPerm252.dropExterior,he]
    | run b a c =>
      cases b with
      | true => simp [SymbolicPerm252.dropExterior,he]
      | false =>
        have hx : xs = tail.reverse ++ [.run false a c] := by
          simpa only [List.reverse_reverse,List.reverse_cons] using congrArg List.reverse he
        simp only [SymbolicPerm252.dropExterior,he]
        rw [hx,tokensPrefix_append]
        simp [tokensPrefix,tokenPrefix]

theorem normL_zero (gap : V) (boxes : Box → V → V) (xs : List Segment) :
    tokensPrefix gap boxes (SymbolicPerm252.normL xs) 0 = tapePrefix gap boxes xs 0 := by
  rw [SymbolicPerm252.normL,dropExterior_zero,norm_prefix]

/-- A numeric frame for the existing standard finite symbolic configuration.
The gap and values supplied by concrete box prefixes may be nonstandard. -/
noncomputable def configValue (gap : V) (boxes : Box → V → V) (s : SConfig) : V :=
  let q : V := (ArithmeticMachinePerm252.stateCode s.state : Nat)
  let left := tapePrefix gap boxes s.left 0
  let right := tapePrefix gap boxes s.right 0
  if s.onLeft then leftFrame q left right else frame q left right

/-- Reuses the literal existing comparison, with exact whole numeric halves. -/
theorem isMatch_value (gap : V) (boxes : Box → V → V) (s t : SConfig)
    (h : SymbolicPerm252.isMatch s t = true) : configValue gap boxes s = configValue gap boxes t := by
  have he : s.state = t.state ∧ s.onLeft = t.onLeft ∧
      SymbolicPerm252.norm s.right = SymbolicPerm252.norm t.right ∧
      SymbolicPerm252.normL s.left = SymbolicPerm252.normL t.left := of_decide_eq_true h
  have hr : tapePrefix gap boxes s.right 0 = tapePrefix gap boxes t.right 0 := by
    rw [←norm_prefix,←norm_prefix,he.2.2.1]
  have hl : tapePrefix gap boxes s.left 0 = tapePrefix gap boxes t.left 0 := by
    rw [←normL_zero,←normL_zero,he.2.2.2]
  simp only [configValue,he.1,he.2.1,hr,hl]

end SetTheory.BusyBeaver.ZFC.ArithmeticSymbolicTapePerm252
