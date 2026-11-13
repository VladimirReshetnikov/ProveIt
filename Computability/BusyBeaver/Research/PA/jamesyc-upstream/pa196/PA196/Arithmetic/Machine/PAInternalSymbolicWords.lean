module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalRunNormalization
public import M6.Runtime
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.Symbolic
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic
open ScanBits M6.Runtime
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Arithmetic interpretation of the existing finite symbolic words. The box
argument is a word-prepending operation; its concrete correctness is separate. -/
noncomputable def word (n : V) (box : BoxSt → V → V) : List Seg → V → V
  | [], t => t
  | .bit b :: xs, t => (1+1)*word n box xs t+b.toNat
  | .run b a c :: xs, t => repeatBits (a*n+c) b.toNat (word n box xs t)
  | .box x :: xs, t => box x (word n box xs t)
noncomputable def tokenWord (n : V) (box : BoxSt → V → V) : List Tok → V → V
  | [], t => t
  | .run b a c :: xs, t => repeatBits (a*n+c) b.toNat (tokenWord n box xs t)
  | .box x :: xs, t => box x (tokenWord n box xs t)

theorem token_append (n : V) (box : BoxSt → V → V) (xs ys : List Tok) (t : V) :
    tokenWord n box (xs++ys) t = tokenWord n box xs (tokenWord n box ys t) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => cases x <;> simp only [List.cons_append,tokenWord,ih]

theorem token_push (n : V) (box : BoxSt → V → V) (x : Tok) (xs : List Tok) (t : V) :
    tokenWord n box (Runtime.push x xs) t = tokenWord n box (x::xs) t := by
  cases x with
  | box x => rfl
  | run b a c =>
    cases a with
    | zero =>
      cases c with
      | zero => simp [Runtime.push,tokenWord]
      | succ c =>
        cases xs with
        | nil => rfl
        | cons y ys =>
          cases y with
          | box x => rfl
          | run b' a' c' =>
            by_cases h : b=b'
            · subst b'
              simp only [Runtime.push,beq_self_eq_true,↓reduceIte,tokenWord,
                Nat.cast_add,Nat.cast_zero,zero_mul,zero_add]
              simp only [Nat.cast_one]
              rw [show (a' : V)*n+((c : V)+1+c') =
                ((c : V)+1)+((a' : V)*n+c') by ring1,repeat_add]
            · simp [Runtime.push,h,tokenWord]
    | succ a =>
      cases xs with
      | nil => rfl
      | cons y ys =>
        cases y with
        | box x => rfl
        | run b' a' c' =>
          by_cases h : b=b'
          · subst b'
            simp only [Runtime.push,beq_self_eq_true,↓reduceIte,tokenWord,Nat.cast_add]
            exact repeat_affine_merge _ _ _ _ _ _ _
          · simp [Runtime.push,h,tokenWord]

theorem word_norm (n : V) (box : BoxSt → V → V) (xs : List Seg) (t : V) :
    tokenWord n box (Runtime.norm xs) t = word n box xs t := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    change tokenWord n box (Runtime.push (Runtime.tokOf x) (Runtime.norm xs)) t = _
    rw [token_push]
    cases x with
    | bit b =>
      simp only [Runtime.tokOf,tokenWord,word,Nat.cast_zero,Nat.cast_one,zero_mul,zero_add]
      rw [ih]
      simpa using (repeat_succ (0 : V) b.toNat (word n box xs t))
    | run b a c =>
      change repeatBits ((a : V)*n+c) b.toNat (tokenWord n box (Runtime.norm xs) t) = _
      rw [ih]
      rfl
    | box x =>
      change box x (tokenWord n box (Runtime.norm xs) t) = _
      rw [ih]
      rfl
/-- Dropping a final zero run preserves the complete arithmetic tape word;
this is exactly the left-tail normalization used by Runtime.sMatches. -/
theorem word_norm_left (n : V) (box : BoxSt → V → V) (xs : List Seg) :
    tokenWord n box (Runtime.normL xs) 0 = word n box xs 0 := by
  rw [← word_norm n box xs 0]
  unfold Runtime.normL
  generalize ht : Runtime.norm xs = ts
  cases hr : ts.reverse with
  | nil =>
    simp only
    simpa only [List.reverse_reverse] using congrArg (fun z => tokenWord n box z 0) (congrArg List.reverse hr).symm
  | cons x tail =>
    cases x with
    | box x =>
      simp only
      simpa only [List.reverse_reverse] using congrArg (fun z => tokenWord n box z 0) (congrArg List.reverse hr).symm
    | run b a c =>
      cases b with
      | true =>
        simp only
        simpa only [List.reverse_reverse] using congrArg (fun z => tokenWord n box z 0) (congrArg List.reverse hr).symm
      | false =>
        simp only [hr]
        have he : ts=tail.reverse++[Tok.run false a c] := by
          have h := congrArg List.reverse hr
          simpa only [List.reverse_reverse,List.reverse_cons] using h
        rw [he,token_append]
        simp [tokenWord,repeat_blank_zero]
structure ModelConf (V : Type*) where
  q : V
  left : V
  right : V
  deriving DecidableEq

noncomputable def config (n : V) (box : BoxSt → V → V) (control : Nat → V)
    (s : SConf) : ModelConf V :=
  if s.2.1 then
    ⟨control s.1, word n box s.2.2.1 0 / 2,
      (1+1)*word n box s.2.2.2 0+word n box s.2.2.1 0 % 2⟩
  else ⟨control s.1,word n box s.2.2.1 0,word n box s.2.2.2 0⟩

/-- The existing Boolean symbolic endpoint matcher is sound for every arithmetic
model interpretation. No execution or box-transition premise is hidden here. -/
theorem matches_config (n : V) (box : BoxSt → V → V) (control : Nat → V)
    (s e : SConf) (h : Runtime.sMatches s e=true) :
    config n box control s = config n box control e := by
  rcases s with ⟨q,onl,l,r⟩
  rcases e with ⟨q',onl',l',r'⟩
  simp only [Runtime.sMatches,Bool.and_eq_true,beq_iff_eq] at h
  rcases h with ⟨⟨⟨hq,hon⟩,hr⟩,hl⟩
  subst q'
  subst onl'
  have leftEq : word n box l 0=word n box l' 0 := by
    rw [← word_norm_left n box l,← word_norm_left n box l',hl]
  have rightEq : word n box r 0=word n box r' 0 := by
    rw [← word_norm n box r 0,← word_norm n box r' 0,hr]
  simp only [config,leftEq,rightEq]
end Models
#print axioms token_push
#print axioms word_norm
#print axioms word_norm_left
#print axioms matches_config
end PA196.Arithmetic.Machine.PA.InternalTrace.Symbolic

