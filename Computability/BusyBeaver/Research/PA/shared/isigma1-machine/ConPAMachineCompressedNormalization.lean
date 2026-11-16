import ConPAMachineCompressedExecutor

/-! Interpretation of normalized compressed tapes and endpoint matches. -/

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace ConPA.Machine.Compressed
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open SetTheory.BusyBeaver.ZFC.ArithmeticTapePrefix254
open M6.Runtime

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem bitPrefix_append (b : Bool) (n m tail : V) :
    bitPrefix b (n+m) tail = bitPrefix b n (bitPrefix b m tail) := by
  cases b with
  | false => simp only [bitPrefix,Bool.false_eq_true,if_false,exp_add,mul_assoc]
  | true =>
    simp only [bitPrefix,if_true]
    have h : onesPrefix (n+m) tail + 1 = onesPrefix n (onesPrefix m tail) + 1 := by
      rw [onesPrefix_add_one,onesPrefix_add_one,onesPrefix_add_one,exp_add,mul_assoc]
    exact add_right_cancel h

theorem blankPrefix (n : V) : bitPrefix false n 0 = 0 := by simp [bitPrefix]

theorem packBits (gap : V) (box : BoxSt → V) (bits : List Bool) (rest : List Seg) :
    packSegments gap box (bits.map Seg.bit ++ rest) =
      bits.foldr push (packSegments gap box rest) := by
  induction bits with
  | nil => rfl
  | cons b bits ih =>
    simp only [List.map_cons,List.cons_append,List.foldr_cons,packSegments,ih]

noncomputable def foldToken (gap : V) (box : BoxSt → V) (tok : Tok) (tail : V) : V :=
  match tok with
  | .run b a c => bitPrefix b (runLength gap a c) tail
  | .box x => box x

noncomputable def packTokens (gap : V) (box : BoxSt → V) (ts : List Tok) : V :=
  ts.foldr (foldToken gap box) 0

theorem lengthAdd (gap : V) (a c a' c' : Nat) :
    runLength gap (a+a') (c+c') = runLength gap a c + runLength gap a' c' := by
  simp only [runLength,Nat.cast_add,add_mul]
  ac_rfl

theorem lengthOne (gap : V) : runLength gap 0 1 = (1 : V) := by simp [runLength]

theorem packPush (gap : V) (box : BoxSt → V) (tok : Tok) (ts : List Tok) :
    packTokens gap box (M6.Runtime.push tok ts) =
      foldToken gap box tok (packTokens gap box ts) := by
  cases tok with
  | box x => rfl
  | run b a c =>
    cases a with
    | zero =>
      cases c with
      | zero => simp only [M6.Runtime.push,foldToken,lengthZero,bitPrefix_zero]
      | succ c =>
        cases ts with
        | nil => rfl
        | cons t ts =>
          cases t with
          | box x => rfl
          | run b' a' c' =>
            by_cases h : b = b'
            · subst b'
              simp only [M6.Runtime.push,if_pos True.intro,packTokens,List.foldr_cons,foldToken,lengthAdd,bitPrefix_append]
            · simp only [M6.Runtime.push,if_neg h,packTokens,List.foldr_cons]
    | succ a =>
      cases ts with
      | nil => rfl
      | cons t ts =>
        cases t with
        | box x => rfl
        | run b' a' c' =>
          by_cases h : b = b'
          · subst b'
            simp only [M6.Runtime.push,if_pos True.intro,packTokens,List.foldr_cons,foldToken,lengthAdd,bitPrefix_append]
          · simp only [M6.Runtime.push,if_neg h,packTokens,List.foldr_cons]

theorem normCorrect (gap : V) (box : BoxSt → V) (s : List Seg) :
    packTokens gap box (norm s) = packSegments gap box s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    rw [show norm (x::xs) = M6.Runtime.push (tokOf x) (norm xs) by rfl,packPush,ih]
    cases x with
    | bit b =>
      simp only [tokOf,foldToken,packSegments,lengthOne]
      simpa only [zero_add,bitPrefix_zero,push] using
        bitPrefix_succ b (0 : V) (packSegments gap box xs)
    | run => rfl
    | box => rfl

theorem dropFinalBlanks (gap : V) (box : BoxSt → V) (ts : List Tok) (a c : Nat) :
    packTokens gap box (ts ++ [.run false a c]) = packTokens gap box ts := by
  simp only [packTokens,List.foldr_append,List.foldr_cons,List.foldr_nil,foldToken,blankPrefix]

theorem normLCorrect (gap : V) (box : BoxSt → V) (s : List Seg) :
    packTokens gap box (normL s) = packSegments gap box s := by
  rw [← normCorrect]
  unfold normL
  cases hr : (norm s).reverse with
  | nil =>
    have hs := congrArg List.reverse hr
    exact congrArg (packTokens gap box) (by simpa using hs)
  | cons tok ts =>
    have hs : norm s = ts.reverse ++ [tok] := by
      have h := congrArg List.reverse hr
      simpa [List.reverse_cons] using h
    cases tok with
    | box x => simp only [List.reverse_cons,←hs]
    | run b a c =>
      cases b with
      | true => simp only [List.reverse_cons,←hs]
      | false => rw [hs,dropFinalBlanks]

/-- The runtime checker can compare normalized endpoints in arbitrary IΣ₁ models. -/
theorem matchesCorrect (label : Nat → Nat) (gap : V) (box : BoxSt → V) (s t : SConf)
    (h : sMatches s t = true) : encode label gap box s = encode label gap box t := by
  rcases s with ⟨q,onl,l,r⟩
  rcases t with ⟨q',onl',l',r'⟩
  have hm : ((q = q' ∧ onl = onl') ∧ norm r = norm r') ∧ normL l = normL l' := by
    simpa only [sMatches, Bool.and_eq_true, beq_iff_eq] using h
  obtain ⟨⟨⟨rfl,rfl⟩,hr⟩,hl⟩ := hm
  have heR : packSegments gap box r = packSegments gap box r' := by
    rw [← normCorrect gap box r,← normCorrect gap box r',hr]
  have heL : packSegments gap box l = packSegments gap box l' := by
    rw [← normLCorrect gap box l,← normLCorrect gap box l',hl]
  cases onl <;> simp only [encode,heR,heL]

/-- A successful comparison against a specified symbolic endpoint proves a
positive arithmetic-time run to its interpretation. -/
theorem checkedMatch {T : Table} {machine : M6.Zip.TMN} {label : Nat → Nat}
    (hr : RowAgreement T machine label) (gap : V) {br : Branch} {box : BoxSt → V}
    (hb : BoxAgreement T label br box) (fuel : Nat) (start finish : SConf)
    (h : (exec machine br (fun s => sMatches s finish) fuel start false).isSome = true) :
    Reach1 T (encode label gap box start) (encode label gap box finish) := by
  cases he : exec machine br (fun s => sMatches s finish) fuel start false with
  | none => simp [he] at h
  | some result =>
    obtain ⟨hm,_,hp⟩ := checkedRun hr gap hb (fun s => sMatches s finish) fuel start result false he
    rw [←matchesCorrect label gap box result finish hm]
    exact hp rfl

#print axioms checkedMatch
#print axioms normCorrect
#print axioms normLCorrect
#print axioms matchesCorrect
end models
end ConPA.Machine.Compressed
