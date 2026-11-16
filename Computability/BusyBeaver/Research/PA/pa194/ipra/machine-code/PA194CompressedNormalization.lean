import PA194CompressedTape
import PA194CompressedRunAlgebra

set_option autoImplicit false
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option linter.unusedSectionVars false

namespace PA194CompressedNormalization
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic LO.FirstOrder
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAExhaustion
open PA194StateOne PA194FiniteControls TableDispatch PA194BidirectionalRow
open PA194BidirectionalRunScan PA194CompressedTape PA194CompressedRunAlgebra
open M6.Runtime

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M] [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)
local instance : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen

noncomputable def foldToken (gap : M) (box : BoxSt → M) (tok : Tok) (tail : M) : M :=
  match tok with
  | .run b a c => F (runCode b) ![runLength gap a c,tail]
  | .box x => box x

noncomputable def packTokens (gap : M) (box : BoxSt → M) (ts : List Tok) : M :=
  ts.foldr (foldToken gap box) 0

theorem lengthAdd (gap : M) (a c a' c' : Nat) :
    runLength gap (a+a') (c+c') = runLength gap a c + runLength gap a' c' := by
  simp only [runLength,modelNumeralAdd,add_mul]
  ac_rfl

theorem lengthOne (gap : M) : runLength gap 0 1 = (1 : M) := by
  unfold runLength
  rw [modelNumeralOne]
  change (0 : M)*gap+1 = 1
  simp

theorem packPush (gap : M) (box : BoxSt → M) (tok : Tok) (ts : List Tok) :
    packTokens gap box (M6.Runtime.push tok ts) =
      foldToken gap box tok (packTokens gap box ts) := by
  cases tok with
  | box x => rfl
  | run b a c =>
    cases a with
    | zero =>
      cases c with
      | zero => simp only [M6.Runtime.push,foldToken,lengthZero,runZero]
      | succ c =>
        cases ts with
        | nil => rfl
        | cons t ts =>
          cases t with
          | box x => rfl
          | run b' a' c' =>
            by_cases h : b = b'
            · subst b'
              simp only [M6.Runtime.push,if_pos True.intro,packTokens,List.foldr_cons,foldToken,lengthAdd,runAppend]
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
            simp only [M6.Runtime.push,if_pos True.intro,packTokens,List.foldr_cons,foldToken,lengthAdd,runAppend]
          · simp only [M6.Runtime.push,if_neg h,packTokens,List.foldr_cons]

theorem normCorrect (gap : M) (box : BoxSt → M) (s : List Seg) :
    packTokens gap box (norm s) = packSegments gap box s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
    rw [show norm (x::xs) = M6.Runtime.push (tokOf x) (norm xs) by rfl,packPush,ih]
    cases x with
    | bit b =>
      simp only [tokOf,foldToken,packSegments,lengthOne]
      have h : (1 : M) = (0 : M)+1 := (zero_add 1).symm
      conv_lhs => rw [h, runSucc,runZero]
    | run => rfl
    | box => rfl

theorem dropFinalBlanks (gap : M) (box : BoxSt → M) (ts : List Tok) (a c : Nat) :
    packTokens gap box (ts ++ [.run false a c]) = packTokens gap box ts := by
  simp only [packTokens,List.foldr_append,List.foldr_cons,List.foldr_nil,foldToken,blankRun]

theorem normLCorrect (gap : M) (box : BoxSt → M) (s : List Seg) :
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

/-- The runtime checker can compare normalized endpoints in arbitrary PRA models. -/
theorem matchesCorrect (label : Nat → Nat) (gap : M) (box : BoxSt → M) (s t : SConf)
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

#print axioms normCorrect
#print axioms normLCorrect
#print axioms matchesCorrect
end models
end PA194CompressedNormalization
