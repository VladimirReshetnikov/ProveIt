import PA194ReturnFile
import PA194UnaryRuns
import PA194State59Even
import PA194RightRows
import PA194ZeroRuns
import PA194Stepper
/-! The all-model two-step state-42 split and its returned-prefix even-tail link. -/
set_option autoImplicit false
namespace PA194State42Boundary
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open BinaryTapeCodes PA194UnaryRuns PA194ZeroRuns PA194BinaryDouble PA194RightRows
open PA194State59Even PA194StateOne PA194ReturnFile PackedIterationModel ConfigurationStep
open PRAExhaustion PRAModelIOpenPairing TableDispatch
section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem packed42zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 42,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 59,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightZero 42 0 59 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem packed59one (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 59,F pairCode ![l,r+r+1]]) =
    F pairCode ![modelNumeral M 1,F pairCode ![l+l,r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  have h := rightOne 59 0 1 (by decide) (by decide +kernel) l r
  simpa only [show modelNumeral M 0 = (0 : M) from rfl,add_zero] using h

theorem packed59zero (l r : M) :
    F PackedClock.encodedStep (fun _ => F pairCode ![modelNumeral M 59,F pairCode ![l,r+r]]) =
    F pairCode ![modelNumeral M 84,F pairCode ![F halfCode (fun _ => l),F parityCode (fun _ => l)+(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  rw [modelEncodedStepAny]
  simp only [modelPairCode,pi₁_pair,pi₂_pair]
  have hm := modelNext (![modelNumeral M 59,l,r+r] : Fin 3 → M)
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two] at hm
  change (F nextQ ![modelNumeral M 59,l,r+r],F nextL ![modelNumeral M 59,l,r+r],
    F nextR ![modelNumeral M 59,l,r+r]) = stepSem (modelNumeral M 59) l (r+r) at hm
  rw [←hm,model59Even]

theorem twoPositive (l r : M) :
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 42,F pairCode ![l,(r+r+1)+(r+r+1)]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![(l+l)+(l+l),r]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
    show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
    PA194Stepper.modelStepperSucc,
    show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
    PA194Stepper.modelStepperZero,packed42zero,packed59one]
  rw [←show modelNumeral M 1 = F Code.succ (fun _ => F (Code.zero 0) Fin.elim0) from rfl]

theorem twoZero (l r : M) :
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 42,F pairCode ![l,(r+r)+(r+r)]]] =
    F pairCode ![modelNumeral M 84,F pairCode ![l,(r+r)+(r+r)]] := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  change F PA194Stepper.stepper ![F Code.succ (fun _ => modelNumeral M 1),_] = _
  rw [PA194Stepper.modelStepperSucc,
    show modelNumeral M 1 = F Code.succ (fun _ => modelNumeral M 0) from rfl,
    PA194Stepper.modelStepperSucc,
    show modelNumeral M 0 = F (Code.zero 0) Fin.elim0 from rfl,
    PA194Stepper.modelStepperZero,packed42zero,packed59zero,(modelDouble l).1,(modelDouble l).2,zero_add]
/-- A successor-length residual run reaches decrement entry with the exact
remaining one-run, for arbitrary model length and suffix. -/
theorem positiveRun (n l w : M) :
    let a := F ones ![n,w]
    let b := F ones ![n+1,w]
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 42,F pairCode ![l,b+b]]] =
    F pairCode ![modelNumeral M 1,F pairCode ![(l+l)+(l+l),a]] := by
  dsimp only
  have h : F ones ![n+1,w] = F ones ![n,w]+F ones ![n,w]+1 := by
    change F ones ![F addCode ![n,F oneCode Fin.elim0],w] = _
    rw [modelAddOne,modelOnesSucc]
  rw [h]
  exact twoPositive l (F ones ![n,w])

/-- An empty residual run and an even tail return to dense 84 without
changing either tape half. -/
theorem zeroRun (l t : M) :
    let w := t+t
    F PA194Stepper.stepper ![modelNumeral M 2,F pairCode ![modelNumeral M 42,F pairCode ![l,F ones ![(0 : M),w]+F ones ![(0 : M),w]]]] =
    F pairCode ![modelNumeral M 84,F pairCode ![l,w+w]] := by
  dsimp only
  simp only [modelOnesZero]
  exact twoZero l t

/-- The state-42 continuation is exhaustive even for nonstandard model
lengths: zero returns to state 84, a successor enters state 1. -/
theorem runDichotomy (n l t : M) :
    let w := t+t
    let c := F pairCode ![modelNumeral M 42,F pairCode ![l,F ones ![n,w]+F ones ![n,w]]]
    (n = (0 : M) ∧ F PA194Stepper.stepper ![modelNumeral M 2,c] = F pairCode ![modelNumeral M 84,F pairCode ![l,w+w]]) ∨
    (∃ m : M, n = m+1 ∧ F PA194Stepper.stepper ![modelNumeral M 2,c] = F pairCode ![modelNumeral M 1,F pairCode ![(l+l)+(l+l),F ones ![m,w]]]) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  rcases modelZeroOrSuccPred n with hz | hs
  · left
    change n = (0 : M) at hz
    subst n
    exact ⟨rfl,zeroRun l t⟩
  · right
    let m := F predCode (fun _ => n)
    have hm : n = m+1 := by
      have hx : F Code.succ (fun _ => m) = m+1 := (modelAddOne m).symm
      exact hs.symm.trans hx
    refine ⟨m,hm,?_⟩
    rw [hm]
    exact positiveRun m l (t+t)
/-- The remainder of the non-first marking prefix is even, including
when it is the empty returned prefix. -/
theorem returnedTailEven (idx : Nat) (e : Fin (idx+2) → M) (t : M) :
    let j : Fin (idx+3) → M := Fin.cases ((t+t)+(t+t)) e
    let w := F (returnCode idx) (Fin.cases (j 0) (fun i => j i.succ.succ))
    ∃ z : M, w = z+z := by
  dsimp only
  cases idx with
  | zero =>
    rw [modelReturnCodeZero]
    refine ⟨t+t,?_⟩
    rfl
  | succ n =>
    rw [modelReturnCodeSucc]
    exact ⟨_,rfl⟩
/-- The dichotomy applies to the exact encoded remainder produced by the
non-first marker; no separate even-tail assumption is needed. -/
theorem returnedRunDichotomy (idx : Nat) (e : Fin (idx+2) → M) (n l t : M) :
    let j : Fin (idx+3) → M := Fin.cases ((t+t)+(t+t)) e
    let w := F (returnCode idx) (Fin.cases (j 0) (fun i => j i.succ.succ))
    let c := F pairCode ![modelNumeral M 42,F pairCode ![l,F ones ![n,w]+F ones ![n,w]]]
    (n = (0 : M) ∧ F PA194Stepper.stepper ![modelNumeral M 2,c] = F pairCode ![modelNumeral M 84,F pairCode ![l,w+w]]) ∨
    (∃ m : M, n = m+1 ∧ F PA194Stepper.stepper ![modelNumeral M 2,c] = F pairCode ![modelNumeral M 1,F pairCode ![(l+l)+(l+l),F ones ![m,w]]]) := by
  dsimp only
  let j : Fin (idx+3) → M := Fin.cases ((t+t)+(t+t)) e
  let w := F (returnCode idx) (Fin.cases (j 0) (fun i => j i.succ.succ))
  obtain ⟨z,hz⟩ := returnedTailEven idx e t
  change w = z+z at hz
  have hd := runDichotomy n l z
  dsimp only at hd
  rw [←hz] at hd
  exact hd
#print axioms returnedRunDichotomy
#print axioms returnedTailEven
#print axioms runDichotomy
#print axioms positiveRun
#print axioms zeroRun
#print axioms twoZero
#print axioms twoPositive
end models
end PA194State42Boundary
