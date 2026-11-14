import PackedIterationModel
import DiophantineConsistency.PRAOpenInduction
import PackedDecoderModel
set_option autoImplicit false
namespace PA194Stepper
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PRAFiniteFunctionCodes PRALanguage PRATheory PRAAddOne PRAHistoryPairCode
open PRAModelIOpenPairing PRAOpenInduction PackedClock PackedIterationModel PackedDecoderModel

def stepperBody : Code 3 := unary encodedStep (.proj 1)
def stepper : Code 2 := .prec (.proj 0) stepperBody

def clockAgreementBody : Semiformula language Nat 1 :=
  .rel Language.ORing.Rel.eq ![.func stepper ![.bvar 0,.func (.zero 0) Fin.elim0],
    .func clock ![.bvar 0]]

theorem clockAgreementBody_open : clockAgreementBody.Open := by
  simp [clockAgreementBody, Semiformula.Open]

section models
variable {M : Type} [Nonempty M] [Structure language M] [Structure.Eq language M]
  [M↓[language] ⊧* PRA]
local instance : Zero M := ⟨Structure.func (L := language) (Code.zero 0) Fin.elim0⟩
local instance : One M := ⟨Structure.func (L := language) oneCode Fin.elim0⟩
local instance : Add M := ⟨fun x y => Structure.func (L := language) addCode ![x,y]⟩
local instance : Mul M := ⟨fun x y => Structure.func (L := language) mulCode ![x,y]⟩
local instance : LT M := ⟨fun x y => Structure.rel (L := language) Language.ORing.Rel.lt ![x,y]⟩
local notation "F" => Structure.func (L := language)

theorem modelStepperZero (x : M) :
    Structure.func (L := language) stepper
      ![Structure.func (L := language) (Code.zero 0) Fin.elim0,x] = x := by
  have h := modelBase (M := M) (Code.proj (0 : Fin 1)) stepperBody (fun _ => x)
  rw [modelProjection] at h
  have hs : Fin.cases (Structure.func (L := language) (Code.zero 0) Fin.elim0)
      (fun _ : Fin 1 => x) = ![Structure.func (L := language) (Code.zero 0) Fin.elim0,x] := by
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  exact h

theorem modelStepperSucc (t x : M) :
    Structure.func (L := language) stepper
      ![Structure.func (L := language) Code.succ (fun _ => t),x] =
    Structure.func (L := language) encodedStep
      (fun _ => Structure.func (L := language) stepper ![t,x]) := by
  have h := modelStep (M := M) (Code.proj (0 : Fin 1)) stepperBody ![t,x]
  have hs : Fin.cases (Structure.func (L := language) Code.succ (fun _ => ![t,x] 0))
      (fun i => ![t,x] i.succ) = ![Structure.func (L := language) Code.succ (fun _ => t),x] := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · rfl
    · exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hs] at h
  have hv : (fun i : Fin 1 => ![t,x] i.succ) = (fun _ => x) := by
    funext j
    exact Fin.cases rfl (fun k => Fin.elim0 k) j
  rw [hv] at h
  simp only [Matrix.cons_val_zero] at h
  change Structure.func (L := language) stepper
    ![Structure.func (L := language) Code.succ (fun _ => t),x] =
    Structure.func (L := language) stepperBody
      (Fin.cases t (Fin.cases (Structure.func (L := language) stepper ![t,x]) (fun _ => x))) at h
  rw [h, stepperBody, unary, modelComposition]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => Fin.elim0 k) j
  change Structure.func (L := language) (Code.proj 1)
      (Fin.cases t (Fin.cases (Structure.func (L := language) stepper ![t,x]) (fun _ => x))) = _
  rw [modelProjection]
  rfl
omit [Nonempty M] [M↓[language] ⊧* PRA] in
theorem clockAgreementBody_eval (t : M) (e : Nat → M) : clockAgreementBody.Eval ![t] e ↔
    Structure.func (L := language) stepper ![t,Structure.func (L := language) (Code.zero 0) Fin.elim0] =
      Structure.func (L := language) clock (fun _ => t) := by
  change Semiformula.EvalAux (inferInstance : Structure language M) e ![t] clockAgreementBody ↔ _
  simp only [clockAgreementBody, Semiformula.EvalAux, eqRel, Matrix.cons_val_zero, Matrix.cons_val_one]
  have hz (v : Fin 1 → M) : (Semiterm.val v e ∘ (Fin.elim0 : Fin 0 → Semiterm language Nat 1)) =
      (Fin.elim0 : Fin 0 → M) := Subsingleton.elim _ _
  simp [Semiterm.val_func, Semiterm.val_bvar, Matrix.fun_eq_vec_one, hz]

/-- Starting the arbitrary-configuration iterator from the packed blank
configuration agrees with the original clock at every model time. -/
theorem modelStepperBlank (t : M) :
    Structure.func (L := language) stepper ![t,Structure.func (L := language) (Code.zero 0) Fin.elim0] =
      Structure.func (L := language) clock (fun _ => t) := by
  let z : M := Structure.func (L := language) (Code.zero 0) Fin.elim0
  let e : Nat → M := fun _ => t
  apply (clockAgreementBody_eval t e).mp
  apply modelOpenInduction (M := M) clockAgreementBody clockAgreementBody_open e
  · apply (clockAgreementBody_eval z e).mpr
    rw [modelStepperZero, modelClockZero]
  · intro x hx
    apply (clockAgreementBody_eval (Structure.func (L := language) Code.succ (fun _ => x)) e).mpr
    rw [modelStepperSucc, modelClockSucc, (clockAgreementBody_eval x e).mp hx]

/-- Decoder correctness makes the stepper valid for any encoded model start
and any model time, including nonstandard inputs. -/
theorem modelStepperDecodedSucc (t x : M) :
    letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
    let n := F stepper ![t,x]
    let n' := F stepper ![F Code.succ (fun _ => t),x]
    (F decodeLeft (fun _ => n'), F decodeLeft (fun _ => F decodeRight (fun _ => n')),
      F decodeRight (fun _ => F decodeRight (fun _ => n'))) =
      ConfigurationStep.stepSem (pi₁ n) (pi₁ (pi₂ n)) (pi₂ (pi₂ n)) := by
  letI : M↓[ℒₒᵣ] ⊧* 𝗜𝗢𝗽𝗲𝗻 := standardModelIOpen
  dsimp only
  rw [modelStepperSucc, modelEncodedStepAny]
  simp only [modelDecodeLeft, modelDecodeRight, modelPairCode, pi₁_pair, pi₂_pair]

#print axioms modelStepperDecodedSucc

#print axioms modelStepperBlank

#print axioms modelStepperZero
#print axioms modelStepperSucc
end models
end PA194Stepper
