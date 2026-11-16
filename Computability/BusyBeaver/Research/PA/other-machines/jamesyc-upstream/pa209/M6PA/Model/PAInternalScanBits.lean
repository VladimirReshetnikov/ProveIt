module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import M6PA.Model.PAInternalTracePrepend
public import M6PA.Model.PAInternalTraceRows
@[expose] public section

/-! Explicit arithmetic coding of arbitrary repeated binary bits. This is not
Foundation's HFS list encoding; HFS sequences encode the resulting run. -/
namespace M6.Arithmetic.PA.InternalTrace.ScanBits
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding

def blueprint : PR.Blueprint 2 where
  zero := .mkSigma “z b t. z = t”
  succ := .mkSigma “z prev i b t. z = (1+1)*prev+b”

section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def construction : PR.Construction V blueprint where
  zero p := p 1
  succ p _ z := (1+1)*z+p 0
  zero_defined := .mk fun v => by simp [blueprint]
  succ_defined := .mk fun v => by simp [blueprint]

noncomputable def repeatBits (n b t : V) : V := construction.result ![b,t] n

def repeatGraph : 𝚺ᴬ₁.Semisentence 4 := blueprint.resultDef

@[simp] theorem repeat_zero (b t : V) : repeatBits 0 b t = t := by
  simp [repeatBits,construction]

@[simp] theorem repeat_succ (n b t : V) : repeatBits (n+1) b t = (1+1)*repeatBits n b t+b := by
  simp [repeatBits,construction]

instance repeat_defined : 𝚺ᴬ₁-Function₃ (repeatBits : V → V → V → V) via repeatGraph :=
  construction.result_defined

instance repeat_definable : 𝚺ᴬ₁-Function₃ (repeatBits : V → V → V → V) :=
  repeat_defined.to_definable

theorem repeat_commute (n b t : V) :
    repeatBits n b ((1+1)*t+b) = (1+1)*repeatBits n b t+b := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => simp only [repeat_succ,ih]

end Models
end M6.Arithmetic.PA.InternalTrace.ScanBits

