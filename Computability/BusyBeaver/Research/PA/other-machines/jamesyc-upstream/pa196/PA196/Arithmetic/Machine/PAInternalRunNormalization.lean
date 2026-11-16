module
/- M6 PA-model runtime port. This is a fresh append-one/table adaptation;
its theorem scope is not the completed PA-unprovability endpoint. -/
public import PA196.Arithmetic.Machine.PAInternalScanBits
public import Mathlib.Tactic.Ring.Basic
@[expose] public section
namespace PA196.Arithmetic.Machine.PA.InternalTrace.ScanBits
open M6
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic FFL.Entailment
open scoped FFL.FirstOrder.Arithmetic
section Models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
/-- Model-valued induction, not recursion on standard Lean naturals. -/
theorem repeat_add (n m b t : V) :
    repeatBits (n+m) b t = repeatBits n b (repeatBits m b t) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    rw [show n+1+m=(n+m)+1 by ring1]
    simp only [repeat_succ,ih]

theorem repeat_blank_zero (n : V) : repeatBits n 0 0=0 := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih => simp [ih]

/-- The exact affine run merge performed by Runtime.push/norm. -/
theorem repeat_affine_merge (a c a' c' n b t : V) :
    repeatBits ((a+a')*n+(c+c')) b t =
      repeatBits (a*n+c) b (repeatBits (a'*n+c') b t) := by
  rw [show (a+a')*n+(c+c')=(a*n+c)+(a'*n+c') by ring1,repeat_add]
end Models

def runNormalizationSentence : ArithmeticSentence :=
  “∀ n m b t, ∃ x y z, !repeatGraph x m b t ∧ !repeatGraph y n b x ∧
    !repeatGraph z (n+m) b t ∧ z=y”
theorem pa_proves_run_normalization : theory ⊢ runNormalizationSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [runNormalizationSentence,models_iff]
  simp [repeat_defined.df]
  exact repeat_add

def blankNormalizationSentence : ArithmeticSentence :=
  “∀ n, !repeatGraph 0 n 0 0”
theorem pa_proves_blank_normalization : theory ⊢ blankNormalizationSentence := by
  apply Arithmetic.complete.{0} theory _
  intro V _ _
  simp only [blankNormalizationSentence,models_iff]
  simp [repeat_defined.df]
  intro n
  exact (repeat_blank_zero n).symm
#print axioms repeat_add
#print axioms repeat_blank_zero
#print axioms repeat_affine_merge
#print axioms pa_proves_run_normalization
#print axioms pa_proves_blank_normalization
end PA196.Arithmetic.Machine.PA.InternalTrace.ScanBits

