import ZFCinPA.ModelCodedDecoderEquality254
import ZFCinPA.ModelCodedDecoderAtomicVacuity254
import BusyBeaver.ZFC.ArithmeticTemplates222

set_option autoImplicit false
noncomputable section

/-! # The changed C222 equality row is internally provable

`growG a b c = (c=a) → ((c=b) → ∀_{wel a b} (a=b))`. In every model of `𝗜𝚺₁`
and every internal labels `a,b,c`, its decoded formula is provable in any
theory containing equality: the C254 equality row `rho7` gives
`(c=a) → (c=b) → a=b`, and the binder `wel a b = 4·cantor(a,b)+1` differs
from both labels, so `a=b` implies its vacuous generalization.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderGrowG222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
open LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor ArithmeticCode254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma cantor_lt_wel (a b : V) : cantor a b < wel a b := by
  unfold wel tagged
  calc cantor a b ≤ 4 * cantor a b := le_mul_of_one_le_left (by simp) (by norm_num)
    _ < 4 * cantor a b + 1 := by simp

lemma wel_ne_left (a b : V) : wel a b ≠ a := by
  intro he
  have h2 := cantor_lt_wel a b
  rw [he] at h2
  exact _root_.lt_irrefl _ (lt_of_le_of_lt (components_le a b).1 h2)

lemma wel_ne_right (a b : V) : wel a b ≠ b := by
  intro he
  have h2 := cantor_lt_wel a b
  rw [he] at h2
  exact _root_.lt_irrefl _ (lt_of_le_of_lt (components_le a b).2 h2)

variable (T : SetTheory) [T.Δ₁] [𝗘𝗤 ℒₛₑₜ ⪯ T]

/-- **The decoded changed equality row is provable from equality alone.** -/
theorem decoded_growG_provable (a b c : V) :
    Provable T (decode (ArithmeticTemplates222.growG a b c)) := by
  classical
  let v := wel a b
  have hv := decoded_weq_vacuity T a b v (wel_ne_left a b) (wel_ne_right a b)
  have hvt : T.internalize V ⊢ decoded (weq a b) 🡒 decoded (wal v (weq a b)) := by
    have h := (tprovable_iff_provable (σ := decoded (wim (weq a b) (wal v (weq a b))))).mpr hv
    simp only [wim, tagged, add_zero] at h
    exact (iff_of_E! (decoded_imp_equiv T (weq a b) (wal v (weq a b)))).mp h
  have h7 : T.internalize V ⊢ decoded (weq c a) 🡒 (decoded (weq c b) 🡒 decoded (weq a b)) := by
    rw [decoded_weq, decoded_weq, decoded_weq]
    exact rho7Template T a b c
  have hgoal : T.internalize V ⊢
      decoded (weq c a) 🡒 (decoded (weq c b) 🡒 decoded (wal v (weq a b))) := by
    cl_prover [h7, hvt]
  have he : T.internalize V ⊢ decoded (ArithmeticTemplates222.growG a b c) 🡘
      (decoded (weq c a) 🡒 (decoded (weq c b) 🡒 decoded (wal v (weq a b)))) := by
    rw [ArithmeticTemplates222.growG_eq]
    simp only [wim, tagged, add_zero]
    apply decoded_imp_congr T
    · exact ⟨E_Id⟩
    · apply decoded_imp_congr T
      · exact ⟨E_Id⟩
      · exact ⟨E_Id⟩
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! he).mpr hgoal

end LeanProofs.ZFCinPA.ModelCodedDecoderGrowG222
