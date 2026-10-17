import ZFCinPA.ModelCodedDecoderPropositional254
import BusyBeaver.ZFC.ArithmeticTemplates254

set_option autoImplicit false

/-!
Interpret the original C254 propositional axiom in every IΣ1 model.
The numerical implication alias at (0,0) is handled by provable equivalence,
not by treating the decoder as an injective syntax homomorphism. The finite
classical proof uses the actual internal Tait proof calculus.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderPropositional254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def decoded (n : V) : Formula V ℒₛₑₜ := ⟨decode n,decode_isFormula n⟩
@[simp] theorem decoded_val (n : V) : (decoded n).val = decode n := rfl

theorem decoded_imp_equiv (T : Theory ℒₛₑₜ) [T.Δ₁] (a b : V) :
    T.internalize V ⊢ decoded (4*cantor a b) 🡘 (decoded a 🡒 decoded b) := by
  classical
  by_cases h : a = 0 ∧ b = 0
  · rcases h with ⟨rfl,rfl⟩
    have hz : 4*cantor (0 : V) 0 = 0 := (impCode_zero_iff 0 0).mpr ⟨rfl,rfl⟩
    rw [hz]
    apply E!_intro
    · exact C!_of_conseq! (show T.internalize V ⊢ decoded (0 : V) 🡒 decoded 0 from ⟨C_id⟩)
    · exact C!_of_conseq! ((tprovable_iff_provable).mpr (decodedProvable_zero T))
  · have he : decoded (4*cantor a b) = decoded a 🡒 decoded b := by
      apply LO.FirstOrder.Arithmetic.Bootstrapping.Semiformula.ext
      exact decode_imp a b h
    rw [he]
    exact ⟨E_Id⟩

theorem decoded_imp_congr (T : Theory ℒₛₑₜ) [T.Δ₁] (a b : V)
    (p q : Formula V ℒₛₑₜ)
    (ha : T.internalize V ⊢ decoded a 🡘 p)
    (hb : T.internalize V ⊢ decoded b 🡘 q) :
    T.internalize V ⊢ decoded (4*cantor a b) 🡘 (p 🡒 q) :=
  E!_trans (decoded_imp_equiv T a b) (ECC!_of_E!_of_E! ha hb)

/-- A fixed classical proof. Under f:(c→u)→a and g:a→c, compose g with f
and apply Peirce at c,u. The remaining antecedent b is unused. -/
noncomputable def rho8Template (T : Theory ℒₛₑₜ) [T.Δ₁]
    (a b c u : Formula V ℒₛₑₜ) :
    T.internalize V ⊢! ((c 🡒 u) 🡒 a) 🡒 ((a 🡒 c) 🡒 (b 🡒 c)) := by
  classical
  apply FiniteContext.deduct'
  apply FiniteContext.deduct
  apply C_of_conseq
  exact (peirce (φ := c) (ψ := u)) ⨀ C_trans
    (FiniteContext.byAxm (φ := (c 🡒 u) 🡒 a) (by simp))
    (FiniteContext.byAxm (φ := a 🡒 c) (by simp))

theorem decoded_rho8_equiv (T : Theory ℒₛₑₜ) [T.Δ₁] (a b c u : V) :
    T.internalize V ⊢ decoded (ArithmeticTemplates254.rho8 a b c u) 🡘
      (((decoded c 🡒 decoded u) 🡒 decoded a) 🡒
        ((decoded a 🡒 decoded c) 🡒 (decoded b 🡒 decoded c))) := by
  simp only [ArithmeticTemplates254.rho8,ArithmeticTemplates254.rho8Circuit,
    ArithmeticTemplates254.Circuit.r8,ArithmeticTemplates254.Circuit.eval_im,
    ArithmeticTemplates254.Circuit.eval_input0,ArithmeticTemplates254.Circuit.eval_input1,
    ArithmeticTemplates254.Circuit.eval_input2,ArithmeticTemplates254.Circuit.eval_input3,
    ArithmeticCode254.wim,ArithmeticCode254.tagged,add_zero]
  apply decoded_imp_congr
  · apply decoded_imp_congr
    · exact decoded_imp_equiv T c u
    · exact ⟨E_Id⟩
  · apply decoded_imp_congr
    · exact decoded_imp_equiv T a c
    · exact decoded_imp_equiv T b c

theorem decoded_rho8_provable (T : Theory ℒₛₑₜ) [T.Δ₁] (a b c u : V) :
    Provable T (decode (ArithmeticTemplates254.rho8 a b c u)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! (decoded_rho8_equiv T a b c u)).mpr
    ⟨rho8Template T (decoded a) (decoded b) (decoded c) (decoded u)⟩

end LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
