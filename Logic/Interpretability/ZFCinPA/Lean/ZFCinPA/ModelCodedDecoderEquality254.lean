import ZFCinPA.ModelCodedDecoderLukasiewicz254
import ZFCinPA.SetCongruence

set_option autoImplicit false

/-!
The three equality rows of actual C254, at arbitrary internal variable labels.
Each fixed closed equality theorem is proved in the ordinary set language,
then internalized before its three bound slots are specialized. Only those
fixed standard templates are quoted; the internal labels are never quoted.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def eqAtom {n : Nat} (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    Bootstrapping.Semiformula V ℒₛₑₜ n :=
  Bootstrapping.Semiformula.rel Language.Set.Rel.eq ![t,u]
noncomputable def memAtom {n : Nat} (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    Bootstrapping.Semiformula V ℒₛₑₜ n :=
  Bootstrapping.Semiformula.rel Language.Set.Rel.mem ![t,u]

lemma quote_vec2 {n : Nat} (t u : SyntacticSemiterm ℒₛₑₜ n) :
    (fun i => (⌜(![t,u]) i⌝ : Bootstrapping.Semiterm V ℒₛₑₜ n)) = ![⌜t⌝,⌜u⌝] :=
  SetCongruence.quote_vec2_eta t u

local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ)
local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := ℒₛₑₜ)

lemma decoded_weq (a b : V) :
    decoded (ArithmeticCode254.weq a b) = eqAtom (&'a) (&'b) := by
  apply Bootstrapping.Semiformula.ext
  rw [decoded_val]
  change decode (4*cantor a b+3) = _
  rw [decode_eq]
  simp [eqAtom,Bootstrapping.Semiformula.rel,atomCode]
  rfl

lemma decoded_wel (a b : V) :
    decoded (ArithmeticCode254.wel a b) = memAtom (&'a) (&'b) := by
  apply Bootstrapping.Semiformula.ext
  rw [decoded_val]
  change decode (4*cantor a b+1) = _
  rw [decode_mem]
  simp [memAtom,Bootstrapping.Semiformula.rel,atomCode]
  change (1 : V) = ((1 : Nat) : V)
  simp

variable (T : SetTheory) [T.Δ₁] [𝗘𝗤 ℒₛₑₜ ⪯ T]

theorem rho7Template (a b c : V) :
    T.internalize V ⊢ eqAtom (&'c) (&'a) 🡒 (eqAtom (&'c) (&'b) 🡒 eqAtom (&'a) (&'b)) := by
  have hs := SetCongruence.subst_eq T (&'c) (&'a) (&'c) (&'b)
  have hr := SetCongruence.set_eq_refl T (&'c)
  change T.internalize V ⊢ eqAtom (&'c) (&'a) 🡒 eqAtom (&'c) (&'b) 🡒
    eqAtom (&'c) (&'c) 🡒 eqAtom (&'a) (&'b) at hs
  change T.internalize V ⊢ eqAtom (&'c) (&'c) at hr
  classical
  cl_prover [hs,hr]

omit [𝗘𝗤 ℒₛₑₜ ⪯ T] in
theorem decoded_rho7_equiv (a b c : V) :
    T.internalize V ⊢ decoded (ArithmeticTemplates254.rho7 a b c) 🡘
      (eqAtom (&'c) (&'a) 🡒 (eqAtom (&'c) (&'b) 🡒 eqAtom (&'a) (&'b))) := by
  simp only [ArithmeticTemplates254.rho7,ArithmeticTemplates254.rho7Circuit,
    ArithmeticTemplates254.Circuit.r7,ArithmeticTemplates254.Circuit.eval_im,
    ArithmeticTemplates254.Circuit.eval_eq,
    ArithmeticTemplates254.Circuit.eval_input0,ArithmeticTemplates254.Circuit.eval_input1,
    ArithmeticTemplates254.Circuit.eval_input2,ArithmeticCode254.wim,
    ArithmeticCode254.tagged,add_zero]
  apply decoded_imp_congr
  · rw [decoded_weq]; exact ⟨E_Id⟩
  · apply decoded_imp_congr <;> rw [decoded_weq] <;> exact ⟨E_Id⟩

theorem decoded_rho7_provable (a b c : V) :
    Provable T (decode (ArithmeticTemplates254.rho7 a b c)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! (decoded_rho7_equiv T a b c)).mpr (rho7Template T a b c)

theorem rho5Template (a b c : V) :
    T.internalize V ⊢ eqAtom (&'c) (&'a) 🡒 (memAtom (&'c) (&'b) 🡒 memAtom (&'a) (&'b)) := by
  have hs := SetCongruence.subst_mem T (&'c) (&'a) (&'b) (&'b)
  have hr := SetCongruence.set_eq_refl T (&'b)
  change T.internalize V ⊢ eqAtom (&'c) (&'a) 🡒 eqAtom (&'b) (&'b) 🡒
    memAtom (&'c) (&'b) 🡒 memAtom (&'a) (&'b) at hs
  change T.internalize V ⊢ eqAtom (&'b) (&'b) at hr
  classical
  cl_prover [hs,hr]

omit [𝗘𝗤 ℒₛₑₜ ⪯ T] in
theorem decoded_rho5_equiv (a b c : V) :
    T.internalize V ⊢ decoded (ArithmeticTemplates254.rho5 a b c) 🡘
      (eqAtom (&'c) (&'a) 🡒 (memAtom (&'c) (&'b) 🡒 memAtom (&'a) (&'b))) := by
  simp only [ArithmeticTemplates254.rho5,ArithmeticTemplates254.rho5Circuit,
    ArithmeticTemplates254.Circuit.r5,ArithmeticTemplates254.Circuit.eval_im,
    ArithmeticTemplates254.Circuit.eval_eq,ArithmeticTemplates254.Circuit.eval_el,
    ArithmeticTemplates254.Circuit.eval_input0,ArithmeticTemplates254.Circuit.eval_input1,
    ArithmeticTemplates254.Circuit.eval_input2,ArithmeticCode254.wim,
    ArithmeticCode254.tagged,add_zero]
  apply decoded_imp_congr
  · rw [decoded_weq]; exact ⟨E_Id⟩
  · apply decoded_imp_congr <;> rw [decoded_wel] <;> exact ⟨E_Id⟩

theorem decoded_rho5_provable (a b c : V) :
    Provable T (decode (ArithmeticTemplates254.rho5 a b c)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! (decoded_rho5_equiv T a b c)).mpr (rho5Template T a b c)

theorem rho3Template (a b c : V) :
    T.internalize V ⊢ eqAtom (&'a) (&'b) 🡒 (memAtom (&'c) (&'a) 🡒 memAtom (&'c) (&'b)) := by
  have hs := SetCongruence.subst_mem T (&'c) (&'c) (&'a) (&'b)
  have hr := SetCongruence.set_eq_refl T (&'c)
  change T.internalize V ⊢ eqAtom (&'c) (&'c) 🡒 eqAtom (&'a) (&'b) 🡒
    memAtom (&'c) (&'a) 🡒 memAtom (&'c) (&'b) at hs
  change T.internalize V ⊢ eqAtom (&'c) (&'c) at hr
  classical
  cl_prover [hs,hr]

omit [𝗘𝗤 ℒₛₑₜ ⪯ T] in
theorem decoded_rho3_equiv (a b c : V) :
    T.internalize V ⊢ decoded (ArithmeticTemplates254.rho3 a b c) 🡘
      (eqAtom (&'a) (&'b) 🡒 (memAtom (&'c) (&'a) 🡒 memAtom (&'c) (&'b))) := by
  simp only [ArithmeticTemplates254.rho3,ArithmeticTemplates254.rho3Circuit,
    ArithmeticTemplates254.Circuit.r3,ArithmeticTemplates254.Circuit.eval_im,
    ArithmeticTemplates254.Circuit.eval_eq,ArithmeticTemplates254.Circuit.eval_el,
    ArithmeticTemplates254.Circuit.eval_input0,ArithmeticTemplates254.Circuit.eval_input1,
    ArithmeticTemplates254.Circuit.eval_input2,ArithmeticCode254.wim,
    ArithmeticCode254.tagged,add_zero]
  apply decoded_imp_congr
  · rw [decoded_weq]; exact ⟨E_Id⟩
  · apply decoded_imp_congr <;> rw [decoded_wel] <;> exact ⟨E_Id⟩

theorem decoded_rho3_provable (a b c : V) :
    Provable T (decode (ArithmeticTemplates254.rho3 a b c)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! (decoded_rho3_equiv T a b c)).mpr (rho3Template T a b c)

end LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
