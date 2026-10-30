import ZFCinPA.ModelCodedDecoderLukasiewicz254

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

private def sEq {ξ : Type*} {n : Nat} (t u : FirstOrder.Semiterm ℒₛₑₜ ξ n) :
    FirstOrder.Semiformula ℒₛₑₜ ξ n :=
  FirstOrder.Semiformula.rel Language.Set.Rel.eq ![t,u]
private def sMem {ξ : Type*} {n : Nat} (t u : FirstOrder.Semiterm ℒₛₑₜ ξ n) :
    FirstOrder.Semiformula ℒₛₑₜ ξ n :=
  FirstOrder.Semiformula.rel Language.Set.Rel.mem ![t,u]
noncomputable def eqAtom {n : Nat} (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    Bootstrapping.Semiformula V ℒₛₑₜ n :=
  Bootstrapping.Semiformula.rel Language.Set.Rel.eq ![t,u]
noncomputable def memAtom {n : Nat} (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    Bootstrapping.Semiformula V ℒₛₑₜ n :=
  Bootstrapping.Semiformula.rel Language.Set.Rel.mem ![t,u]

lemma quote_vec2 {n : Nat} (t u : SyntacticSemiterm ℒₛₑₜ n) :
    (fun i => (⌜(![t,u]) i⌝ : Bootstrapping.Semiterm V ℒₛₑₜ n)) = ![⌜t⌝,⌜u⌝] := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

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

@[simp] private lemma standard_rel_eq {M : Type*} [SetStructure M] (v : Fin 2 → M) :
    Structure.rel (L := ℒₛₑₜ) (M := M) Language.Set.Rel.eq v ↔ v 0 = v 1 := Iff.rfl
@[simp] private lemma standard_rel_mem {M : Type*} [SetStructure M] (v : Fin 2 → M) :
    Structure.rel (L := ℒₛₑₜ) (M := M) Language.Set.Rel.mem v ↔ v 0 ∈ v 1 := Iff.rfl

variable (T : SetTheory) [T.Δ₁] [𝗘𝗤 ℒₛₑₜ ⪯ T]

theorem rho7Template (a b c : V) :
    T.internalize V ⊢ eqAtom (&'c) (&'a) 🡒 (eqAtom (&'c) (&'b) 🡒 eqAtom (&'a) (&'b)) := by
  have houter : T ⊢ ∀⁰ ∀⁰ ∀⁰ (sEq #0 #2 🡒 (sEq #0 #1 🡒 sEq #2 #1)) := by
    refine SetTheory.provable_of_models.{0} T _ ?_
    intro M _ _ _
    simp [models_iff,sEq]
  have hint := internal_provable_of_outer_provable (V := V) houter
  have hq : (⌜(∀⁰ ∀⁰ ∀⁰ (sEq #0 #2 🡒 (sEq #0 #1 🡒 sEq #2 #1)) : SetTheorySentence)⌝ :
      Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ ∀⁰ ∀⁰ (eqAtom (#'0) (#'2) 🡒 (eqAtom (#'0) (#'1) 🡒 eqAtom (#'2) (#'1))) := by
    rw [FirstOrder.Sentence.typed_quote_def]
    simp [sEq,eqAtom,Rew.q_emb,Rew.emb_bvar,quote_vec2]
  rw [hq] at hint
  simpa [eqAtom,memAtom] using TProof.specialize₃! hint (&'c) (&'b) (&'a)

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
  · apply decoded_imp_congr
    · rw [decoded_weq]; exact ⟨E_Id⟩
    · rw [decoded_weq]; exact ⟨E_Id⟩

theorem decoded_rho7_provable (a b c : V) :
    Provable T (decode (ArithmeticTemplates254.rho7 a b c)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! (decoded_rho7_equiv T a b c)).mpr (rho7Template T a b c)

theorem rho5Template (a b c : V) :
    T.internalize V ⊢ eqAtom (&'c) (&'a) 🡒 (memAtom (&'c) (&'b) 🡒 memAtom (&'a) (&'b)) := by
  have houter : T ⊢ ∀⁰ ∀⁰ ∀⁰ (sEq #0 #2 🡒 (sMem #0 #1 🡒 sMem #2 #1)) := by
    refine SetTheory.provable_of_models.{0} T _ ?_
    intro M _ _ _
    simp [models_iff,sEq,sMem]
  have hint := internal_provable_of_outer_provable (V := V) houter
  have hq : (⌜(∀⁰ ∀⁰ ∀⁰ (sEq #0 #2 🡒 (sMem #0 #1 🡒 sMem #2 #1)) : SetTheorySentence)⌝ :
      Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ ∀⁰ ∀⁰ (eqAtom (#'0) (#'2) 🡒 (memAtom (#'0) (#'1) 🡒 memAtom (#'2) (#'1))) := by
    rw [FirstOrder.Sentence.typed_quote_def]
    simp [sEq,sMem,eqAtom,memAtom,Rew.q_emb,Rew.emb_bvar,quote_vec2]
  rw [hq] at hint
  simpa [eqAtom,memAtom] using TProof.specialize₃! hint (&'c) (&'b) (&'a)

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
  · apply decoded_imp_congr
    · rw [decoded_wel]; exact ⟨E_Id⟩
    · rw [decoded_wel]; exact ⟨E_Id⟩

theorem decoded_rho5_provable (a b c : V) :
    Provable T (decode (ArithmeticTemplates254.rho5 a b c)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! (decoded_rho5_equiv T a b c)).mpr (rho5Template T a b c)

theorem rho3Template (a b c : V) :
    T.internalize V ⊢ eqAtom (&'a) (&'b) 🡒 (memAtom (&'c) (&'a) 🡒 memAtom (&'c) (&'b)) := by
  have houter : T ⊢ ∀⁰ ∀⁰ ∀⁰ (sEq #2 #1 🡒 (sMem #0 #2 🡒 sMem #0 #1)) := by
    refine SetTheory.provable_of_models.{0} T _ ?_
    intro M _ _ _
    simp [models_iff,sEq,sMem]
    intro x y z h
    subst y
    exact id
  have hint := internal_provable_of_outer_provable (V := V) houter
  have hq : (⌜(∀⁰ ∀⁰ ∀⁰ (sEq #2 #1 🡒 (sMem #0 #2 🡒 sMem #0 #1)) : SetTheorySentence)⌝ :
      Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ ∀⁰ ∀⁰ (eqAtom (#'2) (#'1) 🡒 (memAtom (#'0) (#'2) 🡒 memAtom (#'0) (#'1))) := by
    rw [FirstOrder.Sentence.typed_quote_def]
    simp [sEq,sMem,eqAtom,memAtom,Rew.q_emb,Rew.emb_bvar,quote_vec2]
  rw [hq] at hint
  simpa [eqAtom,memAtom] using TProof.specialize₃! hint (&'c) (&'b) (&'a)

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
  · apply decoded_imp_congr
    · rw [decoded_wel]; exact ⟨E_Id⟩
    · rw [decoded_wel]; exact ⟨E_Id⟩

theorem decoded_rho3_provable (a b c : V) :
    Provable T (decode (ArithmeticTemplates254.rho3 a b c)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! (decoded_rho3_equiv T a b c)).mpr (rho3Template T a b c)

end LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
