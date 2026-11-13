import ZFCinPA.ModelCodedDecoderGeneralization254
import ZFCinPA.ModelCodedNamedQuantifierTemplates254
import ZFCinPA.ModelCodedDecoderLukasiewicz254

set_option autoImplicit false

/-!
Decoded numerical universal distribution (rho2) in actual internal ZF/ZFC.
The generic helpers expose their exact named-GEN resource; the final actual
ZF/ZFC instances discharge it using the checked all-internal proof renaming.
Implication's zero alias is handled by internal provable equivalence, including
its occurrence under the named universal. No proof selector is assumed.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedNamedBinderLaws
open LeanProofs.ZFCinPA.ModelCodedNamedQuantifierTemplates254
open LeanProofs.ZFCinPA.ModelCodedProofRenaming
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderGeneralization254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable def namedBody (a : V) (p : Formula V ℒₛₑₜ) :
    Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  ⟨bindOneAt ℒₛₑₜ a 0 p.val,by
    simpa only [Nat.cast_zero,Nat.cast_one,zero_add] using
      bindOneAt_isSemiformula p.isSemiformula a⟩
noncomputable def namedFormula (a : V) (p : Formula V ℒₛₑₜ) : Formula V ℒₛₑₜ :=
  ∀⁰ namedBody a p
@[simp] lemma namedFormula_val (a : V) (p : Formula V ℒₛₑₜ) :
    (namedFormula a p).val = namedAll ℒₛₑₜ a p.val := rfl

lemma namedBody_imp (a : V) (p q : Formula V ℒₛₑₜ) :
    namedBody a (p 🡒 q) = namedBody a p 🡒 namedBody a q := by
  apply Bootstrapping.Semiformula.ext
  simp only [Bootstrapping.Semiformula.val_imp]
  exact bindOneAt_imp p.isSemiformula q.isSemiformula a

theorem namedFormula_mono (T : Theory ℒₛₑₜ) [T.Δ₁] (a : V)
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p))
    (p q : Formula V ℒₛₑₜ) (h : T.internalize V ⊢ p 🡒 q) :
    T.internalize V ⊢ namedFormula a p 🡒 namedFormula a q := by
  have hp : Provable T (p 🡒 q).val := (tprovable_iff_provable).mp h
  have hg : Provable T (namedAll ℒₛₑₜ a (p 🡒 q).val) := hGen _ hp
  have hall : T.internalize V ⊢ namedFormula a (p 🡒 q) :=
    (tprovable_iff_provable (σ := namedFormula a (p 🡒 q))).mpr hg
  have hd : T.internalize V ⊢
      (∀⁰ (namedBody a p 🡒 namedBody a q)) := by
    simpa only [namedFormula,namedBody_imp] using hall
  exact (show T.internalize V ⊢
    (∀⁰ (namedBody a p 🡒 namedBody a q)) 🡒
      ((∀⁰ namedBody a p) 🡒 (∀⁰ namedBody a q)) from
      ⟨allDistribution (T.internalize V) (namedBody a p) (namedBody a q)⟩) ⨀ hd

theorem namedFormula_equiv (T : Theory ℒₛₑₜ) [T.Δ₁] (a : V)
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p))
    (p q : Formula V ℒₛₑₜ) (h : T.internalize V ⊢ p 🡘 q) :
    T.internalize V ⊢ namedFormula a p 🡘 namedFormula a q :=
  E!_intro (namedFormula_mono T a hGen p q (C_of_E_mp! h))
    (namedFormula_mono T a hGen q p (C_of_E_mpr! h))

lemma namedFormula_decoded (a h : V) :
    namedFormula a (decoded h) = decoded (ArithmeticCode254.wal a h) := by
  apply Bootstrapping.Semiformula.ext
  exact (decode_wal a h).symm

theorem decoded_all_equiv (T : Theory ℒₛₑₜ) [T.Δ₁] (a h : V)
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p))
    (p : Formula V ℒₛₑₜ) (hp : T.internalize V ⊢ decoded h 🡘 p) :
    T.internalize V ⊢ decoded (ArithmeticCode254.wal a h) 🡘 namedFormula a p := by
  rw [←namedFormula_decoded]
  exact namedFormula_equiv T a hGen (decoded h) p hp

theorem decoded_rho2_equiv (T : Theory ℒₛₑₜ) [T.Δ₁] (a b c : V)
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p)) :
    T.internalize V ⊢ decoded (ArithmeticTemplates254.rho2 a b c) 🡘
      (namedFormula a (decoded b 🡒 decoded c) 🡒
        (namedFormula a (decoded b) 🡒 namedFormula a (decoded c))) := by
  simp only [ArithmeticTemplates254.rho2,ArithmeticTemplates254.rho2Circuit,
    ArithmeticTemplates254.Circuit.r2,ArithmeticTemplates254.Circuit.eval_im,
    ArithmeticTemplates254.Circuit.eval_al,ArithmeticTemplates254.Circuit.eval_input0,
    ArithmeticTemplates254.Circuit.eval_input1,ArithmeticTemplates254.Circuit.eval_input2,
    ArithmeticCode254.wim,ArithmeticCode254.tagged,add_zero]
  apply decoded_imp_congr
  · exact decoded_all_equiv T a _ hGen _ (decoded_imp_equiv T b c)
  · apply decoded_imp_congr
    · rw [namedFormula_decoded]; exact ⟨E_Id⟩
    · rw [namedFormula_decoded]; exact ⟨E_Id⟩

theorem decoded_rho2_provable_of_gen (T : Theory ℒₛₑₜ) [T.Δ₁] (a b c : V)
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p)) :
    Provable T (decode (ArithmeticTemplates254.rho2 a b c)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  apply (iff_of_E! (decoded_rho2_equiv T a b c hGen)).mpr
  have h : T.internalize V ⊢
      (∀⁰ (namedBody a (decoded b) 🡒 namedBody a (decoded c))) 🡒
        ((∀⁰ namedBody a (decoded b)) 🡒 (∀⁰ namedBody a (decoded c))) :=
    ⟨allDistribution (T.internalize V) (namedBody a (decoded b)) (namedBody a (decoded c))⟩
  simpa only [namedFormula,namedBody_imp] using h

theorem zf_decoded_rho2_provable (a b c : V) :
    Provable (𝗭𝗙 : SetTheory) (decode (ArithmeticTemplates254.rho2 a b c)) :=
  decoded_rho2_provable_of_gen (𝗭𝗙 : SetTheory) a b c
    (fun _ hp => zf_provable_namedAll a hp)

theorem zfc_decoded_rho2_provable (a b c : V) :
    Provable (𝗭𝗙𝗖 : SetTheory) (decode (ArithmeticTemplates254.rho2 a b c)) :=
  decoded_rho2_provable_of_gen (𝗭𝗙𝗖 : SetTheory) a b c
    (fun _ hp => zfc_provable_namedAll a hp)

end LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
