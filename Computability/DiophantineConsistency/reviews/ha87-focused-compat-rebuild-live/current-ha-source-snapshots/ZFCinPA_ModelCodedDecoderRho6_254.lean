import ZFCinPA.ModelCodedBinderAbsorption
import ZFCinPA.ModelCodedDecoderRho2_254
import ZFCinPA.ModelCodedDecoderFalsity254

set_option autoImplicit false

/-!
The actual numerical rho6, including selected variable zero. Relative falsity
is decoded membership(0,0), so its provable equivalence to Bottom is transported
through the named binder by actual target GEN. It is never treated as a closed
syntactic constant. Repeated-binding absorption supplies the finite vacuity
proof for arbitrary internal matrices and labels.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedBinderAbsorption
open LeanProofs.ZFCinPA.ModelCodedNamedBinderLaws
open LeanProofs.ZFCinPA.ModelCodedSpecialization
open LeanProofs.ZFCinPA.ModelCodedProofRenaming
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoderFalsity254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticCantor
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

lemma namedBody_open (a : V) (p : Formula V ℒₛₑₜ) :
    (namedBody a p).subst ![Semiterm.fvar a] = p := by
  apply Bootstrapping.Semiformula.ext
  simpa [Bootstrapping.Semiformula.val_substs,SemitermVec.val_cons,
    SemitermVec.val_nil,Semiterm.fvar_val,namedBody,substs1] using
    bindOneAt_open p.isSemiformula a

noncomputable def namedAll_elim (T : InternalTheory V ℒₛₑₜ)
    (a : V) (p : Formula V ℒₛₑₜ) : T ⊢! namedFormula a p 🡒 p := by
  have h : T ⊢! namedFormula a p 🡒 (namedBody a p).subst ![Semiterm.fvar a] :=
    TProof.specializeWithCtxAux (C_id (φ := namedFormula a p)) (Semiterm.fvar a)
  simpa only [namedBody_open] using h

lemma negNamedBody_free (a : V) (p : Formula V ℒₛₑₜ) :
    (namedBody a (∼namedFormula a p)).free = (∼namedFormula a p).shift := by
  apply Bootstrapping.Semiformula.ext
  have hp : IsFormula ℒₛₑₜ p.val := by simpa using p.isSemiformula
  have hq : IsFormula ℒₛₑₜ (namedAll ℒₛₑₜ a p.val) := namedAll_isFormula hp a
  change free ℒₛₑₜ (bindOneAt ℒₛₑₜ a 0 (neg ℒₛₑₜ (namedAll ℒₛₑₜ a p.val))) =
    shift ℒₛₑₜ (neg ℒₛₑₜ (namedAll ℒₛₑₜ a p.val))
  rw [bindOneAt_neg hq a,bindOneAt_namedAll hp a]
  exact free_formula hq.neg

noncomputable def negNamedAll_vacuous (T : InternalTheory V ℒₛₑₜ)
    (a : V) (p : Formula V ℒₛₑₜ) :
    T ⊢! (∼namedFormula a p) 🡒 namedFormula a (∼namedFormula a p) := by
  apply TProof.generalizeAux
  rw [negNamedBody_free]
  exact C_id

theorem existentialAll_elim (T : InternalTheory V ℒₛₑₜ)
    (a : V) (p : Formula V ℒₛₑₜ) :
    T ⊢ (∼namedFormula a (∼namedFormula a p)) 🡒 p := by
  classical
  exact C!_trans (CN!_of_CN!_left ⟨negNamedAll_vacuous T a p⟩) ⟨namedAll_elim T a p⟩

/-- The fixed ordinary ZF theorem is weakened before D1 and specialization;
no arbitrary internal formula is quoted. -/
theorem decoded_one_neg_of_zf (T : SetTheory) [T.Δ₁] (hZF : (𝗭𝗙 : SetTheory) ⪯ T) :
    T.internalize V ⊢ ∼decoded (1 : V) := by
  have hc : Provable T (⌜irreflexivitySentence⌝ : V) :=
    internalize_provability (Entailment.weakening hZF zf_irreflexivity_outer)
  rw [quote_irreflexivity] at hc
  obtain ⟨d,hd⟩ := hc
  have hr : (ℒₛₑₜ).IsRel (2 : V) 1 := by
    simpa using (isRel_quote_quote (V := V) (L := ℒₛₑₜ) (k := 2) (x := 1)).mpr
      ⟨Language.Set.Rel.mem,rfl⟩
  have hb : IsSemiformula ℒₛₑₜ (1 : V) (^nrel 2 1 ?[^#0,^#0]) := by simp [hr]
  apply (tprovable_iff_provable).mpr
  refine ⟨specializeCode ℒₛₑₜ d (^nrel 2 1 ?[^#0,^#0]) (^&0),?_⟩
  have h := specializeCode_isProof T hb (show IsTerm ℒₛₑₜ (^& (0 : V)) by simp) hd
  simpa [decoded,decode_one,substs1,atomCode,hr] using h

theorem relativeFalse_equiv_neg (T : InternalTheory V ℒₛₑₜ)
    (p f : Formula V ℒₛₑₜ) (hf : T ⊢ ∼f) : T ⊢ (p 🡒 f) 🡘 ∼p := by
  classical
  have hfb : T ⊢ f 🡘 ⊥ := E!_intro (N!_iff_CO!.mp hf) efq!
  exact E!_trans (ECC!_of_E!_of_E! (show T ⊢ p 🡘 p from ⟨E_Id⟩) hfb)
    (E!_symm neg_equiv!)

theorem decoded_neg_equiv (T : SetTheory) [T.Δ₁]
    (hFalse : T.internalize V ⊢ ∼decoded (1 : V)) (n : V) :
    T.internalize V ⊢ decoded (ArithmeticCode254.wim n 1) 🡘 ∼decoded n := by
  rw [ArithmeticCode254.wim,ArithmeticCode254.tagged,add_zero]
  exact E!_trans (decoded_imp_equiv T n 1)
    (relativeFalse_equiv_neg (T.internalize V) (decoded n) (decoded 1) hFalse)

theorem decoded_rho6_equiv (T : SetTheory) [T.Δ₁] (a b : V)
    (hFalse : T.internalize V ⊢ ∼decoded (1 : V))
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p)) :
    T.internalize V ⊢ decoded (ArithmeticTemplates254.rho6 a b) 🡘
      ((∼namedFormula a (∼namedFormula a (decoded b))) 🡒 decoded b) := by
  classical
  simp only [ArithmeticTemplates254.rho6,ArithmeticTemplates254.rho6Circuit,
    ArithmeticTemplates254.Circuit.r6,ArithmeticTemplates254.Circuit.ex,
    ArithmeticTemplates254.Circuit.neg,ArithmeticTemplates254.Circuit.eval_im,
    ArithmeticTemplates254.Circuit.eval_al,ArithmeticTemplates254.Circuit.eval_input0,
    ArithmeticTemplates254.Circuit.eval_input1,ArithmeticTemplates254.Circuit.eval_one]
  rw [ArithmeticCode254.wim,ArithmeticCode254.tagged,add_zero]
  apply decoded_imp_congr
  · apply E!_trans (decoded_neg_equiv T hFalse _)
    apply ENN!_of_E!
    apply decoded_all_equiv T a _ hGen
    rw [namedFormula_decoded]
    exact decoded_neg_equiv T hFalse _
  · exact ⟨E_Id⟩

theorem decoded_rho6_provable_of_resources (T : SetTheory) [T.Δ₁] (a b : V)
    (hFalse : T.internalize V ⊢ ∼decoded (1 : V))
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p)) :
    Provable T (decode (ArithmeticTemplates254.rho6 a b)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! (decoded_rho6_equiv T a b hFalse hGen)).mpr
    (existentialAll_elim (T.internalize V) a (decoded b))

theorem zf_decoded_rho6_provable (a b : V) :
    Provable (𝗭𝗙 : SetTheory) (decode (ArithmeticTemplates254.rho6 a b)) :=
  decoded_rho6_provable_of_resources 𝗭𝗙 a b
    (decoded_one_neg_of_zf 𝗭𝗙 inferInstance) (fun _ hp => zf_provable_namedAll a hp)

theorem zfc_decoded_rho6_provable (a b : V) :
    Provable (𝗭𝗙𝗖 : SetTheory) (decode (ArithmeticTemplates254.rho6 a b)) :=
  decoded_rho6_provable_of_resources 𝗭𝗙𝗖 a b
    (decoded_one_neg_of_zf 𝗭𝗙𝗖 (Entailment.WeakerThan.ofSubset Set.subset_union_left))
    (fun _ hp => zfc_provable_namedAll a hp)

end LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254
