import ZFCinPA.ModelCodedDecoderRho6_254
import ZFCinPA.ModelCodedDecoderEquality254

set_option autoImplicit false

/-!
The actual numerical rho1 is existence of an equal object, expressed using
relative falsity. Its named binder is opened at the other variable; this yields
reflexive equality for coincident as well as distinct internal labels. The
fixed ordinary equality theorem is internalized before specialization.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedNamedBinderLaws
open LeanProofs.ZFCinPA.ModelCodedProofRenaming
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho6_254
open LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
open _root_.SetTheory.BusyBeaver.ZFC
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ)
local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := ℒₛₑₜ)

lemma termBindOneVecAt_pair (a depth t u : V)
    (ht : IsUTerm ℒₛₑₜ t) (hu : IsUTerm ℒₛₑₜ u) :
    termBindOneVecAt ℒₛₑₜ a depth 2 ?[t,u] =
      ?[termBindOneAt ℒₛₑₜ a depth t,termBindOneAt ℒₛₑₜ a depth u] := by
  have hv : IsUTermVec ℒₛₑₜ (2 : V) ?[t,u] := by simp [ht,hu]
  apply nth_ext' (2 : V)
  · simp [hv]
  · simp [one_add_one_eq_two]
  · intro i hi
    rw [nth_termBindOneVecAt a depth hv hi]
    rcases le_one_iff_eq_zero_or_one.mp (lt_two_iff_le_one.mp hi) with rfl | rfl <;> simp

noncomputable def namedVar (chosen x : V) : Bootstrapping.Semiterm V ℒₛₑₜ 1 := by
  classical
  exact if x = chosen then #'0 else &'x

lemma namedBody_eqAtom (a b c : V) :
    namedBody a (eqAtom (&'b) (&'c)) = eqAtom (namedVar a b) (namedVar a c) := by
  classical
  have hr : (ℒₛₑₜ).IsRel (2 : V) 0 := by
    simpa using (isRel_quote_quote (V := V) (L := ℒₛₑₜ) (k := 2) (x := 0)).mpr
      ⟨Language.Set.Rel.eq,rfl⟩
  have hv : IsUTermVec ℒₛₑₜ (2 : V) ?[^&b,^&c] := by simp
  apply Bootstrapping.Semiformula.ext
  change bindOneAt ℒₛₑₜ a 0 (^rel 2 0 ?[^&b,^&c]) =
    ^rel 2 0 ?[(namedVar a b).val,(namedVar a c).val]
  rw [bindOneAt_rel a 0 hr hv,termBindOneVecAt_pair a 0 _ _ (by simp) (by simp)]
  by_cases hb : b = a <;> by_cases hc : c = a <;>
    simp [namedVar,termBindOneAt_fvar,hb,hc]

lemma namedBody_neg (a : V) (p : Formula V ℒₛₑₜ) :
    namedBody a (∼p) = ∼namedBody a p := by
  apply Bootstrapping.Semiformula.ext
  exact bindOneAt_neg p.isSemiformula a

lemma negEquality_open_at_other (a b : V) :
    (namedBody a (∼eqAtom (&'a) (&'b))).subst ![&'b] =
      (∼eqAtom (&'b) (&'b) : Formula V ℒₛₑₜ) := by
  classical
  rw [namedBody_neg,namedBody_eqAtom]
  by_cases h : b = a <;> simp [namedVar,h,eqAtom]

def reflexivitySentence : SetTheorySentence :=
  ∀⁰ FirstOrder.Semiformula.rel Language.Set.Rel.eq ![#0,#0]

@[simp] private lemma standard_rel_eq {M : Type*} [SetStructure M] (v : Fin 2 → M) :
    Structure.rel (L := ℒₛₑₜ) (M := M) Language.Set.Rel.eq v ↔ v 0 = v 1 := Iff.rfl

theorem equality_reflexive (T : SetTheory) [T.Δ₁] [𝗘𝗤 ℒₛₑₜ ⪯ T] (b : V) :
    T.internalize V ⊢ eqAtom (&'b) (&'b) := by
  have ho : T ⊢ reflexivitySentence := by
    apply SetTheory.provable_of_models.{0}
    intro M _ _ _
    simp [reflexivitySentence,models_iff]
  have hi := internal_provable_of_outer_provable (V := V) ho
  have hq : (⌜reflexivitySentence⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      ∀⁰ eqAtom (#'0) (#'0) := by
    rw [FirstOrder.Sentence.typed_quote_def]
    simp [reflexivitySentence,eqAtom,Rew.q_emb,Rew.emb_bvar,quote_vec2]
  rw [hq] at hi
  simpa [eqAtom] using TProof.specialize! hi (&'b)

theorem existsNamedEquality (T : SetTheory) [T.Δ₁] [𝗘𝗤 ℒₛₑₜ ⪯ T] (a b : V) :
    T.internalize V ⊢ ∼namedFormula a (∼eqAtom (&'a) (&'b)) := by
  classical
  have h : T.internalize V ⊢ namedFormula a (∼eqAtom (&'a) (&'b)) 🡒
      ∼eqAtom (&'b) (&'b) := by
    have hs := TProof.specializeWithCtxAux
      (T := T.internalize V) (C_id (φ := namedFormula a (∼eqAtom (&'a) (&'b)))) (&'b)
    exact ⟨by simpa only [negEquality_open_at_other] using hs⟩
  exact (CN!_of_CN!_right h) ⨀ equality_reflexive T b

theorem decoded_rho1_equiv (T : SetTheory) [T.Δ₁] (a b : V)
    (hFalse : T.internalize V ⊢ ∼decoded (1 : V))
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p)) :
    T.internalize V ⊢ decoded (ArithmeticCode254.rho1 a b) 🡘
      ∼namedFormula a (∼eqAtom (&'a) (&'b)) := by
  classical
  unfold ArithmeticCode254.rho1
  apply E!_trans (decoded_neg_equiv T hFalse _)
  apply ENN!_of_E!
  apply decoded_all_equiv T a _ hGen
  simpa only [decoded_weq] using decoded_neg_equiv T hFalse (ArithmeticCode254.weq a b)

theorem decoded_rho1_provable_of_resources (T : SetTheory) [T.Δ₁] [𝗘𝗤 ℒₛₑₜ ⪯ T]
    (a b : V) (hFalse : T.internalize V ⊢ ∼decoded (1 : V))
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ a p)) :
    Provable T (decode (ArithmeticCode254.rho1 a b)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! (decoded_rho1_equiv T a b hFalse hGen)).mpr (existsNamedEquality T a b)

theorem zf_decoded_rho1_provable (a b : V) :
    Provable (𝗭𝗙 : SetTheory) (decode (ArithmeticCode254.rho1 a b)) :=
  decoded_rho1_provable_of_resources 𝗭𝗙 a b
    (decoded_one_neg_of_zf 𝗭𝗙 inferInstance) (fun _ hp => zf_provable_namedAll a hp)

theorem zfc_decoded_rho1_provable (a b : V) :
    Provable (𝗭𝗙𝗖 : SetTheory) (decode (ArithmeticCode254.rho1 a b)) :=
  decoded_rho1_provable_of_resources 𝗭𝗙𝗖 a b
    (decoded_one_neg_of_zf 𝗭𝗙𝗖 (Entailment.WeakerThan.ofSubset Set.subset_union_left))
    (fun _ hp => zfc_provable_namedAll a hp)

end LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254
