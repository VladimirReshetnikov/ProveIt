import ZFCinPA.CompiledCollection254
import ZFCinPA.ModelCodedBindTwoSlots
import ZFCinPA.ModelCodedDecoderCollectionNormalization254
import ZFCinPA.ModelCodedDecoderFreshness254

set_option autoImplicit false
noncomputable section

/-!
Exact internal decoded G client. It uses the actual compiled Collection
proof with all callbacks discharged, exact two-slot syntax, and own-code
freshness. Both real bundle gates are retained; zero code and a=b are separate.
The scope is the numerical G row; a PA consistency comparison is separate.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderCollection254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedSpecialization
open LeanProofs.ZFCinPA.ModelCodedBindTwoSlots
open LeanProofs.ZFCinPA.ModelCodedBinderAbsorption
open LeanProofs.ZFCinPA.ModelCodedNamedBinderLaws
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedProofRenaming
open LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254
open LeanProofs.ZFCinPA.ModelCodedDecoderContainer254
open LeanProofs.ZFCinPA.ModelCodedDecoderCollectionNormalization254
open LeanProofs.ZFCinPA.ModelCodedDecoderFreshness254
open LeanProofs.ZFCinPA.SetPlaceholders
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticTemplates254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local instance (k : Nat) : GödelQuote (Language.Set.Rel k) V :=
  gödelQuoteRel (L := ℒₛₑₜ) k
local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ)
local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := ℒₛₑₜ)

private lemma mem_quote : (⌜Language.Set.Rel.mem⌝ : V) = 1 := by
  change ((1 : Nat) : V) = 1
  simp

@[simp] private lemma bindT_neg {n : Nat} (chosen : V)
    (p : Bootstrapping.Semiformula V ℒₛₑₜ n) :
    bindT chosen (∼p) = ∼bindT chosen p := by
  apply Bootstrapping.Semiformula.ext
  exact bindOneAt_neg p.isSemiformula chosen

/-- Abstract only the selected input/output labels; other free parameters stay. -/
noncomputable def binaryBody (a b : V) (p : Formula V ℒₛₑₜ) :
    Bootstrapping.Semiformula V ℒₛₑₜ 2 := bindT b (bindT a p)

lemma binaryBody_subst {m : Nat} (a b : V) (p : Formula V ℒₛₑₜ)
    (i j : Fin m) (hab : a ≠ b) :
    ((binaryBody a b p).subst ![#'i,#'j]).val =
      bindOneAt ℒₛₑₜ b (j : V) (bindOneAt ℒₛₑₜ a (i : V) p.val) := by
  simp only [Bootstrapping.Semiformula.val_substs,Bootstrapping.SemitermVec.val_cons,
    Bootstrapping.SemitermVec.val_nil,Bootstrapping.Semiterm.bvar_val,binaryBody,bindT,
    Nat.cast_zero,Nat.cast_one]
  simpa only [Nat.cast_zero,twoSlotVec_zero,zero_add] using
    bindTwo_reindex p.isSemiformula a b (i : V) (j : V) hab

/-- Exact translated matrix before specializing the source set argument. -/
noncomputable def collectionMatrix (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    Bootstrapping.Semiformula V ℒₛₑₜ 1 :=
  ∃⁰ ((∀⁰ (memAtom (#'0) (#'2) 🡒
    ∀⁰ (K.subst ![#'1,#'0] 🡒
      ∃⁰ (K.subst ![#'2,#'0] ⋏ memAtom (#'0) (#'3))))) ⋏
    (∀⁰ (memAtom (#'0) (#'1) 🡒 ∃⁰ (K.subst ![#'0,#'1]))))

noncomputable def canonicalG (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) (b : V) :
    Formula V ℒₛₑₜ :=
  ∃⁰ ((∀⁰ (memAtom (#'0) (&'b) 🡒
    ∀⁰ (K.subst ![#'1,#'0] 🡒
      ∃⁰ (K.subst ![#'2,#'0] ⋏ memAtom (#'0) (#'3))))) ⋏
    (∀⁰ (memAtom (#'0) (#'1) 🡒 ∃⁰ (K.subst ![#'0,#'1]))))

private lemma translate_vec2 {n : Nat}
    (t u : SyntacticSemiterm CollectionTemplate254.Lang n) :
    (fun i => translateTerm (V := V) (![t,u] i)) = ![translateTerm t,translateTerm u] := by
  funext i
  match i with
  | 0 => rfl
  | 1 => rfl

lemma translate_collectionSentence (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) :
    translateFormula (fun _ : Fin 1 => K)
      (Rewriting.emb CollectionTemplate254.collectionSentence) = ∀⁰ collectionMatrix K := by
  simp [CollectionTemplate254.collectionSentence,CollectionTemplate254.rAtom,
    placeholderRel,FirstOrder.Semiformula.ballMem,FirstOrder.Semiformula.ball_eq,
    translateFormula,collectionMatrix,translate_vec2,
    Rew.q_emb,Rew.emb_bvar,FirstOrder.Semiformula.Operator.mem_def,memAtom,
    Bootstrapping.Semiformula.imp_def,
    Matrix.comp_vecCons',Matrix.comp_vecCons'',Matrix.constant_eq_singleton,Function.comp_def]
  <;> rfl

lemma collectionMatrix_specialize (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) (b : V) :
    (collectionMatrix K).subst ![&'b] = canonicalG K b := by
  simp [collectionMatrix,canonicalG,memAtom,Bootstrapping.SemitermVec.q,
    Bootstrapping.Semiformula.substs_substs,Matrix.comp_vecCons',Function.comp_def]

/-- Actual checked compiler callback family, with no schematic proof premise. -/
theorem zf_canonicalG_provable (K : Bootstrapping.Semiformula V ℒₛₑₜ 2) (b : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ canonicalG K b := by
  have hi : (𝗭𝗙 : SetTheory).internalize V ⊢ ∀⁰ collectionMatrix K := by
    simpa only [translate_collectionSentence] using
      (show (𝗭𝗙 : SetTheory).internalize V ⊢ translateFormula (fun _ : Fin 1 => K)
        (Rewriting.emb CollectionTemplate254.collectionSentence) from
          ⟨CompiledCollection254.collectionProof K⟩)
  simpa only [collectionMatrix_specialize] using TProof.specialize! hi (&'b)

/-- The raw freshness resource is used only inside the generic syntax bridge.
The numerical endpoint below supplies it from positive own-code freshness. -/
private lemma remove_container_binding {p : V} (hp : IsUFormula ℒₛₑₜ p)
    (a b c d e f : V) (hca : c ≠ a) (hcb : c ≠ b)
    (hf : ∀ depth : V, bindOneAt ℒₛₑₜ c depth p = p) :
    bindOneAt ℒₛₑₜ c d (bindOneAt ℒₛₑₜ a e (bindOneAt ℒₛₑₜ b f p)) =
      bindOneAt ℒₛₑₜ a e (bindOneAt ℒₛₑₜ b f p) := by
  rw [bindOneAt_commute (bindOneAt_isUFormula hp b f) c a d e hca,
    bindOneAt_commute hp c b d f hcb,hf d]

lemma nativeG_distinct (a b c : V) (p : Formula V ℒₛₑₜ)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hf : ∀ depth : V, bindOneAt ℒₛₑₜ c depth p.val = p.val) :
    nativeG a b c p = canonicalG (binaryBody a b p) b := by
  classical
  have hAnte :
      bindOneAt ℒₛₑₜ c 2 (bindOneAt ℒₛₑₜ a 1 (bindOneAt ℒₛₑₜ b 0 p.val)) =
        ((binaryBody a b p).subst ![(#'1 : Bootstrapping.Semiterm V ℒₛₑₜ 3),#'0]).val := by
    rw [remove_container_binding p.isSemiformula.isUFormula a b c 2 1 0 hca hcb hf,
      bindOneAt_commute p.isSemiformula.isUFormula a b 1 0 hab]
    simpa using
      (binaryBody_subst (m := 3) a b p (1 : Fin 3) (0 : Fin 3) hab).symm
  have hWitness :
      bindOneAt ℒₛₑₜ c 3 (bindOneAt ℒₛₑₜ a 2
        (bindOneAt ℒₛₑₜ b 1 (bindOneAt ℒₛₑₜ b 0 p.val))) =
        ((binaryBody a b p).subst ![(#'2 : Bootstrapping.Semiterm V ℒₛₑₜ 4),#'0]).val := by
    have hAbs : bindOneAt ℒₛₑₜ b 1 (bindOneAt ℒₛₑₜ b 0 p.val) =
        bindOneAt ℒₛₑₜ b 0 p.val := by
      simpa only [Nat.cast_zero,zero_add] using bindOneAt_absorb p.isSemiformula b
    rw [hAbs,
      remove_container_binding p.isSemiformula.isUFormula a b c 3 2 0 hca hcb hf,
      bindOneAt_commute p.isSemiformula.isUFormula a b 2 0 hab]
    simpa using
      (binaryBody_subst (m := 4) a b p (2 : Fin 4) (0 : Fin 4) hab).symm
  have hSupport :
      bindOneAt ℒₛₑₜ c 2 (bindOneAt ℒₛₑₜ b 1 (bindOneAt ℒₛₑₜ a 0 p.val)) =
        ((binaryBody a b p).subst ![(#'0 : Bootstrapping.Semiterm V ℒₛₑₜ 3),#'1]).val := by
    rw [remove_container_binding p.isSemiformula.isUFormula b a c 2 1 0 hcb hca hf]
    simpa using
      (binaryBody_subst (m := 3) a b p (0 : Fin 3) (1 : Fin 3) hab).symm
  simp only [nativeG,memNamed,namedFormula,namedExists,namedBody_bindT,
    bindT_and,bindT_imp,bindT_all,bindT_ex,bindT_mem,
    termBindT_bvar,termBindT_fvar,hab,hab.symm,hca,hcb,
    hca.symm,hcb.symm,ite_true,ite_false]
  apply Bootstrapping.Semiformula.ext
  simp only [canonicalG,bindT,Bootstrapping.Semiformula.val_all,
    Bootstrapping.Semiformula.val_exs,Bootstrapping.Semiformula.val_and,
    Bootstrapping.Semiformula.val_imp,Nat.cast_add,Nat.cast_zero,Nat.cast_one,
    zero_add,one_add_one_eq_two,two_add_one_eq_three,hAnte,hWitness,hSupport,
    memAtom,Bootstrapping.Semiformula.rel_val,Bootstrapping.SemitermVec.val_cons,
    Bootstrapping.SemitermVec.val_nil,Bootstrapping.Semiterm.bvar_val,
    Bootstrapping.Semiterm.fvar_val,Fin.val_castSucc,Fin.val_last,
    Nat.cast_ofNat] <;> simp

/-- The generic fresh-body client has the actual compiled proof as its source. -/
theorem zf_nativeG_distinct (a b c : V) (p : Formula V ℒₛₑₜ)
    (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b)
    (hf : ∀ depth : V, bindOneAt ℒₛₑₜ c depth p.val = p.val) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ nativeG a b c p := by
  rw [nativeG_distinct a b c p hab hca hcb hf]
  exact zf_canonicalG_provable _ b

/-- One actual empty-set axiom, prior to any internal named-label calculation. -/
private lemma zf_empty_sentence : (𝗭𝗙 : SetTheory) ⊢ Axiom.empty := by
  exact LO.Entailment.Axiomatized.by_axm ZermeloFraenkel.axiom_of_empty_set

private lemma zf_named_empty (a c : V) (hca : c ≠ a) :
    (𝗭𝗙 : SetTheory).internalize V ⊢
      namedExists c (namedFormula a (∼memNamed a c)) := by
  classical
  have hi := internal_provable_of_outer_provable (V := V) zf_empty_sentence
  have hq : (⌜Axiom.empty⌝ : Formula V ℒₛₑₜ) =
      ∃⁰ ∀⁰ ∼memAtom (#'0) (#'1) := by
    rw [FirstOrder.Sentence.typed_quote_def]
    simp [Axiom.empty,memAtom,Rew.q_emb,Rew.emb_bvar,
      FirstOrder.Semiformula.Operator.mem_def,quote_vec2]
  have he : namedExists c (namedFormula a (∼memNamed a c)) =
      ∃⁰ ∀⁰ ∼memAtom (#'0) (#'1) := by
    simp only [namedExists,namedFormula,namedBody_bindT,memNamed,
      bindT_all,bindT_neg,bindT_mem,termBindT_bvar,termBindT_fvar,
      hca,hca.symm,ite_true,ite_false] <;> rfl
  rw [hq] at hi
  simpa only [he] using hi

/-- No output witness is assumed in the coincident-label case: use the empty
container for support and irreflexivity for its cover antecedent. -/
theorem zf_nativeG_coincident (a c : V) (p : Formula V ℒₛₑₜ) (hca : c ≠ a) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ nativeG a a c p := by
  classical
  let cover : Formula V ℒₛₑₜ := namedFormula a
    (memNamed a a 🡒 namedFormula a (p 🡒 namedExists a (p ⋏ memNamed a c)))
  let empty : Formula V ℒₛₑₜ := namedFormula a (∼memNamed a c)
  let support : Formula V ℒₛₑₜ := namedFormula a (memNamed a c 🡒 namedExists a p)
  have hc : (𝗭𝗙 : SetTheory).internalize V ⊢ cover := by
    apply (tprovable_iff_provable (σ := cover)).mpr
    exact zf_provable_namedAll a ((tprovable_iff_provable).mp
      (C_of_N (zf_not_mem_self a)))
  have hs : (𝗭𝗙 : SetTheory).internalize V ⊢ empty 🡒 support :=
    namedFormula_mono 𝗭𝗙 a (fun _ hp => zf_provable_namedAll a hp) _ _ CNC!
  have hb : (𝗭𝗙 : SetTheory).internalize V ⊢ empty 🡒 (cover ⋏ support) :=
    right_K!_intro (C!_of_conseq! hc) hs
  have hx := namedExists_mono 𝗭𝗙 c (fun _ hp => zf_provable_namedAll c hp) hb
  simpa only [nativeG,cover,support,empty] using hx ⨀ zf_named_empty a c hca

lemma decoded_zero_equiv_top (T : InternalTheory V ℒₛₑₜ) :
    T ⊢ decoded (0 : V) 🡘 ⊤ := by
  classical
  apply E!_intro CV!
  have he : decoded (0 : V) = memNamed (0 : V) 0 🡒 memNamed 0 0 := by
    apply Bootstrapping.Semiformula.ext
    change decode (0 : V) = imp ℒₛₑₜ
      (^rel 2 (⌜Language.Set.Rel.mem⌝ : V) ?[^&0,^&0])
      (^rel 2 (⌜Language.Set.Rel.mem⌝ : V) ?[^&0,^&0])
    rw [decode_zero,mem_quote]
    rfl
  have h0 : T ⊢ decoded (0 : V) := by
    rw [he]
    exact C!_id
  exact C!_of_conseq! h0

/-- The actual endpoint keeps only the two genuine bundle gates. -/
theorem zf_nativeG_decoded (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ nativeG a b c (decoded c) := by
  classical
  by_cases hab : a = b
  · subst b
    exact zf_nativeG_coincident a c (decoded c) hca
  · by_cases hz : c = 0
    · subst c
      have ht : (𝗭𝗙 : SetTheory).internalize V ⊢ nativeG a b 0 (⊤ : Formula V ℒₛₑₜ) :=
        zf_nativeG_distinct a b 0 ⊤ hab hca hcb (by intro depth; simp)
      exact (iff_of_E! (nativeG_equiv 𝗭𝗙
        (fun label _ hp => zf_provable_namedAll label hp) a b 0 (decoded 0) ⊤
        (decoded_zero_equiv_top _))).mpr ht
    · exact zf_nativeG_distinct a b c (decoded c) hab hca hcb
        (positive_code_fresh c (lt_of_le_of_ne (by simp) (Ne.symm hz)))

theorem zf_decoded_bundleG_provable (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Provable (𝗭𝗙 : SetTheory) (decode (bundleG a b c)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! (zf_decoded_collection_native_equiv a b c)).mpr
    (zf_nativeG_decoded a b c hca hcb)

end LeanProofs.ZFCinPA.ModelCodedDecoderCollection254
