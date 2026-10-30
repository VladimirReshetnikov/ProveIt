import ZFCinPA.ModelCodedDecoderCircuits254
import ZFCinPA.ModelCodedNamedLogicalNormalization254
import ZFCinPA.NativeZFContainers254
import ZFCinPA.ModelCodedDecoderAtomicVacuity254

set_option autoImplicit false

/-!
Exact internal C client. The circuit is fixed externally; all labels
remain arbitrary internal values. A fixed ordinary ZF row proof is internalized
before specialization. The two actual gates are retained, including a=b.
The G row, full bundle and PA consistency comparison remain separate.
-/
namespace LeanProofs.ZFCinPA.ModelCodedDecoderContainer254
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping LO.FirstOrder.SetTheory
open LO.Entailment
open LeanProofs.ZFCinPA.ModelCodedBindOne
open LeanProofs.ZFCinPA.ModelCodedDecoder254
open LeanProofs.ZFCinPA.ModelCodedDecoderEquality254
open LeanProofs.ZFCinPA.ModelCodedNamedBinderLaws
open LeanProofs.ZFCinPA.ModelCodedDecoderRho1_254
open LeanProofs.ZFCinPA.ModelCodedDecoderAtomicVacuity254
open LeanProofs.ZFCinPA.ModelCodedProofRenaming
open LeanProofs.ZFCinPA.ModelCodedDecoderLukasiewicz254
open LeanProofs.ZFCinPA.ModelCodedDecoderRho2_254
open LeanProofs.ZFCinPA.ModelCodedDecoderCircuits254
open LeanProofs.ZFCinPA.ModelCodedNamedLogicalNormalization254
open _root_.SetTheory.BusyBeaver.ZFC
open ArithmeticTemplates254
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
local instance (k : Nat) : GödelQuote (Language.Set.Rel k) V :=
  gödelQuoteRel (L := ℒₛₑₜ) k

@[simp] private lemma actual_mem_symbol :
    (Language.Mem.mem : (ℒₛₑₜ).Rel 2) = Language.Set.Rel.mem := rfl

local prefix:max "#'" => Bootstrapping.Semiterm.bvar (V := V) (L := ℒₛₑₜ)
local prefix:max "&'" => Bootstrapping.Semiterm.fvar (V := V) (L := ℒₛₑₜ)

noncomputable def memNamed (a b : V) : Formula V ℒₛₑₜ :=
  memAtom (Bootstrapping.Semiterm.fvar a) (Bootstrapping.Semiterm.fvar b)

noncomputable def nativePower (a b c : V) : Formula V ℒₛₑₜ :=
  namedFormula b
    (namedFormula c (memNamed c b 🡒 memNamed c a) 🡒 memNamed b c)

noncomputable def nativeContainer (a b c : V) : Formula V ℒₛₑₜ :=
  namedExists b
    ((namedFormula a (memNamed a b 🡒
      ((namedExists c (nativePower a b c ⋏ memNamed c b)) ⋏
        namedFormula c (memNamed c a 🡒 memNamed c b)))) ⋏ memNamed c b)

theorem interpret_im_congr (T : SetTheory) [T.Δ₁]
    (x y : Circuit) (a b c u : V) (p q : Formula V ℒₛₑₜ)
    (hp : T.internalize V ⊢ interpret x a b c u 🡘 p)
    (hq : T.internalize V ⊢ interpret y a b c u 🡘 q) :
    T.internalize V ⊢ interpret (Circuit.im x y) a b c u 🡘 (p 🡒 q) :=
  ECC!_of_E!_of_E! hp hq

theorem interpret_conj_congr (T : SetTheory) [T.Δ₁]
    (x y : Circuit) (a b c u : V) (p q : Formula V ℒₛₑₜ)
    (hp : T.internalize V ⊢ interpret x a b c u 🡘 p)
    (hq : T.internalize V ⊢ interpret y a b c u 🡘 q) :
    T.internalize V ⊢ interpret (Circuit.conj x y) a b c u 🡘 (p ⋏ q) := by
  apply E!_trans (relativeConj_equiv (T.internalize V) _ _)
  exact EKK!_of_E!_of_E! hp hq

theorem interpret_all_congr (T : SetTheory) [T.Δ₁]
    (hGen : ∀ label p : V, Provable T p → Provable T (namedAll ℒₛₑₜ label p))
    (label x : Circuit) (a b c u : V) (p : Formula V ℒₛₑₜ)
    (hp : T.internalize V ⊢ interpret x a b c u 🡘 p) :
    T.internalize V ⊢ interpret (Circuit.al label x) a b c u 🡘
      namedFormula (label.eval a b c u) p :=
  namedFormula_equiv T _ (hGen _) _ _ hp

theorem interpret_ex_congr (T : SetTheory) [T.Δ₁]
    (hGen : ∀ label p : V, Provable T p → Provable T (namedAll ℒₛₑₜ label p))
    (label x : Circuit) (a b c u : V) (p : Formula V ℒₛₑₜ)
    (hp : T.internalize V ⊢ interpret x a b c u 🡘 p) :
    T.internalize V ⊢ interpret (Circuit.ex label x) a b c u 🡘
      namedExists (label.eval a b c u) p := by
  apply E!_trans (relativeExists_equiv T _ (hGen _) _)
  exact namedExists_equiv T _ (hGen _) _ _ hp

/-- No gate is needed to identify the native formula. Gates enter only when
proving it from the fixed ordinary container theorem. -/
theorem interpret_container_native_equiv (T : SetTheory) [T.Δ₁]
    (hGen : ∀ label p : V, Provable T p → Provable T (namedAll ℒₛₑₜ label p))
    (a b c : V) :
    T.internalize V ⊢ interpret bundleCCircuit a b c 0 🡘 nativeContainer a b c := by
  unfold bundleCCircuit Circuit.container nativeContainer
  apply interpret_ex_congr T hGen
  apply interpret_conj_congr T
  · apply interpret_all_congr T hGen
    apply interpret_im_congr T
    · exact ⟨E_Id⟩
    · apply interpret_conj_congr T
      · apply interpret_ex_congr T hGen
        apply interpret_conj_congr T
        · exact ⟨E_Id⟩
        · exact ⟨E_Id⟩
      · exact ⟨E_Id⟩
  · exact ⟨E_Id⟩

theorem zf_decoded_container_native_equiv (a b c : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢
      decoded (bundleC a b c) 🡘 nativeContainer a b c :=
  E!_trans (zf_decoded_bundleC_equiv a b c)
    (interpret_container_native_equiv 𝗭𝗙
      (fun label _ hp => zf_provable_namedAll label hp) a b c)

/-- One fixed ordinary one-slot matrix, not an internal formula parameter. -/
def containerRowMatrix : SetTheorySemisentence 1 :=
  “c. ∃ b,
    (∀ a, a ∈ b →
      ((∃ p, (∀ z, (∀ u, u ∈ z → u ∈ a) → z ∈ p) ∧ p ∈ b) ∧
        (∀ t, t ∈ a → t ∈ b))) ∧ c ∈ b”

/-- Explicit native bound-slot normal form after substituting the one input. -/
noncomputable def canonicalContainer (c : V) : Formula V ℒₛₑₜ :=
  ∃⁰ ((∀⁰ (memAtom (#'0) (#'1) 🡒
    ((∃⁰ ((∀⁰ ((∀⁰ (memAtom (#'0) (#'1) 🡒 memAtom (#'0) (#'3))) 🡒
        memAtom (#'0) (#'1))) ⋏ memAtom (#'0) (#'2))) ⋏
      (∀⁰ (memAtom (#'0) (#'1) 🡒 memAtom (#'0) (#'2)))))) ⋏
    memAtom (&'c) (#'0))

lemma canonicalContainer_quote_subst (c : V) :
    (⌜containerRowMatrix⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 1).subst ![&'c] =
      canonicalContainer c := by
  have hq : (⌜containerRowMatrix⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 1) =
      ∃⁰ ((∀⁰ (memAtom (#'0) (#'1) 🡒
        ((∃⁰ ((∀⁰ ((∀⁰ (memAtom (#'0) (#'1) 🡒 memAtom (#'0) (#'3))) 🡒
            memAtom (#'0) (#'1))) ⋏ memAtom (#'0) (#'2))) ⋏
          (∀⁰ (memAtom (#'0) (#'1) 🡒 memAtom (#'0) (#'2)))))) ⋏
        memAtom (#'1) (#'0)) := by
    rw [FirstOrder.Sentence.typed_quote_def]
    simp [containerRowMatrix,memAtom,Rew.q_emb,Rew.emb_bvar,
      FirstOrder.Semiformula.Operator.mem_def,quote_vec2]
  rw [hq]
  simp [canonicalContainer,memAtom,Bootstrapping.SemitermVec.q]

theorem zf_canonicalContainer_provable (c : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ canonicalContainer c := by
  have ho : (𝗭𝗙 : SetTheory) ⊢ (∀⁰ containerRowMatrix : SetTheorySentence) := by
    exact NativeZFContainers254.zf_containerRow_sentence
  have hi := internal_provable_of_outer_provable (V := V) ho
  have hq : (⌜(∀⁰ containerRowMatrix : SetTheorySentence)⌝ : Formula V ℒₛₑₜ) =
      ∀⁰ (⌜containerRowMatrix⌝ : Bootstrapping.Semiformula V ℒₛₑₜ 1) := by
    simp [FirstOrder.Sentence.typed_quote_def]
  rw [hq] at hi
  simpa only [canonicalContainer_quote_subst] using TProof.specialize! hi (&'c)

private lemma mem_quote : (⌜Language.Set.Rel.mem⌝ : V) = 1 := by
  change ((1 : Nat) : V) = 1
  simp

private lemma mem_symbol : (ℒₛₑₜ).IsRel (2 : V) ((1 : Nat) : V) := by
  simpa using (isRel_quote_quote (V := V) (L := ℒₛₑₜ) (k := 2) (x := 1)).mpr
    ⟨Language.Set.Rel.mem,rfl⟩


/-- Typed views keep the already checked formation proof attached during the
finite calculation, rather than repeatedly rediscovering it from a raw code. -/
noncomputable def bindT {n : Nat} (chosen : V)
    (p : Bootstrapping.Semiformula V ℒₛₑₜ n) : Bootstrapping.Semiformula V ℒₛₑₜ (n+1) :=
  ⟨bindOneAt ℒₛₑₜ chosen n p.val, by
    simpa only [Nat.cast_add,Nat.cast_one] using bindOneAt_isSemiformula p.isSemiformula chosen⟩
noncomputable def termBindT {n : Nat} (chosen : V)
    (t : Bootstrapping.Semiterm V ℒₛₑₜ n) : Bootstrapping.Semiterm V ℒₛₑₜ (n+1) :=
  ⟨termBindOneAt ℒₛₑₜ chosen n t.val, by
    simpa only [Nat.cast_add,Nat.cast_one] using termBindOneAt_isSemiterm t.isSemiterm chosen⟩
@[simp] lemma namedBody_bindT (chosen : V) (p : Formula V ℒₛₑₜ) :
    namedBody chosen p = bindT chosen p := rfl
@[simp] lemma bindT_and {n : Nat} (chosen : V)
    (p q : Bootstrapping.Semiformula V ℒₛₑₜ n) :
    bindT chosen (p ⋏ q) = bindT chosen p ⋏ bindT chosen q := by
  apply Bootstrapping.Semiformula.ext
  exact bindOneAt_and chosen n p.isSemiformula.isUFormula q.isSemiformula.isUFormula
@[simp] lemma bindT_imp {n : Nat} (chosen : V)
    (p q : Bootstrapping.Semiformula V ℒₛₑₜ n) :
    bindT chosen (p 🡒 q) = bindT chosen p 🡒 bindT chosen q := by
  apply Bootstrapping.Semiformula.ext
  exact bindOneAt_imp p.isSemiformula q.isSemiformula chosen
@[simp] lemma bindT_all {n : Nat} (chosen : V)
    (p : Bootstrapping.Semiformula V ℒₛₑₜ (n+1)) :
    bindT chosen (∀⁰ p) = ∀⁰ bindT chosen p := by
  apply Bootstrapping.Semiformula.ext
  simpa only [bindT,Bootstrapping.Semiformula.val_all,Nat.cast_add,Nat.cast_one] using
    bindOneAt_all chosen (n : V) p.isSemiformula.isUFormula
@[simp] lemma bindT_ex {n : Nat} (chosen : V)
    (p : Bootstrapping.Semiformula V ℒₛₑₜ (n+1)) :
    bindT chosen (∃⁰ p) = ∃⁰ bindT chosen p := by
  apply Bootstrapping.Semiformula.ext
  simpa only [bindT,Bootstrapping.Semiformula.val_exs,Nat.cast_add,Nat.cast_one] using
    bindOneAt_exs chosen (n : V) p.isSemiformula.isUFormula
@[simp] lemma termBindT_bvar {n : Nat} (chosen : V) (i : Fin n) :
    termBindT chosen (Bootstrapping.Semiterm.bvar i) =
      Bootstrapping.Semiterm.bvar i.castSucc := by
  apply Bootstrapping.Semiterm.ext
  simp [termBindT,Bootstrapping.Semiterm.bvar]
@[simp] lemma termBindT_fvar {n : Nat} (chosen x : V) :
    termBindT chosen (Bootstrapping.Semiterm.fvar x : Bootstrapping.Semiterm V ℒₛₑₜ n) =
      if x = chosen then Bootstrapping.Semiterm.bvar (Fin.last n) else Bootstrapping.Semiterm.fvar x := by
  classical
  apply Bootstrapping.Semiterm.ext
  by_cases h : x = chosen <;>
    simp [termBindT,termBindOneAt_fvar,h,Bootstrapping.Semiterm.bvar]
@[simp] lemma bindT_mem {n : Nat} (chosen : V)
    (t u : Bootstrapping.Semiterm V ℒₛₑₜ n) :
    bindT chosen (memAtom t u) = memAtom (termBindT chosen t) (termBindT chosen u) := by
  apply Bootstrapping.Semiformula.ext
  change bindOneAt ℒₛₑₜ chosen n (^rel 2 ((1 : Nat) : V) ?[t.val,u.val]) =
    ^rel 2 ((1 : Nat) : V) ?[(termBindT chosen t).val,(termBindT chosen u).val]
  rw [Nat.cast_one,bindOneAt_rel chosen n (by simpa using mem_symbol (V := V)) (by simp),
    termBindOneVecAt_pair chosen n t.val u.val t.isUTerm u.isUTerm]
  rfl

/-- A finite calculation, not an induction on arbitrary internal syntax.
The two actual bundle gates plus a≠b resolve every named-variable comparison. -/
lemma nativeContainer_distinct (a b c : V) (hab : a ≠ b) (hca : c ≠ a) (hcb : c ≠ b) :
    nativeContainer a b c = canonicalContainer c := by
  classical
  simp [nativeContainer,nativePower,memNamed,canonicalContainer,namedExists,
    namedFormula,hab,Ne.symm hab,Ne.symm hca,hcb,Ne.symm hcb]

/-- The ordinary theorem is fixed before V, then instantiated at an arbitrary
internal free label. This is the coincident-label vacuity resource. -/
theorem zf_not_mem_self (a : V) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ ∼memNamed a a := by
  have hi := internal_provable_of_outer_provable (V := V)
    ModelCodedDecoderFalsity254.zf_irreflexivity_outer
  have hq : (⌜ModelCodedDecoderFalsity254.irreflexivitySentence⌝ : Formula V ℒₛₑₜ) =
      ∀⁰ ∼memAtom (#'0) (#'0) := by
    apply Bootstrapping.Semiformula.ext
    change (⌜ModelCodedDecoderFalsity254.irreflexivitySentence⌝ : V) =
      ^∀ (neg ℒₛₑₜ (^rel 2 ((1 : Nat) : V) ?[^#0,^#0]))
    rw [Nat.cast_one,neg_rel (by simpa using mem_symbol (V := V)) (by simp)]
    exact ModelCodedDecoderFalsity254.quote_irreflexivity (V := V)
  rw [hq] at hi
  simpa [memNamed,memAtom] using TProof.specialize! hi (&'a)

/-- Monotonicity uses the same actual named-GEN resource as the checked
existential equivalence helper; no closedness premise is added. -/
theorem namedExists_mono (T : SetTheory) [T.Δ₁] (label : V)
    (hGen : ∀ p : V, Provable T p → Provable T (namedAll ℒₛₑₜ label p))
    {p q : Formula V ℒₛₑₜ} (h : T.internalize V ⊢ p 🡒 q) :
    T.internalize V ⊢ namedExists label p 🡒 namedExists label q := by
  classical
  have hn := contra! (namedFormula_mono T label hGen (∼q) (∼p) (contra! h))
  simpa only [namedExists_as_negAll] using hn

/-- One fixed ordinary membership-container consequence of Pairing. -/
def membershipContainerSentence : SetTheorySentence := “∀ c, ∃ b, c ∈ b”

theorem zf_membershipContainer_outer : (𝗭𝗙 : SetTheory) ⊢ membershipContainerSentence := by
  apply SetTheory.provable_of_models.{0}
  intro M _ _ _
  have hm : ∀ c : M, ∃ b : M, c ∈ b := by
    intro c
    obtain ⟨b,hb,_⟩ := NativeZFContainers254.power_containers c
    exact ⟨b,hb⟩
  simpa [membershipContainerSentence,models_iff] using hm

theorem zf_named_membership_exists (a c : V) (hca : c ≠ a) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ namedExists a (memNamed c a) := by
  classical
  have hi := internal_provable_of_outer_provable (V := V) zf_membershipContainer_outer
  have hq : (⌜membershipContainerSentence⌝ : Formula V ℒₛₑₜ) =
      ∀⁰ ∃⁰ memAtom (#'1) (#'0) := by
    rw [FirstOrder.Sentence.typed_quote_def]
    simp [membershipContainerSentence,memAtom,Rew.q_emb,Rew.emb_bvar,
      FirstOrder.Semiformula.Operator.mem_def,quote_vec2]
  rw [hq] at hi
  have hs := TProof.specialize! hi (&'c)
  have he : namedExists a (memNamed c a) =
      ∃⁰ memAtom (&'c) (#'0) := by
    rw [namedExists,memNamed,namedBody_memAtom]
    simp [namedVar,hca]
  rw [he]
  simpa [memAtom,Bootstrapping.SemitermVec.q,Function.comp_def] using hs

/-- The a=b case is proved, not excluded from the bundle gates. The repeated
name makes the antecedent x∈x; its deeper consequent may remain arbitrary. -/
theorem zf_nativeContainer_coincident (a c : V) (hca : c ≠ a) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ nativeContainer a a c := by
  classical
  let q : Formula V ℒₛₑₜ :=
    (namedExists c (nativePower a a c ⋏ memNamed c a)) ⋏
      namedFormula c (memNamed c a 🡒 memNamed c a)
  let univ : Formula V ℒₛₑₜ := namedFormula a (memNamed a a 🡒 q)
  have hp : (𝗭𝗙 : SetTheory).internalize V ⊢ memNamed a a 🡒 q :=
    C_of_N (zf_not_mem_self a)
  have hu : (𝗭𝗙 : SetTheory).internalize V ⊢ univ := by
    apply (tprovable_iff_provable (σ := univ)).mpr
    exact zf_provable_namedAll a ((tprovable_iff_provable).mp hp)
  have hm : (𝗭𝗙 : SetTheory).internalize V ⊢
      memNamed c a 🡒 (univ ⋏ memNamed c a) :=
    right_K!_intro (C!_of_conseq! hu) C!_id
  have he := namedExists_mono 𝗭𝗙 a
    (fun _ hp => zf_provable_namedAll a hp) hm
  have hr := he ⨀ zf_named_membership_exists a c hca
  simpa only [nativeContainer,univ,q] using hr

theorem zf_nativeContainer_provable (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    (𝗭𝗙 : SetTheory).internalize V ⊢ nativeContainer a b c := by
  classical
  by_cases hab : a = b
  · subst b
    exact zf_nativeContainer_coincident a c hca
  · rw [nativeContainer_distinct a b c hab hca hcb]
    exact zf_canonicalContainer_provable c

/-- Exact internal C endpoint with only the actual two bundle gates. -/
theorem zf_decoded_bundleC_provable (a b c : V) (hca : c ≠ a) (hcb : c ≠ b) :
    Provable (𝗭𝗙 : SetTheory) (decode (bundleC a b c)) := by
  apply (tprovable_iff_provable (σ := decoded _)).mp
  exact (iff_of_E! (zf_decoded_container_native_equiv a b c)).mpr
    (zf_nativeContainer_provable a b c hca hcb)


end LeanProofs.ZFCinPA.ModelCodedDecoderContainer254
