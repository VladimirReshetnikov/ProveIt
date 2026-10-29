import ZFCinPA.SetRelativization
import ZFCinPA.ValidatorSourceDerivation222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Actual five closed equality-axiom images for the C222 Eind encoder.
The local finite recognizer has exactly the existing ZFDelta1 instance body.
Arbitrary internal membership is extracted from that recognizer, not from
standardness of the ambient model. Literal irreflexivity uses Eind and
relational vacuity. No R2 theorem, NativeTheory or ZFDelta1 is imported. -/
namespace LeanProofs.ZFCinPA.ValidatorEqualityImages222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222 ValidatorEind222
open ValidatorFormulaEncoder222 ValidatorAtomicTransport222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev SF (n : ℕ) := Bootstrapping.Semiformula V ℒₛₑₜ n
abbrev bv {n : ℕ} (i : Fin n) : Bootstrapping.Semiterm V ℒₛₑₜ n :=
  Bootstrapping.Semiterm.bvar i
abbrev eqAtom {n : ℕ} (i j : Fin n) : SF (V := V) n :=
  Bootstrapping.Semiformula.rel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![bv i,bv j]
abbrev memAtom {n : ℕ} (i j : Fin n) : SF (V := V) n :=
  Bootstrapping.Semiformula.rel (Language.Mem.mem : (ℒₛₑₜ).Rel 2) ![bv i,bv j]
abbrev neqAtom {n : ℕ} (i j : Fin n) : SF (V := V) n :=
  Bootstrapping.Semiformula.nrel (Language.Eq.eq : (ℒₛₑₜ).Rel 2) ![bv i,bv j]
abbrev nmemAtom {n : ℕ} (i j : Fin n) : SF (V := V) n :=
  Bootstrapping.Semiformula.nrel (Language.Mem.mem : (ℒₛₑₜ).Rel 2) ![bv i,bv j]

private lemma encode_pair {n : ℕ} (F B s : V) (R : (ℒₛₑₜ).Rel 2) (i j : Fin n) :
    encode F B s (Bootstrapping.Semiformula.rel R ![bv i,bv j]).val =
      if R=(Language.Eq.eq : (ℒₛₑₜ).Rel 2) then Eind B.[(i : V)] B.[(j : V)] else wel B.[(i : V)] B.[(j : V)] := by
  have hu := (Bootstrapping.Semiformula.rel R ![bv (V := V) i,bv j]).isUFormula
  rw [Bootstrapping.Semiformula.rel_val] at hu
  rw [Bootstrapping.Semiformula.rel_val,
    encode_rel F B s (IsUFormula.rel.mp hu).1 (IsUFormula.rel.mp hu).2]
  have hv := (IsUFormula.rel.mp hu).2
  have h0 := ValidatorEnvironmentLabels254.TermLabels.vec_nth F B hv (show (0 : V) < ↑(2 : ℕ) by simp)
  have h1 := ValidatorEnvironmentLabels254.TermLabels.vec_nth F B hv (show (1 : V) < ↑(2 : ℕ) by simp)
  simp only [atom,nth_adjoin_zero,nth_adjoin_one]
  rw [h0,h1]
  cases R with
  | eq =>
    rw [if_pos (by change ((0 : ℕ) : V)=0; simp), if_pos (by rfl)]
    simp [Matrix.vecHead,Matrix.vecTail]
  | mem =>
    rw [if_neg (by change ((1 : ℕ) : V)≠0; simp), if_neg (by intro he; cases he)]
    simp [Matrix.vecHead,Matrix.vecTail]

lemma encode_eqAtom {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (eqAtom (V := V) i j).val = Eind B.[(i : V)] B.[(j : V)] := by
  simpa [eqAtom] using encode_pair F B s (Language.Eq.eq : (ℒₛₑₜ).Rel 2) i j

lemma encode_memAtom {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (memAtom (V := V) i j).val = wel B.[(i : V)] B.[(j : V)] := by
  simpa [memAtom] using encode_pair F B s (Language.Mem.mem : (ℒₛₑₜ).Rel 2) i j

private lemma encode_nrelT {k n : ℕ} (F B s : V) (R : (ℒₛₑₜ).Rel k)
    (v : Bootstrapping.SemitermVec V ℒₛₑₜ k n) :
    encode F B s (Bootstrapping.Semiformula.nrel R v).val =
      wim (encode F B s (Bootstrapping.Semiformula.rel R v).val) 1 := by
  have hu := (Bootstrapping.Semiformula.rel R v).isUFormula
  rw [Bootstrapping.Semiformula.rel_val] at hu
  rw [Bootstrapping.Semiformula.rel_val,Bootstrapping.Semiformula.nrel_val,
    encode_nrel F B s (IsUFormula.rel.mp hu).1 (IsUFormula.rel.mp hu).2,
    encode_rel F B s (IsUFormula.rel.mp hu).1 (IsUFormula.rel.mp hu).2]
private lemma encode_neqAtom {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (neqAtom (V := V) i j).val = wim (Eind B.[(i : V)] B.[(j : V)]) 1 := by
  rw [neqAtom,encode_nrelT,← eqAtom,encode_eqAtom]
private lemma encode_nmemAtom {n : ℕ} (F B s : V) (i j : Fin n) :
    encode F B s (nmemAtom (V := V) i j).val = wim (wel B.[(i : V)] B.[(j : V)]) 1 := by
  rw [nmemAtom,encode_nrelT,← memAtom,encode_memAtom]
private lemma enc_all {n : ℕ} (F B s : V) (p : SF (V := V) (n+1)) :
    encode F B s (∀⁰ p).val = wal s (encode F (s∷B) (s+2) p.val) :=
  encode_all F B s p.isUFormula
private lemma enc_or {n : ℕ} (F B s : V) (p q : SF (V := V) n) :
    encode F B s (p ⋎ q).val = wim (wim (encode F B s p.val) 1) (encode F B s q.val) :=
  encode_or F B s p.isUFormula q.isUFormula
private lemma enc_bot {n : ℕ} (F B s : V) :
    encode F B s (⊥ : SF (V := V) n).val = 1 := by simp

private abbrev D (G : List V) (p : V) := Kalmar.Der wim CProv G p
private lemma h0 {G : List V} {a : V} : D (a::G) a := .cons_head
private lemma h1 {G : List V} {a b : V} : D (b::a::G) a :=
  .hyp (List.mem_cons_of_mem _ (List.mem_cons_self ..))
private lemma ded2 {a b p : V} (h : D [b,a] p) : CProv (wim a (wim b p)) :=
  (Kalmar.deduction cProv_classical (Kalmar.deduction cProv_classical h)).sound
    cProv_classical (fun _ hm => absurd hm List.not_mem_nil)
private abbrev dn (p : V) := wim (wim p 1) 1
private lemma glue_trans {a b c : V} (h : CProv (wim a (wim b c))) :
    CProv (wim (dn a) (wim (dn b) c)) :=
  ded2 (.mp (.mp (.ax h) (.mp (.ax (double_neg_elim a)) h1))
    (.mp (.ax (double_neg_elim b)) h0))
private lemma glue_ext {a b r r' : V} (h : CProv (wim a (wim b (wim r r')))) :
    CProv (wim (conj (dn a) (dn b)) (wim (dn r) r')) := by
  apply ded2
  have ha : D [dn r,conj (dn a) (dn b)] a :=
    .mp (.ax (double_neg_elim a)) (.mp (.ax (conj_left (dn a) (dn b))) h1)
  have hb : D [dn r,conj (dn a) (dn b)] b :=
    .mp (.ax (double_neg_elim b)) (.mp (.ax (conj_right (dn a) (dn b))) h1)
  exact .mp (.mp (.mp (.ax h) ha) hb) (.mp (.ax (double_neg_elim r)) h0)
private lemma nth_two_cons (a b c d : V) : (a∷b∷c∷d).[2]=c := by
  rw [← one_add_one_eq_two,nth_adjoin_succ,nth_adjoin_one,nth_adjoin_zero]
private lemma nth_three_cons (a b c d e : V) : (a∷b∷c∷d∷e).[3]=d := by
  rw [show (3 : V)=2+1 by norm_num,nth_adjoin_succ,nth_two_cons]
private lemma quote_sentence (σ : SetTheorySentence) :
    (⌜σ⌝ : V) = (⌜(Rewriting.emb σ : SetTheoryProposition)⌝ : Bootstrapping.Formula V ℒₛₑₜ).val := rfl

theorem refl_image (F s : V) :
    CProv (encode F 0 s (⌜(Theory.Eq.refl ℒₛₑₜ : SetTheorySentence)⌝ : V)) := by
  rw [quote_sentence,show (⌜(Rewriting.emb (Theory.Eq.refl ℒₛₑₜ) : SetTheoryProposition)⌝ :
    Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ eqAtom 0 0 from rfl,enc_all,encode_eqAtom]
  simpa using cProv_gen s (eind_refl s)
theorem symm_image (F s : V) :
    CProv (encode F 0 s (⌜(Theory.Eq.symm ℒₛₑₜ : SetTheorySentence)⌝ : V)) := by
  rw [quote_sentence,show (⌜(Rewriting.emb (Theory.Eq.symm ℒₛₑₜ) : SetTheoryProposition)⌝ :
    Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ ∀⁰ (neqAtom 1 0 ⋎ eqAtom 0 1) from rfl,
    enc_all,enc_all,enc_or,encode_neqAtom,encode_eqAtom]
  simpa using cProv_gen s (cProv_gen (s+2)
    (compose (double_neg_elim (Eind s (s+2))) (eind_symm s (s+2))))
theorem trans_image (F s : V) :
    CProv (encode F 0 s (⌜(Theory.Eq.trans ℒₛₑₜ : SetTheorySentence)⌝ : V)) := by
  rw [quote_sentence,show (⌜(Rewriting.emb (Theory.Eq.trans ℒₛₑₜ) : SetTheoryProposition)⌝ :
    Bootstrapping.Formula V ℒₛₑₜ) =
      ∀⁰ ∀⁰ ∀⁰ (neqAtom 2 1 ⋎ (neqAtom 1 0 ⋎ eqAtom 2 0)) from rfl,
    enc_all,enc_all,enc_all,enc_or,enc_or,encode_neqAtom,encode_neqAtom,encode_eqAtom]
  simpa [nth_two_cons] using cProv_gen s (cProv_gen (s+2) (cProv_gen (s+2+2)
    (glue_trans (eind_trans s (s+2) (s+2+2)))))
theorem relExt_mem_image (F s : V) :
    CProv (encode F 0 s (⌜(Theory.Eq.relExt (Language.Mem.mem : (ℒₛₑₜ).Rel 2) :
      SetTheorySentence)⌝ : V)) := by
  rw [quote_sentence,show (⌜(Rewriting.emb (Theory.Eq.relExt
    (Language.Mem.mem : (ℒₛₑₜ).Rel 2)) : SetTheoryProposition)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      ∀⁰ ∀⁰ ∀⁰ ∀⁰ ((neqAtom 0 2 ⋎ (neqAtom 1 3 ⋎ ⊥)) ⋎ (nmemAtom 0 1 ⋎ memAtom 2 3)) from rfl,
    enc_all,enc_all,enc_all,enc_all,enc_or,enc_or,enc_or,enc_or,
    encode_neqAtom,encode_neqAtom,encode_nmemAtom,encode_memAtom,enc_bot]
  simpa [nth_two_cons,nth_three_cons,conj,ValidatorRelationalCore222.neg,dn] using
    cProv_gen s (cProv_gen (s+2) (cProv_gen (s+2+2) (cProv_gen (s+2+2+2)
      (glue_ext (rel_congr (s+2+2+2) (s+2) (s+2+2) s)))))
theorem relExt_eq_image (F s : V) :
    CProv (encode F 0 s (⌜(Theory.Eq.relExt (Language.Eq.eq : (ℒₛₑₜ).Rel 2) :
      SetTheorySentence)⌝ : V)) := by
  rw [quote_sentence,show (⌜(Rewriting.emb (Theory.Eq.relExt
    (Language.Eq.eq : (ℒₛₑₜ).Rel 2)) : SetTheoryProposition)⌝ : Bootstrapping.Formula V ℒₛₑₜ) =
      ∀⁰ ∀⁰ ∀⁰ ∀⁰ ((neqAtom 0 2 ⋎ (neqAtom 1 3 ⋎ ⊥)) ⋎ (neqAtom 0 1 ⋎ eqAtom 2 3)) from rfl,
    enc_all,enc_all,enc_all,enc_all,enc_or,enc_or,enc_or,enc_or,
    encode_neqAtom,encode_neqAtom,encode_neqAtom,encode_eqAtom,enc_bot]
  simpa [nth_two_cons,nth_three_cons,conj,ValidatorRelationalCore222.neg,dn] using
    cProv_gen s (cProv_gen (s+2) (cProv_gen (s+2+2) (cProv_gen (s+2+2+2)
      (glue_ext (eind_congr (s+2+2+2) (s+2) (s+2+2) s)))))

/-- The actual finite recognizer, with no assertion about arbitrary Δ₁ codes. -/
noncomputable abbrev equalityDelta : (𝗘𝗤 ℒₛₑₜ : SetTheory).Δ₁ :=
  Theory.Δ₁.ofFinite _ Theory.EqAxiom.finite

theorem mem_ch_ofList {p : V} (l : List SetTheorySentence)
    (h : V ⊧/![p] (Theory.Δ₁.ofList l).ch.val) : ∃ σ ∈ l, p=⌜σ⌝ :=
  LeanProofs.ZFCinPA.SetRelativization.finite_mem_ch_ofList l h

theorem mem_ch_ofFinite (T : SetTheory) (hT : Set.Finite T) {p : V}
    (h : V ⊧/![p] (Theory.Δ₁.ofFinite T hT).ch.val) : ∃ σ ∈ T, p=⌜σ⌝ :=
  LeanProofs.ZFCinPA.SetRelativization.finite_mem_ch_ofFinite T hT h

/-- No image premise, freshness, parity or standardness hypothesis is supplied. -/
theorem axOK_equality :
    letI := equalityDelta
    ValidatorSourceDerivation222.AxOK (𝗘𝗤 ℒₛₑₜ) V := by
  letI := equalityDelta
  intro p _ hp F s _
  obtain ⟨σ,hσ,rfl⟩ := mem_ch_ofFinite (𝗘𝗤 ℒₛₑₜ) Theory.EqAxiom.finite hp
  cases hσ with
  | refl => exact refl_image F s
  | symm => exact symm_image F s
  | trans => exact trans_image F s
  | funcExt f => cases f
  | relExt r =>
      cases r with
      | eq => exact relExt_eq_image F s
      | mem => exact relExt_mem_image F s

lemma wel_zero_zero : wel (0 : V) 0=1 := by
  have h := ArithmeticCantor.triangle_double (0 : V)
  have h0 : ArithmeticCantor.triangle (0 : V)=0 := by simpa using h
  simp [wel,tagged,ArithmeticCantor.cantor,h0]

/-- Existential Eind plus relational vacuity; no Eind-to-weq identification. -/
theorem not_mem_self (s : V) : CProv (wim (wel s s) 1) := by
  by_cases hs : s=0
  · subst s; rw [wel_zero_zero]; exact Kalmar.self_imp cProv_classical 1
  · have L : CProv (wim (Eind 0 s) (wim (wel s s) 1)) := by
      have r := rel_congr s 0 s 0
      rw [wel_zero_zero] at r
      exact ded2 (.mp (.mp (.mp (.ax r) (.mp (.ax (eind_symm 0 s)) h1))
        (.mp (.ax (eind_symm 0 s)) h1)) h0)
    have e : CProv (ex 0 (wim (wel s s) 1)) := cProv_mp (ex_mono 0 L) (Eind_ex 0 s)
    exact cProv_mp (ex_elim_of_vac (vac_neg (vac_rel s s 0 (Ne.symm hs) (Ne.symm hs)))) e

/-- Literal source sentence only: the broad NativeSet.irAx owner is not imported. -/
theorem irreflexivity_image (F s : V) :
    CProv (encode F 0 s (⌜(“∀ x, x ∈ x → ⊥” : SetTheorySentence)⌝ : V)) := by
  rw [quote_sentence,show (⌜(Rewriting.emb (“∀ x, x ∈ x → ⊥” : SetTheorySentence) :
    SetTheoryProposition)⌝ : Bootstrapping.Formula V ℒₛₑₜ) = ∀⁰ (nmemAtom 0 0 ⋎ ⊥) from rfl,
    enc_all,enc_or,encode_nmemAtom,enc_bot]
  simpa using cProv_gen s (compose (double_neg_elim (wel s s)) (not_mem_self s))

theorem equality_refutation_witness :
    letI := equalityDelta
    Provable (𝗘𝗤 ℒₛₑₜ : SetTheory) (^⊥ : V) →
      ∃ code : V, ArithmeticHistory222.value code=2 := by
  letI := equalityDelta
  exact ValidatorSourceDerivation222.refutation_witness axOK_equality

end LeanProofs.ZFCinPA.ValidatorEqualityImages222
