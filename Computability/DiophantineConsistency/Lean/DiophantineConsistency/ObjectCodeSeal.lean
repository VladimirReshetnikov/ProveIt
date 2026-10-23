import DiophantineConsistency.ObjectCodeBound

/-!
# Internal sealing and the consistency sentence for sealed ZFC axioms

The model computes the same syntactic bound and universal closure as `sealF`.
Applying this operation to the canonical ZFC axiom-code predicate supplies a
sealed axiom-code predicate. The resulting consistency sentence ranges over
all internal formula codes and derivation certificates, not only quotations.
No proof of consistency or internal Diophantine equivalence is asserted.
-/

namespace DiophantineConsistency.ObjectCodeSeal

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
open ObjectCodeBound ObjectCodeClosure ObjectConsistency

set_option maxRecDepth 16000
attribute [local irreducible] SetTheory.sealF

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- The exact internal counterpart of `sealF`, restricted to formula codes. -/
def SealCodeRel (H : ZFAxioms mem) (a c : V) : Prop :=
  IsFormCodeSem H a ∧ ∃ b, BoundCodeRel H a b ∧ CloseCodeRel H a b c

def sealCodeForm (c a : Nat) : Form :=
  fAnd (fIsFormCodeF a)
    (fEx (fAnd (boundCodeForm 0 (a+1)) (closeCodeForm (c+1) (a+1) 0)))

theorem sealCodeForm_spec (H : ZFAxioms mem) (ee : Nat → V) (c a : Nat) :
    Sat mem ee (sealCodeForm c a) ↔ SealCodeRel H (ee a) (ee c) := by
  constructor
  · rintro ⟨ha, b, hb, hc⟩
    exact ⟨(fIsFormCodeF_spec H _ a).mp ha, b,
      (boundCodeForm_spec H _ 0 (a+1)).mp hb,
      (closeCodeForm_spec H _ (c+1) (a+1) 0).mp hc⟩
  · rintro ⟨ha, b, hb, hc⟩
    exact ⟨(fIsFormCodeF_spec H _ a).mpr ha, b,
      (boundCodeForm_spec H _ 0 (a+1)).mpr hb,
      (closeCodeForm_spec H _ (c+1) (a+1) 0).mpr hc⟩

theorem sealCodeRel_total (H : ZFAxioms mem) {a : V} (ha : IsFormCodeSem H a) :
    ∃ c, SealCodeRel H a c := by
  obtain ⟨b, hb⟩ := boundCodeRel_total H a ha
  obtain ⟨c, hc⟩ := closeCodeRel_total H a (boundCodeRel_nat H hb)
  exact ⟨c, ha, b, hb, hc⟩

theorem sealCodeRel_unique (H : ZFAxioms mem) {a c c' : V}
    (h : SealCodeRel H a c) (h' : SealCodeRel H a c') : c = c' := by
  obtain ⟨ha, b, hb, hc⟩ := h
  obtain ⟨_, b', hb', hc'⟩ := h'
  have he := boundCodeRel_unique H a ha b b' hb hb'
  rw [← he] at hc'
  exact closeCodeRel_unique H hc hc'

theorem sealCodeRel_isFormCode (H : ZFAxioms mem) {a c : V}
    (h : SealCodeRel H a c) : IsFormCodeSem H c := by
  obtain ⟨ha, _, _, hc⟩ := h
  exact closeCodeRel_isFormCode H ha hc

theorem sealCodeRel_quotation (H : ZFAxioms mem) (f : Form) :
    SealCodeRel H (formCode H f) (formCode H (sealF f)) := by
  refine ⟨formCode_isFormCodeSem H f, natV H (bound f), boundCodeRel_quotation H f, ?_⟩
  simpa only [sealF] using closeCodeRel_quotation H (bound f) f

noncomputable def sealCodeValue (H : ZFAxioms mem) (a : V) : V :=
  closeCodeValue H a (boundCodeValue H a)

theorem sealCodeValue_spec (H : ZFAxioms mem) {a : V} (ha : IsFormCodeSem H a) :
    SealCodeRel H a (sealCodeValue H a) :=
  ⟨ha, boundCodeValue H a, boundCodeValue_spec H ha,
    closeCodeValue_spec H a (boundCodeValue_nat H ha)⟩

theorem sealCodeValue_quotation (H : ZFAxioms mem) (f : Form) :
    sealCodeValue H (formCode H f) = formCode H (sealF f) :=
  sealCodeRel_unique H (sealCodeValue_spec H (formCode_isFormCodeSem H f))
    (sealCodeRel_quotation H f)

def sealCodeTotalForm : Form := sealF
  (fAll (fImp (fIsFormCodeF 0) (fEx (sealCodeForm 0 1))))

def sealCodeUniqueForm : Form := sealF
  (fAll (fAll (fAll
    (fImp (fAnd (sealCodeForm 1 2) (sealCodeForm 0 2)) (fEq 1 0)))))

theorem sentence_sealCodeTotalForm : Sentence sealCodeTotalForm := Sentence_seal _
theorem sentence_sealCodeUniqueForm : Sentence sealCodeUniqueForm := Sentence_seal _

theorem zfc_proves_sealCode_total : BProv ZFCax_s [] sealCodeTotalForm := by
  apply completeness_inf_context ZFCax_s [] sealCodeTotalForm Sentences_ZFC
  intro Dom m ee hmodel _
  let H := zfAxioms_of_zfcModel ee hmodel
  apply (seal_valid _).mpr ?_ ee
  intro ee' a ha
  obtain ⟨c, hc⟩ := sealCodeRel_total H ((fIsFormCodeF_spec H _ 0).mp ha)
  exact ⟨c, (sealCodeForm_spec H _ 0 1).mpr hc⟩

theorem zfc_proves_sealCode_unique : BProv ZFCax_s [] sealCodeUniqueForm := by
  apply completeness_inf_context ZFCax_s [] sealCodeUniqueForm Sentences_ZFC
  intro Dom m ee hmodel _
  let H := zfAxioms_of_zfcModel ee hmodel
  apply (seal_valid _).mpr ?_ ee
  intro ee' a c c' h
  exact sealCodeRel_unique H ((sealCodeForm_spec H _ 1 2).mp h.1)
    ((sealCodeForm_spec H _ 0 2).mp h.2)

/-! ## The sealed axiom-code predicate and its contexts -/

def IsSealedZFCAxiomCode (H : ZFAxioms mem) (c : V) : Prop :=
  ∃ a, IsZFCAxiomCode H a ∧ SealCodeRel H a c

def sealedZFCAxiomCodeForm (c : Nat) : Form :=
  fEx (fAnd (fZFCAxiomCodeF 0) (sealCodeForm (c+1) 0))

theorem sealedZFCAxiomCodeForm_spec (H : ZFAxioms mem) (ee : Nat → V) (c : Nat) :
    Sat mem ee (sealedZFCAxiomCodeForm c) ↔ IsSealedZFCAxiomCode H (ee c) := by
  constructor
  · rintro ⟨a, ha, hc⟩
    exact ⟨a, (fZFCAxiomCodeF_spec H _ 0).mp ha,
      (sealCodeForm_spec H _ (c+1) 0).mp hc⟩
  · rintro ⟨a, ha, hc⟩
    exact ⟨a, (fZFCAxiomCodeF_spec H _ 0).mpr ha,
      (sealCodeForm_spec H _ (c+1) 0).mpr hc⟩

theorem isSealedZFCAxiomCode_quotation (H : ZFAxioms mem) {f : Form}
    (hf : ZFCax_s f) : IsSealedZFCAxiomCode H (formCode H f) := by
  obtain ⟨a, ha, rfl⟩ := sealed_axiom_iff.mp hf
  exact ⟨formCode H a, isZFCAxiomCode_of_ZFCax H ha, sealCodeRel_quotation H a⟩

theorem isSealedZFCAxiomCode_isFormCode (H : ZFAxioms mem) {c : V}
    (h : IsSealedZFCAxiomCode H c) : IsFormCodeSem H c := by
  obtain ⟨_, _, hc⟩ := h
  exact sealCodeRel_isFormCode H hc

def CtxSealedZFCAxioms (H : ZFAxioms mem) (g : V) : Prop :=
  ∀ x, MemCtx H x g → IsSealedZFCAxiomCode H x

def ctxSealedZFCAxiomsForm (g : Nat) : Form :=
  fAll (fImp (fMemCtxF 0 (g+1)) (sealedZFCAxiomCodeForm 0))

theorem ctxSealedZFCAxiomsForm_spec (H : ZFAxioms mem) (ee : Nat → V) (g : Nat) :
    Sat mem ee (ctxSealedZFCAxiomsForm g) ↔ CtxSealedZFCAxioms H (ee g) := by
  constructor
  · intro h x hx
    exact (sealedZFCAxiomCodeForm_spec H _ 0).mp
      (h x ((fMemCtxF_spec H _ 0 (g+1)).mpr hx))
  · intro h x hx
    exact (sealedZFCAxiomCodeForm_spec H _ 0).mpr
      (h x ((fMemCtxF_spec H _ 0 (g+1)).mp hx))

theorem ctxSealedZFCAxioms_quotation (H : ZFAxioms mem) {G : List Form}
    (hG : ∀ f ∈ G, ZFCax_s f) : CtxSealedZFCAxioms H (ctxCode H G) := by
  intro x hx
  obtain ⟨f, hf, rfl⟩ := (memCtx_ctxCode H G x).mp hx
  exact isSealedZFCAxiomCode_quotation H (hG f hf)

/-! ## The actual unbounded sentence, using the sealed convention -/

def SealedRefutation (H : ZFAxioms mem) : Prop :=
  ∃ d g, CtxSealedZFCAxioms H g ∧ Derives H d g (formCode H fBot)

def consistencyBody : Form :=
  fAll (fAll (fAll
    (fImp (fTaggedEmptyF 2 2)
      (fImp (ctxSealedZFCAxiomsForm 1) (fImp (fDerivesF 0 1 2) fBot)))))

theorem consistencyBody_spec (H : ZFAxioms mem) (ee : Nat → V) :
    Sat mem ee consistencyBody ↔ ¬ SealedRefutation H := by
  constructor
  · rintro h ⟨d, g, hax, hd⟩
    exact h (formCode H fBot) g d ((fTaggedEmptyF_spec H _ 2 2).mpr rfl)
      ((ctxSealedZFCAxiomsForm_spec H _ 1).mpr hax)
      ((fDerivesF_spec H _ 0 1 2).mpr hd)
  · intro h c g d hc hax hd
    have hc' : c = formCode H fBot := (fTaggedEmptyF_spec H _ 2 2).mp hc
    have hd' := (fDerivesF_spec H _ 0 1 2).mp hd
    rw [hc'] at hd'
    exact h ⟨d, g, (ctxSealedZFCAxiomsForm_spec H _ 1).mp hax, hd'⟩

/-- Consistency of the internally coded sealed ZFC axiom theory. -/
def consistencySentence : Form := sealF consistencyBody

theorem sentence_consistencySentence : Sentence consistencySentence := Sentence_seal _

/-- Exact semantics with the entire model's internal formulas and proofs. -/
theorem sat_consistencySentence_iff (H : ZFAxioms mem) :
    (∀ ee : Nat → V, Sat mem ee consistencySentence) ↔ ¬ SealedRefutation H := by
  have hs := seal_valid (mem := mem) consistencyBody
  constructor
  · intro h
    exact (consistencyBody_spec H (fun _ => vempty H)).mp (hs.mp h _)
  · intro h
    exact hs.mpr (fun ee => (consistencyBody_spec H ee).mpr h)

theorem sat_consistencySentence_at_iff (H : ZFAxioms mem) (ee : Nat → V) :
    Sat mem ee consistencySentence ↔ ¬ SealedRefutation H := by
  rw [← sat_consistencySentence_iff H]
  constructor
  · intro h ee'
    exact (Sat_sentence_inv _ sentence_consistencySentence ee ee').mp h
  · exact fun h => h ee

/-- Every actual external refutation from `ZFCax_s` is internally quoted. -/
theorem sealedRefutation_of_external (H : ZFAxioms mem)
    (h : BProv ZFCax_s [] fBot) : SealedRefutation H := by
  obtain ⟨G, hG, hp⟩ := h
  have hp' : Prov G fBot := by simpa only [List.append_nil] using hp
  obtain ⟨d, hd⟩ := derives_of_prov H hp'
  exact ⟨d, ctxCode H G, ctxSealedZFCAxioms_quotation H hG, hd⟩

/-- Satisfaction implies the actual external syntactic consistency statement.
The converse is not valid uniformly for nonstandard models. -/
theorem conZFC_of_sat (H : ZFAxioms mem)
    (h : ∀ ee : Nat → V, Sat mem ee consistencySentence) : ¬ BProv ZFCax_s [] fBot :=
  fun hp => (sat_consistencySentence_iff H).mp h (sealedRefutation_of_external H hp)

end DiophantineConsistency.ObjectCodeSeal
