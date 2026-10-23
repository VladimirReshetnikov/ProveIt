import BoundedZFCConsistency.AxiomCode

/-!
# An unbounded object-language consistency sentence

The canonical axiom-code predicate recognizes `ZFCax`, whose schema instances
are not universally sealed. This file removes the numerical bound from the
canonical bounded-consistency sentence and proves its exact semantics in every
ZF model. It does not identify this sentence with consistency of `ZFCax_s`:
an internal transformation between the two proof codings is still required.
-/

namespace DiophantineConsistency.ObjectConsistency

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency

set_option maxRecDepth 12000
attribute [local irreducible] SetTheory.sealF

universe u
variable {V : Type u} {mem : V → V → Prop}

/-- There is an internal coded refutation from the canonical unsealed axioms.
Both the formulas and the proof certificate may be nonstandard. -/
def UnsealedRefutation (H : ZFAxioms mem) : Prop :=
  ∃ d g, CtxZFCAxioms H g ∧ Derives H d g (formCode H fBot)

/-- Slots after the three binders: derivation `0`, context `1`, falsity code `2`.
Unlike `conZFCBodyF`, no bound on the certificate is imposed. -/
def unsealedConsistencyBody : Form :=
  fAll (fAll (fAll
    (fImp (fTaggedEmptyF 2 2)
      (fImp (fCtxZFCAxiomsF 1) (fImp (fDerivesF 0 1 2) fBot)))))

theorem unsealedConsistencyBody_spec (H : ZFAxioms mem) (ee : Nat → V) :
    Sat mem ee unsealedConsistencyBody ↔ ¬ UnsealedRefutation H := by
  constructor
  · rintro h ⟨d, g, hax, hder⟩
    exact h (formCode H fBot) g d
      ((fTaggedEmptyF_spec H _ 2 2).mpr rfl)
      ((fCtxZFCAxiomsF_spec H _ 1).mpr hax)
      ((fDerivesF_spec H _ 0 1 2).mpr hder)
  · intro h c g d hc hax hd
    have hc' : c = formCode H fBot := (fTaggedEmptyF_spec H _ 2 2).mp hc
    have hax' := (fCtxZFCAxiomsF_spec H _ 1).mp hax
    have hder := (fDerivesF_spec H _ 0 1 2).mp hd
    rw [hc'] at hder
    exact h ⟨d, g, hax', hder⟩

/-- The unbounded consistency sentence for the repository's internal
`ZFCax`-code predicate. Its name records the unsealed axiom convention. -/
def unsealedConsistencySentence : Form := sealF unsealedConsistencyBody

theorem sentence_unsealedConsistencySentence : Sentence unsealedConsistencySentence :=
  Sentence_seal _

/-- Exact semantics over every internal formula and certificate, including
nonstandard ones. No consistency assertion is assumed or proved. -/
theorem sat_unsealedConsistencySentence_iff (H : ZFAxioms mem) :
    (∀ ee : Nat → V, Sat mem ee unsealedConsistencySentence) ↔
      ¬ UnsealedRefutation H := by
  have hs := seal_valid (mem := mem) unsealedConsistencyBody
  constructor
  · intro h
    exact (unsealedConsistencyBody_spec H (fun _ => vempty H)).mp (hs.mp h _)
  · intro h
    exact hs.mpr (fun ee => (unsealedConsistencyBody_spec H ee).mpr h)

theorem sat_unsealedConsistencySentence_at_iff (H : ZFAxioms mem) (ee : Nat → V) :
    Sat mem ee unsealedConsistencySentence ↔ ¬ UnsealedRefutation H := by
  rw [← sat_unsealedConsistencySentence_iff H]
  constructor
  · intro h ee'
    exact (Sat_sentence_inv _ sentence_unsealedConsistencySentence ee ee').mp h
  · exact fun h => h ee

/-- Every external derivation from unsealed axioms quotes to a refutation
inside any ZF model. There is deliberately no converse quotation theorem. -/
theorem unsealedRefutation_of_external (H : ZFAxioms mem)
    (h : BProv ZFCax [] fBot) : UnsealedRefutation H := by
  obtain ⟨G, hG, hp⟩ := h
  have hp' : Prov G fBot := by simpa only [List.append_nil] using hp
  obtain ⟨d, hd⟩ := derives_of_prov H hp'
  exact ⟨d, ctxCode H G, ctxZFCAxioms_ctxCode H hG, hd⟩

theorem no_external_unsealed_refutation_of_sat (H : ZFAxioms mem)
    (h : ∀ ee : Nat → V, Sat mem ee unsealedConsistencySentence) :
    ¬ BProv ZFCax [] fBot :=
  fun hp => (sat_unsealedConsistencySentence_iff H).mp h
    (unsealedRefutation_of_external H hp)

/-- The unbounded sentence implies every numeral-bounded canonical sentence
inside every ZF model, without any assumption of consistency. -/
theorem bounded_consistency_of_unbounded (H : ZFAxioms mem) (n : Nat)
    (h : ¬ UnsealedRefutation H) :
    ∀ ee : Nat → V, Sat mem ee (conZFCForm n) := by
  apply (sat_conZFCForm_iff H n).mpr
  rintro ⟨d, g, hax, hd, _⟩
  exact h ⟨d, g, hax, hd⟩

/-- The unbounded-to-bounded implication has an actual object-language ZFC
derivation. This does not give a derivation of either consistency sentence. -/
theorem zfc_proves_unbounded_implies_bounded (n : Nat) :
    BProv ZFCax_s [] (fImp unsealedConsistencySentence (conZFCForm n)) := by
  apply BProv_impI
  apply completeness_inf_context ZFCax_s [unsealedConsistencySentence]
    (conZFCForm n) Sentences_ZFC
  intro Dom m ee hmodel hcontext
  let H := zfAxioms_of_zfcModel ee hmodel
  have hsat : Sat m ee unsealedConsistencySentence :=
    hcontext _ (List.Mem.head _)
  exact bounded_consistency_of_unbounded H n
    ((sat_unsealedConsistencySentence_at_iff H ee).mp hsat) ee

/-! The external relationship between axiom sets is elementary. It does not
supply the missing *internal* formula-code/proof-code transformation. -/

theorem sealed_axiom_iff {f : Form} :
    ZFCax_s f ↔ ∃ a, ZFCax a ∧ f = sealF a := by
  constructor
  · intro h
    rcases h with (rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩ |
      ⟨psi, rfl⟩) | rfl <;>
      first
      | exact ⟨_, Or.inr rfl, rfl⟩
      | refine ⟨_, Or.inl ?_, rfl⟩ <;> simp only [ZFax] <;> grind
  · rintro ⟨a, ha, rfl⟩
    rcases ha with (rfl | rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩ |
      ⟨psi, rfl⟩) | rfl <;>
      simp only [ZFCax_s, ZFax_s] <;> grind

/-- Sealed axiom satisfaction supplies every instance of each unsealed axiom.
This works in an arbitrary structure and needs no set-theory axioms. -/
theorem unsealed_axioms_of_sealed_model (ee : Nat → V)
    (h : ∀ f, ZFCax_s f → Sat mem ee f) :
    ∀ f, ZFCax f → ∀ ee' : Nat → V, Sat mem ee' f := by
  intro f hf
  exact extract ZFCax_s ee f h (sealed_axiom_iff.mpr ⟨f, hf, rfl⟩)

/-- External proofs from unsealed axioms transfer to the sealed sentence
theory. The reverse direction requires more than this quotation identity. -/
theorem sealed_proof_of_unsealed {G : List Form} {f : Form}
    (h : BProv ZFCax G f) : BProv ZFCax_s G f := by
  apply theory_transfer ZFCax ZFCax_s G f Sentences_ZFC ?_ h
  intro Dom m ee hmodel a ha
  exact unsealed_axioms_of_sealed_model ee hmodel a ha ee

end DiophantineConsistency.ObjectConsistency
