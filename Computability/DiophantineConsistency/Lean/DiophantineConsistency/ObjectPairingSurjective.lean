import DiophantineConsistency.ObjectPairingGraph

/-! # Every internal natural has a sharp pairing decomposition

The induction below uses a displayed set-theory formula. It does not
apply external Nat induction to the model's possibly nonstandard omega.
-/
noncomputable section
namespace DiophantineConsistency.ObjectPairingSurjective
set_option maxRecDepth 16000
attribute [local irreducible] ObjectPairingSyntax.expression
open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency ObjectOmegaSemiring
universe u
variable {V : Type u} {mem : V → V → Prop}
variable (H : ZFAxioms mem)
abbrev N := Natural H

private theorem add_one_le_of_lt {a b : N H} (h : a<b) : a+1≤b := by
  obtain ⟨s,rfl⟩ := (ObjectNaturalDiscrete.lt_iff_exists_add_one H a b).mp h
  apply (ObjectNaturalOrder.Natural.le_iff_exists_add H _ _).mpr
  exact ⟨s,by ac_rfl⟩

/-- The two square-boundary transitions are included explicitly. -/
theorem pair_successor (a b : N H) :
    ∃ a' b' : N H, ObjectNatPairing.pair H a' b'=ObjectNatPairing.pair H a b+1 := by
  by_cases hab : a<b
  · have ha1 := add_one_le_of_lt H hab
    rcases lt_or_eq_of_le ha1 with hlt | heq
    · refine ⟨a+1,b,?_⟩
      simp only [ObjectNatPairing.pair,if_pos hlt,if_pos hab]
      ring
    · refine ⟨b,0,?_⟩
      have hb : ¬ b<0 := not_lt_of_ge (ObjectNaturalOrder.Natural.zero_le H b)
      simp only [ObjectNatPairing.pair,if_neg hb,if_pos hab,add_zero]
      rw [← heq]
      ring
  · have hba : b≤a := le_of_not_gt hab
    rcases lt_or_eq_of_le hba with hlt | heq
    · have hb1 := add_one_le_of_lt H hlt
      refine ⟨a,b+1,?_⟩
      simp only [ObjectNatPairing.pair,if_neg hab,if_neg (not_lt_of_ge hb1)]
      ring
    · subst b
      have ha1 : 0<a+1 := (ObjectNaturalDiscrete.lt_iff_exists_add_one H 0 (a+1)).mpr
        ⟨a,by simp⟩
      refine ⟨0,a+1,?_⟩
      simp only [ObjectNatPairing.pair,if_pos ha1,if_neg (lt_irrefl a),add_zero]
      ring

private def stageForm : Form :=
  fEx (fEx (ObjectPairingGraph.graphForm 2 1 0))

private theorem stageForm_spec (z : V) (hz : mem z (omegaV H)) (ee : ℕ → V) :
    Sat mem (scons z ee) stageForm ↔
      ∃ a b : N H, (⟨z,hz⟩ : N H)=ObjectNatPairing.pair H a b := by
  constructor
  · rintro ⟨a,b,h⟩
    obtain ⟨_,ha,hb⟩ := ObjectPairingGraph.graphForm_naturals H _ 2 1 0 h
    exact ⟨⟨a,ha⟩,⟨b,hb⟩,(ObjectPairingGraph.graphForm_spec H _ 2 1 0 hz ha hb).mp h⟩
  · rintro ⟨a,b,h⟩
    exact ⟨a.val,b.val,(ObjectPairingGraph.graphForm_spec H _ 2 1 0
      hz a.property b.property).mpr h⟩

theorem pair_surjective (z : N H) :
    ∃ a b : N H, z=ObjectNatPairing.pair H a b := by
  let ee : ℕ → V := fun _ => vempty H
  have hind : ∀ k, mem k (omegaV H) → Sat mem (scons k ee) stageForm := by
    apply omega_ind H stageForm ee
    · apply (stageForm_spec H (vempty H) (vempty_in_omega H) ee).mpr
      refine ⟨0,0,?_⟩
      simp [ObjectNatPairing.pair]
      rfl
    · intro k hk ih
      apply (stageForm_spec H (vsucc H k) (omega_succ H k hk) ee).mpr
      obtain ⟨a,b,h⟩ := (stageForm_spec H k hk ee).mp ih
      obtain ⟨a',b',hab⟩ := pair_successor H a b
      refine ⟨a',b',?_⟩
      rw [hab,← h]
      apply Subtype.ext
      change vsucc H k=ObjectMultiplication.addValue H k (natV H 1)
      change vsucc H k=ObjectMultiplication.addValue H k (vsucc H (vempty H))
      rw [ObjectMultiplicationLaws.addValue_succ_right H hk (vempty_in_omega H),
        ObjectMultiplicationLaws.addValue_zero_right H hk]
  exact (stageForm_spec H z.val z.property ee).mp (hind z.val z.property)

/-- Surjectivity as an actual sentence in the sealed ZFC calculus. -/
def surjectiveForm : Form := sealF (fImp (fNatF 0) stageForm)
theorem sentence_surjectiveForm : Sentence surjectiveForm := Sentence_seal _

theorem zfc_proves_surjective : BProv ZFCax_s [] surjectiveForm := by
  refine completeness_inf_context ZFCax_s [] surjectiveForm Sentences_ZFC ?_
  intro Dom relation env hmodel _
  let HH := ObjectMultiplication.axioms_of_zfc_model env hmodel
  apply (seal_valid (mem := relation) _).mpr ?_ env
  intro ee h
  have hz := (fNatF_spec HH ee 0).mp h
  have hp := pair_surjective HH ⟨ee 0,hz⟩
  have hs := (stageForm_spec HH (ee 0) hz (fun n => ee (n+1))).mpr hp
  have he : scons (ee 0) (fun n => ee (n+1))=ee := by
    funext n
    cases n <;> rfl
  exact he ▸ hs

end DiophantineConsistency.ObjectPairingSurjective
