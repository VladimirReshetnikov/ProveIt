import ZFCinPA.ValidatorEnvironmentStreams222
import ZFCinPA.ValidatorEnvironmentSubstitution222

set_option autoImplicit false
set_option Elab.async false
noncomputable section

/-! Finite quantifier transport for the actual C222 encoder. The selected
label avoids the original free labels and binder stream. Numeric source
opening and actual alpha transport produce quantified-body equivalences.
The universal inference under a hypothesis retains its explicit vacuity
premise; one shifted source-hypothesis client derives that premise. This
is not the EXS term rule or arbitrary source-proof translation. -/
namespace LeanProofs.ZFCinPA.ValidatorQuantifierRules222
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open LO.FirstOrder.Arithmetic.Bootstrapping
open _root_.SetTheory.BusyBeaver.ZFC ArithmeticCode254
open ValidatorProvability222 ValidatorRelationalCore222
open ValidatorFormulaEncoder222 ValidatorEnvironmentVacuity222
open ValidatorEnvironmentAlpha222 ValidatorEnvironmentStreams222
open ValidatorEnvironmentSubstitution222
open scoped LO.FirstOrder.Arithmetic
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

abbrev eigen (F s : V) : V := alternateStart F s

private lemma streamFree_cons {F s x : V}
    (hs : StreamFree s F) (hx : StreamAvoid x s) : StreamFree s (x∷F) := by
  intro k
  exact ⟨(hs k).1,avoid_cons (hs k).2 (hx k).symm⟩

/-- Only the new label is selected; safety of the original stream is retained.
The same resources permit repeated/zero stored labels and fallback1. -/
lemma fresh_resources (F s : V) (hs : StreamFree s F) :
    FreeAvoid (eigen F s) F ∧ StreamAvoid (eigen F s) s ∧
    StreamFree s (eigen F s∷F) ∧
    StreamFree (eigen F s+2) (eigen F s∷F) ∧ StreamFree (eigen F s) F := by
  have hx : StreamFree (eigen F s) F := alternateStart_free F s F le_rfl
  have hxs : StreamAvoid (eigen F s) s := by
    intro k
    simpa using (alternateStart_apart F s k 0).symm
  exact ⟨by simpa using hx 0,hxs,streamFree_cons hs hxs,
    streamFree_cons (streamFree_next hx) (stream_of_lt (by simp)),hx⟩

section Transport

/-- The source opening is a depth-zero formula, so formula alpha applies
with the unchanged extended free environment on both sides. -/
lemma opened_body_equiv {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F s : V) (hs : StreamFree s F) :
    CProv (wim (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p))
      (encode (eigen F s∷F) 0 (eigen F s+2) (free ℒₛₑₜ p))) ∧
    CProv (wim (encode (eigen F s∷F) 0 (eigen F s+2) (free ℒₛₑₜ p))
      (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p))) := by
  have hr := fresh_resources F s hs
  exact encode_formula_relabel hp.free (eigen F s∷F) s (eigen F s+2)
    hr.2.2.1 hr.2.2.2.1

/-- Object-level equivalence of quantified bodies, not P→∀xP. -/
theorem all_opened_equiv {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F s : V) (hs : StreamFree s F) :
    CProv (wim (wal (eigen F s) (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p)))
      (encode F 0 s (^∀ p))) ∧
    CProv (wim (encode F 0 s (^∀ p))
      (wal (eigen F s) (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p)))) := by
  have hb := opened_body_equiv hp F s hs
  have hr := encode_formula_relabel (show IsFormula ℒₛₑₜ (^∀ p) by simpa using hp)
    F (eigen F s) s (fresh_resources F s hs).2.2.2.2 hs
  have hf := all_mono (eigen F s) hb.1
  have hg := all_mono (eigen F s) hb.2
  rw [←encode_all_opened hp F (eigen F s)] at hf hg
  exact ⟨compose hf hr.1,compose hr.2 hg⟩

/-- This transports an existentially quantified body. Instantiation at an
arbitrary source term is a separate rule, not assumed or proved here. -/
theorem ex_opened_equiv {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F s : V) (hs : StreamFree s F) :
    CProv (wim (ex (eigen F s) (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p)))
      (encode F 0 s (^∃ p))) ∧
    CProv (wim (encode F 0 s (^∃ p))
      (ex (eigen F s) (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p)))) := by
  have hb := opened_body_equiv hp F s hs
  have hr := encode_formula_relabel (show IsFormula ℒₛₑₜ (^∃ p) by simpa using hp)
    F (eigen F s) s (fresh_resources F s hs).2.2.2.2 hs
  have hf := ex_mono (eigen F s) hb.1
  have hg := ex_mono (eigen F s) hb.2
  change CProv (wim (ex (eigen F s) _) (ex (eigen F s) _)) at hf hg
  rw [show ex (eigen F s) (encode (eigen F s∷F) 0 (eigen F s+2) (free ℒₛₑₜ p))=
    encode F 0 (eigen F s) (^∃ p) from (encode_exs_opened hp F (eigen F s)).symm] at hf hg
  exact ⟨compose hf hr.1,compose hr.2 hg⟩

/-- Generalization of an actual theorem, with no undischarged hypothesis. -/
theorem all_rule {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F s : V) (hs : StreamFree s F)
    (h : CProv (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p))) :
    CProv (encode F 0 s (^∀ p)) :=
  cProv_mp (all_opened_equiv hp F s hs).1 (cProv_gen (eigen F s) h)

/-- A hypothesis may be retained only with its actual vacuity certificate. -/
theorem all_rule_under {p : V} (hp : IsSemiformula ℒₛₑₜ 1 p)
    (F s H : V) (hs : StreamFree s F) (hH : Vac (eigen F s) H)
    (h : CProv (wim H (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p)))) :
    CProv (wim H (encode F 0 s (^∀ p))) :=
  compose (compose hH (all_mono (eigen F s) h)) (all_opened_equiv hp F s hs).1

/-- The one-source-hypothesis ALL case uses the literal source shift and
actual encoded vacuity. This is not an arbitrary sequent-context fold. -/
theorem all_rule_under_negated_source {p A : V}
    (hp : IsSemiformula ℒₛₑₜ 1 p) (hA : IsFormula ℒₛₑₜ A)
    (F s : V) (hs : StreamFree s F)
    (h : CProv (wim (neg (encode (eigen F s∷F) 0 s (shift ℒₛₑₜ A)))
      (encode (eigen F s∷F) 0 s (free ℒₛₑₜ p)))) :
    CProv (wim (neg (encode F 0 s A)) (encode F 0 s (^∀ p))) := by
  have he : encode (eigen F s∷F) 0 s (shift ℒₛₑₜ A)=encode F 0 s A := by
    rw [encode_shift hA.isUFormula,ValidatorEnvironmentLabels254.tail_cons]
  rw [he] at h
  have hr := fresh_resources F s hs
  exact all_rule_under hp F s (neg (encode F 0 s A)) hs
    (vac_neg (encode_formula_vac hA F s (eigen F s) hr.1 hr.2.1)) h

end Transport
end LeanProofs.ZFCinPA.ValidatorQuantifierRules222
