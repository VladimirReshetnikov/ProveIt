import BusyBeaver.ZFC.Code254GIC

/-!
The elementary direction between the numerical calculus's two model classes.
Encoding a named formula and then decoding it preserves its satisfaction in
an irreflexive structure. Hence a model of every decoded gated bundle is a
model of every literal encodable bundle. This includes the relative-falsity
encoding of genuine Bottom and the separate truth code zero.

The reverse model implication, quotient ZF calibration, enumerator and binary
execution are separate obligations. No new machine or consistency endpoint is
claimed. The numerical definitions retain their attribution in Code254.
-/

namespace SetTheory.BusyBeaver.ZFC.Code254Models

open Tarski (NF)

universe u
variable {V : Type u}

/-- Semantic round trip, including the Bottom-to-Rel00 alias. No syntactic
round-trip assertion is made for formulas with genuine Bottom. -/
theorem sat_encode_decode (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (f : NF) (e : Nat → V) :
    Tarski.Sat mem e (Code254.dec (Code254.enc f)) ↔ Tarski.Sat mem e f := by
  induction f generalizing e with
  | bot =>
      exact ⟨fun h => Code254.sat_F mem hirr e h, False.elim⟩
  | rel i j => exact Code254.sat_wel mem e i j
  | eq i j => exact Code254.sat_weq mem e i j
  | imp f g ihf ihg =>
      exact (Code254.sat_wim mem e (Code254.enc f) (Code254.enc g)).trans
        (imp_congr (ihf e) (ihg e))
  | all i f ih =>
      exact (Code254.sat_wal mem e i (Code254.enc f)).trans
        (forall_congr' (fun x => ih (Tarski.update e i x)))

/-- The soundness model obligation stated explicitly, with the original gate. -/
def ModelsDecoded (mem : V → V → Prop) : Prop :=
  ∀ a b c, c ≠ a → c ≠ b → ∀ e : Nat → V,
    Tarski.Sat mem e (Code254.dec (Code254.bundle a b c))

/-- The completeness model obligation, without hiding domain inhabitation. -/
def ModelsEncodable (mem : V → V → Prop) : Prop :=
  ∀ f, Code254.EncBundle f → ∀ e : Nat → V, Tarski.Sat mem e f

/-- Every decoded-bundle model supplies the literal encodable instances.
The implication does not require a valuation; both predicates are vacuous on
an empty domain. Statements about consistency must supply one separately. -/
theorem encodable_of_decoded (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (h : ModelsDecoded mem) : ModelsEncodable mem := by
  intro f hf e
  obtain ⟨_, a, b, c, hca, hcb, he⟩ := hf
  apply (sat_encode_decode mem hirr f e).mp
  rw [he]
  exact h a b c hca hcb e

/-- An actual nonempty decoded-bundle model rules out derivation of code1. -/
theorem no_refutation_of_decoded (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (h : ModelsDecoded mem) (valuation : Nat → V) : ¬ Code254.C254 1 := by
  intro hf
  exact Code254.sat_F mem hirr valuation
    (Code254.c254_sound mem hirr h hf valuation)

/-- Both numerical model interfaces now feed the existing CP/GIC interface.
The explicit valuation is retained through the full adapter. -/
theorem modelsCPGIC_of_decoded (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (h : ModelsDecoded mem) (valuation : Nat → V) : ProfileModel.ModelsCPGIC mem :=
  Code254GIC.modelsCPGIC_of_encBundle mem hirr valuation (encodable_of_decoded mem hirr h)

end SetTheory.BusyBeaver.ZFC.Code254Models
