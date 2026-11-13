import BusyBeaver.ZFC.InductiveAttempts
import BusyBeaver.ZFC.QuotientPower
import BusyBeaver.ZFC.PSCCalibration
import BusyBeaver.ZFC.Code254Models
import BusyBeaver.ZFC.Enum254

/-!
The complete model-side CP/GIC quotient comparison with ZF0.

Here ZF0 means exactly PSCCalibration.ZF0Ax: ordinary Infinity and Power Set
are included, Foundation and Choice are omitted. The component proofs use
actual first-order Separation and Replacement instances. The Infinity field
comes from finite attempts, not from an assumed internal omega.

This composes the attributed CP/GIC interpretation and numerical bundle
adapters. It proves a model construction and its ordinary metatheoretic
consistency consequence. It does not give an arithmetic proof-code translator,
a Foundation/Choice consistency bridge or a binary-machine endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.QuotientZF0

universe u
variable {V : Type u}

/-- All six fields, including ordinary Infinity, now hold in the actual quotient. -/
theorem quotient_zfAxioms (mem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC mem) :
    ZFAxioms (QuotientModel.quotientMember mem witness h) where
  ext := QuotientModel.quotient_extensional mem witness h
  sep := QuotientSeparation.quotient_separation mem witness h
  pair := QuotientBasic.quotient_pair mem witness h
  union := QuotientBasic.quotient_union mem witness h
  inf := InductiveAttempts.quotient_infinity mem witness h
  repl := QuotientReplacement.quotient_replacement mem witness h

/-- Power Set is kept explicit, since the repository's ZFAxioms bundle omits it. -/
theorem quotient_zf0 (mem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC mem) :
    ZFAxioms (QuotientModel.quotientMember mem witness h) ∧
      PSCCalibration.PowerSets (QuotientModel.quotientMember mem witness h) :=
  ⟨quotient_zfAxioms mem witness h, QuotientPower.quotient_power mem witness h⟩

/-- Every actual closed ZF0 axiom holds under every quotient valuation. -/
theorem quotient_models (mem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC mem)
    (env : Nat → QuotientModel.Domain mem witness h) :
    ∀ phi, PSCCalibration.ZF0Ax phi →
      Sat (QuotientModel.quotientMember mem witness h) env phi :=
  (PSCCalibration.models_ZF0 _ env).mpr (quotient_zf0 mem witness h)

/-- The explicit raw witness supplies a quotient valuation for soundness. -/
theorem zf0_consistent_of_model (mem : V → V → Prop) (witness : V)
    (h : ProfileModel.ModelsCPGIC mem) : ¬ BProv PSCCalibration.ZF0Ax [] .fBot := by
  intro hf
  exact soundness_BProv hf (fun _ => QuotientModel.mk mem witness h witness)
    (quotient_models mem witness h _) (fun _ hNil => by cases hNil)

/-- Literal decoded numerical bundles feed the full quotient construction. -/
theorem decoded_quotient_zf0 (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (h : Code254Models.ModelsDecoded mem) (valuation : Nat → V) :
    let hCP := Code254Models.modelsCPGIC_of_decoded mem hirr h valuation
    ZFAxioms (QuotientModel.quotientMember mem (valuation 0) hCP) ∧
      PSCCalibration.PowerSets (QuotientModel.quotientMember mem (valuation 0) hCP) :=
  quotient_zf0 mem (valuation 0)
    (Code254Models.modelsCPGIC_of_decoded mem hirr h valuation)

/-- A nonempty decoded numerical model implies the ordinary consistency of ZF0. -/
theorem zf0_consistent_of_decoded (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (h : Code254Models.ModelsDecoded mem) (valuation : Nat → V) :
    ¬ BProv PSCCalibration.ZF0Ax [] .fBot :=
  zf0_consistent_of_model mem (valuation 0)
    (Code254Models.modelsCPGIC_of_decoded mem hirr h valuation)

/-- A refutation of the actual ZF0 theory forces numerical falsity.
Completeness ranges over nonempty EncBundle models via explicit valuations;
no converse model comparison between EncBundle and decoded bundles is needed. -/
theorem c254_of_zf0_refutation (hf : BProv PSCCalibration.ZF0Ax [] .fBot) :
    Code254.C254 Code254.F := by
  apply Code254.c254_complete
  intro D mem hirr hBundle valuation
  exact zf0_consistent_of_model mem (valuation 0)
    (Code254GIC.modelsCPGIC_of_encBundle mem hirr valuation hBundle) hf

/-- This is the abstract six-register enumerator, not Prog254 or the binary TM. -/
theorem enum_halts_of_zf0_refutation (hf : BProv PSCCalibration.ZF0Ax [] .fBot) :
    Enum254.Halts :=
  Enum254.complete (c254_of_zf0_refutation hf)

/-- The corresponding one-way consistency statement, at the abstract level. -/
theorem zf0_consistent_of_enum_nonhalting (h : ¬ Enum254.Halts) :
    ¬ BProv PSCCalibration.ZF0Ax [] .fBot :=
  fun hf => h (enum_halts_of_zf0_refutation hf)

end SetTheory.BusyBeaver.ZFC.QuotientZF0
