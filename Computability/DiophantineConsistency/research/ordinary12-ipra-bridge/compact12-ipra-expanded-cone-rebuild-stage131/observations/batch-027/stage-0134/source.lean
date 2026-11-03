import BusyBeaver.ZFC.NativeDecoded254
import BusyBeaver.ZFC.L2Root254
import FirstOrder.Completeness

/-!
An actual first-order theory for the original numerical calculus.

NativeAx consists exactly of universal closures of CP, each native-Form GIC
instance, and raw irreflexivity. The first-order and named/numerical model
adapters yield refutation equivalence by the existing completeness theorems.
An explicit valuation remains in every semantic statement using a model.

The resulting structured-program theorem concerns the actual219-node DAG
from nextproof=2. It does not identify that DAG with the different literal
Prog254 tree, prove the binary simulation, calibrate to ZFC, or construct a
computable proof-code translator. No quotient or quotient-IR assumption occurs.
-/

namespace SetTheory.BusyBeaver.ZFC.NativeTheory254

open Form ProfileCollection ProfileModel ProfileSyntax NativeDecoded254

/-- Literal first-order irreflexivity, with genuine Bottom. -/
def irForm : Form := fAll (fImp (fMem 0 0) fBot)

/-- All theory axioms are sentences; matrix parameters are universally closed. -/
def NativeAx (f : Form) : Prop :=
  f = sealF containerForm ∨ (∃ phi, f = sealF (gicForm phi)) ∨ f = sealF irForm

theorem sentences_NativeAx : Sentences NativeAx := by
  intro f hf
  rcases hf with rfl | ⟨phi, rfl⟩ | rfl <;> exact Sentence_seal _

universe u
variable {V : Type u}

theorem sat_irForm (mem : V → V → Prop) (v : Nat → V) :
    Sat mem v irForm ↔ ∀ x, ¬ mem x x := Iff.rfl

/-- Exact semantic content, without an arbitrary-relation collection premise. -/
theorem models_NativeAx (mem : V → V → Prop) (v : Nat → V) :
    (∀ f, NativeAx f → Sat mem v f) ↔
      Containers mem ∧ FullGIC mem ∧ (∀ x, ¬ mem x x) := by
  constructor
  · intro h
    refine ⟨(sat_containerForm mem v).mp ?_, ?_, ?_⟩
    · exact extract NativeAx v containerForm h (Or.inl rfl) v
    · intro phi
      exact extract NativeAx v (gicForm phi) h (Or.inr (Or.inl ⟨phi, rfl⟩))
    · exact (sat_irForm mem v).mp
        (extract NativeAx v irForm h (Or.inr (Or.inr rfl)) v)
  · rintro ⟨hc, hg, hirr⟩ f hf
    rcases hf with rfl | ⟨phi, rfl⟩ | rfl
    · exact (closeN_valid (bound containerForm) containerForm).mpr
        (fun env => (sat_containerForm mem env).mpr hc) v
    · exact (closeN_valid (bound (gicForm phi)) (gicForm phi)).mpr (hg phi) v
    · exact (closeN_valid (bound irForm) irForm).mpr
        (fun env => (sat_irForm mem env).mpr hirr) v

/-- Every literal theory model supplies numerical soundness's model class. -/
theorem decoded_of_native (mem : V → V → Prop) (v : Nat → V)
    (h : ∀ f, NativeAx f → Sat mem v f) :
    (∀ x, ¬ mem x x) ∧ Code254Models.ModelsDecoded mem := by
  obtain ⟨hc, hg, hirr⟩ := (models_NativeAx mem v).mp h
  exact ⟨hirr, NativeDecoded254.modelsDecoded mem hirr hc hg⟩

/-- Every nonempty EncBundle model satisfies the actual closed theory. -/
theorem native_of_encodable (mem : V → V → Prop) (hirr : ∀ x, ¬ mem x x)
    (h : Code254Models.ModelsEncodable mem) (v : Nat → V) :
    ∀ f, NativeAx f → Sat mem v f :=
  (models_NativeAx mem v).mpr
    ⟨Code254Containers.containers_of_encBundle mem hirr v h,
      fullGIC_of_encodable mem hirr h v, hirr⟩

/-- Refutation equivalence for the exact numerical and first-order theories. -/
theorem c254_refutation_iff :
    Code254.C254 Code254.F ↔ BProv NativeAx [] fBot := by
  constructor
  · intro hf
    apply completeness_inf NativeAx fBot sentences_NativeAx (by intro n h; exact h)
    intro D mem v hNative
    obtain ⟨hirr, hDecoded⟩ := decoded_of_native mem v hNative
    exact Code254Models.no_refutation_of_decoded mem hirr hDecoded v hf
  · intro hf
    apply Code254.c254_complete
    intro D mem hirr hEnc v
    exact soundness_BProv hf v (native_of_encodable mem hirr hEnc v)
      (fun _ hNil => by cases hNil)

/-- The actual structured program, from its specified boot register vector. -/
theorem program_halts_iff_native_refutation :
    RMDag.IterHalts Dag254.dag254 (RMDag.upd (fun _ => 0) 0 2) ↔
      BProv NativeAx [] fBot :=
  L2.program_halts_iff.trans c254_refutation_iff

/-- Corresponding consistency statement at the actual structured-DAG layer. -/
theorem native_consistency_iff_program_nonhalting :
    (¬ BProv NativeAx [] fBot) ↔
      ¬ RMDag.IterHalts Dag254.dag254 (RMDag.upd (fun _ => 0) 0 2) :=
  not_congr program_halts_iff_native_refutation.symm

end SetTheory.BusyBeaver.ZFC.NativeTheory254
