import BusyBeaver.ZFC.ZFModels
import BusyBeaver.ZFC.ZFRank
import BusyBeaver.ZFC.NativeTheory254
import BoundedZFCConsistency.Choice

/-!
ZF proves the native axioms.

Every model of `SetTheory.ZFax_s` (ZF with Foundation and Power, as closed
sentences) is a model of the native theory `NativeTheory254.NativeAx`:

* raw irreflexivity is Foundation on a singleton (`InternalOrd.mem_irrefl`);
* the containers are `V_λ` for a limit `λ` above the rank (`ZFRank.containers`);
* every native GIC instance is an instance of Collection for that matrix
  (`ZFRank.collection`), proved through the internal cumulative hierarchy.

`theory_transfer` turns this into the syntactic statement that a refutation
of `NativeAx` yields a refutation of ZF (`zf_refutation_of_native`). With the
Codex lane's `NativeTheory254.program_halts_iff_native_refutation`, halting of
the 219-node program from its boot registers yields a refutation of ZF, and
of ZFC by theory monotonicity; contrapositively, `Con(ZF)` implies that the
program never halts. This is the counterpart of upstream `S_sound.v`
(proved there through the constructible universe), developed independently and
semantically.
-/

namespace SetTheory.BusyBeaver.ZFC.ZFNative

open NativeTheory254 InternalOrd

universe u
variable {V : Type u}

-- models_ZF is provided by ZFModels with its original name.

/-- **Every model of ZF is a model of the native theory.** -/
theorem native_of_zf (mem : V → V → Prop) (v : Nat → V) (h : ∀ f, ZFax_s f → Sat mem v f) :
    ∀ f, NativeAx f → Sat mem v f := by
  obtain ⟨H, hP, hR⟩ := models_ZF mem v h
  refine (models_NativeAx mem v).mpr ⟨fun a => ?_, fun phi env => ?_, mem_irrefl H hR⟩
  · obtain ⟨w, ha, ht, hp⟩ := ZFRank.containers H hR hP a
    exact ⟨w, ha, ht, hp⟩
  · refine (ProfileSyntax.sat_gicForm mem phi env).mpr fun a => ?_
    obtain ⟨b, h1, h2⟩ := ZFRank.collection H hR hP phi env a
    exact ⟨b, h1, h2⟩

/-- **A refutation of the native theory is a refutation of ZF.** -/
theorem zf_refutation_of_native (h : BProv NativeAx [] Form.fBot) : BProv ZFax_s [] Form.fBot :=
  theory_transfer NativeAx ZFax_s [] Form.fBot Sentences_ZF
    (fun _ m v hv => native_of_zf m v hv) h

/-- Halting of the 219-node program from its boot registers refutes ZF. -/
theorem zf_refutation_of_halting
    (h : RMDag.IterHalts Dag254.dag254 (RMDag.upd (fun _ => 0) 0 2)) : BProv ZFax_s [] Form.fBot :=
  zf_refutation_of_native (program_halts_iff_native_refutation.mp h)

/-- **Con(ZF) implies non-halting** of the 219-node program. -/
theorem nonhalting_of_zf_consistent (hCon : ¬ BProv ZFax_s [] Form.fBot) :
    ¬ RMDag.IterHalts Dag254.dag254 (RMDag.upd (fun _ => 0) 0 2) :=
  fun h => hCon (zf_refutation_of_halting h)

/-- Halting of the 219-node program refutes ZFC (`ZFCax_s ⊇ ZFax_s`). -/
theorem zfc_refutation_of_halting
    (h : RMDag.IterHalts Dag254.dag254 (RMDag.upd (fun _ => 0) 0 2)) :
    BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot :=
  BProv_theory_mono (fun _ hb => Or.inl hb) (zf_refutation_of_halting h)

/-- **Con(ZFC) implies non-halting** of the 219-node program. -/
theorem nonhalting_of_zfc_consistent
    (hCon : ¬ BProv LeanProofs.BoundedZFCConsistency.ZFCax_s [] Form.fBot) :
    ¬ RMDag.IterHalts Dag254.dag254 (RMDag.upd (fun _ => 0) 0 2) :=
  fun h => hCon (zfc_refutation_of_halting h)

end SetTheory.BusyBeaver.ZFC.ZFNative
