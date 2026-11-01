import BusyBeaver.ZFC.DefinableClosure
import BusyBeaver.ZFC.PowerSets
import ZF.Zf
import FirstOrder.Completeness

/-!
Actual first-order calibration of Extensionality + subset-seeded PSC.

The comparison theory is ZF with Foundation and Choice omitted, with functional
Replacement. The reverse uses the repository's internal definable-recursion
theorem `ClosureFO_of_ZF`; it does not close under arbitrary semantic relations.
Generic first-order completeness then gives deductive equivalence in `BProv`.
This theorem does not produce a computable proof-code translator, formalize the
Foundation/Choice consistency interpretations, or certify any machine endpoint.
-/

namespace SetTheory.BusyBeaver.ZFC.PSCCalibration

open Form DeepPositiveClosure DefinableClosure

universe u
variable {V : Type u}

def swapArgs : Nat → Nat
  | 0 => 1
  | 1 => 0
  | k + 2 => k + 2

theorem sat_swap (mem : V → V → Prop) (phi : Form) (env : Nat → V) (x y : V) :
    Sat mem (scons x (scons y env)) (rename swapArgs phi) ↔
      Sat mem (scons y (scons x env)) phi := by
  exact Sat_rename_ext phi swapArgs _ _
    (fun n => match n with | 0 => rfl | 1 => rfl | _ + 2 => rfl)

/-- The forward constructions have exactly the repository's first-order ZF interface. -/
theorem zfAxioms_of_psc (mem : V → V → Prop) (witness : V)
    (hExt : Bootstrap.Extensional mem) (hPSC : ModelsPSC mem) : ZFAxioms mem := by
  refine ⟨hExt, ?_, pairing_of_model mem hPSC, ?_, ?_, ?_⟩
  · intro phi env a
    exact separation_of_model mem witness hPSC a phi env
  · intro a
    obtain ⟨s, hs⟩ := union_of_model mem witness hPSC a
    refine ⟨s, ?_⟩
    intro y
    apply (hs y).trans
    exact exists_congr (fun x => and_comm)
  · obtain ⟨empty, i, he, hi⟩ := infinity_of_model mem witness hPSC
    refine ⟨i, ⟨empty, hi.1, he⟩, ?_⟩
    intro x hx
    obtain ⟨y, hxy, hy⟩ := hi.2 x hx
    exact ⟨y, hy, hxy⟩
  · intro psi env hFunctional a
    have hSwap (x y : V) :
        MatrixRelation mem (rename swapArgs psi) env x y ↔ relOf mem psi env y x :=
      sat_swap mem psi env x y
    have hFunc : Bootstrap.PartialFunctionalOn mem a
        (MatrixRelation mem (rename swapArgs psi) env) := by
      intro x _ y z hy hz
      exact hFunctional x y z ((hSwap x y).mp hy) ((hSwap x z).mp hz)
    obtain ⟨b, hb⟩ := partial_replacement_of_model mem witness hPSC a
      (rename swapArgs psi) env hFunc
    refine ⟨b, ?_⟩
    intro y
    exact (hb y).trans (exists_congr (fun x => and_congr Iff.rfl (hSwap x y)))

/-- A ZF model's set-like closure hull can be separated to its supported outputs. -/
theorem psc_of_zfAxioms (mem : V → V → Prop) (H : ZFAxioms mem)
    (hPower : PowerSets mem) : ModelsPSC mem := by
  intro phi env
  apply (sat_pscForm mem phi env).mpr
  intro hBound a
  have hSetLike : SetLike mem (relOf mem (rename swapArgs phi) env) := by
    intro x
    obtain ⟨b, hb⟩ := hBound x
    obtain ⟨p, hp⟩ := hPower b
    refine ⟨p, ?_⟩
    intro y hy
    exact (hp y).mpr (hb y ((sat_swap mem phi env y x).mp hy))
  obtain ⟨seed, hSeed⟩ := hPower a
  obtain ⟨w, hw, hClosed⟩ := ClosureFO_of_ZF H (rename swapArgs phi) env hSetLike seed
  obtain ⟨c, hc⟩ := H.sep (fEx phi) env w
  refine ⟨c, ?_, ?_⟩
  · intro x y hActive hxy
    have hxW : mem x w := by
      rcases hActive with hxSeed | hxC
      · exact hw x ((hSeed x).mpr hxSeed)
      · exact ((hc x).mp hxC).1
    have hyW := hClosed y x ((sat_swap mem phi env y x).mpr hxy) hxW
    exact (hc y).mpr ⟨hyW, x, hxy⟩
  · intro y hy
    exact ((hc y).mp hy).2

/-- Model calibration; neither side includes Foundation or Choice. -/
theorem psc_iff_zfAxioms (mem : V → V → Prop) (witness : V) :
    (Bootstrap.Extensional mem ∧ ModelsPSC mem) ↔
      (ZFAxioms mem ∧ PowerSets mem) := by
  constructor
  · rintro ⟨hExt, hPSC⟩
    exact ⟨zfAxioms_of_psc mem witness hExt hPSC, power_of_model mem witness hPSC⟩
  · rintro ⟨H, hPower⟩
    exact ⟨H.ext, psc_of_zfAxioms mem H hPower⟩

/-- Closed sentence presentation of the candidate, with logical equality. -/
def PSCAx (f : Form) : Prop :=
  f = sealF Ext_form ∨ ∃ phi, f = sealF (pscForm phi)

/-- ZF without Foundation or Choice; no Collection schema is added. -/
def ZF0Ax (f : Form) : Prop :=
  f = sealF Ext_form ∨ f = sealF Pow_form ∨ f = sealF Pair_form ∨
  f = sealF Union_form ∨ f = sealF Inf_form ∨
  (∃ phi, f = sealF (Sep_form phi)) ∨ (∃ psi, f = sealF (Repl_form psi))

theorem sentences_PSC : Sentences PSCAx := by
  intro f hf
  rcases hf with rfl | ⟨phi, rfl⟩ <;> exact Sentence_seal _

theorem sentences_ZF0 : Sentences ZF0Ax := by
  intro f hf
  rcases hf with rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩ | ⟨psi, rfl⟩ <;>
    exact Sentence_seal _

theorem models_PSC (mem : V → V → Prop) (v : Nat → V) :
    (∀ f, PSCAx f → Sat mem v f) ↔
      (Bootstrap.Extensional mem ∧ ModelsPSC mem) := by
  constructor
  · intro h
    exact ⟨bridge_Ext.mp (extract PSCAx v Ext_form h (Or.inl rfl)),
      fun phi => extract PSCAx v (pscForm phi) h (Or.inr ⟨phi, rfl⟩)⟩
  · rintro ⟨hExt, hPSC⟩ f hf
    rcases hf with rfl | ⟨phi, rfl⟩
    · exact (closeN_valid (bound Ext_form) Ext_form).mpr (bridge_Ext.mpr hExt) v
    · exact (closeN_valid (bound (pscForm phi)) (pscForm phi)).mpr (hPSC phi) v

theorem models_ZF0 (mem : V → V → Prop) (v : Nat → V) :
    (∀ f, ZF0Ax f → Sat mem v f) ↔ (ZFAxioms mem ∧ PowerSets mem) := by
  constructor
  · intro h
    have hE := extract ZF0Ax v Ext_form h (Or.inl rfl)
    have hP := extract ZF0Ax v Pow_form h (Or.inr (Or.inl rfl))
    have hPair := extract ZF0Ax v Pair_form h (Or.inr (Or.inr (Or.inl rfl)))
    have hU := extract ZF0Ax v Union_form h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
    have hI := extract ZF0Ax v Inf_form h
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
    have hS (phi : Form) := extract ZF0Ax v (Sep_form phi) h
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨phi, rfl⟩))))))
    have hR (psi : Form) := extract ZF0Ax v (Repl_form psi) h
      (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨psi, rfl⟩))))))
    exact ⟨⟨bridge_Ext.mp hE, bridge_Sep.mp hS, bridge_Pair.mp hPair,
      bridge_Union.mp hU, bridge_Inf_fwd v (hI v), bridge_Repl_fwd hR⟩,
      bridge_Pow.mp hP⟩
  · rintro ⟨H, hPower⟩ f hf
    rcases hf with rfl | rfl | rfl | rfl | rfl | ⟨phi, rfl⟩ | ⟨psi, rfl⟩
    · exact (closeN_valid (bound Ext_form) Ext_form).mpr (bridge_Ext.mpr H.ext) v
    · exact (closeN_valid (bound Pow_form) Pow_form).mpr (bridge_Pow.mpr hPower) v
    · exact (closeN_valid (bound Pair_form) Pair_form).mpr (bridge_Pair.mpr H.pair) v
    · exact (closeN_valid (bound Union_form) Union_form).mpr (bridge_Union.mpr H.union) v
    · exact (closeN_valid (bound Inf_form) Inf_form).mpr
        (fun env => (bridge_Inf env).mpr H.inf) v
    · exact (closeN_valid (bound (Sep_form phi)) (Sep_form phi)).mpr
        (fun env => bridge_Sep.mpr H.sep phi env) v
    · exact (closeN_valid (bound (Repl_form psi)) (Repl_form psi)).mpr
        (fun env => (bridge_Repl psi env).mpr (H.repl psi env)) v

theorem same_models (Dom : Type) (mem : Dom → Dom → Prop) (v : Nat → Dom) :
    (∀ f, PSCAx f → Sat mem v f) ↔ (∀ f, ZF0Ax f → Sat mem v f) :=
  (models_PSC mem v).trans ((psc_iff_zfAxioms mem (v 0)).trans (models_ZF0 mem v).symm)

/-- The two actual first-order theories prove the same sentence formulas. -/
theorem psc_iff_zf0 (phi : Form) (hSentence : Sentence phi) :
    BProv PSCAx [] phi ↔ BProv ZF0Ax [] phi :=
  theory_equiv PSCAx ZF0Ax sentences_PSC sentences_ZF0 same_models phi hSentence

theorem psc_consistency_iff_zf0 :
    (¬ BProv PSCAx [] fBot) ↔ (¬ BProv ZF0Ax [] fBot) :=
  not_congr (psc_iff_zf0 fBot (by intro n h; exact h))

#print axioms psc_of_zfAxioms
#print axioms psc_iff_zfAxioms
#print axioms psc_iff_zf0
#print axioms psc_consistency_iff_zf0

end SetTheory.BusyBeaver.ZFC.PSCCalibration
