import BusyBeaver.ZFC.InternalOrd

/-! Semantic content of a ZF model, independent of historical program endpoints.
Moved verbatim from ZFNative.lean; its declaration name is preserved. -/

namespace SetTheory.BusyBeaver.ZFC.ZFNative
open InternalOrd
universe u
variable {V : Type u}

/-- The semantic content of a model of `ZFax_s`. -/
theorem models_ZF (mem : V → V → Prop) (v : Nat → V) (h : ∀ f, ZFax_s f → Sat mem v f) :
    ZFAxioms mem ∧ (∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a) ∧ Regular mem := by
  have hE := extract ZFax_s v Ext_form h (Or.inl rfl)
  have hReg := extract ZFax_s v Reg_form h (Or.inr (Or.inl rfl))
  have hP := extract ZFax_s v Pow_form h (Or.inr (Or.inr (Or.inl rfl)))
  have hPair := extract ZFax_s v Pair_form h (Or.inr (Or.inr (Or.inr (Or.inl rfl))))
  have hU := extract ZFax_s v Union_form h (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl)))))
  have hI := extract ZFax_s v Inf_form h
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl rfl))))))
  have hS (phi : Form) := extract ZFax_s v (Sep_form phi) h
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨phi, rfl⟩)))))))
  have hR (psi : Form) := extract ZFax_s v (Repl_form psi) h
    (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨psi, rfl⟩)))))))
  exact ⟨⟨bridge_Ext.mp hE, bridge_Sep.mp hS, bridge_Pair.mp hPair, bridge_Union.mp hU,
      bridge_Inf_fwd v (hI v), bridge_Repl_fwd hR⟩,
    bridge_Pow.mp hP, bridge_Reg.mp hReg⟩

end SetTheory.BusyBeaver.ZFC.ZFNative
