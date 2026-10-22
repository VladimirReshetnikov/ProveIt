import BusyBeaver.ZFC.ConstructibleOrder
import BusyBeaver.ZFC.ZFModels

/-!
Gödel's theorem: the constructible class of a model of ZF is a model of ZFC,
so ZF and ZFC are equiconsistent.

* `ConstructibleZF.L_models_ZF`: the constructible substructure `N` of a model
  of `ZFax_s` satisfies `ZFax_s`;
* `ConstructibleAbs.vEqL`: `N` satisfies `V = L`;
* `ConstructibleOrder.choice_of_VL`: a model of ZF satisfying `V = L`
  satisfies the selector principle.

Hence `N ⊨ ZFCax_s` (`L_models_ZFC`). By soundness and completeness a ZFC
refutation therefore yields a ZF refutation (`choice_refutation_remove`), the
Choice transport of `foundation_choice_route.md`.
-/

namespace SetTheory.BusyBeaver.ZFC.ConstructibleChoice

open InternalOrd Constructible ConstructibleZF LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

section Model

variable (H : ZFAxioms mem) (hR : Regular mem) (hP : ∀ a, ∃ p, ∀ x, mem x p ↔ Sub mem x a)
include hR

/-- **Choice holds in `L`.** -/
theorem L_choice : ChoiceSem (memL H hP) :=
  ConstructibleOrder.choice_of_VL (L_zfAxioms H hR hP) (L_regular H hR hP) (L_power H hR hP)
    (ConstructibleAbs.vEqL H hR hP)

/-- **The constructible class of a model of ZF is a model of ZFC.** -/
theorem L_models_ZFC (v : Nat → {x // InL H hP x}) : ∀ f, ZFCax_s f → Sat (memL H hP) v f := by
  rintro f (hf | rfl)
  · exact L_models_ZF H hR hP v f hf
  · exact bridge_Choice_sealed.2 (L_choice H hR hP) v

end Model

/-- **The Choice transport**: a refutation of ZFC yields a refutation of ZF
(Gödel 1938). -/
theorem choice_refutation_remove (h : BProv ZFCax_s [] Form.fBot) : BProv ZFax_s [] Form.fBot :=
  completeness_inf_context ZFax_s [] Form.fBot Sentences_ZF fun _ m v hZF _ => by
    obtain ⟨H, hP, hR⟩ := ZFNative.models_ZF m v hZF
    have h0 : InL H hP (vempty H) :=
      inL_ord H hR hP (ord_of_mem (ord_omega H) (vempty_in_omega H))
    exact False.elim (soundness_BProv h (fun _ => (⟨vempty H, h0⟩ : {x // InL H hP x}))
      (L_models_ZFC H hR hP _) fun _ hg => by cases hg)

/-- **ZF and ZFC are equiconsistent.** -/
theorem zf_refutation_iff_zfc_refutation :
    BProv ZFax_s [] Form.fBot ↔ BProv ZFCax_s [] Form.fBot :=
  ⟨BProv_theory_mono (fun _ hb => Or.inl hb), choice_refutation_remove⟩

end SetTheory.BusyBeaver.ZFC.ConstructibleChoice
