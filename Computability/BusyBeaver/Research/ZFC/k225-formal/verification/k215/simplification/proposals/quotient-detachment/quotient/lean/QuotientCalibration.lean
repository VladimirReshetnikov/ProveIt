import Quotient222
import BusyBeaver.ZFC.KUpper222

/-!
The quotient-detachment calculus has the same upper consistency bound as
the existing 222 calculus.  The only extra model property needed by quotient
detachment is a pair of distinct elements.  The empty set and its successor
provide these inside the existing constructible-model interpretation.
-/

namespace SetTheory.BusyBeaver.ZFC.QuotientCalibration

open InternalOrd Constructible ConstructibleZF ConstructibleReflect
open LeanProofs.BoundedZFCConsistency
open KCode222 Quotient222

/-- A quotient-calculus refutation yields an ordinary first-order ZF
refutation, using the repository's existing completeness and L-model bridge. -/
theorem zf_refutation_of_q222 (h : Q222 Code254.F) :
    BProv ZFax_s [] Form.fBot :=
  completeness_inf_context ZFax_s [] Form.fBot Sentences_ZF fun _ m v hZF _ => by
    obtain ⟨H, hP, hR⟩ := ZFNative.models_ZF m v hZF
    have hOrd := ord_of_mem (ord_omega H) (vempty_in_omega H)
    have h0 : InL H hP (vempty H) := inL_ord H hR hP hOrd
    have h1 : InL H hP (vsucc H (vempty H)) :=
      inL_ord H hR hP (ord_succ H hOrd)
    let x : {x // InL H hP x} := ⟨vempty H, h0⟩
    let y : {x // InL H hP x} := ⟨vsucc H (vempty H), h1⟩
    have hxy : x ≠ y := by
      intro he
      have he' : vempty H = vsucc H (vempty H) := congrArg Subtype.val he
      have hs := vsucc_self H (vempty H)
      rw [← he'] at hs
      exact mem_irrefl H hR (vempty H) hs
    exact False.elim (q222_no_false (memL H hP)
      (fun z => mem_irrefl H hR z.1) x y hxy
      (KUpper222.bundles_in_L H hR hP) h)

#print axioms zf_refutation_of_q222

end SetTheory.BusyBeaver.ZFC.QuotientCalibration
