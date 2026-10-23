import BusyBeaver.ZFC.KEndpoint

open SetTheory.BusyBeaver.ZFC
open SetTheory.BusyBeaver.ZFC.KQHyp

#print axioms KQ1ReplacementNative.exact_image
#print axioms KQ1ReplacementNative.sat_guardForm
#print axioms KQ1ReplacementNative.replacement_of_collection
#print axioms KQ1ReplacementNative.quotient_replacement
#print axioms KQ1ReplacementNative.quotient_repl_form
#print axioms KQ1ZF.zf_consistent
#print axioms KEndpoint.blank_halts_iff_zfc_refutation

universe u
example {V : Type u} (mem : V → V → Prop) (w : V) (h : QHyp mem)
    (phi : SetTheory.Form) (env : Nat → KQ1Model.Domain mem w h)
    (hf : SetTheory.Functional (SetTheory.relOf (KQ1Model.quotientMember mem w h) phi env))
    (a : KQ1Model.Domain mem w h) :
    ∃ b, ∀ y, KQ1Model.quotientMember mem w h y b ↔
      ∃ x, KQ1Model.quotientMember mem w h x a ∧
        SetTheory.relOf (KQ1Model.quotientMember mem w h) phi env y x :=
  KQ1ReplacementNative.quotient_replacement mem w h phi env hf a

example {V : Type u} (mem : V → V → Prop) (w : V) (h : QHyp mem) :
    ∀ phi env, SetTheory.Sat (KQ1Model.quotientMember mem w h) env (SetTheory.Repl_form phi) :=
  KQ1ReplacementNative.quotient_repl_form mem w h
