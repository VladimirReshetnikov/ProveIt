import BoundedZFCConsistency.CodedRank

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
open SetTheory.FirstOrderClassicalCompleteness

set_option autoImplicit false

attribute [local irreducible] SetTheory.sealF

#print axioms LeanProofs.BoundedZFCConsistency.fRanksF_spec
#print axioms LeanProofs.BoundedZFCConsistency.rankTotal_of_isFormCodeSem
#print axioms LeanProofs.BoundedZFCConsistency.rankUnique_of_isFormCodeSem
#print axioms LeanProofs.BoundedZFCConsistency.ranks_formCode_iff
#print axioms LeanProofs.BoundedZFCConsistency.quantBounded_formCode_iff
#print axioms LeanProofs.BoundedZFCConsistency.quantBounded_imp
#print axioms LeanProofs.BoundedZFCConsistency.quantBounded_all
#print axioms LeanProofs.BoundedZFCConsistency.rankRen_of_isFormCodeSem
#print axioms LeanProofs.BoundedZFCConsistency.quantBounded_of_renames
#print axioms LeanProofs.BoundedZFCConsistency.derStep_of_derStepBounded
#print axioms LeanProofs.BoundedZFCConsistency.derStepBounded_of_derAllBounded
#print axioms LeanProofs.BoundedZFCConsistency.conBodyF_spec
#print axioms LeanProofs.BoundedZFCConsistency.sentence_conForm
#print axioms LeanProofs.BoundedZFCConsistency.sat_logicConForm_iff
#print axioms LeanProofs.BoundedZFCConsistency.zfcprov_logicConForm_of_valid
#print axioms LeanProofs.BoundedZFCConsistency.zfcprov_logicConForm_of_no_bounded_refutation

universe u
variable {V : Type u} {mem : V → V → Prop}

example (H : ZFAxioms mem) (ee : Nat → V) (c s p : Nat) :
    Sat mem ee (fRanksF c s p) ↔ Ranks H (ee c) (ee s) (ee p) :=
  fRanksF_spec H ee c s p

example (H : ZFAxioms mem) (c : V) (hc : IsFormCodeSem H c) :
    RankTotal H c := rankTotal_of_isFormCodeSem H c hc

example (H : ZFAxioms mem) (c : V) (hc : IsFormCodeSem H c) :
    RankUnique H c := rankUnique_of_isFormCodeSem H c hc

example (H : ZFAxioms mem) (phi : Form) (s p : V) :
    Ranks H (formCode H phi) s p ↔
      s = natV H (sigmaRank phi) ∧ p = natV H (piRank phi) :=
  ranks_formCode_iff H phi s p

example (H : ZFAxioms mem) (n : Nat) (phi : Form) :
    QuantBounded H (natV H n) (formCode H phi) ↔ QuantifierBounded n phi :=
  quantBounded_formCode_iff H n phi

example (H : ZFAxioms mem) {b a a' : V} (hb : mem b (omegaV H))
    (h : QuantBounded H b (kpair H (natV H 3) (kpair H a a'))) :
    QuantBounded H b a ∧ QuantBounded H b a' := quantBounded_imp H hb h

example (H : ZFAxioms mem) {b a : V} (hb : mem b (omegaV H))
    (h : QuantBounded H b (kpair H (natV H 6) a)) :
    QuantBounded H b a := quantBounded_all H hb h

example (H : ZFAxioms mem) (c : V) (hc : IsFormCodeSem H c) :
    RankRen H c := rankRen_of_isFormCodeSem H c hc

example (H : ZFAxioms mem) {b r a c' : V}
    (hc : IsFormCodeSem H a) (hr : IsVarMap H r) (hren : Renames H r a c')
    (h : QuantBounded H b c') : QuantBounded H b a :=
  quantBounded_of_renames H hc hr hren h

example (H : ZFAxioms mem) {b D n g c : V}
    (h : DerStepBounded H b D n g c) : DerStep H D n g c :=
  derStep_of_derStepBounded H h

example (H : ZFAxioms mem) {b d n g c : V} (hbo : mem b (omegaV H))
    (hb : DerAllBounded H b d) (hmem : mem (satTriple H n g c) d)
    (h : DerStep H d n g c) : DerStepBounded H b d n g c :=
  derStepBounded_of_derAllBounded H hbo hb hmem h

example (H : ZFAxioms mem) (n : Nat) (ee : Nat → V) :
    Sat mem ee (logicConBodyF n) ↔
      ¬ ∃ d, Derives H d (ctxNil H) (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d := conBodyF_spec H n ee

example (n : Nat) : Sentence (logicConForm n) := sentence_conForm n

example (H : ZFAxioms mem) (n : Nat) :
    (∀ e : Nat → V, Sat mem e (logicConForm n)) ↔
      ¬ ∃ d, Derives H d (ctxNil H) (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d := sat_logicConForm_iff H n

example (n : Nat) (h : TheorySemanticConsequence ZFCax_s (logicConForm n)) :
    TheorySyntacticConsequence ZFCax_s (logicConForm n) :=
  zfcprov_logicConForm_of_valid n h

example (n : Nat)
    (h : ∀ (Dom : Type) (m : Dom → Dom → Prop) (H : ZFAxioms m),
      ¬ ∃ d, Derives H d (ctxNil H) (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d) :
    TheorySyntacticConsequence ZFCax_s (logicConForm n) :=
  zfcprov_logicConForm_of_no_bounded_refutation n h
