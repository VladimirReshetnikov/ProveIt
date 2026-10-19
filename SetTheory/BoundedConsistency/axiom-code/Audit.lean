import BoundedZFCConsistency.AxiomCode

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
open SetTheory.FirstOrderClassicalCompleteness

set_option autoImplicit false
attribute [local irreducible] SetTheory.sealF

#print axioms LeanProofs.BoundedZFCConsistency.isTwoMap_iff
#print axioms LeanProofs.BoundedZFCConsistency.fTwoMapF_spec
#print axioms LeanProofs.BoundedZFCConsistency.tmplCode_eq_formCode
#print axioms LeanProofs.BoundedZFCConsistency.fTmplCodeF_spec
#print axioms LeanProofs.BoundedZFCConsistency.sepCodeV_formCode
#print axioms LeanProofs.BoundedZFCConsistency.replCodeV_formCode
#print axioms LeanProofs.BoundedZFCConsistency.sepCodeV_isFormCodeSem
#print axioms LeanProofs.BoundedZFCConsistency.replCodeV_isFormCodeSem
#print axioms LeanProofs.BoundedZFCConsistency.fSepCodeF_spec
#print axioms LeanProofs.BoundedZFCConsistency.fReplCodeF_spec
#print axioms LeanProofs.BoundedZFCConsistency.fZFCAxiomCodeF_spec
#print axioms LeanProofs.BoundedZFCConsistency.isZFCAxiomCode_of_ZFCax
#print axioms LeanProofs.BoundedZFCConsistency.fCtxZFCAxiomsF_spec
#print axioms LeanProofs.BoundedZFCConsistency.ctxZFCAxioms_ctxCode
#print axioms LeanProofs.BoundedZFCConsistency.conZFCBodyF_spec
#print axioms LeanProofs.BoundedZFCConsistency.sentence_conZFCForm
#print axioms LeanProofs.BoundedZFCConsistency.sat_conZFCForm_iff
#print axioms LeanProofs.BoundedZFCConsistency.no_bounded_refutation_nil_of_conZFC
#print axioms LeanProofs.BoundedZFCConsistency.zfcprov_conZFCForm_of_valid
#print axioms LeanProofs.BoundedZFCConsistency.zfcprov_conZFCForm_of_no_bounded_refutation

universe u
variable {V : Type u} {mem : V → V → Prop}

example (H : ZFAxioms mem) (r : V) (a0 a1 k : Nat) :
    IsTwoMap H r a0 a1 k ↔ r = twoMapV H a0 a1 k :=
  isTwoMap_iff H r a0 a1 k

example (H : ZFAxioms mem) (ee : Nat → V) (i a0 a1 k : Nat) :
    Sat mem ee (fTwoMapF i a0 a1 k) ↔ IsTwoMap H (ee i) a0 a1 k :=
  fTwoMapF_spec H ee i a0 a1 k

example (H : ZFAxioms mem) (sub : Nat → V) (phi : Form)
    (h : markerFree phi = true) : tmplCode H sub phi = formCode H phi :=
  tmplCode_eq_formCode H sub phi h

example (H : ZFAxioms mem) (t : Form) (q : Nat → Nat) (i : Nat) (ee : Nat → V) :
    Sat mem ee (fTmplCodeF q i t) ↔ ee i = tmplCode H (fun m => ee (q m)) t :=
  fTmplCodeF_spec H t q i ee

example (H : ZFAxioms mem) (phi : Form) :
    sepCodeV H (formCode H phi) = formCode H (Sep_form phi) :=
  sepCodeV_formCode H phi

example (H : ZFAxioms mem) (psi : Form) :
    replCodeV H (formCode H psi) = formCode H (Repl_form psi) :=
  replCodeV_formCode H psi

example (H : ZFAxioms mem) {p : V} (hp : IsFormCodeSem H p) :
    IsFormCodeSem H (sepCodeV H p) := sepCodeV_isFormCodeSem H hp

example (H : ZFAxioms mem) {p : V} (hp : IsFormCodeSem H p) :
    IsFormCodeSem H (replCodeV H p) := replCodeV_isFormCodeSem H hp

example (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fSepCodeF i) ↔
      ∃ p, IsFormCodeSem H p ∧ ee i = sepCodeV H p := fSepCodeF_spec H ee i

example (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fReplCodeF i) ↔
      ∃ p, IsFormCodeSem H p ∧ ee i = replCodeV H p := fReplCodeF_spec H ee i

example (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fZFCAxiomCodeF i) ↔ IsZFCAxiomCode H (ee i) :=
  fZFCAxiomCodeF_spec H ee i

example (H : ZFAxioms mem) {f : Form} (h : ZFCax f) :
    IsZFCAxiomCode H (formCode H f) := isZFCAxiomCode_of_ZFCax H h

example (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fCtxZFCAxiomsF i) ↔ CtxZFCAxioms H (ee i) :=
  fCtxZFCAxiomsF_spec H ee i

example (H : ZFAxioms mem) {G : List Form} (hG : ∀ x ∈ G, ZFCax x) :
    CtxZFCAxioms H (ctxCode H G) := ctxZFCAxioms_ctxCode H hG

example (H : ZFAxioms mem) (n : Nat) (ee : Nat → V) :
    Sat mem ee (conZFCBodyF n) ↔
      ¬ ∃ d g, CtxZFCAxioms H g ∧
        Derives H d g (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d := conZFCBodyF_spec H n ee

example (n : Nat) : Sentence (conZFCForm n) := sentence_conZFCForm n

example (H : ZFAxioms mem) (n : Nat) :
    (∀ e : Nat → V, Sat mem e (conZFCForm n)) ↔
      ¬ ∃ d g, CtxZFCAxioms H g ∧
        Derives H d g (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d := sat_conZFCForm_iff H n

example (H : ZFAxioms mem) (n : Nat)
    (h : ¬ ∃ d g, CtxZFCAxioms H g ∧
      Derives H d g (kpair H (natV H 2) (vempty H)) ∧
      DerAllBounded H (natV H n) d) :
    ¬ ∃ d, Derives H d (ctxNil H) (kpair H (natV H 2) (vempty H)) ∧
      DerAllBounded H (natV H n) d := no_bounded_refutation_nil_of_conZFC H n h

example (n : Nat) (h : TheorySemanticConsequence ZFCax_s (conZFCForm n)) :
    TheorySyntacticConsequence ZFCax_s (conZFCForm n) :=
  zfcprov_conZFCForm_of_valid n h

example (n : Nat)
    (h : ∀ (Dom : Type) (m : Dom → Dom → Prop) (H : ZFAxioms m),
      ¬ ∃ d g, CtxZFCAxioms H g ∧
        Derives H d g (kpair H (natV H 2) (vempty H)) ∧
        DerAllBounded H (natV H n) d) :
    TheorySyntacticConsequence ZFCax_s (conZFCForm n) :=
  zfcprov_conZFCForm_of_no_bounded_refutation n h
