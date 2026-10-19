import BoundedZFCConsistency.UniverseTruthZero

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
set_option autoImplicit false

#print axioms LeanProofs.BoundedZFCConsistency.exists_isUnivEnv
#print axioms LeanProofs.BoundedZFCConsistency.fUnivEnvF_spec
#print axioms LeanProofs.BoundedZFCConsistency.fIsQFCodeF_spec
#print axioms LeanProofs.BoundedZFCConsistency.ranks_zero_of_isQFCodeSem
#print axioms LeanProofs.BoundedZFCConsistency.isQFCodeSem_iff_quantBounded_zero
#print axioms LeanProofs.BoundedZFCConsistency.fQFSatClosedF_spec
#print axioms LeanProofs.BoundedZFCConsistency.qfCertificate_functional
#print axioms LeanProofs.BoundedZFCConsistency.qfCertificate_total
#print axioms LeanProofs.BoundedZFCConsistency.qfCertifies_bit
#print axioms LeanProofs.BoundedZFCConsistency.qfTrue_memAtom
#print axioms LeanProofs.BoundedZFCConsistency.qfTrue_eqAtom
#print axioms LeanProofs.BoundedZFCConsistency.qfTrue_bot
#print axioms LeanProofs.BoundedZFCConsistency.qfTrue_imp
#print axioms LeanProofs.BoundedZFCConsistency.qfTrue_and
#print axioms LeanProofs.BoundedZFCConsistency.qfTrue_or
#print axioms LeanProofs.BoundedZFCConsistency.isQuantFree_iff_quantifierBounded_zero
#print axioms LeanProofs.BoundedZFCConsistency.qfTrue_formCode_iff_apply

universe u
variable {V : Type u} {mem : V → V → Prop}

example (H : ZFAxioms mem) : ∃ E, IsUnivEnv H E := exists_isUnivEnv H

example (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fUnivEnvF i) ↔ IsUnivEnv H (ee i) := fUnivEnvF_spec H ee i

example (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fIsQFCodeF i) ↔ IsQFCodeSem H (ee i) := fIsQFCodeF_spec H ee i

example (H : ZFAxioms mem) (c : V) (hc : IsQFCodeSem H c) :
    Ranks H c (natV H 0) (natV H 0) := ranks_zero_of_isQFCodeSem H c hc

example (H : ZFAxioms mem) {c : V} (hc : IsFormCodeSem H c) :
    IsQFCodeSem H c ↔ QuantBounded H (natV H 0) c :=
  isQFCodeSem_iff_quantBounded_zero H hc

example (H : ZFAxioms mem) (ee : Nat → V) (i : Nat) :
    Sat mem ee (fQFSatClosedF i) ↔ QFSatClosed H (ee i) :=
  fQFSatClosedF_spec H ee i

example (H : ZFAxioms mem) {c e b b' S S' : V} (hc : IsQFCodeSem H c)
    (h : QFCertifies H S c e b) (h' : QFCertifies H S' c e b') : b = b' :=
  qfCertificate_functional H hc h h'

example (H : ZFAxioms mem) (c : V) (hc : IsQFCodeSem H c)
    (e : V) (he : IsUnivEnv H e) : ∃ S b, QFCertifies H S c e b :=
  qfCertificate_total H c hc e he

example (H : ZFAxioms mem) {S c e b : V} (hc : IsQFCodeSem H c)
    (h : QFCertifies H S c e b) : b = vbit H (QFTrue H c e) :=
  qfCertifies_bit H hc h

example (H : ZFAxioms mem) {e i j : V} (hi : mem i (omegaV H))
    (hj : mem j (omegaV H)) (he : IsUnivEnv H e) :
    QFTrue H (kpair H (natV H 0) (kpair H i j)) e ↔
      mem (applyV H e i) (applyV H e j) := qfTrue_memAtom H hi hj he

example (H : ZFAxioms mem) {e i j : V} (hi : mem i (omegaV H))
    (hj : mem j (omegaV H)) (he : IsUnivEnv H e) :
    QFTrue H (kpair H (natV H 1) (kpair H i j)) e ↔
      applyV H e i = applyV H e j := qfTrue_eqAtom H hi hj he

example (H : ZFAxioms mem) (e : V) :
    ¬ QFTrue H (kpair H (natV H 2) (vempty H)) e := qfTrue_bot H

example (H : ZFAxioms mem) {c1 c2 e : V} (h1 : IsQFCodeSem H c1)
    (h2 : IsQFCodeSem H c2) (he : IsUnivEnv H e) :
    QFTrue H (kpair H (natV H 3) (kpair H c1 c2)) e ↔
      (QFTrue H c1 e → QFTrue H c2 e) := qfTrue_imp H h1 h2 he

example (H : ZFAxioms mem) {c1 c2 e : V} (h1 : IsQFCodeSem H c1)
    (h2 : IsQFCodeSem H c2) (he : IsUnivEnv H e) :
    QFTrue H (kpair H (natV H 4) (kpair H c1 c2)) e ↔
      (QFTrue H c1 e ∧ QFTrue H c2 e) := qfTrue_and H h1 h2 he

example (H : ZFAxioms mem) {c1 c2 e : V} (h1 : IsQFCodeSem H c1)
    (h2 : IsQFCodeSem H c2) (he : IsUnivEnv H e) :
    QFTrue H (kpair H (natV H 5) (kpair H c1 c2)) e ↔
      (QFTrue H c1 e ∨ QFTrue H c2 e) := qfTrue_or H h1 h2 he

example (phi : Form) : IsQuantFree phi ↔ QuantifierBounded 0 phi :=
  isQuantFree_iff_quantifierBounded_zero phi

example (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (phi : Form) (hphi : IsQuantFree phi) :
    QFTrue H (formCode H phi) E ↔ Sat mem (fun k => applyV H E (natV H k)) phi :=
  qfTrue_formCode_iff_apply H hE phi hphi

example (H : ZFAxioms mem) {c e : V} (hc : IsQFCodeSem H c)
    (he : IsUnivEnv H e) : ∃ S, QFCertifies H S c e (vbit H (QFTrue H c e)) :=
  exists_qfCertifies H hc he

example (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (v : Nat → V) (hv : ∀ k, v k = applyV H E (natV H k))
    (phi : Form) (hphi : IsQuantFree phi) :
    QFTrue H (formCode H phi) E ↔ Sat mem v phi :=
  qfTrue_formCode_iff H hE v hv phi hphi
