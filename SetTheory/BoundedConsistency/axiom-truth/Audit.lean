import BoundedZFCConsistency.AxiomTruth

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
open SetTheory.FirstOrderClassicalCompleteness

set_option autoImplicit false
attribute [local irreducible] SetTheory.sealF

#print axioms LeanProofs.BoundedZFCConsistency.sat_Ext_form
#print axioms LeanProofs.BoundedZFCConsistency.sat_Pair_form
#print axioms LeanProofs.BoundedZFCConsistency.sat_Union_form
#print axioms LeanProofs.BoundedZFCConsistency.sat_Inf_form
#print axioms LeanProofs.BoundedZFCConsistency.sat_Pow_form
#print axioms LeanProofs.BoundedZFCConsistency.sat_Reg_form
#print axioms LeanProofs.BoundedZFCConsistency.sat_Choice_form
#print axioms LeanProofs.BoundedZFCConsistency.univEnvOf_econs
#print axioms LeanProofs.BoundedZFCConsistency.levelTruth_formCode
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_formCode_of_valid
#print axioms LeanProofs.BoundedZFCConsistency.levelTrue_formCode_of_valid
#print axioms LeanProofs.BoundedZFCConsistency.piBounded_of_quantBounded_all
#print axioms LeanProofs.BoundedZFCConsistency.compV_twoMapV
#print axioms LeanProofs.BoundedZFCConsistency.compV_rsepV_econs
#print axioms LeanProofs.BoundedZFCConsistency.compV_rf1V_econs
#print axioms LeanProofs.BoundedZFCConsistency.compV_rf2V_econs
#print axioms LeanProofs.BoundedZFCConsistency.compV_riV_econs
#print axioms LeanProofs.BoundedZFCConsistency.fSepCondF_spec
#print axioms LeanProofs.BoundedZFCConsistency.sepSet_spec
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_sepCodeVOf
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_sepCodeV
#print axioms LeanProofs.BoundedZFCConsistency.fReplRelF_spec
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_replCodeVOf
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_replCodeV
#print axioms LeanProofs.BoundedZFCConsistency.axiomCodesTrueAt
#print axioms LeanProofs.BoundedZFCConsistency.noBoundedRefutationAtLevel_zfc
#print axioms LeanProofs.BoundedZFCConsistency.zfcAxioms_of_zfcModel
#print axioms LeanProofs.BoundedZFCConsistency.conZFCForm_semanticConsequence_zfc
#print axioms LeanProofs.BoundedZFCConsistency.zfcprov_conZFCForm

universe u
variable {V : Type u} {mem : V → V → Prop}

example (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Ext_form :=
  sat_Ext_form K e

example (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Pair_form :=
  sat_Pair_form K e

example (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Union_form :=
  sat_Union_form K e

example (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Inf_form :=
  sat_Inf_form K e

example (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Pow_form :=
  sat_Pow_form K e

example (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Reg_form :=
  sat_Reg_form K e

example (K : ZFCAxioms mem) (e : Nat → V) :
    Sat mem e Choice_form :=
  sat_Choice_form K e

example (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E) (d : V) :
    univEnvOf H (econs H d E) = scons d (univEnvOf H E) :=
  univEnvOf_econs H hE d

example (H : ZFAxioms mem) :
    ∀ (n : Nat) (phi : Form) (E : V), IsUnivEnv H E →
      (sigmaRank phi ≤ n →
          (SigmaTrue H n (formCode H phi) E ↔ Sat mem (univEnvOf H E) phi)) ∧
        (piRank phi ≤ n →
          (PiFalse H n (formCode H phi) E ↔ ¬ Sat mem (univEnvOf H E) phi)) :=
  levelTruth_formCode H

example (H : ZFAxioms mem) (n : Nat) {E : V}
    (hE : IsUnivEnv H E) (phi : Form)
    (hq : QuantBounded H (natV H n) (formCode H phi))
    (hsat : ∀ e : Nat → V, Sat mem e phi) :
    SigmaTrue H (n+1) (formCode H phi) E :=
  sigmaTrue_formCode_of_valid H n hE phi hq hsat

example (H : ZFAxioms mem) (n : Nat) {E : V}
    (hE : IsUnivEnv H E) (phi : Form)
    (hq : QuantBounded H (natV H n) (formCode H phi))
    (hsat : ∀ e : Nat → V, Sat mem e phi) :
    LevelTrue H n (formCode H phi) E :=
  levelTrue_formCode_of_valid H n hE phi hq hsat

example (H : ZFAxioms mem) {a : V} {n : Nat}
    (hq : QuantBounded H (natV H n) (kpair H (natV H 6) a)) :
    PiBounded H (natV H n) (kpair H (natV H 6) a) :=
  piBounded_of_quantBounded_all H hq

example (H : ZFAxioms mem) {A B : V} (hA : IsUnivEnv H A)
    (hB : IsUnivEnv H B) (a0 a1 k : Nat)
    (h0 : applyV H A (natV H a0) = applyV H B (natV H 0))
    (h1 : applyV H A (natV H a1) = applyV H B (natV H 1))
    (hs : ∀ m, mem m (omegaV H) →
      applyV H A (vsuccIter H k m) = applyV H B (vsucc H (vsucc H m))) :
    compV H A (twoMapV H a0 a1 k) = B :=
  compV_twoMapV H hA hB a0 a1 k h0 h1 hs

example (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (x s d : V) :
    compV H (econs H x (econs H s (econs H d E))) (rsepV H) = econs H x E :=
  compV_rsepV_econs H hE x s d

example (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (x y1 y2 : V) :
    compV H (econs H y2 (econs H y1 (econs H x E))) (rf1V H) =
      econs H y1 (econs H x E) :=
  compV_rf1V_econs H hE x y1 y2

example (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (x y1 y2 : V) :
    compV H (econs H y2 (econs H y1 (econs H x E))) (rf2V H) =
      econs H y2 (econs H x E) :=
  compV_rf2V_econs H hE x y1 y2

example (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (a r y x : V) :
    compV H (econs H x (econs H y (econs H r (econs H a E)))) (riV H) =
      econs H y (econs H x E) :=
  compV_riV_econs H hE a r y x

example (H : ZFAxioms mem) (n : Nat) {E : V} (hE : IsUnivEnv H E)
    (p x : V) :
    Sat mem (scons x (envInstance H p E)) (fSepCondF n) ↔
      SigmaTrue H n p (econs H x E) :=
  fSepCondF_spec H n hE p x

example (H : ZFAxioms mem) (n : Nat) {E : V} (hE : IsUnivEnv H E)
    (p d x : V) :
    mem x (sepSet H n p E d) ↔
      (mem x d ∧ SigmaTrue H n p (econs H x E)) :=
  sepSet_spec H n hE p d x

example (H : ZFAxioms mem) (n : Nat) {q E : V}
    (hq : IsFormCodeSem H q) (hE : IsUnivEnv H E)
    (hbd : QuantBounded H (natV H n) (sepCodeVOf H q))
    (hcarve : ∀ (j : Nat) (d : V), ∃ s, ∀ x, mem x s ↔
        (mem x d ∧ SigmaTrue H j q (econs H x (econs H s (econs H d E))))) :
    SigmaTrue H (n+1) (sepCodeVOf H q) E :=
  sigmaTrue_sepCodeVOf H n hq hE hbd hcarve

example (H : ZFAxioms mem) (n : Nat) {p E : V}
    (hp : IsFormCodeSem H p) (hE : IsUnivEnv H E)
    (hbd : QuantBounded H (natV H n) (sepCodeV H p)) :
    SigmaTrue H (n+1) (sepCodeV H p) E :=
  sigmaTrue_sepCodeV H n hp hE hbd

example (H : ZFAxioms mem) (n : Nat) {E : V} (hE : IsUnivEnv H E)
    (p y x : V) :
    relOf mem (fReplRelF n) (envInstance H p E) y x ↔
      SigmaTrue H n p (econs H y (econs H x E)) :=
  fReplRelF_spec H n hE p y x

example (H : ZFAxioms mem) (n : Nat) {q1 q2 q3 E : V}
    (hq1 : IsFormCodeSem H q1) (hq2 : IsFormCodeSem H q2)
    (hq3 : IsFormCodeSem H q3) (hE : IsUnivEnv H E)
    (hbd : QuantBounded H (natV H n) (replCodeVOf H q1 q2 q3))
    (P : Nat → V → V → Prop)
    (e1 : ∀ (l : Nat) (x y1 y2 : V),
      SigmaTrue H l q1 (econs H y2 (econs H y1 (econs H x E))) ↔ P l y1 x)
    (e2 : ∀ (l : Nat) (x y1 y2 : V),
      SigmaTrue H l q2 (econs H y2 (econs H y1 (econs H x E))) ↔ P l y2 x)
    (e3 : ∀ (l : Nat) (a r y x : V),
      SigmaTrue H l q3 (econs H x (econs H y (econs H r (econs H a E)))) ↔
        P l y x)
    (hmono : ∀ (l l' : Nat), l ≤ l' → ∀ y x, P l y x → P l' y x)
    (himg : ∀ (l : Nat) (a : V), (∀ x y1 y2, P l y1 x → P l y2 x → y1 = y2) →
      ∃ r, ∀ y, mem y r ↔ ∃ x, mem x a ∧ P l y x) :
    SigmaTrue H (n+1) (replCodeVOf H q1 q2 q3) E :=
  sigmaTrue_replCodeVOf H n hq1 hq2 hq3 hE hbd P e1 e2 e3 hmono himg

example (H : ZFAxioms mem) (n : Nat) {p E : V}
    (hp : IsFormCodeSem H p) (hE : IsUnivEnv H E)
    (hbd : QuantBounded H (natV H n) (replCodeV H p)) :
    SigmaTrue H (n+1) (replCodeV H p) E :=
  sigmaTrue_replCodeV H n hp hE hbd

example (K : ZFCAxioms mem) (n : Nat) :
    AxiomCodesTrueAt K.toZFAxioms n :=
  axiomCodesTrueAt K n

example (K : ZFCAxioms mem) (n : Nat) :
    NoBoundedRefutationAtLevel K.toZFAxioms n :=
  noBoundedRefutationAtLevel_zfc K n

example {Dom : Type} {m : Dom → Dom → Prop} (v : Nat → Dom)
    (hmodel : ∀ g, ZFCax_s g → Sat m v g) : ZFCAxioms m :=
  zfcAxioms_of_zfcModel v hmodel

example (n : Nat) :
    TheorySemanticConsequence ZFCax_s (conZFCForm n) :=
  conZFCForm_semanticConsequence_zfc n

example (n : Nat) :
    TheorySyntacticConsequence ZFCax_s (conZFCForm n) :=
  zfcprov_conZFCForm n

/- Explicit internal-code client: there is no quotation or axiom-truth premise. -/
example (K : ZFCAxioms mem) (n : Nat) (c E : V)
    (hc : IsZFCAxiomCode K.toZFAxioms c)
    (hb : QuantBounded K.toZFAxioms (natV K.toZFAxioms n) c)
    (hE : IsUnivEnv K.toZFAxioms E) :
    SigmaTrue K.toZFAxioms (n+1) c E ∧ PiTrue K.toZFAxioms (n+1) c E :=
  axiomCodesTrueAt K n c E hc hb hE

/- Explicit coded-refutation client; n is external, d and g are internal. -/
example (K : ZFCAxioms mem) (n : Nat) :
    ¬ ∃ d g, CtxZFCAxioms K.toZFAxioms g ∧
      Derives K.toZFAxioms d g (kpair K.toZFAxioms (natV K.toZFAxioms 2)
        (vempty K.toZFAxioms)) ∧
      DerAllBounded K.toZFAxioms (natV K.toZFAxioms n) d :=
  noBoundedRefutationAtLevel_zfc K n
