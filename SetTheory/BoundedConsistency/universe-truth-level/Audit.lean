import BoundedZFCConsistency.UniverseTruthLevel

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
set_option autoImplicit false

universe u

#print axioms LeanProofs.BoundedZFCConsistency.econs_isUnivEnv
#print axioms LeanProofs.BoundedZFCConsistency.econs_apply_succ
#print axioms LeanProofs.BoundedZFCConsistency.fSigmaBoundedF_spec
#print axioms LeanProofs.BoundedZFCConsistency.fPiBoundedF_spec
#print axioms LeanProofs.BoundedZFCConsistency.sigmaBounded_formCode_iff
#print axioms LeanProofs.BoundedZFCConsistency.piBounded_formCode_iff
#print axioms LeanProofs.BoundedZFCConsistency.fLevelJustifiedF_spec
#print axioms LeanProofs.BoundedZFCConsistency.fLevelClosedF_spec
#print axioms LeanProofs.BoundedZFCConsistency.levelSatF_spec
#print axioms LeanProofs.BoundedZFCConsistency.fSigmaTrueF_spec
#print axioms LeanProofs.BoundedZFCConsistency.fPiTrueF_spec
#print axioms LeanProofs.BoundedZFCConsistency.levelSat_mono
#print axioms LeanProofs.BoundedZFCConsistency.levelSat_bit
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_zero_iff
#print axioms LeanProofs.BoundedZFCConsistency.piTrue_zero_iff
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_memAtom
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_and
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_and
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_or
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_or
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_imp
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_imp
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_ex
#print axioms LeanProofs.BoundedZFCConsistency.piTrue_all
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_all_of_piTrue
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_ex_of_not_sigmaTrue
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_all_inv
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_ex_inv
#print axioms LeanProofs.BoundedZFCConsistency.not_sigmaTrue_one_all
#print axioms LeanProofs.BoundedZFCConsistency.not_piFalse_one_ex
#print axioms LeanProofs.BoundedZFCConsistency.levelSat_formCode_zero
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_formCode_of_sat
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_formCode_of_not_sat

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E) (d : V),
    IsUnivEnv H (econs H d E) :=
  @LeanProofs.BoundedZFCConsistency.econs_isUnivEnv

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E) (d : V)
    {n : V} (hn : mem n (omegaV H)),
    applyV H (econs H d E) (vsucc H n) = applyV H E n :=
  @LeanProofs.BoundedZFCConsistency.econs_apply_succ

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (ee : Nat → V) (b_i c_i : Nat),
    Sat mem ee (fSigmaBoundedF b_i c_i) ↔ SigmaBounded H (ee b_i) (ee c_i) :=
  @LeanProofs.BoundedZFCConsistency.fSigmaBoundedF_spec

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (ee : Nat → V) (b_i c_i : Nat),
    Sat mem ee (fPiBoundedF b_i c_i) ↔ PiBounded H (ee b_i) (ee c_i) :=
  @LeanProofs.BoundedZFCConsistency.fPiBoundedF_spec

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) (phi : Form),
    SigmaBounded H (natV H n) (formCode H phi) ↔ sigmaRank phi ≤ n :=
  @LeanProofs.BoundedZFCConsistency.sigmaBounded_formCode_iff

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) (phi : Form),
    PiBounded H (natV H n) (formCode H phi) ↔ piRank phi ≤ n :=
  @LeanProofs.BoundedZFCConsistency.piBounded_formCode_iff

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (lF : Nat → Nat → Nat → Form)
    (L : V → V → V → Prop)
    (hl : ∀ (ee' : Nat → V) (c e b : Nat),
      Sat mem ee' (lF c e b) ↔ L (ee' c) (ee' e) (ee' b))
    (ee : Nat → V) (c_i e_i b_i s_i bnd_i : Nat)
    (hE : IsUnivEnv H (ee e_i)),
    Sat mem ee (fLevelJustifiedF lF c_i e_i b_i s_i bnd_i) ↔
      LevelJustified H L (ee bnd_i) (ee s_i) (ee c_i) (ee e_i) (ee b_i) :=
  @LeanProofs.BoundedZFCConsistency.fLevelJustifiedF_spec

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (lF : Nat → Nat → Nat → Form)
    (L : V → V → V → Prop)
    (hl : ∀ (ee' : Nat → V) (c e b : Nat),
      Sat mem ee' (lF c e b) ↔ L (ee' c) (ee' e) (ee' b))
    (ee : Nat → V) (bnd_i s_i : Nat),
    Sat mem ee (fLevelClosedF lF bnd_i s_i) ↔
      LevelClosed H L (ee bnd_i) (ee s_i) :=
  @LeanProofs.BoundedZFCConsistency.fLevelClosedF_spec

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem),
    ∀ (n : Nat) (ee : Nat → V) (c_i e_i b_i : Nat),
      Sat mem ee (levelSatF n c_i e_i b_i) ↔
        LevelSat H n (ee c_i) (ee e_i) (ee b_i) :=
  @LeanProofs.BoundedZFCConsistency.levelSatF_spec

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) (ee : Nat → V)
    (c_i e_i : Nat),
    Sat mem ee (fSigmaTrueF n c_i e_i) ↔ SigmaTrue H n (ee c_i) (ee e_i) :=
  @LeanProofs.BoundedZFCConsistency.fSigmaTrueF_spec

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) (ee : Nat → V)
    (c_i e_i : Nat),
    Sat mem ee (fPiTrueF n c_i e_i) ↔ PiTrue H n (ee c_i) (ee e_i) :=
  @LeanProofs.BoundedZFCConsistency.fPiTrueF_spec

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) {m n : Nat} (hmn : m ≤ n) {c e b : V}
    (he : IsUnivEnv H e) (h : LevelSat H m c e b),
    LevelSat H n c e b :=
  @LeanProofs.BoundedZFCConsistency.levelSat_mono

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem),
    ∀ (n : Nat) (c e b : V), LevelSat H n c e b →
      (b = natV H 0 ∨ b = natV H 1) :=
  @LeanProofs.BoundedZFCConsistency.levelSat_bit

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) {c e : V},
    SigmaTrue H 0 c e ↔ (IsQFCodeSem H c ∧ QFTrue H c e) :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_zero_iff

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) {c e : V} (hq : IsQFCodeSem H c),
    PiTrue H 0 c e ↔ QFTrue H c e :=
  @LeanProofs.BoundedZFCConsistency.piTrue_zero_iff

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem),
    ∀ (n : Nat) {i j e : V}, mem i (omegaV H) → mem j (omegaV H) →
      IsUnivEnv H e →
      (SigmaTrue H n (kpair H (natV H 0) (kpair H i j)) e ↔
        mem (applyV H e i) (applyV H e j)) :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_memAtom

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2) (he : IsUnivEnv H e),
    SigmaTrue H (n+1) (kpair H (natV H 4) (kpair H c1 c2)) e ↔
      (SigmaTrue H (n+1) c1 e ∧ SigmaTrue H (n+1) c2 e) :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_and

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2) (he : IsUnivEnv H e),
    PiFalse H (n+1) (kpair H (natV H 4) (kpair H c1 c2)) e ↔
      (PiFalse H (n+1) c1 e ∨ PiFalse H (n+1) c2 e) :=
  @LeanProofs.BoundedZFCConsistency.piFalse_and

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2) (he : IsUnivEnv H e),
    SigmaTrue H (n+1) (kpair H (natV H 5) (kpair H c1 c2)) e ↔
      (SigmaTrue H (n+1) c1 e ∨ SigmaTrue H (n+1) c2 e) :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_or

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2) (he : IsUnivEnv H e),
    PiFalse H (n+1) (kpair H (natV H 5) (kpair H c1 c2)) e ↔
      (PiFalse H (n+1) c1 e ∧ PiFalse H (n+1) c2 e) :=
  @LeanProofs.BoundedZFCConsistency.piFalse_or

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2) (he : IsUnivEnv H e),
    SigmaTrue H (n+1) (kpair H (natV H 3) (kpair H c1 c2)) e ↔
      (PiFalse H (n+1) c1 e ∨ SigmaTrue H (n+1) c2 e) :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_imp

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {c1 c2 e : V}
    (h1 : IsFormCodeSem H c1) (h2 : IsFormCodeSem H c2) (he : IsUnivEnv H e),
    PiFalse H (n+1) (kpair H (natV H 3) (kpair H c1 c2)) e ↔
      (SigmaTrue H (n+1) c1 e ∧ PiFalse H (n+1) c2 e) :=
  @LeanProofs.BoundedZFCConsistency.piFalse_imp

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (he : IsUnivEnv H e),
    SigmaTrue H (n+1) (kpair H (natV H 7) c1) e ↔
      ∃ d, SigmaTrue H (n+1) c1 (econs H d e) :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_ex

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (he : IsUnivEnv H e),
    PiTrue H (n+1) (kpair H (natV H 6) c1) e ↔
      ∀ d, PiTrue H (n+1) c1 (econs H d e) :=
  @LeanProofs.BoundedZFCConsistency.piTrue_all

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (he : IsUnivEnv H e)
    (hb : PiBounded H (natV H n) (kpair H (natV H 6) c1))
    (hp : PiTrue H n (kpair H (natV H 6) c1) e),
    SigmaTrue H (n+1) (kpair H (natV H 6) c1) e :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_all_of_piTrue

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (he : IsUnivEnv H e)
    (hb : SigmaBounded H (natV H n) (kpair H (natV H 7) c1))
    (hp : ¬ SigmaTrue H n (kpair H (natV H 7) c1) e),
    PiFalse H (n+1) (kpair H (natV H 7) c1) e :=
  @LeanProofs.BoundedZFCConsistency.piFalse_ex_of_not_sigmaTrue

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (h : SigmaTrue H (n+1) (kpair H (natV H 6) c1) e),
    SigmaTrue H n (kpair H (natV H 6) c1) e ∨
      (PiBounded H (natV H n) (kpair H (natV H 6) c1) ∧
        PiTrue H n (kpair H (natV H 6) c1) e) :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_all_inv

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (h : PiFalse H (n+1) (kpair H (natV H 7) c1) e),
    PiFalse H n (kpair H (natV H 7) c1) e ∨
      (SigmaBounded H (natV H n) (kpair H (natV H 7) c1) ∧
        ¬ SigmaTrue H n (kpair H (natV H 7) c1) e) :=
  @LeanProofs.BoundedZFCConsistency.piFalse_ex_inv

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) {c1 e : V},
    ¬ SigmaTrue H 1 (kpair H (natV H 6) c1) e :=
  @LeanProofs.BoundedZFCConsistency.not_sigmaTrue_one_all

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) {c1 e : V},
    ¬ PiFalse H 1 (kpair H (natV H 7) c1) e :=
  @LeanProofs.BoundedZFCConsistency.not_piFalse_one_ex

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (phi : Form) (hphi : IsQuantFree phi),
    (SigmaTrue H 0 (formCode H phi) E ↔
        Sat mem (fun k => applyV H E (natV H k)) phi) ∧
      (PiFalse H 0 (formCode H phi) E ↔
        ¬ Sat mem (fun k => applyV H E (natV H k)) phi) :=
  @LeanProofs.BoundedZFCConsistency.levelSat_formCode_zero

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {E : V}
    (hE : IsUnivEnv H E) (phi : Form) (hphi : IsQuantFree phi)
    (h : Sat mem (fun k => applyV H E (natV H k)) phi),
    SigmaTrue H n (formCode H phi) E :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_formCode_of_sat

example : ∀ {V : Type u} {mem : V → V → Prop},
    ∀ (H : ZFAxioms mem) (n : Nat) {E : V}
    (hE : IsUnivEnv H E) (phi : Form) (hphi : IsQuantFree phi)
    (h : ¬ Sat mem (fun k => applyV H E (natV H k)) phi),
    PiFalse H n (formCode H phi) E :=
  @LeanProofs.BoundedZFCConsistency.piFalse_formCode_of_not_sat

