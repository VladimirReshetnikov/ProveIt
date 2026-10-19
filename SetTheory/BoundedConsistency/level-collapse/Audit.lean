import BoundedZFCConsistency.LevelCollapse

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
set_option autoImplicit false

universe u

#print axioms LeanProofs.BoundedZFCConsistency.sigmaBounded_le
#print axioms LeanProofs.BoundedZFCConsistency.piBounded_le
#print axioms LeanProofs.BoundedZFCConsistency.sigmaBounded_or_piBounded
#print axioms LeanProofs.BoundedZFCConsistency.sigmaBounded_imp
#print axioms LeanProofs.BoundedZFCConsistency.piBounded_imp
#print axioms LeanProofs.BoundedZFCConsistency.piBounded_of_sigmaBounded_all_succ
#print axioms LeanProofs.BoundedZFCConsistency.sigmaBounded_of_piBounded_ex_succ
#print axioms LeanProofs.BoundedZFCConsistency.collapseF_spec
#print axioms LeanProofs.BoundedZFCConsistency.collapse_zero
#print axioms LeanProofs.BoundedZFCConsistency.collapse_succ
#print axioms LeanProofs.BoundedZFCConsistency.collapseAt_of_isFormCodeSem
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_collapse
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_collapse
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_collapse_iff
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_collapse_iff
#print axioms LeanProofs.BoundedZFCConsistency.piTrue_mono
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_all_inv'
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_ex_inv'
#print axioms LeanProofs.BoundedZFCConsistency.exclF_spec
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_not_piFalse
#print axioms LeanProofs.BoundedZFCConsistency.piTrue_of_sigmaTrue
#print axioms LeanProofs.BoundedZFCConsistency.totalF_spec
#print axioms LeanProofs.BoundedZFCConsistency.totalAt_of_isFormCodeSem
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_or_piFalse
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_iff_piTrue
#print axioms LeanProofs.BoundedZFCConsistency.levelTwoValuedAt
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_all_elim
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_all
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_ex_elim
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_ex

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {b b' c : V}
    (hb' : mem b' (omegaV H)) (h : SigmaBounded H b c) (hle : LeN H b b') :
    SigmaBounded H b' c :=
  @LeanProofs.BoundedZFCConsistency.sigmaBounded_le V mem H b b' c hb' h hle

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {b b' c : V}
    (hb' : mem b' (omegaV H)) (h : PiBounded H b c) (hle : LeN H b b') :
    PiBounded H b' c :=
  @LeanProofs.BoundedZFCConsistency.piBounded_le V mem H b b' c hb' h hle

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {b c : V}
    (h : QuantBounded H b c) :
    SigmaBounded H b c ∨ PiBounded H b c :=
  @LeanProofs.BoundedZFCConsistency.sigmaBounded_or_piBounded V mem H b c h

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {b a a' : V}
    (hb : mem b (omegaV H))
    (h : SigmaBounded H b (kpair H (natV H 3) (kpair H a a'))) :
    PiBounded H b a ∧ SigmaBounded H b a' :=
  @LeanProofs.BoundedZFCConsistency.sigmaBounded_imp V mem H b a a' hb h

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {b a a' : V} (hb : mem b (omegaV H))
    (h : PiBounded H b (kpair H (natV H 3) (kpair H a a'))) :
    SigmaBounded H b a ∧ PiBounded H b a' :=
  @LeanProofs.BoundedZFCConsistency.piBounded_imp V mem H b a a' hb h

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {a b : V}
    (hb : mem b (omegaV H))
    (h : SigmaBounded H (vsucc H b) (kpair H (natV H 6) a)) :
    PiBounded H b (kpair H (natV H 6) a) :=
  @LeanProofs.BoundedZFCConsistency.piBounded_of_sigmaBounded_all_succ V mem H a b hb h

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {a b : V}
    (hb : mem b (omegaV H))
    (h : PiBounded H (vsucc H b) (kpair H (natV H 7) a)) :
    SigmaBounded H b (kpair H (natV H 7) a) :=
  @LeanProofs.BoundedZFCConsistency.sigmaBounded_of_piBounded_ex_succ V mem H a b hb h

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) (y : V) :
    Sat mem (scons y (envCollapse H n)) (collapseF n) ↔ CollapseAt H n y :=
  @LeanProofs.BoundedZFCConsistency.collapseF_spec V mem H n y

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) :
    ∀ c, IsFormCodeSem H c → CollapseAt H 0 c :=
  @LeanProofs.BoundedZFCConsistency.collapse_zero V mem H

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (m : Nat) :
    ∀ c, IsFormCodeSem H c → CollapseAt H (m+1) c :=
  @LeanProofs.BoundedZFCConsistency.collapse_succ V mem H m

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) :
    ∀ c, IsFormCodeSem H c → CollapseAt H n c :=
  @LeanProofs.BoundedZFCConsistency.collapseAt_of_isFormCodeSem V mem H n

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c e : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hb : SigmaBounded H (natV H n) c) (h : SigmaTrue H (n+1) c e) :
    SigmaTrue H n c e :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_collapse V mem H n c e hc he hb h

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c e : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hb : PiBounded H (natV H n) c) (h : PiFalse H (n+1) c e) :
    PiFalse H n c e :=
  @LeanProofs.BoundedZFCConsistency.piFalse_collapse V mem H n c e hc he hb h

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {k n : Nat} (hkn : k ≤ n)
    {c e : V} (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hb : SigmaBounded H (natV H k) c) :
    SigmaTrue H n c e ↔ SigmaTrue H k c e :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_collapse_iff V mem H k n hkn c e hc he hb

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {k n : Nat} (hkn : k ≤ n)
    {c e : V} (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hb : PiBounded H (natV H k) c) :
    PiFalse H n c e ↔ PiFalse H k c e :=
  @LeanProofs.BoundedZFCConsistency.piFalse_collapse_iff V mem H k n hkn c e hc he hb

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {k n : Nat} (hkn : k ≤ n) {c e : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e)
    (hb : PiBounded H (natV H k) c) (h : PiTrue H k c e) :
    PiTrue H n c e :=
  @LeanProofs.BoundedZFCConsistency.piTrue_mono V mem H k n hkn c e hc he hb h

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) :
    ∀ (n : Nat) {c1 e : V}, SigmaTrue H n (kpair H (natV H 6) c1) e →
      ∃ k, k < n ∧ PiBounded H (natV H k) (kpair H (natV H 6) c1) ∧
        PiTrue H k (kpair H (natV H 6) c1) e :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_all_inv' V mem H

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) :
    ∀ (n : Nat) {c1 e : V}, PiFalse H n (kpair H (natV H 7) c1) e →
      ∃ k, k < n ∧ SigmaBounded H (natV H k) (kpair H (natV H 7) c1) ∧
        ¬ SigmaTrue H k (kpair H (natV H 7) c1) e :=
  @LeanProofs.BoundedZFCConsistency.piFalse_ex_inv' V mem H

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) (y : V) :
    Sat mem (scons y (envExcl H)) (exclF n) ↔ ExclAt H n y :=
  @LeanProofs.BoundedZFCConsistency.exclF_spec V mem H n y

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) :
    ∀ (n : Nat) (c e : V), IsFormCodeSem H c → IsUnivEnv H e →
      SigmaTrue H n c e → ¬ PiFalse H n c e :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_not_piFalse V mem H

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c e : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e) (h : SigmaTrue H n c e) :
    PiTrue H n c e :=
  @LeanProofs.BoundedZFCConsistency.piTrue_of_sigmaTrue V mem H n c e hc he h

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) (y : V) :
    Sat mem (scons y (envCollapse H n)) (totalF n) ↔ TotalAt H n y :=
  @LeanProofs.BoundedZFCConsistency.totalF_spec V mem H n y

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) :
    ∀ c, IsFormCodeSem H c → TotalAt H n c :=
  @LeanProofs.BoundedZFCConsistency.totalAt_of_isFormCodeSem V mem H n

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c e : V}
    (hc : IsFormCodeSem H c) (hq : QuantBounded H (natV H n) c)
    (he : IsUnivEnv H e) :
    SigmaTrue H (n+1) c e ∨ PiFalse H (n+1) c e :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_or_piFalse V mem H n c e hc hq he

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c e : V}
    (hc : IsFormCodeSem H c) (hq : QuantBounded H (natV H n) c)
    (he : IsUnivEnv H e) :
    SigmaTrue H (n+1) c e ↔ PiTrue H (n+1) c e :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_iff_piTrue V mem H n c e hc hq he

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) :
    LevelTwoValuedAt H n :=
  @LeanProofs.BoundedZFCConsistency.levelTwoValuedAt V mem H n

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (hc : IsFormCodeSem H (kpair H (natV H 6) c1)) (he : IsUnivEnv H e)
    (h : SigmaTrue H (n+1) (kpair H (natV H 6) c1) e) :
    PiTrue H n (kpair H (natV H 6) c1) e :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_all_elim V mem H n c1 e hc he h

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (hc : IsFormCodeSem H (kpair H (natV H 6) c1)) (he : IsUnivEnv H e)
    (hb : PiBounded H (natV H n) (kpair H (natV H 6) c1)) :
    SigmaTrue H (n+1) (kpair H (natV H 6) c1) e ↔
      PiTrue H n (kpair H (natV H 6) c1) e :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_all V mem H n c1 e hc he hb

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (hc : IsFormCodeSem H (kpair H (natV H 7) c1)) (he : IsUnivEnv H e)
    (h : PiFalse H (n+1) (kpair H (natV H 7) c1) e) :
    ¬ SigmaTrue H n (kpair H (natV H 7) c1) e :=
  @LeanProofs.BoundedZFCConsistency.piFalse_ex_elim V mem H n c1 e hc he h

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c1 e : V}
    (hc : IsFormCodeSem H (kpair H (natV H 7) c1)) (he : IsUnivEnv H e)
    (hb : SigmaBounded H (natV H n) (kpair H (natV H 7) c1)) :
    PiFalse H (n+1) (kpair H (natV H 7) c1) e ↔
      ¬ SigmaTrue H n (kpair H (natV H 7) c1) e :=
  @LeanProofs.BoundedZFCConsistency.piFalse_ex V mem H n c1 e hc he hb

