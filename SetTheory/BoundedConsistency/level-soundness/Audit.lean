import BoundedZFCConsistency.LevelSoundness

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
set_option autoImplicit false

universe u

#print axioms LeanProofs.BoundedZFCConsistency.isEnvOn_envCarrier
#print axioms LeanProofs.BoundedZFCConsistency.compV_isUnivEnv
#print axioms LeanProofs.BoundedZFCConsistency.compV_econs_upVU
#print axioms LeanProofs.BoundedZFCConsistency.compV_succMapU
#print axioms LeanProofs.BoundedZFCConsistency.compV_instMapU
#print axioms LeanProofs.BoundedZFCConsistency.fCompF_specU
#print axioms LeanProofs.BoundedZFCConsistency.ranks_renames_iff
#print axioms LeanProofs.BoundedZFCConsistency.sigmaBounded_renames_iff
#print axioms LeanProofs.BoundedZFCConsistency.piBounded_renames_iff
#print axioms LeanProofs.BoundedZFCConsistency.qfSubstOK_of_isQFCodeSem
#print axioms LeanProofs.BoundedZFCConsistency.levelSubst_zero
#print axioms LeanProofs.BoundedZFCConsistency.fLevelSubstOKF_spec
#print axioms LeanProofs.BoundedZFCConsistency.levelSubstOK_of_isFormCodeSem
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_renames
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_renames
#print axioms LeanProofs.BoundedZFCConsistency.piTrue_renames
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_renameV_succMap
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_renameV_succMap
#print axioms LeanProofs.BoundedZFCConsistency.sigmaTrue_renameV_instMap
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_renameV_instMap
#print axioms LeanProofs.BoundedZFCConsistency.noBoundedRefutation_of_levelSoundness

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E)
    (d : V) :
    IsEnvOn H (envCarrier H E d) E :=
  @LeanProofs.BoundedZFCConsistency.isEnvOn_envCarrier V mem H E hE d

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {E r : V} (hE : IsUnivEnv H E)
    (hr : IsVarMap H r) :
    IsUnivEnv H (compV H E r) :=
  @LeanProofs.BoundedZFCConsistency.compV_isUnivEnv V mem H E r hE hr

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {E r : V} (hE : IsUnivEnv H E)
    (hr : IsVarMap H r) (d : V) :
    compV H (econs H d E) (upV H r) = econs H d (compV H E r) :=
  @LeanProofs.BoundedZFCConsistency.compV_econs_upVU V mem H E r hE hr d

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {E : V} (hE : IsUnivEnv H E) (d : V) :
    compV H (econs H d E) (succMap H) = E :=
  @LeanProofs.BoundedZFCConsistency.compV_succMapU V mem H E hE d

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {E k : V} (hE : IsUnivEnv H E)
    (hk : mem k (omegaV H)) :
    compV H E (instMap H k) = econs H (applyV H E k) E :=
  @LeanProofs.BoundedZFCConsistency.compV_instMapU V mem H E k hE hk

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (ee : Nat → V) (i e_i r_i : Nat)
    (he : IsUnivEnv H (ee e_i)) (hr : IsVarMap H (ee r_i)) :
    Sat mem ee (fCompF i e_i r_i) ↔ ee i = compV H (ee e_i) (ee r_i) :=
  @LeanProofs.BoundedZFCConsistency.fCompF_specU V mem H ee i e_i r_i he hr

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {r c c' s p : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (hren : Renames H r c c') :
    Ranks H c s p ↔ Ranks H c' s p :=
  @LeanProofs.BoundedZFCConsistency.ranks_renames_iff V mem H r c c' s p hc hr hren

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {b r c c' : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (hren : Renames H r c c') :
    SigmaBounded H b c ↔ SigmaBounded H b c' :=
  @LeanProofs.BoundedZFCConsistency.sigmaBounded_renames_iff V mem H b r c c' hc hr hren

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {b r c c' : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (hren : Renames H r c c') :
    PiBounded H b c ↔ PiBounded H b c' :=
  @LeanProofs.BoundedZFCConsistency.piBounded_renames_iff V mem H b r c c' hc hr hren

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) :
    ∀ c, IsQFCodeSem H c → QFSubstOK H c :=
  @LeanProofs.BoundedZFCConsistency.qfSubstOK_of_isQFCodeSem V mem H

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) {r c c' e : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (he : IsUnivEnv H e)
    (hren : Renames H r c c') :
    (SigmaTrue H 0 c' e ↔ SigmaTrue H 0 c (compV H e r)) ∧
      (PiFalse H 0 c' e ↔ PiFalse H 0 c (compV H e r)) :=
  @LeanProofs.BoundedZFCConsistency.levelSubst_zero V mem H r c c' e hc hr he hren

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) (y : V) :
    Sat mem (scons y (envLevelSubst H)) (fLevelSubstOKF n) ↔
      LevelSubstOK H n y :=
  @LeanProofs.BoundedZFCConsistency.fLevelSubstOKF_spec V mem H n y

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) :
    ∀ (n : Nat) (c : V), IsFormCodeSem H c → LevelSubstOK H n c :=
  @LeanProofs.BoundedZFCConsistency.levelSubstOK_of_isFormCodeSem V mem H

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c c' r e : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (he : IsUnivEnv H e)
    (hren : Renames H r c c') :
    SigmaTrue H n c' e ↔ SigmaTrue H n c (compV H e r) :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_renames V mem H n c c' r e hc hr he hren

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c c' r e : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (he : IsUnivEnv H e)
    (hren : Renames H r c c') :
    PiFalse H n c' e ↔ PiFalse H n c (compV H e r) :=
  @LeanProofs.BoundedZFCConsistency.piFalse_renames V mem H n c c' r e hc hr he hren

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c c' r e : V}
    (hc : IsFormCodeSem H c) (hr : IsVarMap H r) (he : IsUnivEnv H e)
    (hren : Renames H r c c') :
    PiTrue H n c' e ↔ PiTrue H n c (compV H e r) :=
  @LeanProofs.BoundedZFCConsistency.piTrue_renames V mem H n c c' r e hc hr he hren

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c e d : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e) :
    SigmaTrue H n (renameV H (succMap H) c) (econs H d e) ↔
      SigmaTrue H n c e :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_renameV_succMap V mem H n c e d hc he

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c e d : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e) :
    PiFalse H n (renameV H (succMap H) c) (econs H d e) ↔ PiFalse H n c e :=
  @LeanProofs.BoundedZFCConsistency.piFalse_renameV_succMap V mem H n c e d hc he

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c e k : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e) (hk : mem k (omegaV H)) :
    SigmaTrue H n (renameV H (instMap H k) c) e ↔
      SigmaTrue H n c (econs H (applyV H e k) e) :=
  @LeanProofs.BoundedZFCConsistency.sigmaTrue_renameV_instMap V mem H n c e k hc he hk

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c e k : V}
    (hc : IsFormCodeSem H c) (he : IsUnivEnv H e) (hk : mem k (omegaV H)) :
    PiFalse H n (renameV H (instMap H k) c) e ↔
      PiFalse H n c (econs H (applyV H e k) e) :=
  @LeanProofs.BoundedZFCConsistency.piFalse_renameV_instMap V mem H n c e k hc he hk

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat)
    (hax : AxiomCodesTrueAt H n) (hsound : LevelSoundnessAt H n) :
    NoBoundedRefutationAtLevel H n :=
  @LeanProofs.BoundedZFCConsistency.noBoundedRefutation_of_levelSoundness V mem H n hax hsound

