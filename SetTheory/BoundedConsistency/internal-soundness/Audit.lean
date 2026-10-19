import BoundedZFCConsistency.InternalSoundness

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

#print axioms LeanProofs.BoundedZFCConsistency.upV_isVarMap
#print axioms LeanProofs.BoundedZFCConsistency.compV_econs_upV
#print axioms LeanProofs.BoundedZFCConsistency.compV_succMap
#print axioms LeanProofs.BoundedZFCConsistency.compV_instMap
#print axioms LeanProofs.BoundedZFCConsistency.renTotal_of_isFormCodeSem
#print axioms LeanProofs.BoundedZFCConsistency.renUnique_of_isFormCodeSem
#print axioms LeanProofs.BoundedZFCConsistency.renames_renameV
#print axioms LeanProofs.BoundedZFCConsistency.renameV_isFormCodeSem
#print axioms LeanProofs.BoundedZFCConsistency.satIn_renames
#print axioms LeanProofs.BoundedZFCConsistency.satIn_renameV
#print axioms LeanProofs.BoundedZFCConsistency.satIn_renameV_succMap
#print axioms LeanProofs.BoundedZFCConsistency.satIn_renameV_instMap
#print axioms LeanProofs.BoundedZFCConsistency.renameV_formCode
#print axioms LeanProofs.BoundedZFCConsistency.renameV_formCode_succMap
#print axioms LeanProofs.BoundedZFCConsistency.renameV_formCode_instMap

example (H : ZFAxioms mem) {r : V} (hr : IsVarMap H r) :
    IsVarMap H (upV H r) :=
  LeanProofs.BoundedZFCConsistency.upV_isVarMap H hr

example (H : ZFAxioms mem) {A e r d : V} (he : IsEnvOn H A e)
    (hr : IsVarMap H r) (hd : mem d A) :
    compV H (econs H d e) (upV H r) = econs H d (compV H e r) :=
  LeanProofs.BoundedZFCConsistency.compV_econs_upV H he hr hd

example (H : ZFAxioms mem) {A e d : V} (he : IsEnvOn H A e)
    (hd : mem d A) : compV H (econs H d e) (succMap H) = e :=
  LeanProofs.BoundedZFCConsistency.compV_succMap H he hd

example (H : ZFAxioms mem) {A e k : V} (he : IsEnvOn H A e)
    (hk : mem k (omegaV H)) :
    compV H e (instMap H k) = econs H (applyV H e k) e :=
  LeanProofs.BoundedZFCConsistency.compV_instMap H he hk

example (H : ZFAxioms mem) (c : V) (hc : IsFormCodeSem H c) :
    RenTotal H c :=
  LeanProofs.BoundedZFCConsistency.renTotal_of_isFormCodeSem H c hc

example (H : ZFAxioms mem) (c : V) (hc : IsFormCodeSem H c) :
    RenUnique H c :=
  LeanProofs.BoundedZFCConsistency.renUnique_of_isFormCodeSem H c hc

example (H : ZFAxioms mem) {r c : V} (hc : IsFormCodeSem H c)
    (hr : IsVarMap H r) : Renames H r c (renameV H r c) :=
  LeanProofs.BoundedZFCConsistency.renames_renameV H hc hr

example (H : ZFAxioms mem) {r c : V} (hc : IsFormCodeSem H c)
    (hr : IsVarMap H r) : IsFormCodeSem H (renameV H r c) :=
  LeanProofs.BoundedZFCConsistency.renameV_isFormCodeSem H hc hr

example (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {c c' r e : V} (hc : IsFormCodeSem H c) (hr : IsVarMap H r)
    (he : IsEnvOn H A e) (hren : Renames H r c c') :
    SatIn H A R c' e ↔ SatIn H A R c (compV H e r) :=
  LeanProofs.BoundedZFCConsistency.satIn_renames H hS hc hr he hren

example (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {c r e : V} (hc : IsFormCodeSem H c) (hr : IsVarMap H r)
    (he : IsEnvOn H A e) :
    SatIn H A R (renameV H r c) e ↔ SatIn H A R c (compV H e r) :=
  LeanProofs.BoundedZFCConsistency.satIn_renameV H hS hc hr he

example (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {c e d : V} (hc : IsFormCodeSem H c) (he : IsEnvOn H A e)
    (hd : mem d A) :
    SatIn H A R (renameV H (succMap H) c) (econs H d e) ↔ SatIn H A R c e :=
  LeanProofs.BoundedZFCConsistency.satIn_renameV_succMap H hS hc he hd

example (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {c e k : V} (hc : IsFormCodeSem H c) (he : IsEnvOn H A e)
    (hk : mem k (omegaV H)) :
    SatIn H A R (renameV H (instMap H k) c) e ↔
      SatIn H A R c (econs H (applyV H e k) e) :=
  LeanProofs.BoundedZFCConsistency.satIn_renameV_instMap H hS hc he hk

example (H : ZFAxioms mem) {r : V} (f : Nat → Nat)
    (hr : IsVarMap H r) (h : AgreesWith H r f) (phi : Form) :
    renameV H r (formCode H phi) = formCode H (rename f phi) :=
  LeanProofs.BoundedZFCConsistency.renameV_formCode H f hr h phi

example (H : ZFAxioms mem) (phi : Form) :
    renameV H (succMap H) (formCode H phi) = formCode H (rename Nat.succ phi) :=
  LeanProofs.BoundedZFCConsistency.renameV_formCode_succMap H phi

example (H : ZFAxioms mem) (k : Nat) (phi : Form) :
    renameV H (instMap H (natV H k)) (formCode H phi) =
      formCode H (rename (inst k) phi) :=
  LeanProofs.BoundedZFCConsistency.renameV_formCode_instMap H k phi
