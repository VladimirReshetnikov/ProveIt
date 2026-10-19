import BoundedZFCConsistency.CodedDerivation

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency

universe u
variable {V : Type u} {mem : V → V → Prop}

#print axioms LeanProofs.BoundedZFCConsistency.memCtx_ctxCode
#print axioms LeanProofs.BoundedZFCConsistency.shiftsCtx_ctxCode
#print axioms LeanProofs.BoundedZFCConsistency.fDerivesF_spec
#print axioms LeanProofs.BoundedZFCConsistency.provCode_of_prov
#print axioms LeanProofs.BoundedZFCConsistency.derives_of_prov
#print axioms LeanProofs.BoundedZFCConsistency.ctxSat_shift
#print axioms LeanProofs.BoundedZFCConsistency.soundAt_all
#print axioms LeanProofs.BoundedZFCConsistency.derives_sound
#print axioms LeanProofs.BoundedZFCConsistency.not_derives_bot
#print axioms LeanProofs.BoundedZFCConsistency.prov_satIn

example (H : ZFAxioms mem) (G : List Form) (x : V) :
    MemCtx H x (ctxCode H G) ↔ ∃ a, a ∈ G ∧ x = formCode H a :=
  LeanProofs.BoundedZFCConsistency.memCtx_ctxCode H G x

example (H : ZFAxioms mem) (G : List Form) :
    ShiftsCtx H (ctxCode H G) (ctxCode H (G.map (rename Nat.succ))) :=
  LeanProofs.BoundedZFCConsistency.shiftsCtx_ctxCode H G

example (H : ZFAxioms mem) (ee : Nat → V) (d_i g_i c_i : Nat) :
    Sat mem ee (fDerivesF d_i g_i c_i) ↔ Derives H (ee d_i) (ee g_i) (ee c_i) :=
  LeanProofs.BoundedZFCConsistency.fDerivesF_spec H ee d_i g_i c_i

example (H : ZFAxioms mem) {G : List Form} {a : Form} (h : Prov G a) :
    ∃ (k : Nat) (D : V), DerClosed H D ∧
      mem (satTriple H (natV H k) (ctxCode H G) (formCode H a)) D :=
  LeanProofs.BoundedZFCConsistency.provCode_of_prov H h

example (H : ZFAxioms mem) {G : List Form} {a : Form} (h : Prov G a) :
    ∃ d, Derives H d (ctxCode H G) (formCode H a) :=
  LeanProofs.BoundedZFCConsistency.derives_of_prov H h

example (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {g g' e d : V} (hsh : ShiftsCtx H g g') (he : IsEnvOn H A e)
    (hd : mem d A) (hg : CtxSat H A R g e) :
    CtxSat H A R g' (econs H d e) :=
  LeanProofs.BoundedZFCConsistency.ctxSat_shift H hS hsh he hd hg

example (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {D : V} (hD : DerClosed H D) :
    ∀ n, mem n (omegaV H) → SoundAt H A R D n :=
  LeanProofs.BoundedZFCConsistency.soundAt_all H hS hD

example (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {d g c e : V} (hd : Derives H d g c) (he : IsEnvOn H A e)
    (hg : CtxSat H A R g e) : SatIn H A R c e :=
  LeanProofs.BoundedZFCConsistency.derives_sound H hS hd he hg

example (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R) {d : V}
    (hd : Derives H d (ctxNil H) (kpair H (natV H 2) (vempty H))) : False :=
  LeanProofs.BoundedZFCConsistency.not_derives_bot H hS hd

example (H : ZFAxioms mem) {A R : V} (hS : IsSetStructure H A R)
    {G : List Form} {a : Form} (h : Prov G a) {e : V} (he : IsEnvOn H A e)
    (hg : ∀ b ∈ G, SatIn H A R (formCode H b) e) : SatIn H A R (formCode H a) e :=
  LeanProofs.BoundedZFCConsistency.prov_satIn H hS h he hg
