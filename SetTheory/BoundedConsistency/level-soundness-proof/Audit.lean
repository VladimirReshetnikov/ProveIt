import BoundedZFCConsistency.LevelSoundnessProof

open SetTheory SetTheory.Form
open LeanProofs.BoundedZFCConsistency
set_option autoImplicit false

universe u

#print axioms LeanProofs.BoundedZFCConsistency.levelTrue_of_sigmaTrue
#print axioms LeanProofs.BoundedZFCConsistency.levelTrue_of_piTrue
#print axioms LeanProofs.BoundedZFCConsistency.piFalse_of_not_levelTrue
#print axioms LeanProofs.BoundedZFCConsistency.ctxLevelTrue_cons
#print axioms LeanProofs.BoundedZFCConsistency.ctxLevelTrue_shift
#print axioms LeanProofs.BoundedZFCConsistency.fLevelTrueF_spec
#print axioms LeanProofs.BoundedZFCConsistency.fCtxLevelTrueF_spec
#print axioms LeanProofs.BoundedZFCConsistency.fLevelSoundAtF_spec
#print axioms LeanProofs.BoundedZFCConsistency.fLevelSoundBelowF_spec
#print axioms LeanProofs.BoundedZFCConsistency.levelSoundAt_step
#print axioms LeanProofs.BoundedZFCConsistency.levelSoundBelow
#print axioms LeanProofs.BoundedZFCConsistency.levelSoundAt_all
#print axioms LeanProofs.BoundedZFCConsistency.levelSoundnessAt
#print axioms LeanProofs.BoundedZFCConsistency.noBoundedRefutationAtLevel

example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c E : V}
    (hc : IsFormCodeSem H c) (hE : IsUnivEnv H E)
    (h : SigmaTrue H (n+1) c E) : LevelTrue H n c E :=
  @LeanProofs.BoundedZFCConsistency.levelTrue_of_sigmaTrue V mem H n c E hc hE h


example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c E : V}
    (hc : IsFormCodeSem H c) (hq : QuantBounded H (natV H n) c)
    (hE : IsUnivEnv H E) (h : PiTrue H (n+1) c E) : LevelTrue H n c E :=
  @LeanProofs.BoundedZFCConsistency.levelTrue_of_piTrue V mem H n c E hc hq hE h


example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {c E : V}
    (hc : IsFormCodeSem H c) (hq : QuantBounded H (natV H n) c)
    (hE : IsUnivEnv H E) (h : ¬ LevelTrue H n c E) : PiFalse H (n+1) c E :=
  @LeanProofs.BoundedZFCConsistency.piFalse_of_not_levelTrue V mem H n c E hc hq hE h


example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {g E a : V}
    (hg : CtxLevelTrue H n g E) (ha : LevelTrue H n a E) :
    CtxLevelTrue H n (ctxCons H a g) E :=
  @LeanProofs.BoundedZFCConsistency.ctxLevelTrue_cons V mem H n g E a hg ha


example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {g g' E d : V}
    (hsh : ShiftsCtx H g g') (hE : IsUnivEnv H E)
    (hg : CtxLevelTrue H n g E) : CtxLevelTrue H n g' (econs H d E) :=
  @LeanProofs.BoundedZFCConsistency.ctxLevelTrue_shift V mem H n g g' E d hsh hE hg


example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) (ee : Nat → V)
    (c_i e_i : Nat) :
    Sat mem ee (fLevelTrueF n c_i e_i) ↔ LevelTrue H n (ee c_i) (ee e_i) :=
  @LeanProofs.BoundedZFCConsistency.fLevelTrueF_spec V mem H n ee c_i e_i


example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) (ee : Nat → V)
    (g_i e_i : Nat) :
    Sat mem ee (fCtxLevelTrueF n g_i e_i) ↔
      CtxLevelTrue H n (ee g_i) (ee e_i) :=
  @LeanProofs.BoundedZFCConsistency.fCtxLevelTrueF_spec V mem H n ee g_i e_i


example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) (ee : Nat → V)
    (m_i d_i : Nat) :
    Sat mem ee (fLevelSoundAtF n m_i d_i) ↔
      LevelSoundAt H n (ee d_i) (ee m_i) :=
  @LeanProofs.BoundedZFCConsistency.fLevelSoundAtF_spec V mem H n ee m_i d_i


example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) (D k : V) :
    Sat mem (scons k (envLevelSound D)) (fLevelSoundBelowF n) ↔
      ∀ m, mem m k → LevelSoundAt H n D m :=
  @LeanProofs.BoundedZFCConsistency.fLevelSoundBelowF_spec V mem H n D k


example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {D : V}
    (hD : DerClosed H D) (hb : DerAllBounded H (natV H n) D) {m : V}
    (ih : ∀ k, mem k m → LevelSoundAt H n D k) : LevelSoundAt H n D m :=
  @LeanProofs.BoundedZFCConsistency.levelSoundAt_step V mem H n D hD hb m ih


example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {D : V}
    (hD : DerClosed H D) (hb : DerAllBounded H (natV H n) D) :
    ∀ k, mem k (omegaV H) → ∀ m, mem m k → LevelSoundAt H n D m :=
  @LeanProofs.BoundedZFCConsistency.levelSoundBelow V mem H n D hD hb


example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) {D : V}
    (hD : DerClosed H D) (hb : DerAllBounded H (natV H n) D) :
    ∀ k, mem k (omegaV H) → LevelSoundAt H n D k :=
  @LeanProofs.BoundedZFCConsistency.levelSoundAt_all V mem H n D hD hb


example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat) : LevelSoundnessAt H n :=
  @LeanProofs.BoundedZFCConsistency.levelSoundnessAt V mem H n


example {V : Type u} {mem : V → V → Prop}
    (H : ZFAxioms mem) (n : Nat)
    (hax : AxiomCodesTrueAt H n) : NoBoundedRefutationAtLevel H n :=
  @LeanProofs.BoundedZFCConsistency.noBoundedRefutationAtLevel V mem H n hax

