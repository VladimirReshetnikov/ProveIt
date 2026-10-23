import GuardedSubtype
import BusyBeaver.ZFC.KLowerRel
import BusyBeaver.ZFC.WFRelativization

/-! UNCOMPILED comparison client against the pinned, unchanged definitions.
No old definition is shadowed, and no endpoint equivalence is claimed. -/

namespace SetTheory.BusyBeaver.ZFC.GuardedSubtypeAdapters

open Form
universe u
variable {V : Type u}

def tagTranslate (d : Nat) : Form → Form :=
  GuardedSubtype.translate Nat.succ KLower.sh (fun d => fMem (d + 1) 0) d

def wfTranslate : Form → Form :=
  GuardedSubtype.translate (fun c : Unit => c) (fun _ i => i)
    (fun _ => WellFoundedPart.wfForm 0) ()

/-- Exact source syntax, not merely equisatisfiability. -/
theorem tagTranslate_eq (phi : Form) : ∀ d, tagTranslate d phi = KLower.relT d phi := by
  induction phi with
  | fMem _ _ | fEq _ _ | fBot => intro _; rfl
  | fImp _ _ iha ihb => intro d; exact congrArg₂ fImp (iha d) (ihb d)
  | fAnd _ _ iha ihb => intro d; exact congrArg₂ fAnd (iha d) (ihb d)
  | fOr _ _ iha ihb => intro d; exact congrArg₂ fOr (iha d) (ihb d)
  | fAll _ ih =>
      intro d
      exact congrArg (fun a => fAll (fImp (fMem (d + 1) 0) a)) (ih (d + 1))
  | fEx _ ih =>
      intro d
      exact congrArg (fun a => fEx (fAnd (fMem (d + 1) 0) a)) (ih (d + 1))

theorem wfTranslate_eq (phi : Form) : wfTranslate phi = WFRelativization.translate phi := by
  induction phi with
  | fMem _ _ | fEq _ _ | fBot => rfl
  | fImp _ _ iha ihb => exact congrArg₂ fImp iha ihb
  | fAnd _ _ iha ihb => exact congrArg₂ fAnd iha ihb
  | fOr _ _ iha ihb => exact congrArg₂ fOr iha ihb
  | fAll _ ih =>
      exact congrArg (fun a => fAll (fImp (WellFoundedPart.wfForm 0) a)) ih
  | fEx _ ih =>
      exact congrArg (fun a => fEx (fAnd (WellFoundedPart.wfForm 0) a)) ih

/-- The marker remains at d after d source variables have been pushed. -/
theorem tagged (mem : V → V → Prop) (t : V) (phi : Form) (d : Nat)
    (e : Nat → KLower.Tag mem t) (r : Nat → V)
    (he : KLower.Shows t d e r) (ht : r d = t) :
    Sat mem r (tagTranslate d phi) ↔ Sat (KLower.tmem mem t) e phi := by
  apply GuardedSubtype.sat_translate mem (fun x => mem t x)
    Nat.succ KLower.sh (fun d => fMem (d + 1) 0)
    (fun d r => r d = t)
    (fun d => by simp [KLower.sh])
    (fun d i => by unfold KLower.sh; split <;> split <;> omega)
    (fun _ _ _ h => h)
    (fun d r x h => by change (mem (r d) x ↔ mem t x); rw [h])
    phi d e r ht he

theorem wellFounded (mem : V → V → Prop) (phi : Form)
    (e : Nat → WellFoundedPart.Domain mem) :
    Sat mem (WFRelativization.liftEnv mem e) (wfTranslate phi) ↔
      Sat (WellFoundedPart.domainMem mem) e phi := by
  apply GuardedSubtype.sat_translate mem (WellFoundedPart.WF mem)
    (fun c : Unit => c) (fun _ i => i) (fun _ => WellFoundedPart.wfForm 0)
    (fun _ _ => True) (fun _ => rfl) (fun _ _ => rfl)
    (fun _ _ _ _ => True.intro)
    (fun _ r x _ => WellFoundedPart.sat_wfForm mem (scons x r) 0)
    phi () e (WFRelativization.liftEnv mem e) True.intro (fun _ => rfl)

end SetTheory.BusyBeaver.ZFC.GuardedSubtypeAdapters
