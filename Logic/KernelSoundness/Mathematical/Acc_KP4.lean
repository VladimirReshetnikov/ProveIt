/-
KP3: labelled kernel-defeq report + the complete non-transitivity chain.
-/
import Lean
open Lean Elab Command Meta Term

set_option linter.unusedVariables false
set_option linter.defProp false
universe u v

syntax (name := kdefeqCmd) "#kd " str " : " term " =?= " term : command

@[command_elab kdefeqCmd] def elabKdefeq : CommandElab := fun stx => do
  match stx with
  | `(#kd $lbl:str : $a =?= $b) =>
    liftTermElabM do
      let ea ← elabTerm a none
      synthesizeSyntheticMVarsNoPostponing
      let ea ← instantiateMVars ea
      let ty ← inferType ea
      let eb ← elabTerm b ty
      synthesizeSyntheticMVarsNoPostponing
      let eb ← instantiateMVars eb
      if ea.hasExprMVar || eb.hasExprMVar || ea.hasFVar || eb.hasFVar then
        logError m!"open term / metavariables remain"; return
      let type ← mkEq ea eb
      let value ← mkEqRefl ea
      let nm := Name.mkSimple s!"kdProbe_{hash (toString type)}"
      let env ← getEnv
      let t0 ← IO.monoMsNow
      match env.addDeclCore 4000000
              (.thmDecl { name := nm, levelParams := [], type, value }) none true with
      | .ok _    => logInfo m!"[KERNEL ACCEPT] {lbl.getString}  ({(← IO.monoMsNow) - t0}ms)"
      | .error _ => logInfo m!"[KERNEL REJECT] {lbl.getString}  ({(← IO.monoMsNow) - t0}ms)"
  | _ => throwUnsupportedSyntax

/-! ## setup: a genuinely well-founded relation, all proofs whnf-transparent -/

def tr {α : Sort u} {motive : α → Prop} {a b : α} (h : a = b) (x : motive a) : motive b :=
  @Eq.rec α a (fun z _ => motive z) x b h

def R (a b : Nat) : Prop := a + 1 = b

def Racc : ∀ n, Acc R n :=
  Nat.rec
    (Acc.intro 0 (fun y hy => absurd (show y + 1 = 0 from hy) (Nat.succ_ne_zero y)))
    (fun n ih => Acc.intro (n + 1) (fun y hy =>
      tr (motive := fun z => Acc R z)
        (Eq.symm (Nat.add_right_cancel (show y + 1 = n + 1 from hy))) ih))

noncomputable def cnt : {x : Nat} → Acc R x → Nat := fun {x} h =>
  Acc.rec (motive := fun _ _ => Nat)
    (fun x _ ih =>
      Nat.casesOn (motive := fun z => ((y : Nat) → R y z → Nat) → Nat) x
        (fun _ => 0) (fun k f => (f k rfl) + 1) (fun y hy => ih y hy)) h

/-! ## the three terms of the non-transitivity chain (all closed) -/
noncomputable def A : Acc R 3 → Nat := fun h => cnt h
noncomputable def B : Acc R 3 → Nat := fun _ => cnt (Racc 3)
noncomputable def C : Acc R 3 → Nat := fun _ => 3

/-! ## non-transitivity, closed terms, labelled -/
noncomputable def A : Acc R 3 → Nat := fun h => cnt h
noncomputable def B : Acc R 3 → Nat := fun _ => cnt (Racc 3)
noncomputable def C : Acc R 3 → Nat := fun _ => 3

#kd "A =?= B" : A =?= B
#kd "B =?= C" : B =?= C
#kd "A =?= C" : A =?= C

theorem AB : A = B := rfl
theorem BC : B = C := funext (fun _ => (rfl : cnt (Racc 3) = 3))
theorem AC : A = C := AB.trans BC
theorem pointwise (h : Acc R 3) : cnt h = 3 := congrFun AC h
#print axioms pointwise

/-! ## the false context, labelled -/
def R0 : Unit → Unit → Prop := fun _ _ => True
noncomputable def cnt0 (h : Acc R0 ()) : Nat :=
  Acc.rec (motive := fun _ _ => Nat) (fun x f ih => (ih x trivial).succ) h
def eta (h : Acc R0 ()) : Acc R0 () := Acc.intro () (fun y _ => h)

noncomputable def P : Acc R0 () → Nat := fun h => cnt0 h
noncomputable def Q : Acc R0 () → Nat := fun h => cnt0 (eta h)
noncomputable def S : Acc R0 () → Nat := fun h => (cnt0 h).succ

#kd "id =?= eta (proof irrel)" : (fun (h : Acc R0 ()) => h) =?= eta
#kd "P =?= Q" : P =?= Q
#kd "Q =?= S" : Q =?= S
#kd "P =?= S  (n =?= n+1)" : P =?= S

theorem PQ : P = Q := rfl
theorem QS : Q = S := rfl
theorem PS : P = S := PQ.trans QS
theorem notAcc0 : ¬ Acc R0 () := fun h => Nat.succ_ne_self (cnt0 h) (congrFun PS h).symm
#print axioms notAcc0

/-! ## WellFounded.fix_eq, labelled -/
def Rwf : WellFounded R := WellFounded.intro Racc
noncomputable def FF : (x : Nat) → ((y : Nat) → R y x → Nat) → Nat := fun x g =>
  Nat.casesOn (motive := fun z => ((y : Nat) → R y z → Nat) → Nat) x
    (fun _ => 0) (fun k f => (f k rfl) + 1) g
#kd "fix Rwf FF 4 =?= 4" : WellFounded.fix Rwf FF 4 =?= 4
#kd "fix_eq at concrete WF proof" :
  WellFounded.fix Rwf FF 4 =?= FF 4 (fun y _ => WellFounded.fix Rwf FF y)
#kd "fix_eq under an opaque WF proof" :
  (fun (hwf : WellFounded R) => WellFounded.fix hwf FF 4)
    =?= (fun (hwf : WellFounded R) => FF 4 (fun y _ => WellFounded.fix hwf FF y))
