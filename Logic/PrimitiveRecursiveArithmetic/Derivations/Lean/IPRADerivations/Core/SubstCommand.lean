import IPRADerivations.Core.Integers

/-!
# Substitution lemmas for defined terms

A defined term `f (a b : PTm n) : PTm n` needs the simp lemma
`subst_f σ a b : Syn.subst σ (f a b) = f (Syn.subst σ a) (Syn.subst σ b)` before it can be used under binders or
in inductions. The command `ipra_subst f` states and proves it (`by simp [f]`); `ipra_subst f [l₁, …]` adds simp
lemmas for the proof. Arguments of type `PTm n`, `ZT n`, `Fm PTm n` are substituted, the others are kept; for a
formula or an integer term the lemma reads `(f a b).subst σ = …`.
-/

open Lean Elab Command Meta Term

namespace LeanProofs.IPRA.SubstCommand

/-- How an argument (or the result) depends on the dimension variable. -/
inductive Kind
  | tm | zt | fm | other
  deriving DecidableEq

/-- Classify a type relative to the dimension variable `n`. -/
def classify (n : Expr) (ty : Expr) : MetaM Kind := do
  let ty ← whnfR ty
  if !ty.containsFVar n.fvarId! then return .other
  match ty.getAppFn.constName?, ty.getAppArgs with
  | some ``LeanProofs.ConciseIPRA.PTm, #[k] => if k == n then return .tm else return .other
  | some ``LeanProofs.IPRA.ZT, #[k] => if k == n then return .zt else return .other
  | some ``LeanProofs.ConciseIPRA.Fm, #[_, _, k] => if k == n then return .fm else return .other
  | some ``LeanProofs.ConciseIPRA.Fm, #[_, k] => if k == n then return .fm else return .other
  | _, _ => throwError "ipra_subst: unsupported argument type {ty}"

end LeanProofs.IPRA.SubstCommand

/-- `ipra_subst f` generates the simp lemma `subst_f` that pushes a substitution through the defined term `f`. -/
syntax "ipra_subst " ident (" [" Lean.Parser.Tactic.simpLemma,* "]")? : command

open LeanProofs.IPRA.SubstCommand in
elab_rules : command
  | `(ipra_subst $id $[[$ext,*]]?) => do
  let c ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo id
  let info ← getConstInfo c
  let short := c.components.getLast!
  let thmName := mkIdent (Name.mkSimple ("subst_" ++ short.toString))
  let cmd ← liftTermElabM do
    forallTelescope info.type fun xs body => do
      let body ← whnfR body
      -- the dimension variable: the last argument of the result type
      let some n := body.getAppArgs.back? | throwError "ipra_subst: no dimension in {body}"
      unless n.isFVar && xs.contains n do throwError "ipra_subst: the dimension {n} is not a parameter"
      let resKind ← classify n body
      if resKind == .other then throwError "ipra_subst: unsupported result type {body}"
      let m := mkIdent `m
      let σ := mkIdent `σ
      let mut binders : Array (TSyntax ``Lean.Parser.Term.bracketedBinder) := #[]
      let mut args : Array Term := #[]
      let mut args' : Array Term := #[]
      for x in xs do
        let decl ← x.fvarId!.getDecl
        let nm := mkIdent decl.userName
        let ty ← PrettyPrinter.delab decl.type
        if x == n then
          binders := binders.push (← `(bracketedBinder| {$nm : $ty}))
          binders := binders.push (← `(bracketedBinder| {$m : ℕ}))
          binders := binders.push (← `(bracketedBinder| ($σ : Fin $nm → LeanProofs.ConciseIPRA.PTm $m)))
          continue
        let kind ← if decl.type.containsFVar n.fvarId! then classify n decl.type else pure Kind.other
        match decl.binderInfo with
        | .implicit => binders := binders.push (← `(bracketedBinder| {$nm : $ty}))
        | .instImplicit => binders := binders.push (← `(bracketedBinder| [$ty]))
        | .strictImplicit => binders := binders.push (← `(bracketedBinder| ⦃$nm : $ty⦄))
        | _ =>
          binders := binders.push (← `(bracketedBinder| ($nm : $ty)))
          args := args.push nm
          match kind with
          | .tm => args' := args'.push (← `((LeanProofs.ConciseIPRA.Syn.subst $σ $nm)))
          | .zt => args' := args'.push (← `(($nm).subst $σ))
          | .fm => args' := args'.push (← `(($nm).subst $σ))
          | .other => args' := args'.push nm
      let f := mkIdent c
      let lhs ← if resKind == .tm then `(LeanProofs.ConciseIPRA.Syn.subst $σ ($f $args*))
                else `(($f $args*).subst $σ)
      let rhs ← `($f $args'*)
      let first ← `(Lean.Parser.Tactic.simpLemma| $f:term)
      let lemmas : Array (TSyntax ``Lean.Parser.Tactic.simpLemma) :=
        #[first] ++ (match ext with | some ls => ls.getElems | none => #[])
      `(command| @[simp] theorem $thmName $binders* : $lhs = $rhs := by simp [$lemmas,*])
  elabCommand cmd
