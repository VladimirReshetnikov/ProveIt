import DiophantineConsistency.PRCode
import DiophantineConsistency.ScalarPRCode
import Lean.Elab.Term
import Lean.Meta.Tactic.Rewrite

/-!
# A narrow elaboration-time extractor for primitive recursive proofs

`prcode% h` accepts a proof of `Nat.Primrec' f` whose unfolded proof uses the
five constructors, `of_eq`, and closed finite composition arities. The
original equivalences stored in syntactic `propext` transports are also
recognized; arbitrary proposition equalities are never inverted. It
constructs an explicit `PRCode.Realizes f` using certified data constructors.
Unsupported proof heads cause elaboration to fail. This is an elaborator, not an object-language
elimination from `Prop` to `Type`, and adds no axioms.
-/

namespace DiophantineConsistency
namespace PRCode

open Lean Meta Elab Term

private def finLiteral (n i : ℕ) : TermElabM Lean.Expr := do
  let hi ← mkDecideProof (← mkLt (mkNatLit i) (mkNatLit n))
  mkAppM ``Fin.mk #[mkNatLit i, hi]

private def finFamily (motive : Lean.Expr) : List Lean.Expr → TermElabM Lean.Expr
  | [] => withLocalDeclD `i (mkApp (mkConst ``Fin) (mkNatLit 0)) fun i => do
      let impossible ← mkAppOptM ``Fin.elim0 #[some (mkApp motive i), some i]
      mkLambdaFVars #[i] impossible
  | head :: tail => do
      let n := mkNatLit tail.length
      let tailMotive ← withLocalDeclD `i (mkApp (mkConst ``Fin) n) fun i => do
        let successor ← mkAppM ``Fin.succ #[i]
        mkLambdaFVars #[i] (mkApp motive successor)
      let rest ← finFamily tailMotive tail
      mkAppOptM ``Fin.cases #[some n, some motive, some head, some rest]

private partial def unfoldOpaqueHead? (e : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  let args := e.getAppArgs
  match e.getAppFn with
  | .const name levels =>
    let info ← getConstInfo name
    if let .recInfo recursor := info then
      let index := recursor.getMajorIdx
      if index < args.size then
        let major ← withTransparency .all (whnf args[index]!)
        return (← unfoldOpaqueHead? major).map fun expanded =>
          mkAppN e.getAppFn (args.set! index expanded)
    return (info.value? (allowOpaque := true)).map fun value =>
      mkAppN (value.instantiateLevelParams info.levelParams levels) args
  | .proj structName index body =>
    let body ← withTransparency .all (whnf body)
    return (← unfoldOpaqueHead? body).map fun expanded =>
      mkAppN (.proj structName index expanded) args
  | _ => return none

/-- Recover only equivalences explicitly used to build a proposition equality.
This does not invert the axiom `propext`: the original equivalence is an
argument stored in the proof term. -/
private def propositionIff? (fuel : ℕ) (e : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    let e ← withTransparency .all (whnf e)
    let type ← whnf (← inferType e)
    unless type.isAppOfArity ``Eq 3 do return none
    unless ← isDefEq type.getAppArgs[0]! (mkSort .zero) do return none
    let args := e.getAppArgs
    match e.getAppFn.constName? with
    | some ``propext => return some args[2]!
    | some ``Eq.symm =>
      let some h ← propositionIff? fuel args.back! | return none
      return some (← mkAppM ``Iff.symm #[h])
    | some ``Eq.trans =>
      let some h ← propositionIff? fuel args[args.size - 2]! | return none
      let some k ← propositionIff? fuel args.back! | return none
      return some (← mkAppM ``Iff.trans #[h, k])
    | some ``Eq.refl =>
      return some (← mkAppOptM ``Iff.rfl #[some args[1]!])
    | _ =>
      match ← unfoldOpaqueHead? e with
      | some expanded => propositionIff? fuel expanded
      | none => return none

private def peelTransport? (proof : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  let args := proof.getAppArgs
  if proof.getAppFn.isConstOf ``Eq.rec || proof.getAppFn.isConstOf ``Eq.ndrec ||
      proof.getAppFn.isConstOf ``Eq.mp || proof.getAppFn.isConstOf ``Eq.mpr then
    -- Closed arity transports often carry an opaque proof of an equality
    -- whose sides reduce to the same natural. Replacing that proof by
    -- reflexivity is justified by definitional equality/proof irrelevance.
    for i in [:args.size] do
      let type ← whnf (← inferType args[i]!)
      if type.isAppOfArity ``Eq 3 then
        let eqArgs := type.getAppArgs
        if ← withTransparency .all (isDefEq eqArgs[1]! eqArgs[2]!) then
          let reflexivity ← mkEqRefl eqArgs[1]!
          return some (mkAppN proof.getAppFn (args.set! i reflexivity))
        if let some equivalence ← propositionIff? 200 args[i]! then
          let payload := args[3]!
          let payloadType ← inferType payload
          let resultType ← inferType proof
          if ← isDefEq payloadType eqArgs[1]! then
            let converted ← mkAppM ``Iff.mp #[equivalence, payload]
            if ← isDefEq (← inferType converted) resultType then
              return some converted
          if ← isDefEq payloadType eqArgs[2]! then
            let converted ← mkAppM ``Iff.mpr #[equivalence, payload]
            if ← isDefEq (← inferType converted) resultType then
              return some converted
  return none

private partial def exposeProof? (proof : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  let proof ← withTransparency .all (whnf proof)
  if let some converted ← peelTransport? proof then return some converted
  let args := proof.getAppArgs
  match proof.getAppFn with
  | .const name _ =>
    if let .recInfo recursor ← getConstInfo name then
      let index := recursor.getMajorIdx
      if index < args.size then
        if let some major ← exposeProof? args[index]! then
          return some (mkAppN proof.getAppFn (args.set! index major))
  | .proj structName index body =>
    if let some expanded ← exposeProof? body then
      return some (mkAppN (.proj structName index expanded) args)
  | _ => pure ()
  unfoldOpaqueHead? proof

private def nextProof? (proof : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  if let some next ← unfoldDefinition? proof (ignoreTransparency := true) then
    let next ← withTransparency .all (whnf next)
    if next != proof then return some next
  if let some next ← exposeProof? proof then
    let next ← withTransparency .all (whnf next)
    if next != proof then return some next
  if let some next ← unfoldOpaqueHead? proof then
    let next ← withTransparency .all (whnf next)
    if next != proof then return some next
  return none

/-- Prove only congruences generated by definitional equality, function
extensionality, and equality of subsingleton arguments. In particular this
handles different decidable instances without analyzing a proposition equality. -/
private def structuralEquality? (fuel : ℕ) (left right : Lean.Expr) :
    TermElabM (Option Lean.Expr) := do
  if ← withTransparency .all (isDefEq left right) then
    return some (← mkEqRefl left)
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    let leftType ← inferType left
    unless ← withTransparency .all (isDefEq leftType (← inferType right)) do return none
    try
      let subsingleton ← synthInstance (← mkAppM ``Subsingleton #[leftType])
      return some (← mkAppOptM ``Subsingleton.elim
        #[some leftType, some subsingleton, some left, some right])
    catch _ => pure ()
    match left, right with
    | .lam name domain body _, .lam _ domain' body' _ =>
      unless ← withTransparency .all (isDefEq domain domain') do return none
      withLocalDeclD name domain fun x => do
        let some equality ← structuralEquality? fuel (body.instantiate1 x) (body'.instantiate1 x)
          | return none
        let pointwise ← mkLambdaFVars #[x] equality
        return some (← mkAppM ``funext #[pointwise])
    | .app f a, .app g b =>
      let some hf ← structuralEquality? fuel f g | return none
      let some ha ← structuralEquality? fuel a b | return none
      try return some (← mkCongr hf ha) catch _ => return none
    | _, _ => return none

private def transportEndpoints? (predicate : Name) (arity : ℕ)
    (proof : Lean.Expr) : TermElabM (Option (Lean.Expr × Lean.Expr)) := do
  let head := proof.getAppFn
  unless head.isConstOf ``Eq.rec || head.isConstOf ``Eq.ndrec do return none
  let args := proof.getAppArgs
  unless args.size == 6 do return none
  let source ← withTransparency .all (whnf (← inferType args[3]!))
  let target ← withTransparency .all (whnf (← inferType proof))
  unless source.isAppOfArity predicate arity && target.isAppOfArity predicate arity do
    return none
  let f := source.getAppArgs.back!
  let g := target.getAppArgs.back!
  let some equality ← structuralEquality? 300 f g | return none
  let pointwise ← withLocalDeclD `n (← inferType f >>= fun t => do
      let t ← whnf t
      return t.bindingDomain!) fun n => do
    mkLambdaFVars #[n] (← mkCongrFun equality n)
  return some (args[3]!, pointwise)

private def realizerMotive? (predicate : Name) (arity : ℕ) (realizes : Name)
    (proof : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  let head := proof.getAppFn
  unless head.isConstOf ``Eq.rec || head.isConstOf ``Eq.ndrec do return none
  let args := proof.getAppArgs
  unless args.size == 6 do return none
  withLocalDeclD `index args[0]! fun index => do
    if head.isConstOf ``Eq.rec then
      withLocalDeclD `equality (← mkEq args[1]! index) fun equality => do
        let target ← whnf (mkAppN args[2]! #[index, equality])
        unless target.isAppOfArity predicate arity do return none
        let type ← mkAppM realizes #[target.getAppArgs.back!]
        return some (← mkLambdaFVars #[index, equality] type)
    else
      let target ← whnf (mkApp args[2]! index)
      unless target.isAppOfArity predicate arity do return none
      let type ← mkAppM realizes #[target.getAppArgs.back!]
      return some (← mkLambdaFVars #[index] type)

private def transportProgram (proof motive payload : Lean.Expr) : TermElabM Lean.Expr := do
  let args := proof.getAppArgs
  mkAppOptM proof.getAppFn.constName!
    #[some args[0]!, some args[1]!, some motive, some payload, some args[4]!, some args[5]!]

private def existentialPayload? (fuel : ℕ) (proof : Lean.Expr) :
    TermElabM (Option Lean.Expr) := do
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    let proof ← withTransparency .all (whnf proof)
    if proof.getAppFn.isConstOf ``Exists.intro then return some proof.getAppArgs.back!
    let some expanded ← nextProof? proof | throwError "existential unsupported: {proof}"
    existentialPayload? fuel expanded

/-- A syntactically supplied existential witness may replace a chosen
subsingleton witness only after the resulting functions have been proved equal.
There is no general extraction of arbitrary existential proofs. -/
private def chosenScalarPayload? (proof : Lean.Expr) :
    TermElabM (Option (Lean.Expr × Lean.Expr)) := do
  let mut existence : Option Lean.Expr := none
  let args := proof.getAppArgs
  if proof.getAppFn.isConstOf ``Exists.choose_spec ||
      proof.getAppFn.isConstOf ``Classical.choose_spec then
    existence := some args.back!
  else if let .proj _ 1 body := proof.getAppFn then
    if body.getAppFn.isConstOf ``Classical.indefiniteDescription then
      existence := some body.getAppArgs.back!
  let some existenceProof := existence | return none
  let some payload ← existentialPayload? 2000 existenceProof | throwError "chosen existential could not be expanded: {existenceProof}"
  let source ← withTransparency .all (whnf (← inferType payload))
  let target ← withTransparency .all (whnf (← inferType proof))
  unless source.isAppOfArity ``Nat.Primrec 1 && target.isAppOfArity ``Nat.Primrec 1 do
    return none
  let some equality ← structuralEquality? 300 source.getAppArgs[0]! target.getAppArgs[0]!
    | throwError "chosen existential function mismatch: {source} versus {target}"
  let pointwise ← withLocalDeclD `n (mkConst ``Nat) fun n => do
    mkLambdaFVars #[n] (← mkCongrFun equality n)
  return some (payload, pointwise)

private abbrev ExtractionCache := IO.Ref (Std.HashMap Lean.Expr (Option Lean.Expr))

private def extract (cache : ExtractionCache) (fuel : ℕ) (proof : Lean.Expr) :
    TermElabM Lean.Expr := do
  let proof ← instantiateMVars proof
  let proof ← withTransparency .all (whnf proof)
  if let some known := (← cache.get)[proof]? then
    match known with
    | some result => return result
    | none => throwError "prcode%: recursive proof expansion at {proof.getAppFn}"
  cache.modify (fun entries => entries.insert proof none)
  let result : Lean.Expr ← do
    match fuel with
    | 0 => throwError "prcode%: constructor expansion limit reached at {proof.getAppFn}"
    | fuel + 1 =>
      let proof ← withTransparency .all (whnf proof)
      let args := proof.getAppArgs
      match proof.getAppFn.constName? with
      | some ``Nat.Primrec'.zero => pure (mkConst ``Realizes.zero)
      | some ``Nat.Primrec'.succ => pure (mkConst ``Realizes.succ)
      | some ``Nat.Primrec'.get => mkAppM ``Realizes.get #[args[1]!]
      | some ``Nat.Primrec'.of_eq =>
        let original ← extract cache fuel args[3]!
        mkAppM ``Realizes.ofEq #[original, args[4]!]
      | some ``Nat.Primrec'.comp =>
        let outer ← extract cache fuel args[4]!
        let arity ← whnf args[1]!
        let some n ← getNatValue? arity
          | throwError "prcode%: composition arity is not a closed natural number: {arity}"
        let mut inner := []
        for i in [:n] do
          let index ← finLiteral n i
          inner := inner.concat (← extract cache fuel (mkApp args[5]! index))
        let motive ← withLocalDeclD `i (mkApp (mkConst ``Fin) args[1]!) fun i => do
          let target ← mkAppM ``PRCode.Realizes #[mkApp args[3]! i]
          mkLambdaFVars #[i] target
        let family ← finFamily motive inner
        mkAppM ``Realizes.comp #[outer, family]
      | some ``Nat.Primrec'.prec =>
        let base ← extract cache fuel args[3]!
        let step ← extract cache fuel args[4]!
        mkAppM ``Realizes.prec #[base, step]
      | _ =>
        if let some motive ← realizerMotive? ``Nat.Primrec' 2 ``PRCode.Realizes proof then
          let payload ← extract cache fuel args[3]!
          transportProgram proof motive payload
        else
          if let some expanded ← nextProof? proof then
            extract cache fuel expanded
          else
            throwError "prcode%: unsupported unfolded proof head {proof.getAppFn}"
  cache.modify (fun entries => entries.insert proof (some result))
  return result

/-- Extract only supported constructor proofs; the emitted specification is
checked by Lean's kernel along with the rest of the elaborated declaration. -/
elab "prcode% " proof:term : term => do
  let proof ← elabTerm proof none
  let type ← whnf (← inferType proof)
  unless type.isAppOfArity ``Nat.Primrec' 2 do
    throwError "prcode% expects a proof of Nat.Primrec', got {type}"
  let function := type.getAppArgs[1]!
  let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr (Option Lean.Expr))
  let result ← extract cache 10000 proof
  let wanted ← mkAppM ``PRCode.Realizes #[function]
  unless ← withTransparency .all (isDefEq (← inferType result) wanted) do
    throwError "prcode%: internal specification mismatch"
  return result

/-- Specifications use a canonical decision procedure only in `Prop`; the
program itself is always supplied explicitly. -/
private noncomputable def predicateFunction {α : Type} [Primcodable α]
    (p : α → Prop) : ℕ → ℕ := by
  classical
  exact fun n => Encodable.encode ((@Encodable.decode α _ n).map (fun a => decide (p a)))

@[reducible] private noncomputable def canonicalDecision {α : Type} (p : α → Prop) : DecidablePred p := by
  classical
  exact fun a => Classical.propDecidable (p a)

private def realizeSelf (c : ScalarPRCode) : ScalarPRCode.Realizes c.eval :=
  ⟨c, fun _ => rfl⟩

private theorem realizePrimrec {f : ℕ → ℕ} (c : ScalarPRCode.Realizes f) : Nat.Primrec f :=
  c.val.primrec.of_eq c.property

private def existentialPredicate? (proof : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  let type ← withTransparency .all (whnf (← inferType proof))
  unless type.isAppOfArity ``Exists 2 do return none
  let decisionType ← whnf type.getAppArgs[0]!
  unless decisionType.isForall do return none
  withLocalDeclD `a decisionType.bindingDomain! fun a => do
    let body ← whnf (decisionType.bindingBody!.instantiate1 a)
    unless body.isAppOfArity ``Decidable 1 do return none
    return some (← mkLambdaFVars #[a] body.getAppArgs[0]!)

private def storedEquality? (fuel : ℕ) (left right evidence : Lean.Expr) :
    TermElabM (Option Lean.Expr) := do
  if let some equality ← structuralEquality? 300 left right then return some equality
  match fuel with
  | 0 => return none
  | fuel + 1 =>
    unless evidence.hasLooseBVars do
      let type ← whnf (← inferType evidence)
      if type.isAppOfArity ``Eq 3 then
        for backwards in [false, true] do
          try
            let goal ← mkFreshExprMVar (← mkEq left right)
            let rewritten ← goal.mvarId!.rewrite left evidence backwards
            if rewritten.mvarIds.isEmpty &&
                (← withTransparency .all (isDefEq rewritten.eNew right)) then
              return some rewritten.eqProof
          catch _ => pure ()
    for argument in evidence.getAppArgs do
      if let some equality ← storedEquality? fuel left right argument then return some equality
    match evidence.getAppFn with
    | .proj _ _ body => storedEquality? fuel left right body
    | _ => return none

private def chosenExistence? (proof : Lean.Expr) : TermElabM (Option Lean.Expr) := do
  let args := proof.getAppArgs
  if proof.getAppFn.isConstOf ``Exists.choose_spec ||
      proof.getAppFn.isConstOf ``Classical.choose_spec then
    return some args.back!
  if let .proj _ 1 body := proof.getAppFn then
    if body.getAppFn.isConstOf ``Classical.indefiniteDescription then
      return some body.getAppArgs.back!
  return none

mutual
private partial def extractScalar (cache : ExtractionCache) (fuel : ℕ) (proof : Lean.Expr) :
    TermElabM Lean.Expr := do
  let proof ← instantiateMVars proof
  let proof ← withTransparency .all (whnf proof)
  if let some known := (← cache.get)[proof]? then
    match known with
    | some result => return result
    | none => throwError "scalar_prcode%: recursive proof expansion at {proof.getAppFn}"
  cache.modify (fun entries => entries.insert proof none)
  let result : Lean.Expr ← do
    match fuel with
    | 0 => throwError "scalar_prcode%: constructor expansion limit reached at {proof.getAppFn}"
    | fuel + 1 =>
      let args := proof.getAppArgs
      match proof.getAppFn.constName? with
      | some ``realizePrimrec => pure args.back!
      | some ``ScalarPRCode.primrec => mkAppM ``realizeSelf #[args.back!]
      | some ``Nat.Primrec.zero => pure (mkConst ``ScalarPRCode.Realizes.zero)
      | some ``Nat.Primrec.succ => pure (mkConst ``ScalarPRCode.Realizes.succ)
      | some ``Nat.Primrec.left => pure (mkConst ``ScalarPRCode.Realizes.left)
      | some ``Nat.Primrec.right => pure (mkConst ``ScalarPRCode.Realizes.right)
      | some ``Nat.Primrec.of_eq =>
        let original ← extractScalar cache fuel args[2]!
        mkAppM ``ScalarPRCode.Realizes.ofEq #[original, args[3]!]
      | some ``Nat.Primrec.pair =>
        let first ← extractScalar cache fuel args[2]!
        let second ← extractScalar cache fuel args[3]!
        mkAppM ``ScalarPRCode.Realizes.pair #[first, second]
      | some ``Nat.Primrec.comp =>
        let outer ← extractScalar cache fuel args[2]!
        let inner ← extractScalar cache fuel args[3]!
        mkAppM ``ScalarPRCode.Realizes.comp #[outer, inner]
      | some ``Nat.Primrec.prec =>
        let base ← extractScalar cache fuel args[2]!
        let step ← extractScalar cache fuel args[3]!
        mkAppM ``ScalarPRCode.Realizes.prec #[base, step]
      | _ =>
        if let some (source, equality) ← transportEndpoints? ``Nat.Primrec 1 proof then
          let payload ← extractScalar cache fuel source
          mkAppM ``ScalarPRCode.Realizes.ofEq #[payload, equality]
        else if let some motive ← realizerMotive? ``Nat.Primrec 1 ``ScalarPRCode.Realizes proof then
          let payload ← extractScalar cache fuel args[3]!
          transportProgram proof motive payload
        else if let some existence ← chosenExistence? proof then
          let payload ← extractPredicate cache fuel existence
          let target ← withTransparency .all (whnf (← inferType proof))
          let source ← inferType payload
          let some equality ← structuralEquality? 300 source.getAppArgs[0]! target.getAppArgs[0]!
            | throwError "scalar_prcode%: chosen predicate specification mismatch"
          let pointwise ← withLocalDeclD `n (mkConst ``Nat) fun n => do
            mkLambdaFVars #[n] (← mkCongrFun equality n)
          mkAppM ``ScalarPRCode.Realizes.ofEq #[payload, pointwise]
        else
          if let some expanded ← nextProof? proof then
            extractScalar cache fuel expanded
          else
            if proof.getAppFn.isConstOf ``Eq.rec then
              throwError "scalar_prcode%: unsupported Eq.rec ({args.size} arguments), \
                motive {args[2]!}; payload type {← inferType args[3]!}; equality {args[5]!} : {← inferType args[5]!}"
            else
              throwError "scalar_prcode%: unsupported unfolded proof head {proof.getAppFn}"
  cache.modify (fun entries => entries.insert proof (some result))
  return result

private partial def extractPredicate (cache : ExtractionCache) (fuel : ℕ)
    (proof : Lean.Expr) : TermElabM Lean.Expr := do
  match fuel with
  | 0 => throwError "scalar_prcode%: predicate expansion limit reached"
  | fuel + 1 =>
    let proof ← instantiateMVars proof
    let proof ← withTransparency .all (whnf proof)
    let some predicate ← existentialPredicate? proof
      | throwError "scalar_prcode%: unsupported predicate evidence type {← inferType proof}"
    let targetFunction ← mkAppM ``predicateFunction #[predicate]
    let args := proof.getAppArgs
    if proof.getAppFn.isConstOf ``Exists.intro then
      let payload ← extractScalar cache fuel args.back!
      let source ← inferType payload
      let some equality ← structuralEquality? 300 source.getAppArgs.back! targetFunction
        | throwError "scalar_prcode%: explicit predicate function mismatch"
      let pointwise ← withLocalDeclD `n (mkConst ``Nat) fun n => do
        mkLambdaFVars #[n] (← mkCongrFun equality n)
      mkAppM ``ScalarPRCode.Realizes.ofEq #[payload, pointwise]
    else if proof.getAppFn.isConstOf ``Eq.rec || proof.getAppFn.isConstOf ``Eq.ndrec then
      let payload ← extractPredicate cache fuel args[3]!
      let some sourcePredicate ← existentialPredicate? args[3]!
        | throwError "scalar_prcode%: transported predicate source mismatch"
      let some equality ← storedEquality? 200 sourcePredicate predicate args[5]!
        | throwError "scalar_prcode%: unsupported predicate transport {sourcePredicate} to {predicate}"
      let motive ← withLocalDeclD `p (← inferType predicate) fun p => do
        let function ← mkAppM ``predicateFunction #[p]
        mkLambdaFVars #[p] (← mkAppM ``ScalarPRCode.Realizes #[function])
      mkAppM ``Eq.mp #[(← mkCongrArg motive equality), payload]
    else if let .const name _ := proof.getAppFn then
      if let .recInfo recursor ← getConstInfo name then
        let majorIndex := recursor.getMajorIdx
        if majorIndex < args.size then
          if let some majorPredicate ← existentialPredicate? args[majorIndex]! then
            let majorProgram ← extractPredicate cache fuel args[majorIndex]!
            let witness ← mkAppM ``canonicalDecision #[majorPredicate]
            let specification ← mkAppM ``realizePrimrec #[majorProgram]
            let explicit ← mkAppM ``Exists.intro #[witness, specification]
            let expanded := mkAppN proof.getAppFn (args.set! majorIndex explicit)
            return ← extractPredicate cache fuel expanded
      if let some expanded ← nextProof? proof then
        extractPredicate cache fuel expanded
      else
        throwError "scalar_prcode%: unsupported predicate proof head {proof.getAppFn}"
    else if let some expanded ← nextProof? proof then
      extractPredicate cache fuel expanded
    else
      throwError "scalar_prcode%: unsupported predicate proof head {proof.getAppFn}"
end

/-- Extract scalar programs directly, keeping pairing/unpairing primitive. -/
elab "scalar_prcode% " proof:term : term => do
  let proof ← elabTerm proof none
  let type ← whnf (← inferType proof)
  unless type.isAppOfArity ``Nat.Primrec 1 do
    throwError "scalar_prcode% expects a proof of Nat.Primrec, got {type}"
  let function := type.getAppArgs[0]!
  let cache ← IO.mkRef ({} : Std.HashMap Lean.Expr (Option Lean.Expr))
  let result ← extractScalar cache 10000 proof
  let wanted ← mkAppM ``ScalarPRCode.Realizes #[function]
  unless ← withTransparency .all (isDefEq (← inferType result) wanted) do
    throwError "scalar_prcode%: internal specification mismatch"
  return result

end PRCode
end DiophantineConsistency
