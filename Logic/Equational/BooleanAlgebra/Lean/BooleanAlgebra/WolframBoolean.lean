import ShefferStroke.Sheffer
import BooleanAlgebra.WolframBooleanHuntingtonCertificates

/-!
# Wolfram's and Meredith's Sheffer-stroke axioms

This module formalizes a computationally checkable core of the classical
single-operator Boolean-logic story, over the shared stroke language of
`ShefferStroke.Sheffer` and the first-order terms of
`EquationalLogic.Checker`.

Lean already uses `↑` for coercions, so this file writes the stroke connective
as `⊙`.  On truth values the two Sheffer strokes are NAND and its dual NOR.

The file proves:

* Wolfram's single equation
  `((a ⊙ b) ⊙ c) ⊙ (a ⊙ ((a ⊙ c) ⊙ a)) = c`
  equationally derives the standard three Sheffer-stroke axioms for every
  carrier type with one binary operation, and therefore a standard Huntington
  Boolean-algebra basis for the derived operations.
* Meredith's two equations equationally derive Wolfram's single equation, and
  therefore also the same Boolean-algebra basis.
* On the two-element Boolean algebra, Wolfram's equation and Meredith's pair
  each have exactly the two Sheffer truth-table models, NAND and NOR.
* Both Sheffer truth tables express all ordinary classical connectives.
* Wolfram's equation has six occurrences of the primitive binary operation and
  characterizes the Sheffer truth tables on the two-element Boolean algebra.
  A finite Lean-checked countermodel certificate shows that every single
  equation with at most five primitive binary-operation occurrences that is
  true in those Boolean Sheffer tables is also true in some finite algebra
  where Wolfram's axiom fails.

The last point is the formalized finite-model obstruction behind the usual
"minimal number of operators" statement for single equations: any shorter
single-equation axiomatization of the one-binary-operation Boolean theory would
also hold in a finite non-Wolfram algebra.
-/

namespace LeanProofs

namespace WolframBoolean

open Sheffer

/-! ## Single-equation and few-equation axiom systems -/

/-- Wolfram's single axiom, for an arbitrary binary operation. -/
def WolframAxiom {α : Type u} (op : α → α → α) : Prop :=
  ∀ a b c, op (op (op a b) c) (op a (op (op a c) a)) = c

/-- Meredith's two-axiom Sheffer-stroke system. -/
def MeredithAxioms {α : Type u} (op : α → α → α) : Prop :=
  (∀ p q r, op p (op q (op p r)) = op (op (op r q) q) p) ∧
  (∀ p q, op (op p p) (op q p) = p)

/-- A standard three-equation basis for Sheffer-stroke Boolean algebras. -/
def ShefferAxioms {α : Type u} (op : α → α → α) : Prop :=
  (∀ a, op (op a a) (op a a) = a) ∧
  (∀ a b, op a (op b (op b b)) = op a a) ∧
  (∀ a b c,
    op (op a (op b c)) (op a (op b c)) =
      op (op (op b b) a) (op (op c c) a))

/-- Complement derived from a Sheffer stroke: `¬ a = a ⊙ a`. -/
def strokeCompl {α : Type u} (op : α → α → α) (a : α) : α :=
  op a a

/-- Join derived from a Sheffer stroke: `a ∨ b = ¬a ⊙ ¬b`. -/
def strokeJoin {α : Type u} (op : α → α → α) (a b : α) : α :=
  op (strokeCompl op a) (strokeCompl op b)

/--
Huntington's three-equation Boolean-algebra basis, in the language of join and
complement.
-/
def HuntingtonAxioms {α : Type u} (sup : α → α → α) (compl : α → α) : Prop :=
  (∀ a b, sup a b = sup b a) ∧
  (∀ a b c, sup a (sup b c) = sup (sup a b) c) ∧
  (∀ a b,
    sup (compl (sup (compl a) b))
      (compl (sup (compl a) (compl b))) = a)

/-- The two Boolean Sheffer truth tables, allowing the order-dual convention. -/
def IsBooleanSheffer (op : Bool → Bool → Bool) : Prop :=
  op = boolNand ∨ op = boolNor

/-! ## Equational certificates over arbitrary carriers -/

/-- Environment sending equation variables `0`, `1`, `2` to `a`, `b`, `c`. -/
def env3 {α : Type u} (a b c : α) : Nat → α
  | 0 => a
  | 1 => b
  | 2 => c
  | _ => a

/--
Wolfram's single equation derives the standard three Sheffer-stroke axioms in
pure equational logic, for any carrier type with one binary operation.

The proof is checked by `BooleanAlgebra.WolframBooleanCertificates`, a small
first-order equational checker applied to a certificate extracted from
Wolfram Language's `FindEquationalProof`.
-/
theorem wolfram_derives_sheffer_axioms {α : Type u} (op : α → α → α)
    (h : WolframAxiom op) : ShefferAxioms op := by
  have hW :
      EquationalLogic.Equation.Valid op WolframBooleanCertificates.wolframEquation :=
    fun env => h (env 0) (env 1) (env 2)
  rcases WolframBooleanCertificates.wolframToSheffer_valid op hW with ⟨h1, h2, h3⟩
  exact ⟨fun a => h1 (env3 a a a), fun a b => h2 (env3 a b a),
    fun a b c => h3 (env3 a b c)⟩

/-- Meredith's two axioms derive Wolfram's single axiom in pure equational logic. -/
theorem meredith_derives_wolfram_axiom {α : Type u} (op : α → α → α)
    (h : MeredithAxioms op) : WolframAxiom op := by
  have hM1 :
      EquationalLogic.Equation.Valid op WolframBooleanCertificates.meredithEquation1 :=
    fun env => h.1 (env 0) (env 1) (env 2)
  have hM2 :
      EquationalLogic.Equation.Valid op WolframBooleanCertificates.meredithEquation2 :=
    fun env => h.2 (env 0) (env 1)
  have hW := WolframBooleanCertificates.meredithToWolfram_valid op hM1 hM2
  exact fun a b c => hW (env3 a b c)

/-- Meredith's two axioms are complete for the same Sheffer-stroke basis. -/
theorem meredith_derives_sheffer_axioms {α : Type u} (op : α → α → α)
    (h : MeredithAxioms op) : ShefferAxioms op :=
  wolfram_derives_sheffer_axioms op (meredith_derives_wolfram_axiom op h)

open WolframBooleanHuntingtonCertificates in
/--
The standard Sheffer axioms derive Huntington's equational basis for Boolean
algebra under the usual definitions `¬a = a ⊙ a` and
`a ∨ b = ¬a ⊙ ¬b`.
-/
theorem sheffer_derives_huntington_axioms {α : Type u} (op : α → α → α)
    (h : ShefferAxioms op) : HuntingtonAxioms (strokeJoin op) (strokeCompl op) := by
  have hS1 : EquationalLogic.Equation.Valid op
      WolframBooleanCertificates.shefferEquation1 :=
    fun env => h.1 (env 0)
  have hS2 : EquationalLogic.Equation.Valid op
      WolframBooleanCertificates.shefferEquation2 :=
    fun env => h.2.1 (env 0) (env 1)
  have hS3 : EquationalLogic.Equation.Valid op
      WolframBooleanCertificates.shefferEquation3 :=
    fun env => h.2.2 (env 0) (env 1) (env 2)
  rcases shefferToHuntington_valid op hS1 hS2 hS3 with ⟨hComm, hAssoc, hHunt⟩
  refine ⟨fun a b => ?_, fun a b c => ?_, fun a b => ?_⟩
  · simpa [strokeJoin, strokeCompl, hJoin, hCompl, huntingtonEquation1,
      C.e, C.o, C.v, env3, EquationalLogic.Term.eval] using hComm (env3 a b a)
  · simpa [strokeJoin, strokeCompl, hJoin, hCompl, huntingtonEquation2,
      C.e, C.o, C.v, env3, EquationalLogic.Term.eval] using hAssoc (env3 a b c)
  · simpa [strokeJoin, strokeCompl, hJoin, hCompl, huntingtonEquation3,
      C.e, C.o, C.v, env3, EquationalLogic.Term.eval] using hHunt (env3 a b a)

/-- Wolfram's single axiom derives Huntington's Boolean-algebra basis. -/
theorem wolfram_derives_huntington_axioms {α : Type u} (op : α → α → α)
    (h : WolframAxiom op) : HuntingtonAxioms (strokeJoin op) (strokeCompl op) :=
  sheffer_derives_huntington_axioms op (wolfram_derives_sheffer_axioms op h)

/-- Meredith's two axioms derive Huntington's Boolean-algebra basis. -/
theorem meredith_derives_huntington_axioms {α : Type u} (op : α → α → α)
    (h : MeredithAxioms op) : HuntingtonAxioms (strokeJoin op) (strokeCompl op) :=
  sheffer_derives_huntington_axioms op (meredith_derives_sheffer_axioms op h)

theorem boolNand_wolfram : WolframAxiom boolNand := by
  intro a b c
  cases a <;> cases b <;> cases c <;> rfl

theorem boolNor_wolfram : WolframAxiom boolNor := by
  intro a b c
  cases a <;> cases b <;> cases c <;> rfl

theorem boolNand_sheffer : ShefferAxioms boolNand :=
  wolfram_derives_sheffer_axioms boolNand boolNand_wolfram

theorem boolNor_sheffer : ShefferAxioms boolNor :=
  wolfram_derives_sheffer_axioms boolNor boolNor_wolfram

theorem boolNand_meredith : MeredithAxioms boolNand := by
  constructor
  · intro p q r
    cases p <;> cases q <;> cases r <;> rfl
  · intro p q
    cases p <;> cases q <;> rfl

theorem boolNor_meredith : MeredithAxioms boolNor := by
  constructor
  · intro p q r
    cases p <;> cases q <;> cases r <;> rfl
  · intro p q
    cases p <;> cases q <;> rfl

/--
On the two-element algebra, Wolfram's equation has exactly the two Sheffer
truth-table models: NAND and NOR.
-/
theorem wolfram_characterizes_sheffer_on_bool
    (op : Bool → Bool → Bool) (h : WolframAxiom op) : IsBooleanSheffer op := by
  cases hff : op false false <;> cases hft : op false true <;>
    cases htf : op true false <;> cases htt : op true true <;>
    simp [WolframAxiom, hff, hft, htf, htt] at h
  · right
    funext a b
    cases a <;> cases b <;> simp [boolNor, hff, hft, htf, htt]
  · left
    funext a b
    cases a <;> cases b <;> simp [boolNand, hff, hft, htf, htt]

/--
On the two-element algebra, Meredith's two equations have exactly the same two
Sheffer truth-table models: NAND and NOR.  This is immediate from the
equational derivation of Wolfram's axiom, so no second truth-table search is
needed.
-/
theorem meredith_characterizes_sheffer_on_bool
    (op : Bool → Bool → Bool) (h : MeredithAxioms op) : IsBooleanSheffer op :=
  wolfram_characterizes_sheffer_on_bool op (meredith_derives_wolfram_axiom op h)

/-! ## Functional completeness for ordinary connectives -/

open Sheffer.ClassicalFormula in
/--
Either Boolean Sheffer operation expresses every ordinary classical connective,
via the shared Sheffer-stroke translations: the translation is `toNand` or
`toNor` according to which operation `op` agrees with.  Functional completeness
depends on the operation only through this, so each axiom system below reduces
to it through its own characterization theorem.
-/
theorem sheffer_functionally_complete
    (op : Bool → Bool → Bool) (h : IsBooleanSheffer op) (p : ClassicalFormula α) :
    ∃ q : StrokeFormula α, ∀ v : α → Bool, q.evalWith op v = eval v p := by
  rcases h with hop | hop
  · exact ⟨toNand p, fun v => by simp [hop, eval_toNand]⟩
  · exact ⟨toNor p, fun v => by simp [hop, eval_toNor]⟩

open Sheffer.ClassicalFormula in
/--
Any Boolean binary operation satisfying Wolfram's axiom expresses every ordinary
classical connective, via the shared Sheffer-stroke translations.
-/
theorem wolfram_functionally_complete
    (op : Bool → Bool → Bool) (h : WolframAxiom op) (p : ClassicalFormula α) :
    ∃ q : StrokeFormula α, ∀ v : α → Bool, q.evalWith op v = eval v p :=
  sheffer_functionally_complete op (wolfram_characterizes_sheffer_on_bool op h) p

open Sheffer.ClassicalFormula in
/--
Any Boolean binary operation satisfying Meredith's two axioms expresses every
ordinary classical connective, via the shared Sheffer-stroke translations.
-/
theorem meredith_functionally_complete
    (op : Bool → Bool → Bool) (h : MeredithAxioms op) (p : ClassicalFormula α) :
    ∃ q : StrokeFormula α, ∀ v : α → Bool, q.evalWith op v = eval v p :=
  sheffer_functionally_complete op (meredith_characterizes_sheffer_on_bool op h) p

/-! ## Certified finite search for the six-operator lower bound

The finite search reuses the first-order terms of
`EquationalLogic.Checker` rather than a private copy of the same syntax.
-/

open EquationalLogic (Term)

/--
A binary Boolean operation represented by its truth table in the order
`00, 01, 10, 11`.
-/
structure BinOp where
  ff : Bool
  ft : Bool
  tf : Bool
  tt : Bool
  deriving DecidableEq, Repr

namespace BinOp

/-- Evaluate a tabulated binary Boolean operation. -/
def apply (op : BinOp) : Bool → Bool → Bool
  | false, false => op.ff
  | false, true => op.ft
  | true, false => op.tf
  | true, true => op.tt

end BinOp

def nandTable : BinOp := { ff := true, ft := true, tf := true, tt := false }

def norTable : BinOp := { ff := true, ft := false, tf := false, tt := false }

def bools : List Bool := [false, true]

/-- All sixteen binary Boolean truth tables. -/
def allBinOps : List BinOp :=
  List.flatMap (fun ff =>
  List.flatMap (fun ft =>
  List.flatMap (fun tf =>
  List.map (fun tt => { ff, ft, tf, tt }) bools) bools) bools) bools

/-- Number of binary-operation occurrences in a term. -/
def nodeCount : Term → Nat
  | .var _ => 0
  | .op l r => nodeCount l + nodeCount r + 1

/-- One more than the largest variable index occurring in a term. -/
def varBound : Term → Nat
  | .var i => i + 1
  | .op l r => max (varBound l) (varBound r)

/-- Interpret a term in a tabulated two-element algebra. -/
def evalTable (op : BinOp) (env : List Bool) : Term → Bool
  | .var i => env.getD i false
  | .op l r => op.apply (evalTable op env l) (evalTable op env r)

/-- All Boolean environments of a fixed length. -/
def allEnvs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => List.flatMap (fun env => [false :: env, true :: env]) (allEnvs n)

/--
Canonical terms with a fixed number of binary nodes.

Variables are introduced in order of first occurrence.  At any leaf we may
reuse one of the previously introduced variables or introduce the next fresh
one.  The second component is the next fresh variable after the term.
-/
def canonicalTermsAux : Nat → Nat → Nat → List (Term × Nat)
  | _, 0, next =>
      (List.range (next + 1)).map fun i =>
        (Term.var i, if i == next then next + 1 else next)
  | 0, _ + 1, _ => []
  | fuel + 1, nodes + 1, next =>
      List.flatMap (fun leftNodes =>
        let rightNodes := nodes - leftNodes
        List.flatMap (fun left =>
          (canonicalTermsAux fuel rightNodes left.2).map fun right =>
            (Term.op left.1 right.1, right.2))
          (canonicalTermsAux fuel leftNodes next))
        (List.range (nodes + 1))

/-- All canonical equations whose two sides contain at most `maxNodes` nodes in total.

Variables are introduced from left to right across the whole equation, first
through the left-hand side and then through the right-hand side.  This is the
canonical representative scheme used by the finite lower-bound search.
-/
def equationsUpTo (maxNodes : Nat) : List (Term × Term) :=
  List.flatMap (fun leftNodes =>
    List.flatMap (fun rightNodes =>
      List.flatMap (fun lhs =>
        (canonicalTermsAux rightNodes rightNodes lhs.2).map fun rhs => (lhs.1, rhs.1))
        (canonicalTermsAux leftNodes leftNodes 0))
      (List.range (maxNodes + 1 - leftNodes)))
    (List.range (maxNodes + 1))

/-- Whether an equation holds in the two-element algebra represented by `op`. -/
def equationHolds (op : BinOp) (lhs rhs : Term) : Bool :=
  (allEnvs 7).all fun env => evalTable op env lhs == evalTable op env rhs

/-- The list of two-element truth-table models of an equation. -/
def equationModels (lhs rhs : Term) : List BinOp :=
  allBinOps.filter fun op => equationHolds op lhs rhs

def validInBooleanShefferTables (lhs rhs : Term) : Bool :=
  equationHolds nandTable lhs rhs && equationHolds norTable lhs rhs

def hasExactlyModels (models : List BinOp) (lhs rhs : Term) : Bool :=
  equationModels lhs rhs == models

def characterizesShefferTables (lhs rhs : Term) : Bool :=
  hasExactlyModels [norTable, nandTable] lhs rhs

/-- Wolfram's six-node left-hand side as a first-order term. -/
def wolframLhs : Term :=
  let a := Term.var 0
  let b := Term.var 1
  let c := Term.var 2
  Term.op
    (Term.op (Term.op a b) c)
    (Term.op a (Term.op (Term.op a c) a))

/-- Wolfram's right-hand side as a first-order term. -/
def wolframRhs : Term := Term.var 2

theorem wolfram_operator_count : nodeCount wolframLhs + nodeCount wolframRhs = 6 := by
  decide

theorem wolfram_equation_characterizes_sheffer_tables :
    characterizesShefferTables wolframLhs wolframRhs = true := by
  native_decide

/-! ## Finite countermodel certificate for the five-operator lower bound -/

/-- A finite one-operation algebra, represented by a flattened multiplication table. -/
structure FiniteOp where
  size : Nat
  table : List Nat
  deriving DecidableEq, Repr

namespace FiniteOp

def apply (op : FiniteOp) (x y : Nat) : Nat :=
  if op.size = 0 then
    0
  else
    (op.table.getD (x * op.size + y) 0) % op.size

end FiniteOp

/-- All environments of a fixed length over `{0, ..., size - 1}`. -/
def allFiniteEnvs (size : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 =>
      List.flatMap (fun env => (List.range size).map fun x => x :: env)
        (allFiniteEnvs size n)

/-- Interpret a term in a tabulated finite one-operation algebra. -/
def evalFinite (op : FiniteOp) (env : List Nat) : Term → Nat
  | .var i => env.getD i 0
  | .op l r => op.apply (evalFinite op env l) (evalFinite op env r)

def finiteEquationHolds (op : FiniteOp) (lhs rhs : Term) : Bool :=
  (allFiniteEnvs op.size (max (varBound lhs) (varBound rhs))).all fun env =>
    evalFinite op env lhs == evalFinite op env rhs

def finiteWolframHolds (op : FiniteOp) : Bool :=
  (allFiniteEnvs op.size 3).all fun env =>
    let a := env.getD 0 0
    let b := env.getD 1 0
    let c := env.getD 2 0
    let lhs := op.apply (op.apply (op.apply a b) c)
      (op.apply a (op.apply (op.apply a c) a))
    lhs == c

/--
A pool of finite non-Wolfram algebras used by the lower-bound certificate.
The tables were found by finite-model search and are rechecked by Lean.
-/
def shortCountermodelPool : List FiniteOp := [
  { size := 2, table := [0, 0, 0, 0] },
  { size := 2, table := [0, 0, 0, 1] },
  { size := 2, table := [0, 0, 1, 1] },
  { size := 2, table := [0, 1, 0, 1] },
  { size := 2, table := [0, 1, 1, 0] },
  { size := 3, table := [0, 2, 1, 2, 2, 0, 1, 0, 1] },
  { size := 4, table := [0, 3, 3, 0, 2, 1, 1, 2, 0, 3, 3, 0, 2, 1, 1, 2] },
  { size := 4, table := [0, 2, 0, 2, 0, 2, 0, 2, 1, 3, 1, 3, 1, 3, 1, 3] },
  { size := 2, table := [0, 0, 1, 0] },
  { size := 4, table := [0, 3, 3, 0, 0, 3, 3, 0, 1, 2, 2, 1, 1, 2, 2, 1] },
  { size := 3, table := [0, 0, 1, 2, 2, 1, 0, 0, 1] },
  { size := 3, table := [0, 0, 1, 2, 0, 2, 0, 0, 2] },
  { size := 3, table := [0, 0, 1, 2, 0, 2, 2, 0, 2] },
  { size := 4, table := [1, 2, 2, 1, 3, 0, 0, 3, 1, 2, 2, 1, 3, 0, 0, 3] },
  { size := 3, table := [0, 1, 2, 2, 0, 1, 1, 2, 0] },
  { size := 3, table := [0, 0, 1, 0, 2, 1, 1, 1, 1] },
  { size := 4, table := [0, 2, 0, 2, 3, 1, 3, 1, 3, 1, 3, 1, 0, 2, 0, 2] },
  { size := 4, table := [1, 3, 1, 3, 2, 0, 2, 0, 2, 0, 2, 0, 1, 3, 1, 3] },
  { size := 3, table := [0, 2, 1, 1, 0, 2, 2, 1, 0] },
  { size := 3, table := [0, 0, 1, 2, 2, 2, 0, 0, 1] },
  { size := 3, table := [0, 0, 1, 2, 2, 0, 1, 0, 1] },
  { size := 4, table := [0, 0, 1, 1, 3, 3, 2, 2, 3, 3, 2, 2, 0, 0, 1, 1] },
  { size := 3, table := [0, 0, 1, 2, 1, 1, 2, 0, 2] },
  { size := 4, table := [3, 1, 3, 1, 3, 1, 3, 1, 2, 0, 2, 0, 2, 0, 2, 0] },
  { size := 3, table := [0, 0, 1, 2, 1, 1, 0, 0, 0] },
  { size := 3, table := [0, 0, 1, 2, 2, 2, 0, 0, 2] },
  { size := 4, table := [2, 1, 1, 2, 2, 1, 1, 2, 3, 0, 0, 3, 3, 0, 0, 3] },
  { size := 4, table := [3, 3, 2, 2, 1, 1, 0, 0, 3, 3, 2, 2, 1, 1, 0, 0] },
  { size := 4, table := [0, 0, 1, 1, 2, 2, 3, 3, 0, 0, 1, 1, 2, 2, 3, 3] },
  { size := 4, table := [2, 2, 3, 3, 1, 1, 0, 0, 1, 1, 0, 0, 2, 2, 3, 3] }
]

def hasFiniteNonWolframCountermodel (lhs rhs : Term) : Bool :=
  shortCountermodelPool.any fun op =>
    finiteEquationHolds op lhs rhs && !finiteWolframHolds op

/--
Every equation with at most five operation occurrences that is true in the two
Boolean Sheffer tables is true in one of the finite algebras above while
Wolfram's axiom is false there.
-/
def shortEquationCountermodelCheck : Bool :=
  (equationsUpTo 5).all fun e =>
    !validInBooleanShefferTables e.1 e.2 ||
      hasFiniteNonWolframCountermodel e.1 e.2

theorem every_short_boolean_sheffer_equation_has_finite_nonwolfram_countermodel :
    shortEquationCountermodelCheck = true := by
  native_decide

/--
Entry-point theorem for the finite lower-bound result: Wolfram's equation has
six primitive binary-operation occurrences, it characterizes the Sheffer truth
tables on the two-element Boolean algebra, and every shorter equation that is
even true of those Boolean Sheffer tables has a finite non-Wolfram model.
-/
theorem wolfram_six_operations_is_minimal_for_single_equational_axioms :
    nodeCount wolframLhs + nodeCount wolframRhs = 6 ∧
      characterizesShefferTables wolframLhs wolframRhs = true ∧
      shortEquationCountermodelCheck = true := by
  exact ⟨wolfram_operator_count, wolfram_equation_characterizes_sheffer_tables,
    every_short_boolean_sheffer_equation_has_finite_nonwolfram_countermodel⟩

end WolframBoolean

end LeanProofs
