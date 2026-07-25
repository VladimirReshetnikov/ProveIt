(*
  Coq port of the Lean module BooleanAlgebra.WolframBoolean.

  The generated equational certificates live in
  WolframBooleanCertificates.v and WolframBooleanHuntingtonCertificates.v.
  This file exposes their algebraic consequences, the two-valued Boolean
  functional-completeness layer (over the shared stroke language of
  Sheffer.v), and the certified finite search behind the six-operator
  lower bound, including the Lean pair's finite countermodel certificate
  `shortEquationCountermodelCheck = true`.
*)

From Stdlib Require Import Bool.Bool.
From Stdlib Require Import Arith.PeanoNat.
From Stdlib Require Import Lists.List.
From ShefferStroke Require Import Sheffer.
From EquationalLogic Require Import Checker.
From BooleanAlgebra Require Import
  WolframBooleanCertificates
  WolframBooleanHuntingtonCertificates.

Import ListNotations.
Set Implicit Arguments.
Import LeanProofs.EquationalLogic.

Module LeanProofs.
Module WolframBoolean.

Module WBC :=
  BooleanAlgebra.WolframBooleanCertificates.LeanProofs.WolframBooleanCertificates.
Module WBH :=
  BooleanAlgebra.WolframBooleanHuntingtonCertificates.LeanProofs.WolframBooleanHuntingtonCertificates.
Module Sheffer := ShefferStroke.Sheffer.LeanProofs.Sheffer.
Import Sheffer.

(* ------------------------------------------------------------------ *)
(* Single-equation and few-equation axiom systems                      *)
(* ------------------------------------------------------------------ *)

Definition WolframAxiom {A : Type} (op : A -> A -> A) : Prop :=
  forall a b c, op (op (op a b) c) (op a (op (op a c) a)) = c.

Definition MeredithAxioms {A : Type} (op : A -> A -> A) : Prop :=
  (forall p q r, op p (op q (op p r)) = op (op (op r q) q) p) /\
  (forall p q, op (op p p) (op q p) = p).

Definition ShefferAxioms {A : Type} (op : A -> A -> A) : Prop :=
  (forall a, op (op a a) (op a a) = a) /\
  (forall a b, op a (op b (op b b)) = op a a) /\
  (forall a b c,
    op (op a (op b c)) (op a (op b c)) =
      op (op (op b b) a) (op (op c c) a)).

Definition strokeCompl {A : Type} (op : A -> A -> A) (a : A) : A :=
  op a a.

Definition strokeJoin {A : Type} (op : A -> A -> A) (a b : A) : A :=
  op (strokeCompl op a) (strokeCompl op b).

Definition HuntingtonAxioms {A : Type}
    (sup : A -> A -> A) (compl : A -> A) : Prop :=
  (forall a b, sup a b = sup b a) /\
  (forall a b c, sup a (sup b c) = sup (sup a b) c) /\
  (forall a b,
    sup (compl (sup (compl a) b))
      (compl (sup (compl a) (compl b))) = a).

Definition SameBoolOp (op op' : bool -> bool -> bool) : Prop :=
  forall a b, op a b = op' a b.

Definition IsBooleanSheffer (op : bool -> bool -> bool) : Prop :=
  SameBoolOp op boolNand \/ SameBoolOp op boolNor.

(* ------------------------------------------------------------------ *)
(* Equational certificates over arbitrary carriers                     *)
(* ------------------------------------------------------------------ *)

Theorem wolfram_derives_sheffer_axioms {A : Type} (op : A -> A -> A)
    (h : WolframAxiom op) : ShefferAxioms op.
Proof.
  assert (hW : Equation.Valid op WBC.wolframEquation).
  { intro env. exact (h (env 0) (env 1) (env 2)). }
  destruct (@WBC.wolframToSheffer_valid A op hW) as [h1 [h2 h3]].
  split.
  - intro a. exact (h1 (fun _ => a)).
  - split.
    + intros a b.
      exact (h2 (fun n => match n with 0 => a | 1 => b | _ => a end)).
    + intros a b c.
      exact (h3 (fun n => match n with 0 => a | 1 => b | 2 => c | _ => a end)).
Qed.

Theorem meredith_derives_wolfram_axiom {A : Type} (op : A -> A -> A)
    (h : MeredithAxioms op) : WolframAxiom op.
Proof.
  assert (hM1 : Equation.Valid op WBC.meredithEquation1).
  { intro env. exact (proj1 h (env 0) (env 1) (env 2)). }
  assert (hM2 : Equation.Valid op WBC.meredithEquation2).
  { intro env. exact (proj2 h (env 0) (env 1)). }
  pose proof (@WBC.meredithToWolfram_valid A op hM1 hM2) as hW.
  intros a b c.
  exact (hW (fun n => match n with 0 => a | 1 => b | 2 => c | _ => a end)).
Qed.

Theorem meredith_derives_sheffer_axioms {A : Type} (op : A -> A -> A)
    (h : MeredithAxioms op) : ShefferAxioms op.
Proof.
  exact (@wolfram_derives_sheffer_axioms A op
    (@meredith_derives_wolfram_axiom A op h)).
Qed.

Theorem sheffer_derives_huntington_axioms {A : Type} (op : A -> A -> A)
    (h : ShefferAxioms op) : HuntingtonAxioms (strokeJoin op) (strokeCompl op).
Proof.
  destruct h as [hS1 [hS2 hS3]].
  assert (h1 : Equation.Valid op WBC.shefferEquation1).
  { intro env. exact (hS1 (env 0)). }
  assert (h2 : Equation.Valid op WBC.shefferEquation2).
  { intro env. exact (hS2 (env 0) (env 1)). }
  assert (h3 : Equation.Valid op WBC.shefferEquation3).
  { intro env. exact (hS3 (env 0) (env 1) (env 2)). }
  destruct (@WBH.shefferToHuntington_valid A op h1 h2 h3)
    as [hComm [hAssoc hHunt]].
  unfold HuntingtonAxioms, strokeJoin, strokeCompl.
  split.
  - intros a b.
    exact (hComm (fun n => match n with 0 => a | 1 => b | _ => a end)).
  - split.
    + intros a b c.
      exact (hAssoc (fun n => match n with 0 => a | 1 => b | 2 => c | _ => a end)).
    + intros a b.
      exact (hHunt (fun n => match n with 0 => a | 1 => b | _ => a end)).
Qed.

Theorem wolfram_derives_huntington_axioms {A : Type} (op : A -> A -> A)
    (h : WolframAxiom op) : HuntingtonAxioms (strokeJoin op) (strokeCompl op).
Proof.
  exact (@sheffer_derives_huntington_axioms A op
    (@wolfram_derives_sheffer_axioms A op h)).
Qed.

Theorem meredith_derives_huntington_axioms {A : Type} (op : A -> A -> A)
    (h : MeredithAxioms op) : HuntingtonAxioms (strokeJoin op) (strokeCompl op).
Proof.
  exact (@sheffer_derives_huntington_axioms A op
    (@meredith_derives_sheffer_axioms A op h)).
Qed.

Theorem boolNand_wolfram : WolframAxiom boolNand.
Proof.
  intros [] [] []; reflexivity.
Qed.

Theorem boolNor_wolfram : WolframAxiom boolNor.
Proof.
  intros [] [] []; reflexivity.
Qed.

Theorem boolNand_sheffer : ShefferAxioms boolNand.
Proof.
  exact (@wolfram_derives_sheffer_axioms bool boolNand boolNand_wolfram).
Qed.

Theorem boolNor_sheffer : ShefferAxioms boolNor.
Proof.
  exact (@wolfram_derives_sheffer_axioms bool boolNor boolNor_wolfram).
Qed.

Theorem boolNand_meredith : MeredithAxioms boolNand.
Proof.
  split.
  - intros [] [] []; reflexivity.
  - intros [] []; reflexivity.
Qed.

Theorem boolNor_meredith : MeredithAxioms boolNor.
Proof.
  split.
  - intros [] [] []; reflexivity.
  - intros [] []; reflexivity.
Qed.

Ltac prove_same_bool_op :=
  intros [] [];
  unfold boolNand, boolNor;
  cbn;
  repeat match goal with
  | H : ?op false false = _ |- context[?op false false] => rewrite H
  | H : ?op false true = _ |- context[?op false true] => rewrite H
  | H : ?op true false = _ |- context[?op true false] => rewrite H
  | H : ?op true true = _ |- context[?op true true] => rewrite H
  end;
  reflexivity.

Definition wolframHoldsBool (op : bool -> bool -> bool) : bool :=
  let row a b c :=
    Bool.eqb (op (op (op a b) c) (op a (op (op a c) a))) c in
  row false false false &&
  row false false true &&
  row false true false &&
  row false true true &&
  row true false false &&
  row true false true &&
  row true true false &&
  row true true true.

Lemma wolframAxiom_to_bool (op : bool -> bool -> bool)
    (h : WolframAxiom op) : wolframHoldsBool op = true.
Proof.
  unfold wolframHoldsBool.
  repeat rewrite h.
  repeat rewrite Bool.eqb_reflx.
  reflexivity.
Qed.

(* Once an axiom system has been reduced to the boolean fact that its truth
   table evaluates to [true], identifying the operation is the same finite
   case analysis for every such system: split on the four entries of [op],
   propagate those equations into the table, and read off which of the two
   Sheffer operations [op] agrees with.  Only the table being unfolded
   differs, so the caller unfolds it and this tactic does the rest. *)
Ltac characterize_sheffer_from_table op htable :=
  destruct (op false false) eqn:?;
  destruct (op false true) eqn:?;
  destruct (op true false) eqn:?;
  destruct (op true true) eqn:?;
  cbn in htable;
  repeat match goal with
  | H : op _ _ = _ |- _ => rewrite H in htable
  end;
  cbn in htable;
  try (left; prove_same_bool_op);
  try (right; prove_same_bool_op);
  discriminate.

Theorem wolfram_characterizes_sheffer_on_bool
    (op : bool -> bool -> bool) (h : WolframAxiom op) : IsBooleanSheffer op.
Proof.
  pose proof (@wolframAxiom_to_bool op h) as htable.
  unfold wolframHoldsBool in htable.
  characterize_sheffer_from_table op htable.
Qed.

Definition meredithHoldsBool (op : bool -> bool -> bool) : bool :=
  let row1 p q r :=
    Bool.eqb (op p (op q (op p r))) (op (op (op r q) q) p) in
  let row2 p q :=
    Bool.eqb (op (op p p) (op q p)) p in
  row1 false false false &&
  row1 false false true &&
  row1 false true false &&
  row1 false true true &&
  row1 true false false &&
  row1 true false true &&
  row1 true true false &&
  row1 true true true &&
  row2 false false &&
  row2 false true &&
  row2 true false &&
  row2 true true.

Lemma meredithAxioms_to_bool (op : bool -> bool -> bool)
    (h : MeredithAxioms op) : meredithHoldsBool op = true.
Proof.
  destruct h as [h1 h2].
  unfold meredithHoldsBool.
  repeat rewrite h1.
  repeat rewrite h2.
  repeat rewrite Bool.eqb_reflx.
  reflexivity.
Qed.

Theorem meredith_characterizes_sheffer_on_bool
    (op : bool -> bool -> bool) (h : MeredithAxioms op) : IsBooleanSheffer op.
Proof.
  pose proof (@meredithAxioms_to_bool op h) as htable.
  unfold meredithHoldsBool in htable.
  characterize_sheffer_from_table op htable.
Qed.

(* ------------------------------------------------------------------ *)
(* Functional completeness for ordinary connectives                    *)
(*                                                                     *)
(* The stroke and classical languages and the toNand/toNor             *)
(* translations are the shared ones from Sheffer.v.                    *)
(* ------------------------------------------------------------------ *)

Lemma strokeEvalWith_same {A : Type} (op op' : bool -> bool -> bool)
    (hsame : SameBoolOp op op') (v : A -> bool) :
    forall p : StrokeFormula A,
      evalWith op v p = evalWith op' v p.
Proof.
  induction p; simpl.
  - reflexivity.
  - rewrite IHp1, IHp2. apply hsame.
Qed.

(* Functional completeness depends on the operation only through the fact
   that it is one of the two boolean Sheffer operations: the translation is
   [toNand] or [toNor] accordingly, and [strokeEvalWith_same] transports the
   correctness lemma along the pointwise agreement.  Proving it at that level
   of generality lets each axiom system contribute only its own
   characterization theorem. *)
Theorem sheffer_functionally_complete {A : Type}
    (op : bool -> bool -> bool) (h : IsBooleanSheffer op)
    (p : ClassicalFormula A) :
    exists q : StrokeFormula A,
      forall v : A -> bool, evalWith op v q = eval v p.
Proof.
  destruct h as [hop | hop].
  - exists (toNand p). intro v.
    rewrite (strokeEvalWith_same hop v (toNand p)).
    apply eval_toNand.
  - exists (toNor p). intro v.
    rewrite (strokeEvalWith_same hop v (toNor p)).
    apply eval_toNor.
Qed.

Theorem wolfram_functionally_complete {A : Type}
    (op : bool -> bool -> bool) (h : WolframAxiom op)
    (p : ClassicalFormula A) :
    exists q : StrokeFormula A,
      forall v : A -> bool, evalWith op v q = eval v p.
Proof.
  exact (@sheffer_functionally_complete A op
    (@wolfram_characterizes_sheffer_on_bool op h) p).
Qed.

Theorem meredith_functionally_complete {A : Type}
    (op : bool -> bool -> bool) (h : MeredithAxioms op)
    (p : ClassicalFormula A) :
    exists q : StrokeFormula A,
      forall v : A -> bool, evalWith op v q = eval v p.
Proof.
  exact (@sheffer_functionally_complete A op
    (@meredith_characterizes_sheffer_on_bool op h) p).
Qed.

(* ------------------------------------------------------------------ *)
(* Certified finite search for the six-operator lower bound            *)
(*                                                                     *)
(* The finite search reuses the first-order terms of                   *)
(* EquationalLogic.Checker rather than a private copy of the syntax.  *)
(* ------------------------------------------------------------------ *)

Record BinOp : Type := {
  ff : bool;
  ft : bool;
  tf : bool;
  tt : bool
}.

Definition binOpApply (op : BinOp) : bool -> bool -> bool :=
  fun p q =>
    match p, q with
    | false, false => ff op
    | false, true => ft op
    | true, false => tf op
    | true, true => tt op
    end.

Definition binOpEqb (x y : BinOp) : bool :=
  Bool.eqb (ff x) (ff y) &&
  Bool.eqb (ft x) (ft y) &&
  Bool.eqb (tf x) (tf y) &&
  Bool.eqb (tt x) (tt y).

Definition nandTable : BinOp :=
  {| ff := true; ft := true; tf := true; tt := false |}.

Definition norTable : BinOp :=
  {| ff := true; ft := false; tf := false; tt := false |}.

Definition bools : list bool := [false; true].

Definition allBinOps : list BinOp :=
  flat_map (fun ff =>
  flat_map (fun ft =>
  flat_map (fun tf =>
  map (fun tt => {| ff := ff; ft := ft; tf := tf; tt := tt |}) bools)
    bools) bools) bools.

Notation SearchTerm := Term.

Fixpoint listEqb {A : Type} (eqb : A -> A -> bool)
    (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => eqb x y && listEqb eqb xs' ys'
  | _, _ => false
  end.

Fixpoint nodeCount (t : SearchTerm) : nat :=
  match t with
  | Var _ => 0
  | Op l r => nodeCount l + nodeCount r + 1
  end.

Fixpoint varBound (t : SearchTerm) : nat :=
  match t with
  | Var i => S i
  | Op l r => Nat.max (varBound l) (varBound r)
  end.

Fixpoint evalSearchTerm (op : BinOp) (env : list bool)
    (t : SearchTerm) : bool :=
  match t with
  | Var i => nth i env false
  | Op l r => binOpApply op (evalSearchTerm op env l) (evalSearchTerm op env r)
  end.

Fixpoint allEnvs (n : nat) : list (list bool) :=
  match n with
  | 0 => [[]]
  | S n' => flat_map (fun env => [false :: env; true :: env]) (allEnvs n')
  end.

Fixpoint canonicalTermsAux (fuel nodes next : nat)
    {struct fuel} : list (SearchTerm * nat) :=
  match nodes with
  | 0 =>
      map (fun i => (Var i, if Nat.eqb i next then S next else next))
        (seq 0 (S next))
  | S nodes' =>
      match fuel with
      | 0 => []
      | S fuel' =>
          flat_map (fun leftNodes =>
            let rightNodes := nodes' - leftNodes in
            flat_map (fun left =>
              map (fun right => (Op (fst left) (fst right), snd right))
                (canonicalTermsAux fuel' rightNodes (snd left)))
              (canonicalTermsAux fuel' leftNodes next))
            (seq 0 (S nodes'))
      end
  end.

Definition equationsUpTo (maxNodes : nat) : list (SearchTerm * SearchTerm) :=
  flat_map (fun leftNodes =>
    flat_map (fun rightNodes =>
      flat_map (fun lhs =>
        map (fun rhs => (fst lhs, fst rhs))
          (canonicalTermsAux rightNodes rightNodes (snd lhs)))
        (canonicalTermsAux leftNodes leftNodes 0))
      (seq 0 (S (maxNodes - leftNodes))))
    (seq 0 (S maxNodes)).

Definition equationHolds (op : BinOp) (lhs rhs : SearchTerm) : bool :=
  forallb (fun env =>
    Bool.eqb (evalSearchTerm op env lhs) (evalSearchTerm op env rhs))
    (allEnvs 7).

Definition equationModels (lhs rhs : SearchTerm) : list BinOp :=
  filter (fun op => equationHolds op lhs rhs) allBinOps.

Definition validInBooleanShefferTables (lhs rhs : SearchTerm) : bool :=
  equationHolds nandTable lhs rhs && equationHolds norTable lhs rhs.

Definition hasExactlyModels (models : list BinOp) (lhs rhs : SearchTerm) : bool :=
  listEqb binOpEqb (equationModels lhs rhs) models.

Definition characterizesShefferTables (lhs rhs : SearchTerm) : bool :=
  hasExactlyModels [norTable; nandTable] lhs rhs.

Definition wolframLhs : SearchTerm :=
  let a := Var 0 in
  let b := Var 1 in
  let c := Var 2 in
  Op
    (Op (Op a b) c)
    (Op a (Op (Op a c) a)).

Definition wolframRhs : SearchTerm := Var 2.

Theorem wolfram_operator_count :
    nodeCount wolframLhs + nodeCount wolframRhs = 6.
Proof. vm_compute. reflexivity. Qed.

Theorem wolfram_equation_characterizes_sheffer_tables :
    characterizesShefferTables wolframLhs wolframRhs = true.
Proof. vm_compute. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* Finite countermodel certificate for the five-operator lower bound   *)
(* ------------------------------------------------------------------ *)

Record FiniteOp : Type := {
  fsize : nat;
  ftable : list nat
}.

Definition finiteApply (op : FiniteOp) (x y : nat) : nat :=
  match fsize op with
  | 0 => 0
  | size => (nth (x * size + y) (ftable op) 0) mod size
  end.

Fixpoint allFiniteEnvs (size n : nat) : list (list nat) :=
  match n with
  | 0 => [[]]
  | S n' =>
      flat_map (fun env => map (fun x => x :: env) (seq 0 size))
        (allFiniteEnvs size n')
  end.

Fixpoint evalFiniteSearchTerm (op : FiniteOp) (env : list nat)
    (t : SearchTerm) : nat :=
  match t with
  | Var i => nth i env 0
  | Op l r => finiteApply op (evalFiniteSearchTerm op env l)
    (evalFiniteSearchTerm op env r)
  end.

Definition finiteEquationHolds (op : FiniteOp)
    (lhs rhs : SearchTerm) : bool :=
  forallb (fun env =>
    Nat.eqb (evalFiniteSearchTerm op env lhs) (evalFiniteSearchTerm op env rhs))
    (allFiniteEnvs (fsize op) (Nat.max (varBound lhs) (varBound rhs))).

Definition finiteWolframHolds (op : FiniteOp) : bool :=
  forallb (fun env =>
    let a := nth 0 env 0 in
    let b := nth 1 env 0 in
    let c := nth 2 env 0 in
    let lhs := finiteApply op (finiteApply op (finiteApply op a b) c)
      (finiteApply op a (finiteApply op (finiteApply op a c) a)) in
    Nat.eqb lhs c)
    (allFiniteEnvs (fsize op) 3).

Definition shortCountermodelPool : list FiniteOp := [
  {| fsize := 2; ftable := [0; 0; 0; 0] |};
  {| fsize := 2; ftable := [0; 0; 0; 1] |};
  {| fsize := 2; ftable := [0; 0; 1; 1] |};
  {| fsize := 2; ftable := [0; 1; 0; 1] |};
  {| fsize := 2; ftable := [0; 1; 1; 0] |};
  {| fsize := 3; ftable := [0; 2; 1; 2; 2; 0; 1; 0; 1] |};
  {| fsize := 4; ftable := [0; 3; 3; 0; 2; 1; 1; 2; 0; 3; 3; 0; 2; 1; 1; 2] |};
  {| fsize := 4; ftable := [0; 2; 0; 2; 0; 2; 0; 2; 1; 3; 1; 3; 1; 3; 1; 3] |};
  {| fsize := 2; ftable := [0; 0; 1; 0] |};
  {| fsize := 4; ftable := [0; 3; 3; 0; 0; 3; 3; 0; 1; 2; 2; 1; 1; 2; 2; 1] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 2; 1; 0; 0; 1] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 0; 2; 0; 0; 2] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 0; 2; 2; 0; 2] |};
  {| fsize := 4; ftable := [1; 2; 2; 1; 3; 0; 0; 3; 1; 2; 2; 1; 3; 0; 0; 3] |};
  {| fsize := 3; ftable := [0; 1; 2; 2; 0; 1; 1; 2; 0] |};
  {| fsize := 3; ftable := [0; 0; 1; 0; 2; 1; 1; 1; 1] |};
  {| fsize := 4; ftable := [0; 2; 0; 2; 3; 1; 3; 1; 3; 1; 3; 1; 0; 2; 0; 2] |};
  {| fsize := 4; ftable := [1; 3; 1; 3; 2; 0; 2; 0; 2; 0; 2; 0; 1; 3; 1; 3] |};
  {| fsize := 3; ftable := [0; 2; 1; 1; 0; 2; 2; 1; 0] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 2; 2; 0; 0; 1] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 2; 0; 1; 0; 1] |};
  {| fsize := 4; ftable := [0; 0; 1; 1; 3; 3; 2; 2; 3; 3; 2; 2; 0; 0; 1; 1] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 1; 1; 2; 0; 2] |};
  {| fsize := 4; ftable := [3; 1; 3; 1; 3; 1; 3; 1; 2; 0; 2; 0; 2; 0; 2; 0] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 1; 1; 0; 0; 0] |};
  {| fsize := 3; ftable := [0; 0; 1; 2; 2; 2; 0; 0; 2] |};
  {| fsize := 4; ftable := [2; 1; 1; 2; 2; 1; 1; 2; 3; 0; 0; 3; 3; 0; 0; 3] |};
  {| fsize := 4; ftable := [3; 3; 2; 2; 1; 1; 0; 0; 3; 3; 2; 2; 1; 1; 0; 0] |};
  {| fsize := 4; ftable := [0; 0; 1; 1; 2; 2; 3; 3; 0; 0; 1; 1; 2; 2; 3; 3] |};
  {| fsize := 4; ftable := [2; 2; 3; 3; 1; 1; 0; 0; 1; 1; 0; 0; 2; 2; 3; 3] |}
].

Definition hasFiniteNonWolframCountermodel (lhs rhs : SearchTerm) : bool :=
  existsb (fun op =>
    finiteEquationHolds op lhs rhs && negb (finiteWolframHolds op))
    shortCountermodelPool.

Definition shortEquationCountermodelCheck : bool :=
  forallb (fun e =>
    negb (validInBooleanShefferTables (fst e) (snd e)) ||
      hasFiniteNonWolframCountermodel (fst e) (snd e))
    (equationsUpTo 5).

(*
  Lazy short-circuit machinery for evaluating the certificate.

  `andb`/`orb`/`forallb`/`existsb` are ordinary function applications, so
  `vm_compute` (call-by-value) evaluates both arguments before combining
  them: a direct `vm_compute` on `shortEquationCountermodelCheck` runs the
  full 128-environment sweep and the entire finite countermodel search for
  every candidate equation, which is far too slow.  The match-based
  combinators below keep the recursive call inside a `match` branch, so the
  VM short-circuits: the countermodel search runs only on the (rare)
  Sheffer-valid equations, each equation sweep stops at the first failing
  environment, and the constant non-Wolfram pool is hoisted out of the
  per-equation loop.  The bridge lemmas transport the fast evaluation back
  to the original eager definitions, so the capstone theorems below are
  stated about `shortEquationCountermodelCheck` itself.
*)

Fixpoint lforallb {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => true
  | x :: l' => if f x then lforallb f l' else false
  end.

Fixpoint lexistsb {A : Type} (f : A -> bool) (l : list A) : bool :=
  match l with
  | [] => false
  | x :: l' => if f x then true else lexistsb f l'
  end.

Lemma lforallb_forallb {A : Type} (f : A -> bool) (l : list A) :
    lforallb f l = forallb f l.
Proof.
  induction l as [| x l IH]; simpl.
  - reflexivity.
  - destruct (f x); simpl; [exact IH | reflexivity].
Qed.

Lemma lexistsb_existsb {A : Type} (f : A -> bool) (l : list A) :
    lexistsb f l = existsb f l.
Proof.
  induction l as [| x l IH]; simpl.
  - reflexivity.
  - destruct (f x); simpl; [reflexivity | exact IH].
Qed.

Lemma existsb_filter {A : Type} (f g : A -> bool) (l : list A) :
    existsb (fun x => f x && g x) l = existsb f (filter g l).
Proof.
  induction l as [| x l IH]; simpl.
  - reflexivity.
  - destruct (g x); simpl.
    + rewrite Bool.andb_true_r, IH. reflexivity.
    + rewrite Bool.andb_false_r. simpl. exact IH.
Qed.

Lemma forallb_ext {A : Type} (f g : A -> bool) (l : list A)
    (h : forall x, f x = g x) : forallb f l = forallb g l.
Proof.
  induction l as [| x l IH]; simpl.
  - reflexivity.
  - rewrite h, IH. reflexivity.
Qed.

Lemma existsb_ext {A : Type} (f g : A -> bool) (l : list A)
    (h : forall x, f x = g x) : existsb f l = existsb g l.
Proof.
  induction l as [| x l IH]; simpl.
  - reflexivity.
  - rewrite h, IH. reflexivity.
Qed.

Definition lazyEquationHolds (op : BinOp) (lhs rhs : SearchTerm) : bool :=
  lforallb (fun env =>
    Bool.eqb (evalSearchTerm op env lhs) (evalSearchTerm op env rhs))
    (allEnvs 7).

Definition lazyValidInBooleanShefferTables (lhs rhs : SearchTerm) : bool :=
  if lazyEquationHolds nandTable lhs rhs
  then lazyEquationHolds norTable lhs rhs
  else false.

Definition lazyFiniteEquationHolds (op : FiniteOp)
    (lhs rhs : SearchTerm) : bool :=
  lforallb (fun env =>
    Nat.eqb (evalFiniteSearchTerm op env lhs) (evalFiniteSearchTerm op env rhs))
    (allFiniteEnvs (fsize op) (Nat.max (varBound lhs) (varBound rhs))).

(* The non-Wolfram sub-pool is constant, so it is evaluated once here
   instead of refiltering `shortCountermodelPool` for every equation. *)
Definition nonWolframPool : list FiniteOp :=
  Eval vm_compute in
    filter (fun op => negb (finiteWolframHolds op)) shortCountermodelPool.

Definition lazyHasFiniteNonWolframCountermodel (lhs rhs : SearchTerm) : bool :=
  lexistsb (fun op => lazyFiniteEquationHolds op lhs rhs) nonWolframPool.

Definition lazyShortEquationCountermodelCheck : bool :=
  lforallb (fun e =>
    if lazyValidInBooleanShefferTables (fst e) (snd e)
    then lazyHasFiniteNonWolframCountermodel (fst e) (snd e)
    else true)
    (equationsUpTo 5).

Lemma lazyEquationHolds_eq (op : BinOp) (lhs rhs : SearchTerm) :
    lazyEquationHolds op lhs rhs = equationHolds op lhs rhs.
Proof.
  apply lforallb_forallb.
Qed.

Lemma lazyValidInBooleanShefferTables_eq (lhs rhs : SearchTerm) :
    lazyValidInBooleanShefferTables lhs rhs =
      validInBooleanShefferTables lhs rhs.
Proof.
  unfold lazyValidInBooleanShefferTables, validInBooleanShefferTables.
  rewrite !lazyEquationHolds_eq.
  destruct (equationHolds nandTable lhs rhs); reflexivity.
Qed.

Lemma nonWolframPool_eq :
    nonWolframPool =
      filter (fun op => negb (finiteWolframHolds op)) shortCountermodelPool.
Proof.
  vm_compute. reflexivity.
Qed.

Lemma lazyHasFiniteNonWolframCountermodel_eq (lhs rhs : SearchTerm) :
    lazyHasFiniteNonWolframCountermodel lhs rhs =
      hasFiniteNonWolframCountermodel lhs rhs.
Proof.
  unfold lazyHasFiniteNonWolframCountermodel, hasFiniteNonWolframCountermodel.
  rewrite lexistsb_existsb, nonWolframPool_eq, <- existsb_filter.
  apply existsb_ext.
  intro op.
  unfold lazyFiniteEquationHolds, finiteEquationHolds.
  rewrite lforallb_forallb.
  reflexivity.
Qed.

Lemma shortEquationCountermodelCheck_eq_lazy :
    shortEquationCountermodelCheck = lazyShortEquationCountermodelCheck.
Proof.
  unfold shortEquationCountermodelCheck, lazyShortEquationCountermodelCheck.
  rewrite lforallb_forallb.
  apply forallb_ext.
  intro e.
  cbv beta.
  rewrite (lazyValidInBooleanShefferTables_eq (fst e) (snd e)).
  rewrite (lazyHasFiniteNonWolframCountermodel_eq (fst e) (snd e)).
  destruct (validInBooleanShefferTables (fst e) (snd e)); reflexivity.
Qed.

(*
  Every equation with at most five operation occurrences that is true in the
  two Boolean Sheffer tables is true in one of the finite algebras above
  while Wolfram's axiom is false there.  This is the Coq replay of the Lean
  `native_decide` certificate, via the lazy evaluation bridge.
*)
Theorem every_short_boolean_sheffer_equation_has_finite_nonwolfram_countermodel :
    shortEquationCountermodelCheck = true.
Proof.
  rewrite shortEquationCountermodelCheck_eq_lazy.
  vm_compute.
  reflexivity.
Qed.

(*
  Entry-point theorem for the finite lower-bound result: Wolfram's equation
  has six primitive binary-operation occurrences, it characterizes the
  Sheffer truth tables on the two-element Boolean algebra, and every shorter
  equation that is even true of those Boolean Sheffer tables has a finite
  non-Wolfram model.
*)
Theorem wolfram_six_operations_is_minimal_for_single_equational_axioms :
    nodeCount wolframLhs + nodeCount wolframRhs = 6 /\
      characterizesShefferTables wolframLhs wolframRhs = true /\
      shortEquationCountermodelCheck = true.
Proof.
  split; [exact wolfram_operator_count |].
  split; [exact wolfram_equation_characterizes_sheffer_tables |].
  exact every_short_boolean_sheffer_equation_has_finite_nonwolfram_countermodel.
Qed.

End WolframBoolean.
End LeanProofs.
