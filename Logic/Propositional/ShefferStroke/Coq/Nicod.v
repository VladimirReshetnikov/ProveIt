(*
  Coq port of the Lean module ShefferStroke.Nicod.

  As in the Lean original (which builds on ShefferStroke.Sheffer), the NAND-only
  language is the shared stroke syntax of Sheffer.v.  The formalization keeps
  the proof-theoretic part first: Nicod's one axiom and one rule derive the
  three Lukasiewicz Hilbert axiom schemata and modus ponens.  The semantic
  part then proves classical soundness and NAND functional completeness via
  the shared Sheffer translations.
*)

From Stdlib Require Import Bool.Bool.
(* Required: `tauto` needs the classical `classic` axiom this module
   provides to prove `prop_nand_imp` below (its right-to-left direction is
   not intuitionistically valid). *)
From Stdlib Require Import Logic.Classical_Prop.
From ShefferStroke Require Import Sheffer.

Set Implicit Arguments.

Module LeanProofs.
Module Nicod.

Module Sheffer := ShefferStroke.Sheffer.LeanProofs.Sheffer.
Import Sheffer.

(* Formulas whose only logical connective is NAND: the shared stroke syntax
   of Sheffer.v, exactly as Lean's `Nicod.Formula` abbreviates
   `Sheffer.StrokeFormula`. *)
Notation Formula := StrokeFormula.
Notation atom := strokeAtom.
Notation nand := stroke.

Module Formula.

(* Boolean semantics for NAND-only formulas. *)
Fixpoint eval {A : Type} (v : A -> bool) (p : Formula A) : bool :=
  match p with
  | atom a => v a
  | nand p q => boolNand (eval v p) (eval v q)
  end.

(* Nicod's NAND-fixed semantics is the shared stroke semantics at `boolNand`. *)
Lemma eval_eq_evalWith {A : Type} (v : A -> bool) :
    forall p : Formula A, eval v p = evalWith boolNand v p.
Proof.
  induction p; simpl.
  - reflexivity.
  - rewrite IHp1, IHp2. reflexivity.
Qed.

(* Classical validity of a NAND-only formula. *)
Definition Valid {A : Type} (p : Formula A) : Prop :=
  forall v : A -> bool, eval v p = true.

(* Nicod's single axiom schema, in NAND-only syntax. *)
Definition nicodAxiom {A : Type}
    (p q r u w : Formula A) : Formula A :=
  nand (nand p (nand q r))
    (nand (nand u (nand u u))
      (nand (nand w q) (nand (nand p w) (nand p w)))).

(* The exact one-axiom/one-rule Nicod proof system. *)
Inductive Provable {A : Type} : Formula A -> Prop :=
| singleAxiom (p q r u w : Formula A) :
    Provable (nicodAxiom p q r u w)
| rule (p q r : Formula A) :
    Provable (nand p (nand q r)) -> Provable p -> Provable r.

(* Implication expressed in the NAND-only language. *)
Definition imp {A : Type} (p q : Formula A) : Formula A :=
  nand p (nand q q).

(* Negation expressed in the NAND-only language. *)
Definition neg {A : Type} (p : Formula A) : Formula A :=
  nand p p.

(* Nicod's axiom used as an inference schema.  This is Metamath's `nic-imp`. *)
Theorem nicImp {A : Type} {p q r : Formula A} (u w : Formula A)
    (h : Provable (nand p (nand q r))) :
    Provable (nand (nand w q) (nand (nand p w) (nand p w))).
Proof.
  exact (rule (singleAxiom p q r u w) h).
Qed.

(* Lemma for the NAND identity theorem.  This is Metamath's `nic-idlem1`. *)
Theorem nicIdlem1 {A : Type} (p q r u w : Formula A) :
    Provable (nand (nand w (nand u (nand u u)))
      (nand (nand (nand p (nand q r)) w)
        (nand (nand p (nand q r)) w))).
Proof.
  exact (nicImp u w (singleAxiom p q r u p)).
Qed.

(* Lemma for the NAND identity theorem.  This is Metamath's `nic-idlem2`. *)
Theorem nicIdlem2 {A : Type}
    (eta p q r theta u : Formula A)
    (h : Provable (nand eta (nand (nand p (nand q r)) theta))) :
    Provable (nand (nand theta (nand u (nand u u))) eta).
Proof.
  pose proof (nicImp eta eta
    (nicIdlem1 p q r u theta)) as hmajor.
  exact (rule hmajor h).
Qed.

(* `p -> p`, expressed as a NAND formula.  This is Metamath's `nic-id`. *)
Theorem nicId {A : Type} (p : Formula A) :
    Provable (nand p (nand p p)).
Proof.
  set (i := nand p (nand p p)).
  set (c := nand (nand p p) (nand (nand p p) (nand p p))).
  assert (h1 : Provable (nand i (nand i c))).
  { change (Provable (nicodAxiom p p p p p)).
    exact (singleAxiom p p p p p). }
  assert (h2 : Provable (nand (nand c i) i)).
  { change (Provable (nand (nand c (nand p (nand p p)))
      (nand p (nand p p)))).
    exact (@nicIdlem2 A i p p p c p h1). }
  assert (h3 : Provable (nand (nand i i)
      (nand (nand c i) (nand c i)))).
  { change (Provable
      (nand (nand i i) (nand (nand c i) (nand c i)))).
    exact (nicIdlem1 (nand p p) (nand p p) (nand p p) p i). }
  assert (h4 : Provable (nand (nand (nand c i) i) (nand i i))).
  { exact (@nicIdlem2 A (nand i i) c p (nand p p) (nand c i) p h3). }
  exact (rule h4 h2).
Qed.

(* Symmetry of NAND in theorem form.  This is Metamath's `nic-swap`. *)
Theorem nicSwap {A : Type} (p q : Formula A) :
    Provable (nand (nand q p) (nand (nand p q) (nand p q))).
Proof.
  exact (rule (singleAxiom p p p p q) (nicId p)).
Qed.

(* Inference version of `nicSwap`.  This is Metamath's `nic-isw1`. *)
Theorem nicIsw1 {A : Type} {p q : Formula A}
    (h : Provable (nand q p)) : Provable (nand p q).
Proof.
  exact (rule (nicSwap p q) h).
Qed.

(* Inference for swapping nested terms.  This is Metamath's `nic-isw2`. *)
Theorem nicIsw2 {A : Type} {p q r : Formula A}
    (h : Provable (nand p (nand q r))) : Provable (nand p (nand r q)).
Proof.
  pose proof (nicImp p p (nicSwap q r)) as hmajor.
  pose proof (rule hmajor h) as htmp.
  exact (nicIsw1 htmp).
Qed.

(* Inference version of `nicImp` using a right-handed term. *)
Theorem nicIimp1 {A : Type} {p q r u : Formula A}
    (hmain : Provable (nand p (nand q r)))
    (harg : Provable (nand u q)) :
    Provable (nand u p).
Proof.
  pose proof (nicImp p u hmain) as hmajor.
  pose proof (rule hmajor harg) as htmp.
  exact (nicIsw1 htmp).
Qed.

(* Inference version of `nicImp` using a left-handed term. *)
Theorem nicIimp2 {A : Type} {p q r u : Formula A}
    (hmain : Provable (nand (nand p q) (nand r r)))
    (harg : Provable (nand u p)) :
    Provable (nand u (nand r r)).
Proof.
  exact (nicIimp1 (nicIsw1 hmain) harg).
Qed.

(* Remove the trailing term.  This is Metamath's `nic-idel`. *)
Theorem nicIdel {A : Type} {p q r : Formula A}
    (h : Provable (nand p (nand q r))) :
    Provable (nand p (nand q q)).
Proof.
  pose proof (nicIsw1 (nicId q)) as hqqq.
  pose proof (nicImp p (nand q q) h) as hmajor.
  exact (rule hmajor hqqq).
Qed.

(* Chained inference for NAND-encoded implication.  This is Metamath's `nic-ich`. *)
Theorem nicIch {A : Type} {p q r : Formula A}
    (hpq : Provable (nand p (nand q q)))
    (hqr : Provable (nand q (nand r r))) :
    Provable (nand p (nand r r)).
Proof.
  pose proof (nicIsw1 hqr) as hrq.
  pose proof (nicImp p (nand r r) hpq) as hmajor.
  exact (rule hmajor hrq).
Qed.

(* Double the terms, a contraposition-like inference.  This is Metamath's
   `nic-idbl`. *)
Theorem nicIdbl {A : Type} {p q : Formula A}
    (hpq : Provable (nand p (nand q q))) :
    Provable (nand (nand q q) (nand (nand p p) (nand p p))).
Proof.
  pose proof (nicImp p q hpq) as h1.
  pose proof (nicImp p p hpq) as h2.
  exact (nicIch h1 h2).
Qed.

(* Extract one side of a NAND biconditional-definition shape. *)
Theorem nicBi1 {A : Type} {p q : Formula A}
    (h : Provable (nand (nand p q) (nand (nand p p) (nand q q)))) :
    Provable (nand p (nand q q)).
Proof.
  pose proof (nicId p) as hp.
  pose proof (nicIimp1 h hp) as h1.
  pose proof (nicIsw2 h1) as h2.
  exact (nicIdel h2).
Qed.

(* Extract the other side of a NAND biconditional-definition shape. *)
Theorem nicBi2 {A : Type} {p q : Formula A}
    (h : Provable (nand (nand p q) (nand (nand p p) (nand q q)))) :
    Provable (nand q (nand p p)).
Proof.
  pose proof (nicIsw2 h) as h1.
  pose proof (nicId q) as hq.
  pose proof (nicIimp1 h1 hq) as h2.
  exact (nicIdel h2).
Qed.

(* The biconditional-definition justification shape. *)
Theorem nicBijust {A : Type} (p : Formula A) :
    Provable (nand (nand p p) (nand (nand p p) (nand p p))).
Proof.
  exact (nicSwap p p).
Qed.

(* The NAND definition of implication, stated in Metamath's definition shape. *)
Theorem nicDfim {A : Type} (p q : Formula A) :
    Provable (nand (nand (imp p q) (imp p q))
      (nand (nand (imp p q) (imp p q)) (nand (imp p q) (imp p q)))).
Proof.
  exact (nicBijust (imp p q)).
Qed.

(* The NAND definition of negation, stated in Metamath's definition shape. *)
Theorem nicDfneg {A : Type} (p : Formula A) :
    Provable (nand (nand (neg p) (neg p))
      (nand (nand (neg p) (neg p)) (nand (neg p) (neg p)))).
Proof.
  exact (nicBijust (neg p)).
Qed.

(* Standard modus ponens for NAND-defined implication. *)
Theorem nicStdmp {A : Type} {p q : Formula A}
    (hp : Provable p) (hpq : Provable (imp p q)) :
    Provable q.
Proof.
  exact (rule hpq hp).
Qed.

(* The first Lukasiewicz axiom schema, derived from Nicod's axiom and rule. *)
Theorem nicLuk1 {A : Type} (p q r : Formula A) :
    Provable (imp (imp p q) (imp (imp q r) (imp p r))).
Proof.
  set (c := imp p r).
  set (f := nand (nand r r) q).
  set (d := nand f (nand c c)).
  set (e := nand (nand c c) f).
  set (x := imp (imp q r) c).
  assert (h3 : Provable (nand (imp p q)
      (nand (nand p (nand p p)) d))).
  { change (Provable (nicodAxiom p q q p (nand r r))).
    exact (singleAxiom p q q p (nand r r)). }
  pose proof (nicIsw2 h3) as h4.
  pose proof (nicIdel h4) as h5.
  pose proof (nicId (nand c c)) as h8.
  pose proof (nicImp (nand c c) f h8) as h9.
  pose proof (nicSwap (nand r r) q) as h12.
  pose proof (nicImp (imp q r) (nand c c) h12) as h14.
  pose proof (nicIch h9 h14) as h15.
  pose proof (nicIch h5 h15) as h16.
  exact h16.
Qed.

(* The second Lukasiewicz axiom schema, derived from Nicod's axiom and rule. *)
Theorem nicLuk2 {A : Type} (p : Formula A) :
    Provable (imp (imp (neg p) p) p).
Proof.
  exact (nicIsw1 (nicId (neg p))).
Qed.

(* The third Lukasiewicz axiom schema, derived from Nicod's axiom and rule. *)
Theorem nicLuk3 {A : Type} (p q : Formula A) :
    Provable (imp p (imp (neg p) q)).
Proof.
  pose proof (nicId (imp (neg p) q)) as hmain.
  pose proof (nicId p) as hpnot.
  change (Provable (imp p (imp (neg p) q))).
  exact (nicIimp2 hmain hpnot).
Qed.

(* The standard three-axiom Lukasiewicz Hilbert calculus for classical
   propositional logic, expressed using the NAND-defined connectives. *)
Inductive LukasiewiczProvable {A : Type} : Formula A -> Prop :=
| luk1 (p q r : Formula A) :
    LukasiewiczProvable (imp (imp p q) (imp (imp q r) (imp p r)))
| luk2 (p : Formula A) :
    LukasiewiczProvable (imp (imp (neg p) p) p)
| luk3 (p q : Formula A) :
    LukasiewiczProvable (imp p (imp (neg p) q))
| mp (p q : Formula A) :
    LukasiewiczProvable p ->
    LukasiewiczProvable (imp p q) ->
    LukasiewiczProvable q.

(* Every theorem of the standard Lukasiewicz Hilbert calculus is derivable in
   Nicod's one-axiom/one-rule NAND calculus. *)
Theorem LukasiewiczProvable_toNicod {A : Type} {p : Formula A}
    (h : LukasiewiczProvable p) : Provable p.
Proof.
  induction h.
  - apply nicLuk1.
  - apply nicLuk2.
  - apply nicLuk3.
  - exact (nicStdmp IHh1 IHh2).
Qed.

(* Nicod's system implements classical propositional calculus in the concrete
   sense that it derives every formula provable in the standard Lukasiewicz
   Hilbert calculus. *)
Theorem implementsLukasiewicz {A : Type} {p : Formula A}
    (h : LukasiewiczProvable p) : Provable p.
Proof.
  exact (LukasiewiczProvable_toNicod h).
Qed.

(* Nicod's axiom schema is a tautology under NAND semantics. *)
Theorem nicodAxiom_valid {A : Type} (p q r u w : Formula A) :
    Valid (nicodAxiom p q r u w).
Proof.
  intro v.
  unfold nicodAxiom; simpl.
  destruct (eval v p), (eval v q), (eval v r), (eval v u), (eval v w);
    reflexivity.
Qed.

(* Nicod's inference rule is sound for classical NAND semantics. *)
Theorem nicodRule_sound {A : Type} {p q r : Formula A}
    (hmain : Valid (nand p (nand q r))) (hp : Valid p) : Valid r.
Proof.
  intro v.
  specialize (hp v).
  specialize (hmain v).
  simpl in *.
  destruct (eval v p), (eval v q), (eval v r); simpl in *; try discriminate;
    reflexivity.
Qed.

(* Soundness of the one-axiom/one-rule Nicod calculus. *)
Theorem Provable_sound {A : Type} {p : Formula A} (h : Provable p) :
    Valid p.
Proof.
  induction h.
  - apply nicodAxiom_valid.
  - exact (nicodRule_sound IHh1 IHh2).
Qed.

(* The implemented Lukasiewicz calculus is sound because its proofs translate
   to Nicod proofs. *)
Theorem LukasiewiczProvable_sound {A : Type} {p : Formula A}
    (h : LukasiewiczProvable p) : Valid p.
Proof.
  exact (Provable_sound (LukasiewiczProvable_toNicod h)).
Qed.

End Formula.

(*
  The shared classical propositional language and its NAND translation come
  from Sheffer.v (`ClassicalFormula`, `eval`, `toNand`); only the
  Nicod-specific validity bridges live here.
*)
Module ClassicalFormula.

Notation eval := Sheffer.eval.
Notation toNand := Sheffer.toNand.

(* Nicod's NAND semantics agrees with the shared classical semantics across
   the shared `toNand` translation. *)
Theorem eval_toNand {A : Type} (v : A -> bool) :
    forall p : ClassicalFormula A, Formula.eval v (toNand p) = eval v p.
Proof.
  intro p.
  rewrite Formula.eval_eq_evalWith.
  apply Sheffer.eval_toNand.
Qed.

(* The Sheffer stroke is functionally complete: validity is preserved by the
   shared translation from ordinary classical formulas to NAND-only formulas. *)
Theorem toNand_valid_iff {A : Type} {p : ClassicalFormula A} :
    Formula.Valid (toNand p) <-> forall v : A -> bool, eval v p = true.
Proof.
  split.
  - intros h v.
    rewrite <- eval_toNand.
    apply h.
  - intros h v.
    rewrite eval_toNand.
    apply h.
Qed.

End ClassicalFormula.

(* NAND as a connective on Coq propositions. *)
Definition propNand (p q : Prop) : Prop := ~ (p /\ q).

(* The object-language NAND semantics agrees with the familiar propositional
   reading. *)
Theorem prop_nand_not (p : Prop) : propNand p p <-> ~ p.
Proof.
  unfold propNand; tauto.
Qed.

(* `p -> q` expressed with NAND alone.  This is where the `Classical_Prop`
   import is required: without `classic` in the environment, `tauto`
   cannot prove the right-to-left double-negation step. *)
Theorem prop_nand_imp (p q : Prop) :
    propNand p (propNand q q) <-> (p -> q).
Proof.
  unfold propNand; tauto.
Qed.

(* `p /\ q` expressed with NAND alone. *)
Theorem prop_nand_and (p q : Prop) :
    propNand (propNand p q) (propNand p q) <-> p /\ q.
Proof.
  unfold propNand; tauto.
Qed.

(* `p \/ q` expressed with NAND alone. *)
Theorem prop_nand_or (p q : Prop) :
    propNand (propNand p p) (propNand q q) <-> p \/ q.
Proof.
  unfold propNand; tauto.
Qed.

(* Nicod's single axiom, read directly as a classical propositional
   tautology. *)
Theorem prop_nicod_axiom (p q r u w : Prop) :
    propNand (propNand p (propNand q r))
      (propNand (propNand u (propNand u u))
        (propNand (propNand w q) (propNand (propNand p w) (propNand p w)))).
Proof.
  unfold propNand; tauto.
Qed.

(* Nicod's single inference rule, read directly over propositions. *)
Theorem prop_nicod_rule {p q r : Prop} :
    propNand p (propNand q r) -> p -> r.
Proof.
  unfold propNand; tauto.
Qed.

End Nicod.
End LeanProofs.
