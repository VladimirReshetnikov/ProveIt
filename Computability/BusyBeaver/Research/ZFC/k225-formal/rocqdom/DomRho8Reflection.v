(** Generic, purely syntactic certificate soundness for dominated implication. *)
From Stdlib Require Import Arith Lia List Bool NArith.
From K230L Require Import Codes230.
Import ListNotations.

Record DomImp (T : nat -> Prop) : Prop := {
  dtruth : T 0;
  dmp : forall a b, T (wim a b) -> T a -> T b;
  drho8 : forall a b c u, u <= a -> T (rho8 a b c u) }.
Arguments dtruth {T} _.
Arguments dmp {T} _ _ _ _ _.
Arguments drho8 {T} _ _ _ _ _ _.

(** Implementation details stay qualified; the public interface is DomImp and rho8_all. *)
Module Certificate.

Inductive expr := Z | V (i : nat) | I (a b : expr).
(** This is the only normalization used by the certificate. Its semantic law
    below proves that the native alias wim 0 0 = 0 is respected. *)
Definition imp a b := match a,b with Z,Z => Z | _,_ => I a b end.
Fixpoint eval (v : nat -> nat) (a : expr) : nat :=
  match a with Z => 0 | V i => v i | I b c => wim (eval v b) (eval v c) end.
Lemma eval_imp v a b : eval v (imp a b) = wim (eval v a) (eval v b).
Proof. destruct a,b; reflexivity. Qed.

Fixpoint eqb (a b : expr) : bool :=
  match a,b with
  | Z,Z => true | V i,V j => Nat.eqb i j
  | I a b,I c d => eqb a c && eqb b d
  | _,_ => false end.
Lemma eqb_sound a b : eqb a b = true -> a = b.
Proof.
 revert b; induction a; intros b H; destruct b; simpl in H; try discriminate; auto.
 - apply Nat.eqb_eq in H. now subst.
 - apply andb_true_iff in H as [H1 H2]. now rewrite (IHa1 _ H1), (IHa2 _ H2).
Qed.

Fixpoint subst (env : list expr) (a : expr) : expr :=
 match a with Z => Z | V i => nth i env Z | I b c => imp (subst env b) (subst env c) end.
Lemma eval_subst v env a : eval v (subst env a) = eval (fun i => eval v (nth i env Z)) a.
Proof. induction a; simpl; auto. now rewrite eval_imp, IHa1, IHa2. Qed.

Fixpoint subterm (u a : expr) : bool :=
 eqb u a || match a with I b c => subterm u b || subterm u c | _ => false end.
Definition dominated u a := eqb u Z || subterm u a.
Lemma subterm_sound u a : subterm u a = true -> forall v, eval v u <= eval v a.
Proof.
 induction a; simpl; intros H v; apply orb_true_iff in H as [H|H].
 - apply eqb_sound in H. subst; simpl; lia.
 - discriminate.
 - apply eqb_sound in H. subst; simpl; lia.
 - discriminate.
 - apply eqb_sound in H. subst; simpl; lia.
 - apply orb_true_iff in H as [H|H]; simpl.
   + specialize (IHa1 H v). unfold wim. pose proof (P_ge_l (eval v a1) (eval v a2)). lia.
   + specialize (IHa2 H v). unfold wim. pose proof (P_ge_r (eval v a1) (eval v a2)). lia.
Qed.
Lemma dominated_sound u a : dominated u a = true -> forall v, eval v u <= eval v a.
Proof.
 unfold dominated. intros H v. apply orb_true_iff in H as [H|H].
 - apply eqb_sound in H. subst; simpl; lia.
 - now apply subterm_sound.
Qed.
Local Opaque wim.
Definition rho a b c u := imp (imp (imp c u) a) (imp (imp a c) (imp b c)).
Lemma eval_rho v a b c u : eval v (rho a b c u) = rho8 (eval v a) (eval v b) (eval v c) (eval v u).
Proof. unfold rho, rho8. repeat rewrite eval_imp. reflexivity. Qed.

(** The term table is a DAG: references are backward distances. Out-of-range
    indices mean truth, so malformed input cannot introduce an assumption. *)
Inductive term := TZero | TVar (i : nat) | TImp (a b : nat).
Definition term_expr (seen : list expr) (t : term) :=
 match t with TZero => Z | TVar i => V i | TImp a b => I (nth a seen Z) (nth b seen Z) end.
Definition decode (ts : list term) : list expr :=
 fold_left (fun seen t => term_expr seen t :: seen) ts [].

Definition get (xs : list expr) (i : nat) := nth i xs Z.
Inductive rule := Truth | Ax (a b c u : nat) | MP (major minor : nat) | Inst (parent : nat) (env : list nat).
(** Every instruction is sound, including malformed ones: a rejected axiom or
    detachment returns truth. Hence checking the final symbolic result suffices. *)
Definition derive (ts seen : list expr) (r : rule) : expr :=
 match r with
 | Truth => Z
 | Ax a b c u =>
   if dominated (get ts u) (get ts a)
   then rho (get ts a) (get ts b) (get ts c) (get ts u) else Z
 | MP major minor =>
   match get seen major with
   | I a b => if eqb a (get seen minor) then b else Z
   | _ => Z end
 | Inst p env => subst (map (get ts) env) (get seen p)
 end.
Fixpoint run (ts : list expr) (steps : list rule) (seen : list expr) : list expr :=
 match steps with [] => seen | s :: ss => run ts ss (derive ts seen s :: seen) end.
Definition check ts steps goal := eqb (get (run ts steps []) 0) goal.

Section Soundness.
Variable T : nat -> Prop.
Variable h : DomImp T.
Definition valid a := forall v, T (eval v a).
Lemma valid_truth : valid Z.
Proof. intros v; apply (dtruth h). Qed.
Lemma get_valid xs i : Forall valid xs -> valid (get xs i).
Proof.
 unfold get; intros H; revert i. induction H; intros [|i]; simpl; auto using valid_truth.
Qed.
Lemma inst_valid env a : valid a -> valid (subst env a).
Proof. intros H v; rewrite eval_subst; apply H. Qed.
Lemma derive_sound ts seen r : Forall valid seen -> valid (derive ts seen r).
Proof.
 intros Hs; destruct r; cbn [derive].
 - apply valid_truth.
 - destruct (dominated (get ts u) (get ts a)) eqn:Hd; [|apply valid_truth].
   intros v. rewrite eval_rho. apply (drho8 h). now apply dominated_sound.
 - pose proof (get_valid seen major Hs) as Hmaj.
   destruct (get seen major) as [|i|a b]; try apply valid_truth.
   destruct (eqb a (get seen minor)) eqn:He; [|apply valid_truth].
   apply eqb_sound in He. intros v. specialize (Hmaj v). cbn [eval] in Hmaj.
   rewrite He in Hmaj. exact (dmp h _ _ Hmaj (get_valid seen minor Hs v)).
 - apply inst_valid. now apply get_valid.
Qed.
Lemma run_sound ts steps seen : Forall valid seen -> Forall valid (run ts steps seen).
Proof.
 revert seen. induction steps as [|s ss IH]; intros seen Hs; simpl; [exact Hs|].
 apply IH. constructor; [now apply derive_sound|exact Hs].
Qed.
Theorem check_sound ts steps goal : check ts steps goal = true -> valid goal.
Proof.
 unfold check; intros H; apply eqb_sound in H; rewrite <- H.
 apply get_valid. apply run_sound. constructor.
Qed.
End Soundness.
End Certificate.
Print Assumptions Certificate.check_sound.
