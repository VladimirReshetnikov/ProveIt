(** Semantic soundness of the Type-valued first-order LK calculus. *)

From Stdlib Require Import Lists.List Vectors.Fin Logic.Classical
  Logic.FunctionalExtensionality.
From FoundationModal Require Import GenericAdjunctiveSet GenericCalculus.
From Foundation.Syntax.Predicate Require Import Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus Operator.
From Foundation.FirstOrder.Basic.Semantics Require Import
  Semantics RewriteClosure.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition first_order_empty_env {M : Type} : Fin.t 0 -> M :=
  fun i => match i with end.

Definition first_order_sequent_true {L M}
    (Str : first_order_structure L M) (f : nat -> M)
    (Gamma : first_order_sequent L) : Prop :=
  exists p, generic_list_member p Gamma /\ formula_eval Str f p.

Lemma fin_env_snoc_empty_eq_cons : forall M (a : M),
  fin_env_snoc (@first_order_empty_env M) a =
  fin_env_cons a first_order_empty_env.
Proof.
  intros. apply functional_extensionality. intro i.
  assert (Hi : i = Fin.F1) by apply fin_one_eq_f1.
  subst i.
  change (fin_env_snoc first_order_empty_env a (Fin.R 0 Fin.F1) = a).
  apply fin_env_snoc_right.
Qed.

Lemma first_order_shifted_context_true :
  forall L M (Str : first_order_structure L M) (f : nat -> M) a Gamma,
    first_order_sequent_true Str (nat_env_cons a f)
      (first_order_sequent_shift Gamma) ->
    first_order_sequent_true Str f Gamma.
Proof.
  intros L M Str f a Gamma [q [Hq Hval]].
  unfold first_order_sequent_shift in Hq.
  destruct (@generic_list_member_map_elim
    (proposition L) (proposition L) (@semiformula_shift L 0)
    q Gamma Hq) as [p [Hmem Hp]].
  subst q.
  exists p. split; [exact Hmem |].
  apply (proj1 (semiformula_eval_shift
    Str first_order_empty_env f a p)). exact Hval.
Qed.

Theorem first_order_derivation_sound :
  forall L Gamma (d : first_order_derivation L Gamma)
         M (Str : first_order_structure L M) (f : nat -> M),
    first_order_sequent_true Str f Gamma.
Proof.
  intros L Gamma d; induction d; intros M Str f.
  - destruct (classic (structure_rel Str r
      (fun i => semiterm_val Str first_order_empty_env f (v i)))) as [Hr | Hr].
    + exists (Semiformula_rel r v). split; [now left | exact Hr].
    + exists (Semiformula_nrel r v). split; [now right; left | exact Hr].
  - destruct (IHd1 M Str f) as [q [[Hq | Hq] Hval]].
    + subst q.
      destruct (IHd2 M Str f) as [q [[Hq | Hq] Hnval]].
      * subst q. apply (proj1 (semiformula_eval_neg
          Str first_order_empty_env f p)) in Hnval.
        contradiction.
      * exists q. split.
        -- apply (proj2 (generic_list_member_app_iff q Gamma Delta)).
           now right.
        -- exact Hnval.
    + exists q. split.
      * apply (proj2 (generic_list_member_app_iff q Gamma Delta)). now left.
      * exact Hval.
  - destruct (IHd M Str f) as [p [Hp Hval]].
    exists p. split; [now apply g | exact Hval].
  - exists (Semiformula_verum 0). split; [now left | constructor].
  - destruct (IHd M Str f) as [r [[Hr | [Hr | Hr]] Hval]].
    + subst r. exists (Semiformula_or p q). split; [now left | now left].
    + subst r. exists (Semiformula_or p q). split; [now left | now right].
    + exists r. split; [now right | exact Hval].
  - destruct (IHd1 M Str f) as [r [[Hr | Hr] Hval]].
    + subst r.
      destruct (IHd2 M Str f) as [r [[Hr | Hr] Hqval]].
      * subst r. exists (Semiformula_and p q).
        split; [now left | now split].
      * exists r. split; [now right | exact Hqval].
    + exists r. split; [now right | exact Hval].
  - destruct (classic (first_order_sequent_true Str f Gamma)) as [Hctx | Hctx].
    + destruct Hctx as [q [Hq Hval]].
      exists q. split; [now right | exact Hval].
    + exists (Semiformula_all p). split; [now left |].
      intro a.
      destruct (IHd M Str (nat_env_cons a f)) as
        [q [[Hq | Hq] Hval]].
      * subst q.
        apply (proj1 (semiformula_eval_free
          Str first_order_empty_env f a p)) in Hval.
        now rewrite fin_env_snoc_empty_eq_cons in Hval.
      * exfalso. apply Hctx.
        apply first_order_shifted_context_true with (a := a).
        exists q. now split.
  - destruct (IHd M Str f) as [q [[Hq | Hq] Hval]].
    + subst q. exists (Semiformula_exists p). split; [now left |].
      unfold formula_eval in Hval.
      apply (proj1 (@semiformula_eval_substitute
        L M nat 1 0 Str first_order_empty_env f
        (fun _ : Fin.t 1 => t) p)) in Hval.
      exists (semiterm_val Str first_order_empty_env f t).
      assert (Henv :
        (fun _ : Fin.t 1 => semiterm_val Str first_order_empty_env f t) =
        fin_env_cons (semiterm_val Str first_order_empty_env f t)
          first_order_empty_env).
      { apply functional_extensionality. intro i.
        assert (Hi : i = Fin.F1) by apply fin_one_eq_f1.
        now subst i. }
      rewrite Henv in Hval. exact Hval.
    + exists q. split; [now right | exact Hval].
Qed.

Corollary first_order_derivation_nil_empty :
  forall L, first_order_derivation L [] -> False.
Proof.
  intros L d.
  destruct (first_order_derivation_sound d
    (unit_first_order_structure L) (fun _ => tt)) as [p [Hp _]].
  contradiction.
Qed.
