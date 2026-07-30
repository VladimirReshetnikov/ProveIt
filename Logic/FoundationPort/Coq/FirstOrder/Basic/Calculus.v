(**
  A one-sided classical sequent calculus for first-order NNF formulas.

  This begins the port of [Foundation/FirstOrder/Basic/Calculus.lean].  The
  primitive derivation stays in [Type], preserving proof data, and uses the
  duplicate-insensitive generic list inclusion shared by the audited
  one-sided calculus infrastructure.
*)

From Stdlib Require Import Arith.PeanoNat Lists.List Vectors.Fin.
From FoundationModal Require Import
  GenericAdjunctiveSet GenericCalculus GenericEntailment.
From Foundation.Syntax.Predicate Require Import Language Quantifier Term Rew.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition first_order_sequent (L : language) : Type := list (proposition L).

Definition first_order_sequent_shift {L}
    (Gamma : first_order_sequent L) : first_order_sequent L :=
  map semiformula_shift Gamma.

Definition first_order_sequent_language_map {L M}
    (h : language_hom L M) (Gamma : first_order_sequent L) :
    first_order_sequent M :=
  map (semiformula_language_map h) Gamma.

Lemma first_order_sequent_language_map_shift :
  forall L M (h : language_hom L M) (Gamma : first_order_sequent L),
    first_order_sequent_language_map h (first_order_sequent_shift Gamma) =
    first_order_sequent_shift (first_order_sequent_language_map h Gamma).
Proof.
  intros L M h Gamma. induction Gamma as [|p Gamma IH]; simpl.
  - reflexivity.
  - now rewrite semiformula_language_map_shift, IH.
Qed.

Definition first_order_sequent_rewrite {L}
    (f : nat -> syntactic_term L) (Gamma : first_order_sequent L) :
    first_order_sequent L :=
  map (semiformula_rewrite (rew_rewrite f)) Gamma.

Lemma first_order_sequent_rewrite_under_free_shift :
  forall L (f : nat -> syntactic_term L) (Gamma : first_order_sequent L),
    first_order_sequent_rewrite (rew_rewrite_under_free f)
      (first_order_sequent_shift Gamma) =
    first_order_sequent_shift (first_order_sequent_rewrite f Gamma).
Proof.
  intros L f Gamma. induction Gamma as [|p Gamma IH]; simpl.
  - reflexivity.
  - now rewrite semiformula_rewrite_under_free_shift, IH.
Qed.

(** Primitive LK rules.  Contraction includes exchange and weakening because
    [generic_list_subset] is pointwise list inclusion. *)
Inductive first_order_derivation (L : language) :
    first_order_sequent L -> Type :=
| FODIdentity : forall k (r : language_rel L k)
    (v : Fin.t k -> syntactic_term L),
    @first_order_derivation L
      [Semiformula_rel r v; Semiformula_nrel r v]
| FODCut : forall (p : proposition L) Gamma Delta,
    @first_order_derivation L (p :: Gamma) ->
    @first_order_derivation L (semiformula_neg p :: Delta) ->
    @first_order_derivation L (Gamma ++ Delta)
| FODContraction : forall Gamma Delta,
    @first_order_derivation L Gamma ->
    generic_list_subset Gamma Delta ->
    @first_order_derivation L Delta
| FODVerum : @first_order_derivation L [Semiformula_verum 0]
| FODOr : forall (p q : proposition L) Gamma,
    @first_order_derivation L (p :: q :: Gamma) ->
    @first_order_derivation L (Semiformula_or p q :: Gamma)
  | FODAnd : forall (p q : proposition L) Gamma,
    @first_order_derivation L (p :: Gamma) ->
    @first_order_derivation L (q :: Gamma) ->
    @first_order_derivation L (Semiformula_and p q :: Gamma)
| FODAll : forall (p : semiproposition L 1) Gamma,
    @first_order_derivation L
      (@semiformula_free L 0 p :: first_order_sequent_shift Gamma) ->
    @first_order_derivation L (Semiformula_all p :: Gamma)
| FODExists : forall (p : semiproposition L 1)
    (t : syntactic_term L) Gamma,
    @first_order_derivation L
      (semiformula_substitute (fun _ : Fin.t 1 => t) p :: Gamma) ->
    @first_order_derivation L (Semiformula_exists p :: Gamma).

Arguments first_order_derivation L Gamma : clear implicits.
Arguments FODIdentity {L k} _ _.
Arguments FODCut {L p Gamma Delta} _ _.
Arguments FODContraction {L Gamma Delta} _ _.
Arguments FODVerum {L}.
Arguments FODOr {L p q Gamma} _.
Arguments FODAnd {L p q Gamma} _ _.
Arguments FODAll {L p Gamma} _.
Arguments FODExists {L p t Gamma} _.

Fixpoint first_order_derivation_height {L Gamma}
    (d : first_order_derivation L Gamma) : nat :=
  match d with
  | FODIdentity _ _ => 0
  | FODCut dp dn =>
      S (Nat.max (first_order_derivation_height dp)
                 (first_order_derivation_height dn))
  | FODContraction d _ => S (first_order_derivation_height d)
  | FODVerum => 0
  | FODOr d => S (first_order_derivation_height d)
  | FODAnd dp dq =>
      S (Nat.max (first_order_derivation_height dp)
                 (first_order_derivation_height dq))
  | FODAll d => S (first_order_derivation_height d)
  | FODExists d => S (first_order_derivation_height d)
  end.

Definition first_order_derivation_cast {L Gamma Delta}
    (d : first_order_derivation L Gamma) (e : Gamma = Delta) :
    first_order_derivation L Delta :=
  generic_lk_cast (first_order_derivation L) d e.

Lemma first_order_derivation_height_cast :
  forall L Gamma Delta (d : first_order_derivation L Gamma)
         (e : Gamma = Delta),
    first_order_derivation_height (first_order_derivation_cast d e) =
    first_order_derivation_height d.
Proof. intros L Gamma Delta d e; destruct e; reflexivity. Qed.

Definition first_order_derivation_contra {L Gamma Delta}
    (d : first_order_derivation L Gamma)
    (H : generic_list_subset Gamma Delta) :
    first_order_derivation L Delta :=
  FODContraction d H.

Definition first_order_derivation_top {L Gamma}
    (Htop : generic_list_member (Semiformula_verum 0) Gamma) :
    first_order_derivation L Gamma.
Proof.
  apply (FODContraction FODVerum).
  intros p [Hp | Hp].
  - now subst p.
  - contradiction.
Defined.

Definition first_order_derivation_atomic_identity {L k}
    (r : language_rel L k) (v : Fin.t k -> syntactic_term L)
    (Gamma : first_order_sequent L)
    (Hpos : generic_list_member (Semiformula_rel r v) Gamma)
    (Hneg : generic_list_member (Semiformula_nrel r v) Gamma) :
    first_order_derivation L Gamma.
Proof.
  apply (FODContraction (FODIdentity r v)).
  intros p [Hp | [Hp | Hp]].
  - now subst p.
  - now subst p.
  - contradiction.
Defined.

Definition first_order_derivation_rotate {L p Gamma}
    (d : first_order_derivation L (p :: Gamma)) :
    first_order_derivation L (Gamma ++ [p]) :=
  FODContraction d (@generic_list_subset_rotate _ p Gamma).

Definition first_order_derivation_tensor {L p q Gamma Delta}
    (dp : first_order_derivation L (p :: Gamma))
    (dq : first_order_derivation L (q :: Delta)) :
    first_order_derivation L
      (Semiformula_and p q :: Gamma ++ Delta) :=
  FODAnd
    (FODContraction dp
      (@generic_list_subset_cons_append_right _ p Gamma Delta))
    (FODContraction dq
      (@generic_list_subset_cons_append_left _ q Gamma Delta)).

Fixpoint first_order_derivation_eta_rewrite {L X n}
    (p : semiformula L X n) (w : rew L X n nat 0) {struct p} :
    first_order_derivation L
      [semiformula_rewrite w p;
       semiformula_neg (semiformula_rewrite w p)].
Proof.
  revert w.
  destruct p as [n0 | n0 | n0 k r v | n0 k r v |
    n0 p q | n0 p q | n0 p | n0 p]; intro w.
  - apply first_order_derivation_top. now left.
  - apply first_order_derivation_top. right. now left.
  - exact (FODIdentity r (fun i => rew_apply w (v i))).
  - exact (first_order_derivation_rotate
      (FODIdentity r (fun i => rew_apply w (v i)))).
  - exact (first_order_derivation_rotate
      (FODOr
        (first_order_derivation_rotate
          (first_order_derivation_tensor
            (@first_order_derivation_eta_rewrite L X n0 p w)
            (@first_order_derivation_eta_rewrite L X n0 q w))))).
  - exact (FODOr
      (first_order_derivation_rotate
        (first_order_derivation_tensor
          (first_order_derivation_rotate
            (@first_order_derivation_eta_rewrite L X n0 p w))
          (first_order_derivation_rotate
            (@first_order_derivation_eta_rewrite L X n0 q w))))).
  - pose (body := semiformula_rewrite (rew_q w) p).
    pose (dfree_raw := @first_order_derivation_eta_rewrite L X (S n0) p
      (rew_comp (@rew_free L 0) (rew_q w))).
    assert (dfree : first_order_derivation L
      [@semiformula_free L 0 body;
       semiformula_neg (@semiformula_free L 0 body)]).
    { refine (first_order_derivation_cast dfree_raw _).
      unfold body. simpl. rewrite semiformula_rewrite_comp. reflexivity. }
    pose (dneg := first_order_derivation_rotate dfree).
    pose (dinstance := first_order_derivation_cast dneg
      (eq_trans
        (f_equal (fun x => [x; @semiformula_free L 0 body])
          (eq_sym
            (semiformula_substitute_neg_shift_one_eq_neg_free body)))
        eq_refl)).
    pose (dexists := FODExists dinstance).
    assert (dallpremise : first_order_derivation L
      [@semiformula_free L 0 body;
       semiformula_shift
         (Semiformula_exists (semiformula_neg body))]).
    { refine (first_order_derivation_cast
        (first_order_derivation_rotate dexists) _).
      simpl. f_equal.
      rewrite semiformula_shift_exists.
      unfold semiformula_shift. now rewrite semiformula_rewrite_neg. }
    exact (@FODAll L body
      [Semiformula_exists (semiformula_neg body)] dallpremise).
  - pose (body := semiformula_rewrite (rew_q w) p).
    pose (dfree_raw := @first_order_derivation_eta_rewrite L X (S n0) p
      (rew_comp (@rew_free L 0) (rew_q w))).
    assert (dfree : first_order_derivation L
      [@semiformula_free L 0 body;
       semiformula_neg (@semiformula_free L 0 body)]).
    { refine (first_order_derivation_cast dfree_raw _).
      unfold body. simpl. rewrite semiformula_rewrite_comp. reflexivity. }
    assert (dinstance : first_order_derivation L
      [semiformula_substitute
         (fun _ : Fin.t 1 => Semiterm_fvar 0)
         (semiformula_shift body);
       @semiformula_free L 0 (semiformula_neg body)]).
    { refine (first_order_derivation_cast dfree _).
      simpl. now rewrite semiformula_substitute_shift_one_eq_free,
        semiformula_free_neg. }
    pose (dexists := FODExists dinstance).
    assert (dallpremise : first_order_derivation L
      [@semiformula_free L 0 (semiformula_neg body);
       semiformula_shift (Semiformula_exists body)]).
    { refine (first_order_derivation_cast
        (first_order_derivation_rotate dexists) _).
      simpl. now rewrite semiformula_shift_exists. }
    exact (first_order_derivation_rotate
      (@FODAll L (semiformula_neg body)
        [Semiformula_exists body] dallpremise)).
Defined.

Definition first_order_derivation_eta {L} (p : proposition L) :
    first_order_derivation L [p; semiformula_neg p].
Proof.
  refine (first_order_derivation_cast
    (first_order_derivation_eta_rewrite p rew_id) _).
  now rewrite semiformula_rewrite_id.
Defined.

(** The first-order rules form the generic one-sided classical calculus.
    Keeping this dictionary explicit lets all generic structural and
    entailment constructions reuse the quantified identity expansion above. *)
Definition first_order_one_sided_lk (L : language) :
    generic_one_sided_lk (semiformula_connectives L nat 0)
      (first_order_derivation L).
Proof.
  constructor.
  - intro p. exact (first_order_derivation_eta p).
  - intros delta gamma d Hsub. exact (FODContraction d Hsub).
  - exact FODVerum.
  - intros p q gamma dp dq. exact (FODAnd dp dq).
  - intros p q gamma d. exact (FODOr d).
Defined.

Definition first_order_one_sided_lk_cut (L : language) :
    generic_one_sided_lk_cut (semiformula_connectives L nat 0)
      (first_order_derivation L).
Proof.
  constructor.
  - exact (first_order_one_sided_lk L).
  - intros p gamma delta dp dn. exact (FODCut dp dn).
Defined.

Definition first_order_sequent_is_closed {L}
    (Gamma : first_order_sequent L) : Prop :=
  exists p,
    generic_list_member p Gamma /\
    generic_list_member (semiformula_neg p) Gamma.

Definition first_order_derivation_close {L} (p : proposition L)
    {Gamma : first_order_sequent L}
    (Hp : generic_list_member p Gamma)
    (Hn : generic_list_member (semiformula_neg p) Gamma) :
    first_order_derivation L Gamma :=
  @generic_lk_close (proposition L) (semiformula_connectives L nat 0)
    (first_order_derivation L) (first_order_one_sided_lk L)
    p Gamma Hp Hn.

Definition first_order_derivation_of_is_closed {L}
    {Gamma : first_order_sequent L}
    (Hclosed : first_order_sequent_is_closed Gamma) :
    inhabited (first_order_derivation L Gamma).
Proof.
  destruct Hclosed as [p [Hp Hn]].
  exact (inhabits (@first_order_derivation_close L p Gamma Hp Hn)).
Defined.

(** The principal proof system has one marker and takes singleton LK
    derivations as its raw proofs, exactly matching the source presentation. *)
Inductive first_order_lk (L : language) : Type :=
| FirstOrderLK : first_order_lk L.

Arguments FirstOrderLK {L}.

Definition first_order_lk_entailment (L : language) :
    generic_entailment (first_order_lk L) (proposition L) :=
  {| generic_proof :=
       fun _ p => first_order_derivation L [p] |}.

Definition first_order_lk_principal (L : language) :
    generic_principal_entailment
      (first_order_lk_entailment L)
      (first_order_derivation L) FirstOrderLK.
Proof.
  constructor. intro p.
  refine {| generic_equiv_to := fun d => d;
            generic_equiv_from := fun d => d |}; reflexivity.
Defined.

Definition first_order_lk_provable {L} (p : proposition L) : Prop :=
  generic_provable (first_order_lk_entailment L) FirstOrderLK p.

Lemma first_order_lk_provable_iff : forall L (p : proposition L),
  first_order_lk_provable p <->
  inhabited (first_order_derivation L [p]).
Proof.
  intros L p.
  exact (@generic_principal_provable_iff
    (first_order_lk L) (proposition L)
    (first_order_lk_entailment L) (first_order_derivation L)
    FirstOrderLK (first_order_lk_principal L) p).
Qed.

Lemma first_order_lk_provable_cast : forall L (p q : proposition L),
  first_order_lk_provable p -> p = q -> first_order_lk_provable q.
Proof.
  intros L p q Hp Heq.
  exact (@generic_provable_cast
    (first_order_lk L) (proposition L)
    (first_order_lk_entailment L) FirstOrderLK p q Hp Heq).
Qed.

Definition first_order_lk_classical (L : language) :
    generic_classical_entailment
      (first_order_lk_entailment L)
      (semiformula_connectives L nat 0) FirstOrderLK.
Proof.
  refine (@generic_principal_classical
    (first_order_lk L) (proposition L)
    (first_order_lk_entailment L)
    (semiformula_connectives L nat 0)
    (first_order_derivation L) FirstOrderLK
    (first_order_lk_principal L)
    (@semiformula_neg_involutive L nat 0)
    eq_refl (fun _ _ => eq_refl)
    (fun _ _ => eq_refl) (fun _ _ => eq_refl)
    (first_order_one_sided_lk_cut L)).
Defined.

Definition first_order_lk_all {L} (p : semiproposition L 1)
    (Hp : first_order_lk_provable (@semiformula_free L 0 p)) :
    first_order_lk_provable (Semiformula_all p).
Proof.
  destruct Hp as [d]. constructor.
  exact (@FODAll L p [] d).
Defined.

Lemma first_order_lk_provable_all_fix_iter : forall L
    (p : proposition L),
  first_order_lk_provable p -> forall m,
  first_order_lk_provable
    (first_all_closure (semiformula_universal_quantifier L nat) m
      (semiformula_rewrite (@rew_fix_iter L 0 m) p)).
Proof.
  intros L p Hp m; induction m as [|m IH].
  - apply (first_order_lk_provable_cast Hp).
    symmetry. apply semiformula_rewrite_fix_iter_zero.
  - pose (closed :=
      first_all_closure (semiformula_universal_quantifier L nat) m
        (semiformula_rewrite (@rew_fix_iter L 0 m) p)).
    assert (Hfree : first_order_lk_provable
      (semiformula_free (semiformula_fix closed))).
    { apply (first_order_lk_provable_cast IH).
      unfold closed. symmetry. apply semiformula_free_fix. }
    pose proof (@first_order_lk_all L (semiformula_fix closed) Hfree) as Hall.
    apply (first_order_lk_provable_cast Hall).
    unfold closed. apply semiformula_all_fix_iter_closure_step.
Qed.

Definition first_order_lk_provable_universal_closure_open {L}
    (p : proposition L) (Hp : first_order_lk_provable p) :
    first_order_lk_provable (semiformula_universal_closure_open p) :=
  @first_order_lk_provable_all_fix_iter L p Hp
    (semiformula_free_bound p).

(** Closed sentences embed into propositions by the unique map out of the
    empty free-variable type. *)
Definition first_order_sentence_embed {L} (p : sentence L) : proposition L :=
  semiformula_rewrite
    (@rew_emb L Empty_set nat 0 (fun x => match x with end)) p.

Definition first_order_closed_term_embed {L} (t : closed_term L) :
    syntactic_term L :=
  rew_apply (@rew_emb L Empty_set nat 0 (fun x => match x with end)) t.

Lemma first_order_sentence_embed_substitute : forall L
    (p : semisentence L 1) (t : closed_term L),
  first_order_sentence_embed
      (semiformula_substitute (fun _ : Fin.t 1 => t) p) =
  semiformula_substitute
      (fun _ : Fin.t 1 => first_order_closed_term_embed t)
      (semiformula_rewrite
        (rew_q (@rew_emb L Empty_set nat 0
          (fun x => match x with end))) p).
Proof.
  intros L p t.
  unfold first_order_sentence_embed, first_order_closed_term_embed,
    semiformula_substitute.
  rewrite <- !semiformula_rewrite_comp.
  apply semiformula_rewrite_ext, rew_equiv_of_variables.
  - intro i. assert (Hi : i = Fin.F1) by apply fin_one_eq_f1.
    now subst i.
  - intro x. exact (match x with end).
Qed.

Definition first_order_sentence_embed_lk_hom (L : language) :
    generic_lk_connective_hom
      (semiformula_connectives L nat 0)
      (semiformula_connectives L Empty_set 0)
      (@first_order_sentence_embed L).
Proof.
  constructor.
  - reflexivity.
  - intro p. apply semiformula_rewrite_neg.
  - intros p q. reflexivity.
  - intros p q. reflexivity.
Qed.

Definition first_order_sentence_one_sided_lk (L : language) :
    generic_one_sided_lk (semiformula_connectives L Empty_set 0)
      (generic_lk_pullback (first_order_derivation L)
        (@first_order_sentence_embed L)) :=
  generic_lk_pullback_one_sided
    (first_order_sentence_embed_lk_hom L)
    (first_order_one_sided_lk L).

Definition first_order_sentence_one_sided_lk_cut (L : language) :
    generic_one_sided_lk_cut (semiformula_connectives L Empty_set 0)
      (generic_lk_pullback (first_order_derivation L)
        (@first_order_sentence_embed L)) :=
  generic_lk_pullback_cut
    (first_order_sentence_embed_lk_hom L)
    (first_order_one_sided_lk_cut L).

Definition first_order_sentence_lk_entailment (L : language) :=
  generic_pullback_entailment (first_order_lk_entailment L)
    (@first_order_sentence_embed L).

Definition first_order_sentence_lk_system (L : language) :=
  generic_pullback_of (@FirstOrderLK L) (@first_order_sentence_embed L).

Definition first_order_sentence_lk_principal (L : language) :
    generic_principal_entailment
      (first_order_sentence_lk_entailment L)
      (generic_lk_pullback (first_order_derivation L)
        (@first_order_sentence_embed L))
      (first_order_sentence_lk_system L) :=
  generic_lk_pullback_principal
    (@first_order_sentence_embed L) (first_order_lk_principal L).

(** A theory proof is exactly a finite axiom witness together with the
    pulled-back LK derivation of the conclusion against their negations. *)
Definition first_order_theory_proof {L}
    (T : theory L) (sigma : sentence L) : Type :=
  { w : generic_context_witness
      (generic_predicate_adjunctive_set (sentence L)) T &
    generic_lk_pullback (first_order_derivation L)
      (@first_order_sentence_embed L)
      (sigma :: map semiformula_neg
        (generic_context_witness_formulas w)) }.

Definition first_order_theory_entailment (L : language) :
    generic_entailment (theory L) (sentence L) :=
  {| generic_proof := first_order_theory_proof |}.

Definition first_order_theory_contextual (L : language) :
    generic_contextual_entailment
      (first_order_theory_entailment L)
      (generic_predicate_adjunctive_set (sentence L))
      semiformula_neg
      (generic_lk_pullback (first_order_derivation L)
        (@first_order_sentence_embed L)).
Proof.
  constructor. intros T sigma.
  refine {| generic_equiv_to := fun d => d;
            generic_equiv_from := fun d => d |}; reflexivity.
Defined.

Definition first_order_theory_provable {L}
    (T : theory L) (sigma : sentence L) : Prop :=
  generic_provable (first_order_theory_entailment L) T sigma.

Lemma first_order_theory_provable_iff : forall L
    (T : theory L) (sigma : sentence L),
  first_order_theory_provable T sigma <->
  exists Gamma : list (sentence L),
    (forall tau, generic_list_member tau Gamma -> T tau) /\
    inhabited
      (generic_lk_pullback (first_order_derivation L)
        (@first_order_sentence_embed L)
        (sigma :: map semiformula_neg Gamma)).
Proof.
  intros L T sigma.
  exact (@generic_contextual_provable_iff
    (theory L) (sentence L)
    (first_order_theory_entailment L)
    (generic_predicate_adjunctive_set (sentence L))
    semiformula_neg
    (generic_lk_pullback (first_order_derivation L)
      (@first_order_sentence_embed L))
    (first_order_theory_contextual L) T sigma).
Qed.

Lemma first_order_theory_inconsistent_iff : forall L (T : theory L),
  generic_inconsistent (first_order_theory_entailment L) T <->
  exists Gamma : list (sentence L),
    (forall tau, generic_list_member tau Gamma -> T tau) /\
    inhabited
      (generic_lk_pullback (first_order_derivation L)
        (@first_order_sentence_embed L)
        (map semiformula_neg Gamma)).
Proof.
  intros L T.
  exact (@generic_contextual_inconsistent_iff
    (theory L) (sentence L)
    (first_order_theory_entailment L)
    (generic_predicate_adjunctive_set (sentence L))
    (semiformula_connectives L Empty_set 0)
    (generic_lk_pullback (first_order_derivation L)
      (@first_order_sentence_embed L))
    (first_order_theory_contextual L) eq_refl
    (first_order_sentence_one_sided_lk_cut L) T).
Qed.

Lemma first_order_empty_theory_provable_iff : forall L
    (sigma : sentence L),
  first_order_theory_provable (fun _ => False) sigma <->
  generic_provable (first_order_sentence_lk_entailment L)
    (first_order_sentence_lk_system L) sigma.
Proof.
  intros L sigma.
  exact (generic_contextual_empty_provable_iff_principal
    (first_order_theory_entailment L)
    (first_order_sentence_lk_entailment L)
    (generic_predicate_adjunctive_set (sentence L))
    semiformula_neg
    (generic_lk_pullback (first_order_derivation L)
      (@first_order_sentence_embed L))
    (first_order_theory_contextual L)
    (first_order_sentence_lk_system L)
    (first_order_sentence_lk_principal L) sigma).
Qed.

Lemma first_order_theory_of_lk_provable : forall L
    (T : theory L) (sigma : sentence L),
  generic_provable (first_order_sentence_lk_entailment L)
    (first_order_sentence_lk_system L) sigma ->
  first_order_theory_provable T sigma.
Proof.
  intros L T sigma.
  exact (generic_contextual_of_principal_provable
    (first_order_theory_entailment L)
    (first_order_sentence_lk_entailment L)
    (generic_predicate_adjunctive_set (sentence L))
    semiformula_neg
    (generic_lk_pullback (first_order_derivation L)
      (@first_order_sentence_embed L))
    (first_order_theory_contextual L)
    (first_order_sentence_lk_system L)
    (first_order_sentence_lk_principal L) T sigma).
Qed.

Definition first_order_theory_specialize {L} (T : theory L)
    (p : semisentence L 1) (t : closed_term L) :
    first_order_theory_provable T
      (semiformula_imp (Semiformula_all p)
        (semiformula_substitute (fun _ : Fin.t 1 => t) p)).
Proof.
  apply first_order_theory_of_lk_provable. constructor.
  pose (body := semiformula_rewrite
    (rew_q (@rew_emb L Empty_set nat 0
      (fun x => match x with end))) p).
  pose (term := first_order_closed_term_embed t).
  pose (instance := semiformula_substitute
    (fun _ : Fin.t 1 => term) body).
  assert (dinstance : first_order_derivation L
    [semiformula_substitute
       (fun _ : Fin.t 1 => term) (semiformula_neg body);
     instance]).
  { refine (first_order_derivation_cast
      (first_order_derivation_rotate
        (first_order_derivation_eta instance)) _).
    unfold instance. simpl. f_equal.
    unfold semiformula_substitute.
    symmetry. apply semiformula_rewrite_neg. }
  pose (dexists := @FODExists L (semiformula_neg body) term
    [instance] dinstance).
  pose proof (@first_order_sentence_embed_substitute L p t) as Hsubst.
  unfold first_order_sentence_embed, first_order_closed_term_embed in Hsubst.
  refine (first_order_derivation_cast (FODOr dexists) _).
  unfold first_order_sentence_embed, semiformula_imp, body, instance, term.
  simpl. rewrite semiformula_rewrite_neg.
  rewrite Hsubst. reflexivity.
Defined.

Definition first_order_theory_axiomatized (L : language) :
    generic_axiomatized
      (first_order_theory_entailment L)
      (generic_predicate_adjunctive_set (sentence L)) :=
  @generic_contextual_axiomatized
    (theory L) (sentence L)
    (first_order_theory_entailment L)
    (generic_predicate_adjunctive_set (sentence L))
    (semiformula_connectives L Empty_set 0)
    (generic_lk_pullback (first_order_derivation L)
      (@first_order_sentence_embed L))
    (first_order_theory_contextual L)
    (first_order_sentence_one_sided_lk L).

Definition first_order_theory_compact (L : language) :
    generic_compact_entailment
      (first_order_theory_entailment L)
      (generic_predicate_adjunctive_set (sentence L)).
Proof.
  pose (core :=
    fun (T : theory L) (sigma : sentence L)
        (b : first_order_theory_proof T sigma) (tau : sentence L) =>
      generic_list_member tau
        (generic_context_witness_formulas (projT1 b))).
  refine (@Build_generic_compact_entailment
    (theory L) (sentence L) (first_order_theory_entailment L)
    (generic_predicate_adjunctive_set (sentence L)) core _ _ _).
  - intros T sigma [w d].
    refine (existT _
      (exist _ (generic_context_witness_formulas w) _) d).
    intros tau Htau. exact Htau.
  - intros T sigma [w d] tau Htau.
    exact (generic_context_witness_covers w tau Htau).
  - intros T sigma [w d].
    exists (generic_context_witness_formulas w).
    intros tau Htau. exact Htau.
Defined.

Lemma first_order_theory_weaker_of_subset : forall L
    (T U : theory L),
  (forall sigma, T sigma -> U sigma) ->
  generic_weaker_than
    (first_order_theory_entailment L)
    (first_order_theory_entailment L) T U.
Proof.
  intros L T U Hsub.
  exact (@generic_axiomatized_weaker_of_subset
    (theory L) (sentence L)
    (first_order_theory_entailment L)
    (generic_predicate_adjunctive_set (sentence L))
    (first_order_theory_axiomatized L) T U Hsub).
Qed.

Definition first_order_theory_classical {L} (T : theory L) :
    generic_classical_entailment
      (first_order_theory_entailment L)
      (semiformula_connectives L Empty_set 0) T.
Proof.
  refine (@generic_contextual_classical
    (theory L) (sentence L)
    (first_order_theory_entailment L)
    (generic_predicate_adjunctive_set (sentence L))
    (semiformula_connectives L Empty_set 0)
    (generic_lk_pullback (first_order_derivation L)
      (@first_order_sentence_embed L))
    (first_order_theory_contextual L)
    (@semiformula_neg_involutive L Empty_set 0)
    eq_refl (fun _ _ => eq_refl)
    (fun _ _ => eq_refl) (fun _ _ => eq_refl)
    (first_order_sentence_one_sided_lk_cut L) T).
Defined.

Definition first_order_theory_deduction (L : language) :
    generic_deduction
      (first_order_theory_entailment L)
      (semiformula_imp (L := L) (X := Empty_set) (n := 0))
      (generic_adjunctive_adjoin
        (generic_predicate_adjunctive_set (sentence L))).
Proof.
  refine (@generic_contextual_deduction
    (theory L) (sentence L)
    (first_order_theory_entailment L)
    (generic_predicate_adjunctive_set (sentence L))
    (semiformula_connectives L Empty_set 0)
    (generic_lk_pullback (first_order_derivation L)
      (@first_order_sentence_embed L))
    (first_order_theory_contextual L)
    (@semiformula_neg_involutive L Empty_set 0)
    (fun _ _ => eq_refl) (fun _ _ => eq_refl)
    (first_order_sentence_one_sided_lk_cut L)).
Defined.

Definition first_order_theory_closure {L} (T : theory L) : theory L :=
  fun sigma => first_order_theory_provable T sigma.

Lemma first_order_theory_closure_spec : forall L
    (T : theory L) (sigma : sentence L),
  first_order_theory_closure T sigma <->
  first_order_theory_provable T sigma.
Proof. reflexivity. Qed.

(** Every derivation is functorial in the underlying first-order language. *)
Fixpoint first_order_derivation_language_map {L M Gamma}
    (h : language_hom L M) (d : first_order_derivation L Gamma) {struct d} :
    first_order_derivation M (first_order_sequent_language_map h Gamma).
Proof.
  destruct d as [k r v | p Gamma Delta dp dn | Gamma Delta d Hsub |
    | p q Gamma d | p q Gamma dp dq | p Gamma d | p t Gamma d].
  - exact (FODIdentity (hom_rel h r)
      (fun i => semiterm_language_map h (v i))).
  - pose (dp' := @first_order_derivation_language_map L M _ h dp).
    pose (dn' := @first_order_derivation_language_map L M _ h dn).
    refine (first_order_derivation_cast
      (FODCut dp'
        (first_order_derivation_cast dn' _)) _).
    + simpl. now rewrite semiformula_language_map_neg.
    + unfold first_order_sequent_language_map. simpl.
      now rewrite List.map_app.
  - apply (FODContraction (@first_order_derivation_language_map L M _ h d)).
    now apply generic_list_map_subset.
  - exact FODVerum.
  - exact (FODOr (@first_order_derivation_language_map L M _ h d)).
  - exact (FODAnd (@first_order_derivation_language_map L M _ h dp)
                  (@first_order_derivation_language_map L M _ h dq)).
  - apply FODAll.
    refine (first_order_derivation_cast
      (@first_order_derivation_language_map L M _ h d) _).
    simpl. rewrite semiformula_language_map_free.
    now rewrite first_order_sequent_language_map_shift.
  - apply (FODExists (t := semiterm_language_map h t)).
    refine (first_order_derivation_cast
      (@first_order_derivation_language_map L M _ h d) _).
    simpl. now rewrite semiformula_language_map_substitute.
Defined.

Definition first_order_lk_provable_language_map {L M}
    (h : language_hom L M) (p : proposition L)
    (Hp : first_order_lk_provable p) :
    first_order_lk_provable (semiformula_language_map h p).
Proof.
  destruct Hp as [d]. constructor.
  exact (@first_order_derivation_language_map L M [p] h d).
Defined.

(** Simultaneously rewrite every free variable occurring in a derivation. *)
Fixpoint first_order_derivation_rewrite {L Gamma}
    (f : nat -> syntactic_term L) (d : first_order_derivation L Gamma)
    {struct d} :
    first_order_derivation L (first_order_sequent_rewrite f Gamma).
Proof.
  destruct d as [k r v | p Gamma Delta dp dn | Gamma Delta d Hsub |
    | p q Gamma d | p q Gamma dp dq | p Gamma d | p t Gamma d].
  - exact (FODIdentity r
      (fun i => rew_apply (rew_rewrite f) (v i))).
  - pose (dp' := @first_order_derivation_rewrite L _ f dp).
    pose (dn' := @first_order_derivation_rewrite L _ f dn).
    refine (first_order_derivation_cast
      (FODCut dp'
        (first_order_derivation_cast dn' _)) _).
    + simpl. now rewrite semiformula_rewrite_neg.
    + unfold first_order_sequent_rewrite. simpl.
      now rewrite List.map_app.
  - apply (FODContraction (@first_order_derivation_rewrite L _ f d)).
    now apply generic_list_map_subset.
  - exact FODVerum.
  - exact (FODOr (@first_order_derivation_rewrite L _ f d)).
  - exact (FODAnd (@first_order_derivation_rewrite L _ f dp)
                  (@first_order_derivation_rewrite L _ f dq)).
  - apply FODAll.
    refine (first_order_derivation_cast
      (@first_order_derivation_rewrite L _
        (rew_rewrite_under_free f) d) _).
    simpl. rewrite semiformula_rewrite_under_free_free.
    now rewrite first_order_sequent_rewrite_under_free_shift.
  - apply (FODExists
      (t := rew_apply (rew_rewrite f) t)).
    refine (first_order_derivation_cast
      (@first_order_derivation_rewrite L _ f d) _).
    simpl. now rewrite semiformula_rewrite_substitute_one.
Defined.

Definition first_order_derivation_map {L Gamma}
    (d : first_order_derivation L Gamma) (f : nat -> nat) :
    first_order_derivation L
      (first_order_sequent_rewrite
        (fun x => Semiterm_fvar (f x)) Gamma) :=
  first_order_derivation_rewrite (fun x => Semiterm_fvar (f x)) d.

Definition first_order_derivation_shift {L Gamma}
    (d : first_order_derivation L Gamma) :
    first_order_derivation L (first_order_sequent_shift Gamma) :=
  first_order_derivation_rewrite (fun x => Semiterm_fvar (S x)) d.

Definition first_order_fresh_map (m x : nat) : nat :=
  if Nat.eq_dec x m then 0 else S x.

Lemma semiformula_rewrite_map_substitute_fresh :
  forall L (p : semiproposition L 1) m,
    ~ semiformula_free_occurs m p ->
    semiformula_rewrite
      (rew_rewrite
        (fun x => Semiterm_fvar (first_order_fresh_map m x)))
      (semiformula_substitute
        (fun _ : Fin.t 1 => Semiterm_fvar m) p) =
    @semiformula_free L 0 p.
Proof.
  intros L p m Hfresh.
  unfold semiformula_substitute, semiformula_free.
  rewrite <- semiformula_rewrite_comp.
  apply semiformula_rewrite_ext_on_free.
  - intro i. assert (Hi : i = Fin.F1) by apply fin_one_eq_f1.
    subst i. cbn. unfold first_order_fresh_map.
    destruct (Nat.eq_dec m m); [reflexivity | contradiction].
  - intros x Hx. cbn.
    assert (Hxm : x <> m).
    { intro Heq. subst x. exact (Hfresh Hx). }
    unfold first_order_fresh_map.
    destruct (Nat.eq_dec x m); [contradiction | reflexivity].
Qed.

Lemma semiformula_rewrite_map_fresh_eq_shift :
  forall L (p : proposition L) m,
    ~ semiformula_free_occurs m p ->
    semiformula_rewrite
      (rew_rewrite
        (fun x => Semiterm_fvar (first_order_fresh_map m x))) p =
    semiformula_shift p.
Proof.
  intros L p m Hfresh. unfold semiformula_shift.
  apply semiformula_rewrite_ext_on_free.
  - intro i. exact (Fin.case0 (fun _ => _ = _) i).
  - intros x Hx. cbn.
    assert (Hxm : x <> m).
    { intro Heq. subst x. exact (Hfresh Hx). }
    unfold first_order_fresh_map.
    destruct (Nat.eq_dec x m); [contradiction | reflexivity].
Qed.

Lemma first_order_sequent_rewrite_map_fresh_eq_shift :
  forall L (Gamma : first_order_sequent L) m,
    (forall p, In p Gamma -> ~ semiformula_free_occurs m p) ->
    first_order_sequent_rewrite
      (fun x => Semiterm_fvar (first_order_fresh_map m x)) Gamma =
    first_order_sequent_shift Gamma.
Proof.
  intros L Gamma. induction Gamma as [|p Gamma IH]; intros m Hfresh; simpl.
  - reflexivity.
  - f_equal.
    + apply semiformula_rewrite_map_fresh_eq_shift.
      apply Hfresh. now left.
    + apply IH. intros q Hq. apply Hfresh. now right.
Qed.

(** Universal introduction from an instance at a genuinely fresh free
    variable.  No decidable equality on formulas or language symbols is
    required. *)
Definition first_order_derivation_generalize_fresh {L p m Gamma}
    (Hp : ~ semiformula_free_occurs m p)
    (HGamma : forall q, In q Gamma -> ~ semiformula_free_occurs m q)
    (d : first_order_derivation L
      (semiformula_substitute
        (fun _ : Fin.t 1 => Semiterm_fvar m) p :: Gamma)) :
    first_order_derivation L (Semiformula_all p :: Gamma).
Proof.
  apply FODAll.
  refine (first_order_derivation_cast
    (first_order_derivation_map d (first_order_fresh_map m)) _).
  simpl. f_equal.
  - apply semiformula_rewrite_map_substitute_fresh. exact Hp.
  - apply first_order_sequent_rewrite_map_fresh_eq_shift. exact HGamma.
Defined.

Definition first_order_sequent_new_variable {L}
    (Gamma : first_order_sequent L) : nat :=
  list_nat_max (map semiformula_fv_sup Gamma).

Lemma first_order_sequent_fv_sup_le_new_variable :
  forall L (Gamma : first_order_sequent L) p,
    In p Gamma ->
    semiformula_fv_sup p <= first_order_sequent_new_variable Gamma.
Proof.
  intros L Gamma p Hp. unfold first_order_sequent_new_variable.
  apply in_list_nat_max. now apply in_map.
Qed.

Lemma first_order_sequent_new_variable_fresh :
  forall L (Gamma : first_order_sequent L) p,
    In p Gamma ->
    ~ semiformula_free_occurs
      (first_order_sequent_new_variable Gamma) p.
Proof.
  intros L Gamma p Hp.
  apply semiformula_no_free_occurs_above_fv_sup.
  now apply first_order_sequent_fv_sup_le_new_variable.
Qed.

Lemma generic_list_member_of_list_in :
  forall (A : Type) (x : A) xs,
    In x xs -> generic_list_member x xs.
Proof.
  intros A x xs. induction xs as [|y ys IH]; simpl; [tauto |].
  intros [Hxy | Hx].
  - now left.
  - right. now apply IH.
Qed.

Definition first_order_derivation_all_new_variable {L p Gamma}
    (Hall : In (Semiformula_all p) Gamma)
    (d : first_order_derivation L
      (semiformula_substitute
        (fun _ : Fin.t 1 =>
          Semiterm_fvar (first_order_sequent_new_variable Gamma)) p
       :: Gamma)) :
    first_order_derivation L Gamma.
Proof.
  pose (m := first_order_sequent_new_variable Gamma).
  assert (Hp : ~ semiformula_free_occurs m p).
  { intro Hocc.
    apply (first_order_sequent_new_variable_fresh Hall).
    exact Hocc. }
  assert (HGamma : forall q, In q Gamma ->
      ~ semiformula_free_occurs m q).
  { intros q Hq. apply first_order_sequent_new_variable_fresh. exact Hq. }
  pose (dgeneral := first_order_derivation_generalize_fresh
    (m := m) (p := p) (Gamma := Gamma) Hp HGamma d).
  apply (FODContraction dgeneral). intros q [Hq | Hq].
  - subst q. now apply generic_list_member_of_list_in.
  - exact Hq.
Defined.

Lemma generic_list_subset_contract_head :
  forall (A : Type) (x : A) (xs : list A),
    generic_list_subset (x :: x :: xs) (x :: xs).
Proof.
  intros A x xs y [Hy | [Hy | Hy]].
  - now left.
  - now left.
  - now right.
Qed.

Lemma generic_list_subset_weaken_head :
  forall (A : Type) (x : A) (xs : list A),
    generic_list_subset xs (x :: xs).
Proof. intros A x xs y Hy. now right. Qed.

Fixpoint first_order_derivation_exists_of_instances {L}
    (ts : list (syntactic_term L)) (p : semiproposition L 1)
    (Gamma : first_order_sequent L)
    (d : first_order_derivation L
      (map (fun t => semiformula_substitute
        (fun _ : Fin.t 1 => t) p) ts ++ Gamma)) {struct ts} :
    first_order_derivation L (Semiformula_exists p :: Gamma).
Proof.
  destruct ts as [|t ts].
  - simpl in d. apply (FODContraction d).
    apply generic_list_subset_weaken_head.
  - simpl in d.
    pose (dexists := FODExists d).
    pose (drotated := FODContraction dexists
      (@generic_list_subset_rotate_across _
        (Semiformula_exists p)
        (map (fun u => semiformula_substitute
          (fun _ : Fin.t 1 => u) p) ts) Gamma)).
    pose (drest := @first_order_derivation_exists_of_instances L
      ts p (Semiformula_exists p :: Gamma) drotated).
    exact (FODContraction drest
      (@generic_list_subset_contract_head _
        (Semiformula_exists p) Gamma)).
Defined.

Definition first_order_derivation_exists_of_instances_present {L}
    (ts : list (syntactic_term L)) (p : semiproposition L 1)
    (Gamma : first_order_sequent L)
    (d : first_order_derivation L
      (Semiformula_exists p ::
       map (fun t => semiformula_substitute
         (fun _ : Fin.t 1 => t) p) ts ++ Gamma)) :
    first_order_derivation L (Semiformula_exists p :: Gamma).
Proof.
  pose (drotated := FODContraction d
    (@generic_list_subset_rotate_across _
      (Semiformula_exists p)
      (map (fun t => semiformula_substitute
        (fun _ : Fin.t 1 => t) p) ts) Gamma)).
  pose (dall := @first_order_derivation_exists_of_instances L
    ts p (Semiformula_exists p :: Gamma) drotated).
  exact (FODContraction dall
    (@generic_list_subset_contract_head _
      (Semiformula_exists p) Gamma)).
Defined.

Lemma first_order_derivation_height_identity :
  forall L k (r : language_rel L k) v,
    first_order_derivation_height (FODIdentity r v) = 0.
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_cut :
  forall L p Gamma Delta
         (dp : first_order_derivation L (p :: Gamma))
         (dn : first_order_derivation L (semiformula_neg p :: Delta)),
    first_order_derivation_height (FODCut dp dn) =
    S (Nat.max (first_order_derivation_height dp)
               (first_order_derivation_height dn)).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_contraction :
  forall L Gamma Delta (d : first_order_derivation L Gamma) H,
    first_order_derivation_height (@FODContraction L Gamma Delta d H) =
    S (first_order_derivation_height d).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_or :
  forall L p q Gamma (d : first_order_derivation L (p :: q :: Gamma)),
    first_order_derivation_height (FODOr d) =
    S (first_order_derivation_height d).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_and :
  forall L p q Gamma
         (dp : first_order_derivation L (p :: Gamma))
         (dq : first_order_derivation L (q :: Gamma)),
    first_order_derivation_height (FODAnd dp dq) =
    S (Nat.max (first_order_derivation_height dp)
               (first_order_derivation_height dq)).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_all :
  forall L (p : semiproposition L 1) Gamma
         (d : first_order_derivation L
           (@semiformula_free L 0 p :: first_order_sequent_shift Gamma)),
    first_order_derivation_height (FODAll d) =
    S (first_order_derivation_height d).
Proof. reflexivity. Qed.

Lemma first_order_derivation_height_exists :
  forall L (p : semiproposition L 1) t Gamma
         (d : first_order_derivation L
           (semiformula_substitute (fun _ : Fin.t 1 => t) p :: Gamma)),
    first_order_derivation_height (FODExists d) =
    S (first_order_derivation_height d).
Proof. reflexivity. Qed.
