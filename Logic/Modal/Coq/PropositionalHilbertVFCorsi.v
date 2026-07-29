(** Corsi proof algebra for Hilbert VF.

    This ports Foundation/Propositional/Entailment/Corsi/{Basic,VF}.  The
    source's finite-set conjunctions and disjunctions are replaced by folds
    over duplicate-tolerant lists, eliminating every decidable-equality
    premise while retaining the induction principles used by the Hintikka
    completeness construction.  Raw proof terms and their inhabited wrappers
    share the same small collection of rule combinators. *)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  PropositionalFormula PropositionalSlash PropositionalHilbertVF.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Basic Corsi combinators *)

Definition phvf_collect_or_and {Atom : Type}
    (p q r : pformula Atom) : pformula Atom :=
  PImp (PAnd (POr p q) (POr p r)) (POr p (PAnd q r)).

Definition phvf_iff {Atom : Type}
    (p q : pformula Atom) : pformula Atom :=
  PAnd (PImp p q) (PImp q p).

Definition phvf_proof_iff_identity {Atom : Type}
    {H : phvf_hilbert Atom} {p : pformula Atom} :
    phvf_proof H (phvf_iff p p) :=
  PHVFPAndRule (PHVFPIdentity p) (PHVFPIdentity p).

Definition phvf_proof_and_comm {Atom : Type} {H : phvf_hilbert Atom}
    {p q : pformula Atom} :
    phvf_proof H (PImp (PAnd p q) (PAnd q p)) :=
  PHVFPRuleC (PHVFPAndElimR p q) (PHVFPAndElimL p q).

Definition phvf_proof_or_comm {Atom : Type} {H : phvf_hilbert Atom}
    {p q : pformula Atom} :
    phvf_proof H (PImp (POr p q) (POr q p)) :=
  PHVFPRuleD (PHVFPOrIntroR q p) (PHVFPOrIntroL q p).

Definition phvf_proof_and_right_cancel {Atom : Type}
    {H : phvf_hilbert Atom} {p q r : pformula Atom}
    (Hpqr : phvf_proof H (PImp (PAnd p q) r))
    (Hq : phvf_proof H q) :
    phvf_proof H (PImp p r) :=
  PHVFPRuleI
    (PHVFPRuleC (PHVFPIdentity p) (PHVFPFortiori p Hq)) Hpqr.

Definition phvf_proof_and_right_replace {Atom : Type}
    {H : phvf_hilbert Atom} {p q q' r : pformula Atom}
    (Hpqr : phvf_proof H (PImp (PAnd p q) r))
    (Hq'q : phvf_proof H (PImp q' q)) :
    phvf_proof H (PImp (PAnd p q') r) :=
  PHVFPRuleI
    (PHVFPRuleC (PHVFPAndElimL p q')
      (PHVFPRuleI (PHVFPAndElimR p q') Hq'q)) Hpqr.

Definition phvf_proof_collect_or_and {Atom : Type}
    {H : phvf_hilbert Atom} {p q r : pformula Atom} :
    phvf_proof H (phvf_collect_or_and p q r).
Proof.
  refine (PHVFPRuleI (PHVFPDistributeAndOr (POr p q) p r) _).
  apply PHVFPRuleD.
  - exact (PHVFPRuleI (PHVFPAndElimR (POr p q) p)
      (PHVFPOrIntroL p (PAnd q r))).
  - refine (PHVFPRuleI phvf_proof_and_comm _).
    refine (PHVFPRuleI (PHVFPDistributeAndOr r p q) _).
    apply PHVFPRuleD.
    + exact (PHVFPRuleI (PHVFPAndElimR r p)
        (PHVFPOrIntroL p (PAnd q r))).
    + exact (PHVFPRuleI phvf_proof_and_comm
        (PHVFPOrIntroR p (PAnd q r))).
Defined.

Definition phvf_proof_or_replace_both {Atom : Type}
    {H : phvf_hilbert Atom} {p p' q q' : pformula Atom}
    (Hpp' : phvf_proof H (PImp p p'))
    (Hqq' : phvf_proof H (PImp q q')) :
    phvf_proof H (PImp (POr p q) (POr p' q')) :=
  PHVFPRuleD
    (PHVFPRuleI Hpp' (PHVFPOrIntroL p' q'))
    (PHVFPRuleI Hqq' (PHVFPOrIntroR p' q')).

Definition phvf_proof_or_replace_left {Atom : Type}
    {H : phvf_hilbert Atom} {p p' q : pformula Atom}
    (Hpp' : phvf_proof H (PImp p p')) :
    phvf_proof H (PImp (POr p q) (POr p' q)) :=
  phvf_proof_or_replace_both Hpp' (PHVFPIdentity q).

Definition phvf_proof_or_replace_right {Atom : Type}
    {H : phvf_hilbert Atom} {p q q' : pformula Atom}
    (Hqq' : phvf_proof H (PImp q q')) :
    phvf_proof H (PImp (POr p q) (POr p q')) :=
  phvf_proof_or_replace_both (PHVFPIdentity p) Hqq'.

Definition phvf_proof_imp_replace_both {Atom : Type}
    {H : phvf_hilbert Atom} {p p' q q' : pformula Atom}
    (Hpq : phvf_proof H (PImp p q))
    (Hp'p : phvf_proof H (PImp p' p))
    (Hqq' : phvf_proof H (PImp q q')) :
    phvf_proof H (PImp p' q') :=
  PHVFPRuleI Hp'p (PHVFPRuleI Hpq Hqq').

Definition phvf_proof_and_right_covariant {Atom : Type}
    {H : phvf_hilbert Atom} {p q q' : pformula Atom}
    (Hqq' : phvf_proof H (PImp q q')) :
    phvf_proof H (PImp (PAnd p q) (PAnd p q')) :=
  PHVFPRuleC (PHVFPAndElimL p q)
    (PHVFPRuleI (PHVFPAndElimR p q) Hqq').

Lemma phvf_provable_collect_or_and :
  forall (Atom : Type) (H : phvf_hilbert Atom) p q r,
    phvf_provable H (phvf_collect_or_and p q r).
Proof. intros; constructor; apply phvf_proof_collect_or_and. Qed.

Lemma phvf_provable_iff_identity :
  forall (Atom : Type) (H : phvf_hilbert Atom) p,
    phvf_provable H (phvf_iff p p).
Proof. intros; constructor; apply phvf_proof_iff_identity. Qed.

Lemma phvf_provable_and_comm :
  forall (Atom : Type) (H : phvf_hilbert Atom) p q,
    phvf_provable H (PImp (PAnd p q) (PAnd q p)).
Proof. intros; constructor; apply phvf_proof_and_comm. Qed.

Lemma phvf_provable_or_comm :
  forall (Atom : Type) (H : phvf_hilbert Atom) p q,
    phvf_provable H (PImp (POr p q) (POr q p)).
Proof. intros; constructor; apply phvf_proof_or_comm. Qed.

Lemma phvf_provable_and_right_cancel :
  forall (Atom : Type) (H : phvf_hilbert Atom) p q r,
    phvf_provable H (PImp (PAnd p q) r) ->
    phvf_provable H q -> phvf_provable H (PImp p r).
Proof.
  intros Atom H p q r [Hpqr] [Hq]; constructor.
  exact (phvf_proof_and_right_cancel Hpqr Hq).
Qed.

Lemma phvf_provable_and_right_replace :
  forall (Atom : Type) (H : phvf_hilbert Atom) p q q' r,
    phvf_provable H (PImp (PAnd p q) r) ->
    phvf_provable H (PImp q' q) ->
    phvf_provable H (PImp (PAnd p q') r).
Proof.
  intros Atom H p q q' r [Hpqr] [Hq'q]; constructor.
  exact (phvf_proof_and_right_replace Hpqr Hq'q).
Qed.

Lemma phvf_provable_or_replace_both :
  forall (Atom : Type) (H : phvf_hilbert Atom) p p' q q',
    phvf_provable H (PImp p p') ->
    phvf_provable H (PImp q q') ->
    phvf_provable H (PImp (POr p q) (POr p' q')).
Proof.
  intros Atom H p p' q q' [Hpp'] [Hqq']; constructor.
  exact (phvf_proof_or_replace_both Hpp' Hqq').
Qed.

Lemma phvf_provable_imp_replace_both :
  forall (Atom : Type) (H : phvf_hilbert Atom) p p' q q',
    phvf_provable H (PImp p q) ->
    phvf_provable H (PImp p' p) ->
    phvf_provable H (PImp q q') ->
    phvf_provable H (PImp p' q').
Proof.
  intros Atom H p p' q q' [Hpq] [Hp'p] [Hqq']; constructor.
  exact (phvf_proof_imp_replace_both Hpq Hp'p Hqq').
Qed.

Lemma phvf_provable_or_replace_left :
  forall (Atom : Type) (H : phvf_hilbert Atom) p p' q,
    phvf_provable H (PImp p p') ->
    phvf_provable H (PImp (POr p q) (POr p' q)).
Proof.
  intros Atom H p p' q [Hpp']; constructor.
  exact (phvf_proof_or_replace_left Hpp').
Qed.

Lemma phvf_provable_or_replace_right :
  forall (Atom : Type) (H : phvf_hilbert Atom) p q q',
    phvf_provable H (PImp q q') ->
    phvf_provable H (PImp (POr p q) (POr p q')).
Proof.
  intros Atom H p q q' [Hqq']; constructor.
  exact (phvf_proof_or_replace_right Hqq').
Qed.

Lemma phvf_provable_and_right_covariant :
  forall (Atom : Type) (H : phvf_hilbert Atom) p q q',
    phvf_provable H (PImp q q') ->
    phvf_provable H (PImp (PAnd p q) (PAnd p q')).
Proof.
  intros Atom H p q q' [Hqq']; constructor.
  exact (phvf_proof_and_right_covariant Hqq').
Qed.

Lemma phvf_consistent_not_bottom :
  forall (Atom : Type) (H : phvf_hilbert Atom),
    phvf_consistent H -> ~ phvf_provable H PFalsum.
Proof. exact (fun _ _ Hconsistent => Hconsistent). Qed.

(** * Equality-free finite conjunctions and disjunctions *)

Fixpoint phvf_list_conj {Atom : Type}
    (Gamma : list (pformula Atom)) : pformula Atom :=
  match Gamma with
  | [] => ptop
  | p :: Delta => PAnd p (phvf_list_conj Delta)
  end.

Fixpoint phvf_list_disj {Atom : Type}
    (Gamma : list (pformula Atom)) : pformula Atom :=
  match Gamma with
  | [] => PFalsum
  | p :: Delta => POr p (phvf_list_disj Delta)
  end.

(** Raw Hilbert derivations live in [Type], so their positional witnesses do
    too.  The proposition-level API below continues to expose ordinary
    [List.In]. *)
Inductive phvf_list_member {A : Type} (x : A) : list A -> Type :=
| PHVFListHere : forall xs, phvf_list_member x (x :: xs)
| PHVFListThere : forall y xs,
    phvf_list_member x xs -> phvf_list_member x (y :: xs).

Arguments PHVFListHere {A x} xs.
Arguments PHVFListThere {A x} y xs _.

Fixpoint phvf_proof_list_conj_intro {Atom : Type}
    {H : phvf_hilbert Atom} (p : pformula Atom)
    (Gamma : list (pformula Atom)) :
    (forall q, phvf_list_member q Gamma -> phvf_proof H (PImp p q)) ->
    phvf_proof H (PImp p (phvf_list_conj Gamma)).
Proof.
  destruct Gamma as [|q Delta].
  - intros _. exact (PHVFPFortiori p (PHVFPIdentity PFalsum)).
  - intro Hall. cbn. apply PHVFPRuleC.
    + exact (Hall q (PHVFListHere Delta)).
    + apply phvf_proof_list_conj_intro. intros r Hr.
      exact (Hall r (PHVFListThere q Delta Hr)).
Defined.

Fixpoint phvf_proof_list_conj_member {Atom : Type}
    {H : phvf_hilbert Atom} (Gamma : list (pformula Atom))
    (p : pformula Atom) :
    phvf_list_member p Gamma ->
    phvf_proof H (PImp (phvf_list_conj Gamma) p).
Proof.
  destruct Gamma as [|q Delta].
  - intro Hin. inversion Hin.
  - intro Hin. inversion Hin; subst.
    + cbn. apply PHVFPAndElimL.
    + cbn. exact (PHVFPRuleI (PHVFPAndElimR q (phvf_list_conj Delta))
        (@phvf_proof_list_conj_member Atom H Delta p X)).
Defined.

Definition phvf_proof_list_conj_subset {Atom : Type}
    {H : phvf_hilbert Atom}
    (Gamma Delta : list (pformula Atom))
    (Hsub : forall p,
      phvf_list_member p Delta -> phvf_list_member p Gamma) :
    phvf_proof H (PImp (phvf_list_conj Gamma) (phvf_list_conj Delta)) :=
  @phvf_proof_list_conj_intro Atom H (phvf_list_conj Gamma) Delta
    (fun p Hp => @phvf_proof_list_conj_member Atom H Gamma p (Hsub p Hp)).

Definition phvf_proof_list_conj_cons {Atom : Type}
    {H : phvf_hilbert Atom} (p : pformula Atom)
    (Gamma : list (pformula Atom)) :
    phvf_proof H
      (PImp (PAnd p (phvf_list_conj Gamma))
        (phvf_list_conj (p :: Gamma))) :=
  PHVFPIdentity (PAnd p (phvf_list_conj Gamma)).

Fixpoint phvf_proof_list_disj_member {Atom : Type}
    {H : phvf_hilbert Atom} (Gamma : list (pformula Atom))
    (p : pformula Atom) :
    phvf_list_member p Gamma ->
    phvf_proof H (PImp p (phvf_list_disj Gamma)).
Proof.
  destruct Gamma as [|q Delta].
  - intro Hin. inversion Hin.
  - intro Hin. inversion Hin; subst.
    + cbn. apply PHVFPOrIntroL.
    + cbn. exact (PHVFPRuleI
        (@phvf_proof_list_disj_member Atom H Delta p X)
        (PHVFPOrIntroR q (phvf_list_disj Delta))).
Defined.

Fixpoint phvf_proof_list_disj_elim {Atom : Type}
    {H : phvf_hilbert Atom} (p : pformula Atom)
    (Gamma : list (pformula Atom)) :
    (forall q, phvf_list_member q Gamma -> phvf_proof H (PImp q p)) ->
    phvf_proof H (PImp (phvf_list_disj Gamma) p).
Proof.
  destruct Gamma as [|q Delta].
  - intros _. apply PHVFPEfq.
  - intro Hall. cbn. apply PHVFPRuleD.
    + exact (Hall q (PHVFListHere Delta)).
    + apply phvf_proof_list_disj_elim. intros r Hr.
      exact (Hall r (PHVFListThere q Delta Hr)).
Defined.

Lemma phvf_provable_list_conj_intro :
  forall (Atom : Type) (H : phvf_hilbert Atom) p Gamma,
    (forall q, In q Gamma -> phvf_provable H (PImp p q)) ->
    phvf_provable H (PImp p (phvf_list_conj Gamma)).
Proof.
  intros Atom H p Gamma. induction Gamma as [|q Delta IH]; intro Hall.
  - constructor. exact (PHVFPFortiori p (PHVFPIdentity PFalsum)).
  - destruct (Hall q (or_introl eq_refl)) as [Hq].
    destruct (IH (fun r Hr => Hall r (or_intror Hr))) as [HDelta].
    constructor. exact (PHVFPRuleC Hq HDelta).
Qed.

Lemma phvf_provable_list_conj_member :
  forall (Atom : Type) (H : phvf_hilbert Atom) Gamma p,
    In p Gamma ->
    phvf_provable H (PImp (phvf_list_conj Gamma) p).
Proof.
  intros Atom H Gamma. induction Gamma as [|q Delta IH]; intros p Hin.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + constructor. apply PHVFPAndElimL.
    + destruct (IH p Hin) as [Hp]. constructor.
      exact (PHVFPRuleI (PHVFPAndElimR q (phvf_list_conj Delta)) Hp).
Qed.

Lemma phvf_provable_list_conj_subset :
  forall (Atom : Type) (H : phvf_hilbert Atom) Gamma Delta,
    (forall p, In p Delta -> In p Gamma) ->
    phvf_provable H
      (PImp (phvf_list_conj Gamma) (phvf_list_conj Delta)).
Proof.
  intros Atom H Gamma Delta Hsub.
  apply phvf_provable_list_conj_intro. intros p Hp.
  apply phvf_provable_list_conj_member, Hsub, Hp.
Qed.

Lemma phvf_provable_list_conj_cons :
  forall (Atom : Type) (H : phvf_hilbert Atom) p Gamma,
    phvf_provable H
      (PImp (PAnd p (phvf_list_conj Gamma))
        (phvf_list_conj (p :: Gamma))).
Proof. intros; constructor; apply phvf_proof_list_conj_cons. Qed.

Lemma phvf_provable_list_disj_member :
  forall (Atom : Type) (H : phvf_hilbert Atom) Gamma p,
    In p Gamma ->
    phvf_provable H (PImp p (phvf_list_disj Gamma)).
Proof.
  intros Atom H Gamma. induction Gamma as [|q Delta IH]; intros p Hin.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + constructor. apply PHVFPOrIntroL.
    + destruct (IH p Hin) as [Hp]. constructor.
      exact (PHVFPRuleI Hp (PHVFPOrIntroR q (phvf_list_disj Delta))).
Qed.

Lemma phvf_provable_list_disj_elim :
  forall (Atom : Type) (H : phvf_hilbert Atom) p Gamma,
    (forall q, In q Gamma -> phvf_provable H (PImp q p)) ->
    phvf_provable H (PImp (phvf_list_disj Gamma) p).
Proof.
  intros Atom H p Gamma. induction Gamma as [|q Delta IH]; intro Hall.
  - constructor. apply PHVFPEfq.
  - destruct (Hall q (or_introl eq_refl)) as [Hq].
    destruct (IH (fun r Hr => Hall r (or_intror Hr))) as [HDelta].
    constructor. exact (PHVFPRuleD Hq HDelta).
Qed.

Theorem phvf_provable_list_disjunct :
  forall (Atom : Type) (H : phvf_hilbert Atom),
    phvf_consistent H ->
    pformula_predicate_disjunctive (phvf_provable H) ->
    forall Gamma,
      phvf_provable H (phvf_list_disj Gamma) ->
      exists p, In p Gamma /\ phvf_provable H p.
Proof.
  intros Atom H Hconsistent Hdisj Gamma.
  induction Gamma as [|p Delta IH]; cbn.
  - intro Hbot. contradiction.
  - intro Hor. destruct (Hdisj p (phvf_list_disj Delta) Hor) as [Hp | HDelta].
    + exists p. split; [now left | exact Hp].
    + destruct (IH HDelta) as [q [Hq Hprov]].
      exists q. split; [now right | exact Hprov].
Qed.
