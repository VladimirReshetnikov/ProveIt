(**
  Alternative finite-context presentation of first-order LK.

  This ports
  [Foundation/FirstOrder/Basic/Calculus2.lean].  Foundation uses finsets and
  consequently assumes decidable formula equality.  Coq instead reuses the
  duplicate-insensitive list membership relation from the generic calculus:
  contexts have the same set-like rules, but neither the syntax nor the
  translations require an equality decision.  Both presentations are proved
  equivalent to the existing finite-support theory calculus.
*)

From Stdlib Require Import Lists.List Vectors.Fin.
From FoundationModal Require Import GenericAdjunctiveSet GenericCalculus.
From Foundation.Syntax.Predicate Require Import Language Rew Term.
From Foundation.FirstOrder.Basic.Syntax Require Import Formula.
From Foundation.FirstOrder.Basic Require Import Calculus.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** Set-style rules over duplicate-tolerant finite list contexts. *)
Inductive first_order_derivation2 (L : language) (T : theory L) :
    first_order_sequent L -> Type :=
| FOD2Closed : forall Gamma (p : proposition L),
    generic_list_member p Gamma ->
    generic_list_member (semiformula_neg p) Gamma ->
    @first_order_derivation2 L T Gamma
| FOD2Axiom : forall Gamma (sigma : sentence L),
    T sigma ->
    generic_list_member (first_order_sentence_embed sigma) Gamma ->
    @first_order_derivation2 L T Gamma
| FOD2Verum : forall Gamma,
    generic_list_member (Semiformula_verum 0) Gamma ->
    @first_order_derivation2 L T Gamma
| FOD2And : forall Gamma (p q : proposition L),
    generic_list_member (Semiformula_and p q) Gamma ->
    @first_order_derivation2 L T (p :: Gamma) ->
    @first_order_derivation2 L T (q :: Gamma) ->
    @first_order_derivation2 L T Gamma
| FOD2Or : forall Gamma (p q : proposition L),
    generic_list_member (Semiformula_or p q) Gamma ->
    @first_order_derivation2 L T (p :: q :: Gamma) ->
    @first_order_derivation2 L T Gamma
| FOD2All : forall Gamma (p : semiproposition L 1),
    generic_list_member (Semiformula_all p) Gamma ->
    @first_order_derivation2 L T
      (@semiformula_free L 0 p :: first_order_sequent_shift Gamma) ->
    @first_order_derivation2 L T Gamma
| FOD2Exists : forall Gamma (p : semiproposition L 1),
    generic_list_member (Semiformula_exists p) Gamma ->
    forall t : syntactic_term L,
    @first_order_derivation2 L T
      (semiformula_substitute (fun _ : Fin.t 1 => t) p :: Gamma) ->
    @first_order_derivation2 L T Gamma
| FOD2Weakening : forall Delta Gamma,
    @first_order_derivation2 L T Delta ->
    generic_list_subset Delta Gamma ->
    @first_order_derivation2 L T Gamma
| FOD2Shift : forall Gamma,
    @first_order_derivation2 L T Gamma ->
    @first_order_derivation2 L T (first_order_sequent_shift Gamma)
| FOD2Cut : forall Gamma (p : proposition L),
    @first_order_derivation2 L T (p :: Gamma) ->
    @first_order_derivation2 L T (semiformula_neg p :: Gamma) ->
    @first_order_derivation2 L T Gamma.

Arguments first_order_derivation2 L T Gamma : clear implicits.
Arguments FOD2Closed {L T Gamma} p _ _.
Arguments FOD2Axiom {L T Gamma} sigma _ _.
Arguments FOD2Verum {L T Gamma} _.
Arguments FOD2And {L T Gamma p q} _ _ _.
Arguments FOD2Or {L T Gamma p q} _ _.
Arguments FOD2All {L T Gamma p} _ _.
Arguments FOD2Exists {L T Gamma p} _ t _.
Arguments FOD2Weakening {L T Delta Gamma} _ _.
Arguments FOD2Shift {L T Gamma} _.
Arguments FOD2Cut {L T Gamma p} _ _.

Definition first_order_derivable2 {L}
    (T : theory L) (Gamma : first_order_sequent L) : Prop :=
  inhabited (first_order_derivation2 L T Gamma).

Definition first_order_derivation2_cast {L T Gamma Delta}
    (d : first_order_derivation2 L T Gamma) (e : Gamma = Delta) :
    first_order_derivation2 L T Delta :=
  match e with
  | eq_refl => d
  end.

(** Every ordinary LK derivation is an alternative derivation over any
    ambient theory.  No formula equality or theory membership is used. *)
Fixpoint first_order_derivation_to_derivation2 {L T Gamma}
    (d : first_order_derivation L Gamma) {struct d} :
    first_order_derivation2 L T Gamma.
Proof.
  destruct d as [k r v | p Gamma Delta dp dn | Gamma Delta d Hsub |
    | p q Gamma d | p q Gamma dp dq | p Gamma d | p t Gamma d].
  - apply (FOD2Closed (Semiformula_rel r v));
      [now left | now right; left].
  - apply (FOD2Cut (p := p)).
    + apply (FOD2Weakening
        (@first_order_derivation_to_derivation2 L T _ dp)).
      exact (@generic_list_subset_cons_append_right
        (proposition L) p Gamma Delta).
    + apply (FOD2Weakening
        (@first_order_derivation_to_derivation2 L T _ dn)).
      exact (@generic_list_subset_cons_append_left
        (proposition L) (semiformula_neg p) Gamma Delta).
  - exact (FOD2Weakening
      (@first_order_derivation_to_derivation2 L T _ d) Hsub).
  - apply FOD2Verum. now left.
  - apply (FOD2Or (p := p) (q := q)); [now left |].
    apply (FOD2Weakening
      (@first_order_derivation_to_derivation2 L T _ d)).
    intros x [Hx | [Hx | Hx]].
    + now left.
    + right. now left.
    + right. right. now right.
  - apply (FOD2And (p := p) (q := q)); [now left | |].
    + apply (FOD2Weakening
        (@first_order_derivation_to_derivation2 L T _ dp)).
      intros x [Hx | Hx]; [now left | right; now right].
    + apply (FOD2Weakening
        (@first_order_derivation_to_derivation2 L T _ dq)).
      intros x [Hx | Hx]; [now left | right; now right].
  - apply (FOD2All (p := p)); [now left |].
    apply (FOD2Weakening
      (@first_order_derivation_to_derivation2 L T _ d)).
    intros x [Hx | Hx]; [now left |].
    right. simpl. now right.
  - refine (@FOD2Exists L T (Semiformula_exists p :: Gamma) p
      (or_introl eq_refl) t _).
    apply (FOD2Weakening
      (@first_order_derivation_to_derivation2 L T _ d)).
    intros x [Hx | Hx]; [now left | right; now right].
Defined.

(** Negated embeddings of the finite theory support carried by an ordinary
    LK derivation. *)
Definition first_order_axiom_suffix {L} (A : list (sentence L)) :
    first_order_sequent L :=
  map semiformula_neg (map first_order_sentence_embed A).

Lemma first_order_axiom_suffix_app : forall L
    (A B : list (sentence L)),
  first_order_axiom_suffix (A ++ B) =
  first_order_axiom_suffix A ++ first_order_axiom_suffix B.
Proof.
  intros L A B. unfold first_order_axiom_suffix.
  now rewrite !List.map_app.
Qed.

(** Embedded sentences are closed, so shifting their free variables—and the
    entire negated support suffix—is definitionally irrelevant up to the
    rewrite laws. *)
Lemma first_order_sentence_embed_shift : forall L (sigma : sentence L),
  semiformula_shift (first_order_sentence_embed sigma) =
  first_order_sentence_embed sigma.
Proof.
  intros L sigma.
  unfold semiformula_shift, first_order_sentence_embed.
  rewrite <- semiformula_rewrite_comp.
  apply semiformula_rewrite_ext.
  apply rew_shift_comp_emb.
Qed.

Lemma first_order_axiom_suffix_shift : forall L
    (A : list (sentence L)),
  first_order_sequent_shift (first_order_axiom_suffix A) =
  first_order_axiom_suffix A.
Proof.
  intros L A. unfold first_order_axiom_suffix.
  induction A as [|sigma A IH]; simpl; [reflexivity |].
  unfold semiformula_shift at 1.
  rewrite semiformula_rewrite_neg.
  pose proof (@first_order_sentence_embed_shift L sigma) as Hsigma.
  unfold semiformula_shift in Hsigma.
  now rewrite Hsigma, IH.
Qed.

Lemma first_order_sequent_shift_with_axiom_suffix : forall L
    (Gamma : first_order_sequent L) (A : list (sentence L)),
  first_order_sequent_shift (Gamma ++ first_order_axiom_suffix A) =
  first_order_sequent_shift Gamma ++ first_order_axiom_suffix A.
Proof.
  intros L Gamma A. unfold first_order_sequent_shift at 1.
  rewrite List.map_app.
  change (first_order_sequent_shift Gamma ++
    first_order_sequent_shift (first_order_axiom_suffix A) =
    first_order_sequent_shift Gamma ++ first_order_axiom_suffix A).
  now rewrite first_order_axiom_suffix_shift.
Qed.

Definition first_order_derivation_extend_axiom_suffix_right
    {L : language} {Gamma : first_order_sequent L}
    {A : list (sentence L)}
    (d : first_order_derivation L
      (Gamma ++ first_order_axiom_suffix A))
    (B : list (sentence L)) :
    first_order_derivation L
      (Gamma ++ first_order_axiom_suffix (A ++ B)).
Proof.
  apply (FODContraction d). intros p Hp.
  apply (proj1 (generic_list_member_app_iff p Gamma
    (first_order_axiom_suffix A))) in Hp.
  apply (proj2 (generic_list_member_app_iff p Gamma
    (first_order_axiom_suffix (A ++ B)))).
  destruct Hp as [Hp | Hp]; [now left | right].
  rewrite first_order_axiom_suffix_app.
  apply (proj2 (generic_list_member_app_iff p
    (first_order_axiom_suffix A) (first_order_axiom_suffix B))).
  now left.
Defined.

Definition first_order_derivation_extend_axiom_suffix_left
    {L : language} {Gamma : first_order_sequent L}
    (A : list (sentence L)) {B : list (sentence L)}
    (d : first_order_derivation L
      (Gamma ++ first_order_axiom_suffix B)) :
    first_order_derivation L
      (Gamma ++ first_order_axiom_suffix (A ++ B)).
Proof.
  apply (FODContraction d). intros p Hp.
  apply (proj1 (generic_list_member_app_iff p Gamma
    (first_order_axiom_suffix B))) in Hp.
  apply (proj2 (generic_list_member_app_iff p Gamma
    (first_order_axiom_suffix (A ++ B)))).
  destruct Hp as [Hp | Hp]; [now left | right].
  rewrite first_order_axiom_suffix_app.
  apply (proj2 (generic_list_member_app_iff p
    (first_order_axiom_suffix A) (first_order_axiom_suffix B))).
  now right.
Defined.

Definition first_order_derivation_contract_member
    {L : language} {p : proposition L}
    {Gamma : first_order_sequent L}
    (Hp : generic_list_member p Gamma)
    (d : first_order_derivation L (p :: Gamma)) :
    first_order_derivation L Gamma.
Proof.
  apply (FODContraction d). intros q [Hq | Hq].
  - now subst q.
  - exact Hq.
Defined.

(** The reverse translation records the finite theory support accumulated by
    an alternative derivation. *)
Record first_order_derivation2_proof_data {L}
    (T : theory L) (Gamma : first_order_sequent L) : Type := {
  first_order_derivation2_axioms : list (sentence L);
  first_order_derivation2_axioms_member :
    forall sigma,
      generic_list_member sigma first_order_derivation2_axioms -> T sigma;
  first_order_derivation2_lk :
    first_order_derivation L
      (Gamma ++ first_order_axiom_suffix first_order_derivation2_axioms)
}.

(** Proof data is monotone in its formula context. *)
Definition first_order_derivation2_proof_data_weaken
    {L : language} {T : theory L}
    {Delta Gamma : first_order_sequent L}
    (d : first_order_derivation2_proof_data T Delta)
    (Hsub : generic_list_subset Delta Gamma) :
    first_order_derivation2_proof_data T Gamma.
Proof.
  destruct d as [A HA d].
  refine {| first_order_derivation2_axioms := A;
            first_order_derivation2_axioms_member := HA;
            first_order_derivation2_lk := FODContraction d _ |}.
  intros p Hp.
  apply (proj1 (generic_list_member_app_iff p Delta
    (first_order_axiom_suffix A))) in Hp.
  apply (proj2 (generic_list_member_app_iff p Gamma
    (first_order_axiom_suffix A))).
  destruct Hp as [Hp | Hp]; [left; now apply Hsub | now right].
Defined.

(** Extend finite support on either side, retaining the same formula
    context.  These two adapters factor all binary reverse-translation
    cases. *)
Definition first_order_derivation2_proof_data_extend_right
    {L : language} {T : theory L} {Gamma : first_order_sequent L}
    (d : first_order_derivation2_proof_data T Gamma)
    (B : list (sentence L))
    (HB : forall sigma, generic_list_member sigma B -> T sigma) :
    first_order_derivation2_proof_data T Gamma.
Proof.
  destruct d as [A HA d].
  refine {| first_order_derivation2_axioms := A ++ B;
            first_order_derivation2_axioms_member := _;
            first_order_derivation2_lk := FODContraction d _ |}.
  - intros sigma Hsigma.
    apply (proj1 (generic_list_member_app_iff sigma A B)) in Hsigma.
    now destruct Hsigma as [Hsigma | Hsigma]; [apply HA | apply HB].
  - intros p Hp.
    apply (proj1 (generic_list_member_app_iff p Gamma
      (first_order_axiom_suffix A))) in Hp.
    apply (proj2 (generic_list_member_app_iff p Gamma
      (first_order_axiom_suffix (A ++ B)))).
    destruct Hp as [Hp | Hp]; [now left | right].
    rewrite first_order_axiom_suffix_app.
    apply (proj2 (generic_list_member_app_iff p
      (first_order_axiom_suffix A) (first_order_axiom_suffix B))).
    now left.
Defined.

Definition first_order_derivation2_proof_data_extend_left
    {L : language} {T : theory L} {Gamma : first_order_sequent L}
    (A : list (sentence L))
    (HA : forall sigma, generic_list_member sigma A -> T sigma)
    (d : first_order_derivation2_proof_data T Gamma) :
    first_order_derivation2_proof_data T Gamma.
Proof.
  destruct d as [B HB d].
  refine {| first_order_derivation2_axioms := A ++ B;
            first_order_derivation2_axioms_member := _;
            first_order_derivation2_lk := FODContraction d _ |}.
  - intros sigma Hsigma.
    apply (proj1 (generic_list_member_app_iff sigma A B)) in Hsigma.
    now destruct Hsigma as [Hsigma | Hsigma]; [apply HA | apply HB].
  - intros p Hp.
    apply (proj1 (generic_list_member_app_iff p Gamma
      (first_order_axiom_suffix B))) in Hp.
    apply (proj2 (generic_list_member_app_iff p Gamma
      (first_order_axiom_suffix (A ++ B)))).
    destruct Hp as [Hp | Hp]; [now left | right].
    rewrite first_order_axiom_suffix_app.
    apply (proj2 (generic_list_member_app_iff p
      (first_order_axiom_suffix A) (first_order_axiom_suffix B))).
    now right.
Defined.

(** Recursively forget the set-style presentation while retaining exactly the
    finite theory support used by axiom leaves. *)
Fixpoint first_order_derivation2_to_proof_data
    {L : language} {T : theory L} {Gamma : first_order_sequent L}
    (d : first_order_derivation2 L T Gamma) {struct d} :
    first_order_derivation2_proof_data T Gamma.
Proof.
  destruct d as
    [Gamma p Hp Hn
    | Gamma sigma HT Hsigma
    | Gamma Htop
    | Gamma p q Hand dp dq
    | Gamma p q Hor d
    | Gamma p Hall d
    | Gamma p Hex t d
    | Delta Gamma d Hsub
    | Gamma d
    | Gamma p dp dn].
  - refine {| first_order_derivation2_axioms := [];
              first_order_derivation2_axioms_member := _;
              first_order_derivation2_lk := _ |}.
    + intros sigma Hsigma. contradiction.
    + simpl. apply (FODContraction (first_order_derivation_eta p)).
      intros x [Hx | [Hx | Hx]].
      * subst x. apply (proj2 (generic_list_member_app_iff p Gamma [])).
        now left.
      * subst x. apply (proj2 (generic_list_member_app_iff
          (semiformula_neg p) Gamma [])). now left.
      * contradiction.
  - refine {| first_order_derivation2_axioms := [sigma];
              first_order_derivation2_axioms_member := _;
              first_order_derivation2_lk := _ |}.
    + intros tau [Htau | Htau]; [now subst tau | contradiction].
    + simpl. apply (FODContraction
        (first_order_derivation_eta
          (first_order_sentence_embed sigma))).
      intros x [Hx | [Hx | Hx]].
      * subst x. apply (proj2 (generic_list_member_app_iff
          (first_order_sentence_embed sigma) Gamma
          [semiformula_neg (first_order_sentence_embed sigma)])).
        now left.
      * subst x. apply (proj2 (generic_list_member_app_iff
          (semiformula_neg (first_order_sentence_embed sigma)) Gamma
          [semiformula_neg (first_order_sentence_embed sigma)])).
        right. now left.
      * contradiction.
  - refine {| first_order_derivation2_axioms := [];
              first_order_derivation2_axioms_member := _;
              first_order_derivation2_lk := _ |}.
    + intros sigma Hsigma. contradiction.
    + simpl. apply (FODContraction FODVerum).
      intros x [Hx | Hx].
      * subst x. apply (proj2 (generic_list_member_app_iff
          (Semiformula_verum 0) Gamma [])). now left.
      * contradiction.
  - destruct (@first_order_derivation2_to_proof_data L T _ dp)
      as [A HA da].
    destruct (@first_order_derivation2_to_proof_data L T _ dq)
      as [B HB db].
    refine {| first_order_derivation2_axioms := A ++ B;
              first_order_derivation2_axioms_member := _;
              first_order_derivation2_lk := _ |}.
    + intros sigma Hsigma.
      apply (proj1 (generic_list_member_app_iff sigma A B)) in Hsigma.
      now destruct Hsigma as [Hsigma | Hsigma]; [apply HA | apply HB].
    + apply (first_order_derivation_contract_member
        (p := Semiformula_and p q)
        (Gamma := Gamma ++ first_order_axiom_suffix (A ++ B))).
      * apply (proj2 (generic_list_member_app_iff
          (Semiformula_and p q) Gamma
          (first_order_axiom_suffix (A ++ B)))).
        now left.
      * apply FODAnd.
        -- exact (first_order_derivation_extend_axiom_suffix_right da B).
        -- exact (first_order_derivation_extend_axiom_suffix_left A db).
  - destruct (@first_order_derivation2_to_proof_data L T _ d)
      as [A HA da].
    refine {| first_order_derivation2_axioms := A;
              first_order_derivation2_axioms_member := HA;
              first_order_derivation2_lk := _ |}.
    apply (first_order_derivation_contract_member
      (p := Semiformula_or p q)
      (Gamma := Gamma ++ first_order_axiom_suffix A)).
    + apply (proj2 (generic_list_member_app_iff
        (Semiformula_or p q) Gamma (first_order_axiom_suffix A))).
      now left.
    + exact (FODOr da).
  - destruct (@first_order_derivation2_to_proof_data L T _ d)
      as [A HA da].
    refine {| first_order_derivation2_axioms := A;
              first_order_derivation2_axioms_member := HA;
              first_order_derivation2_lk := _ |}.
    apply (first_order_derivation_contract_member
      (p := Semiformula_all p)
      (Gamma := Gamma ++ first_order_axiom_suffix A)).
    + apply (proj2 (generic_list_member_app_iff
        (Semiformula_all p) Gamma (first_order_axiom_suffix A))).
      now left.
    + apply FODAll.
      refine (first_order_derivation_cast da _).
      simpl. f_equal. symmetry.
      apply first_order_sequent_shift_with_axiom_suffix.
  - destruct (@first_order_derivation2_to_proof_data L T _ d)
      as [A HA da].
    refine {| first_order_derivation2_axioms := A;
              first_order_derivation2_axioms_member := HA;
              first_order_derivation2_lk := _ |}.
    apply (first_order_derivation_contract_member
      (p := Semiformula_exists p)
      (Gamma := Gamma ++ first_order_axiom_suffix A)).
    + apply (proj2 (generic_list_member_app_iff
        (Semiformula_exists p) Gamma (first_order_axiom_suffix A))).
      now left.
    + exact (@FODExists L p t
        (Gamma ++ first_order_axiom_suffix A) da).
  - exact (first_order_derivation2_proof_data_weaken
      (@first_order_derivation2_to_proof_data L T _ d) Hsub).
  - destruct (@first_order_derivation2_to_proof_data L T _ d)
      as [A HA da].
    refine {| first_order_derivation2_axioms := A;
              first_order_derivation2_axioms_member := HA;
              first_order_derivation2_lk := _ |}.
    exact (first_order_derivation_cast
      (first_order_derivation_shift da)
      (first_order_sequent_shift_with_axiom_suffix Gamma A)).
  - destruct (@first_order_derivation2_to_proof_data L T _ dp)
      as [A HA da].
    destruct (@first_order_derivation2_to_proof_data L T _ dn)
      as [B HB db].
    refine {| first_order_derivation2_axioms := A ++ B;
              first_order_derivation2_axioms_member := _;
              first_order_derivation2_lk := _ |}.
    + intros sigma Hsigma.
      apply (proj1 (generic_list_member_app_iff sigma A B)) in Hsigma.
      now destruct Hsigma as [Hsigma | Hsigma]; [apply HA | apply HB].
    + apply (FODContraction
        (FODCut
          (first_order_derivation_extend_axiom_suffix_right da B)
          (first_order_derivation_extend_axiom_suffix_left A db))).
      intros x Hx.
      apply (proj1 (generic_list_member_app_iff x
        (Gamma ++ first_order_axiom_suffix (A ++ B))
        (Gamma ++ first_order_axiom_suffix (A ++ B)))) in Hx.
      now destruct Hx as [Hx | Hx].
Defined.

Definition first_order_derivation2_to_proof
    {L : language} {T : theory L} {Gamma : first_order_sequent L}
    (d : first_order_derivation2 L T Gamma) :
  exists A : list (sentence L),
    (forall sigma, generic_list_member sigma A -> T sigma) /\
    inhabited (first_order_derivation L
      (Gamma ++ first_order_axiom_suffix A)).
Proof.
  destruct (first_order_derivation2_to_proof_data d) as [A HA da].
  exists A. split; [exact HA | now constructor].
Qed.

(** Repeated same-context cuts discharge a finite list of theory axioms from
    an alternative derivation. *)
Fixpoint first_order_derivation2_cut_axioms
    {L : language} {T : theory L} (p : proposition L)
    (A : list (sentence L))
    (HA : forall sigma, generic_list_member sigma A -> T sigma)
    (d : first_order_derivation2 L T
      (p :: first_order_axiom_suffix A)) {struct A} :
    first_order_derivation2 L T [p].
Proof.
  destruct A as [|sigma A].
  - exact d.
  - apply (@first_order_derivation2_cut_axioms L T p A
      (fun tau Htau => HA tau (or_intror Htau))).
    apply (FOD2Cut (p := first_order_sentence_embed sigma)).
    + apply (FOD2Axiom sigma (HA sigma (or_introl eq_refl))).
      now left.
    + apply (FOD2Weakening d).
      intros x [Hx | [Hx | Hx]].
      * subst x. right. now left.
      * subst x. now left.
      * right. now right.
Defined.

Definition first_order_derivable2_cut_axioms
    {L : language} {T : theory L} (p : proposition L)
    (A : list (sentence L))
    (HA : forall sigma, generic_list_member sigma A -> T sigma)
    (d : first_order_derivable2 T
      (p :: first_order_axiom_suffix A)) :
    first_order_derivable2 T [p] :=
  match d with
  | inhabits d0 => inhabits
      (@first_order_derivation2_cut_axioms L T p A HA d0)
  end.

Lemma first_order_sentence_embed_neg : forall L (sigma : sentence L),
  first_order_sentence_embed (semiformula_neg sigma) =
  semiformula_neg (first_order_sentence_embed sigma).
Proof.
  intros L sigma. unfold first_order_sentence_embed.
  apply semiformula_rewrite_neg.
Qed.

Lemma first_order_sentence_embed_neg_map : forall L
    (A : list (sentence L)),
  map first_order_sentence_embed (map semiformula_neg A) =
  first_order_axiom_suffix A.
Proof.
  intros L A. induction A as [|sigma A IH]; simpl; [reflexivity |].
  now rewrite first_order_sentence_embed_neg, IH.
Qed.

(** Singleton alternative proofs and ordinary finite-support theory proofs
    carry equivalent data. *)
Definition first_order_theory_proof2 {L : language}
    (T : theory L) (sigma : sentence L) : Type :=
  first_order_derivation2 L T [first_order_sentence_embed sigma].

Definition first_order_theory_provable2 {L : language}
    (T : theory L) (sigma : sentence L) : Prop :=
  inhabited (first_order_theory_proof2 T sigma).

Definition first_order_theory_proof_to_proof2
    {L : language} {T : theory L} {sigma : sentence L}
    (b : first_order_theory_proof T sigma) :
    first_order_theory_proof2 T sigma.
Proof.
  destruct b as [w d]. destruct w as [A HA].
  apply (@first_order_derivation2_cut_axioms L T
    (first_order_sentence_embed sigma) A HA).
  apply first_order_derivation_to_derivation2.
  refine (first_order_derivation_cast d _).
  unfold generic_lk_pullback. simpl.
  f_equal. apply first_order_sentence_embed_neg_map.
Defined.

Definition first_order_theory_proof2_to_proof
    {L : language} {T : theory L} {sigma : sentence L}
    (d : first_order_theory_proof2 T sigma) :
    first_order_theory_proof T sigma.
Proof.
  destruct (first_order_derivation2_to_proof_data d) as [A HA da].
  refine (existT _ (exist _ A HA) _).
  unfold generic_lk_pullback. simpl.
  refine (first_order_derivation_cast da _).
  simpl.
  f_equal. symmetry. apply first_order_sentence_embed_neg_map.
Defined.

Lemma first_order_theory_provable_iff_derivable2 : forall L
    (T : theory L) (sigma : sentence L),
  first_order_theory_provable T sigma <->
  first_order_theory_provable2 T sigma.
Proof.
  intros L T sigma. split.
  - intros [b]. constructor. exact (first_order_theory_proof_to_proof2 b).
  - intros [d]. constructor. exact (first_order_theory_proof2_to_proof d).
Qed.
