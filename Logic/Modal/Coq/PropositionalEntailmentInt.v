(** Generic derived rules for intuitionistic propositional entailment.

    This module ports the central, system-independent results from
    [Propositional/Entailment/Int/Basic.lean].  Foundation combines minimal
    entailment and ex falso through typeclasses; Coq records the same boundary
    explicitly.  Positional list membership keeps all finite-disjunction
    constructions proof-relevant, duplicate-safe, and independent of formula
    equality.
*)

From Stdlib Require Import Lists.List Program.Equality.
From FoundationModal Require Import
  GenericSemantics GenericEntailment GenericLogicSymbol
  PropositionalEntailmentAxioms
  PropositionalEntailmentMinimal.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Intuitionistic capability *)

Record generic_intuitionistic_entailment {S F : Type}
    (E : generic_entailment S F)
    (C : generic_connectives F) (s : S) : Type := {
  generic_intuitionistic_minimal : generic_minimal_entailment E C s;
  generic_intuitionistic_has_efq : generic_has_axiom_efq E C s
}.

Arguments generic_intuitionistic_minimal {S F E C s} _.
Arguments generic_intuitionistic_has_efq {S F E C s} _.

Definition generic_intuitionistic_efq_elim_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s) (p : F)
    (d : generic_proof E s (generic_bottom C)) :
    generic_proof E s p :=
  generic_efq_elim_raw
    (generic_minimal_mdp (generic_intuitionistic_minimal H))
    (generic_intuitionistic_has_efq H) p d.

Arguments generic_intuitionistic_efq_elim_raw {S F E C s} _ _ _.

(** Proof-relevant predicate contexts generalize both of Foundation's finite
    and set-context explosion lemmas.  Membership evidence is consumed
    directly, so no equality decision or witness choice is needed. *)
Definition generic_intuitionistic_type_context_explosion_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    {T : F -> Type} (p q : F) (hp : T p) (hnp : T (generic_neg C p)) :
    generic_type_context_derivation E s C T q :=
  let Hm := generic_intuitionistic_minimal H in
  GTCD_mdp (GTCD_theorem (generic_efq_raw
      (generic_intuitionistic_has_efq H) q))
    (GTCD_mdp
      (GTCD_mdp
        (GTCD_theorem (generic_minimal_iff_elim_left_raw Hm _ _
          (generic_minimal_neg_equiv Hm p)))
        (GTCD_assumption hnp))
      (GTCD_assumption hp)).

Arguments generic_intuitionistic_type_context_explosion_raw {S F E C s}
  _ {T} _ _ _ _.

Lemma generic_intuitionistic_inconsistent_of_provable_neg :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_intuitionistic_entailment E C s -> forall p,
      generic_provable E s p ->
      generic_provable E s (generic_neg C p) ->
      generic_inconsistent E s.
Proof.
  intros S F E C s H p [dp] [dnp] q. constructor.
  exact (generic_intuitionistic_efq_elim_raw H q
    (generic_minimal_bottom_of_proof_neg_raw
      (generic_intuitionistic_minimal H) p dp dnp)).
Qed.

(** * Explosion and implication *)

Definition generic_intuitionistic_imp_neg_explosion_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C p (generic_imp C (generic_neg C p) q)) :=
  let Hm := generic_intuitionistic_minimal H in
  generic_minimal_curry_raw Hm p (generic_neg C p) q
    (generic_minimal_imp_trans_raw Hm
      (generic_and C p (generic_neg C p)) (generic_bottom C) q
      (generic_minimal_contradiction_axiom_raw Hm p)
      (generic_efq_raw (generic_intuitionistic_has_efq H) q)).

Arguments generic_intuitionistic_imp_neg_explosion_raw {S F E C s}
  _ _ _.

Definition generic_intuitionistic_neg_imp_explosion_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_neg C p) (generic_imp C p q)) :=
  let Hm := generic_intuitionistic_minimal H in
  @generic_minimal_imp_swap_raw S F E C s Hm p (generic_neg C p) q
    (generic_intuitionistic_imp_neg_explosion_raw H p q).

Arguments generic_intuitionistic_neg_imp_explosion_raw {S F E C s}
  _ _ _.

Definition generic_intuitionistic_neg_or_to_imp_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C (generic_or C (generic_neg C p) q)
        (generic_imp C p q)) :=
  let Hm := generic_intuitionistic_minimal H in
  generic_minimal_or_elim_raw Hm (generic_neg C p) q
    (generic_imp C p q)
    (generic_intuitionistic_neg_imp_explosion_raw H p q)
    (generic_minimal_K Hm q p).

Arguments generic_intuitionistic_neg_or_to_imp_raw {S F E C s}
  _ _ _.

(** The intuitionistic converse to minimal logic's stable-implication map:
    [(~~p -> ~~q) -> ~~(p -> q)].  The proof factors through
    [~(p -> q) -> (~~p /\ ~q)], exposing the exact use of ex falso in the
    preceding [~p \/ q -> p -> q] theorem. *)
Definition generic_intuitionistic_double_neg_imp_converse_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s) (p q : F) :
    generic_proof E s
      (generic_imp C
        (generic_imp C (generic_neg C (generic_neg C p))
          (generic_neg C (generic_neg C q)))
        (generic_neg C (generic_neg C (generic_imp C p q)))).
Proof.
  set (Hm := generic_intuitionistic_minimal H).
  set (f := generic_imp C p q).
  set (nf := generic_neg C f).
  set (np := generic_neg C p).
  set (nnp := generic_neg C np).
  set (nq := generic_neg C q).
  set (nnq := generic_neg C nq).
  set (h := generic_imp C nnp nnq).
  pose (dnf_to_nor := generic_minimal_contraposition_raw Hm
    (generic_or C np q) f
    (generic_intuitionistic_neg_or_to_imp_raw H p q)).
  pose (dnf_to_pair := generic_minimal_imp_trans_raw Hm nf
    (generic_neg C (generic_or C np q))
    (generic_and C nnp nq) dnf_to_nor
    (generic_minimal_neg_or_to_and_neg_raw Hm np q)).
  assert (dnf : generic_list_derivation E s C [nf; h] nf).
  { exact (GLD_assumption (GRLM_here [h])). }
  assert (dh : generic_list_derivation E s C [nf; h] h).
  { exact (GLD_assumption (GRLM_there nf (GRLM_here []))). }
  pose (dpair := GLD_mdp (GLD_theorem dnf_to_pair) dnf).
  pose (dnnp := GLD_mdp
    (GLD_theorem (generic_minimal_and1 Hm nnp nq)) dpair).
  pose (dnq := GLD_mdp
    (GLD_theorem (generic_minimal_and2 Hm nnp nq)) dpair).
  pose (dnnq := GLD_mdp dh dnnp).
  pose (dnqbot := GLD_mdp
    (GLD_theorem (generic_minimal_iff_elim_left_raw Hm _ _
      (generic_minimal_neg_equiv Hm nq))) dnnq).
  pose (dbot := GLD_mdp dnqbot dnq).
  pose (dnfbot := generic_list_deduction (generic_minimal_mdp Hm)
    (generic_minimal_K Hm) (generic_minimal_S Hm) dbot).
  pose (dnnf := GLD_mdp
    (GLD_theorem (generic_minimal_iff_elim_right_raw Hm _ _
      (generic_minimal_neg_equiv Hm nf))) dnfbot).
  exact (generic_empty_derivation_raw (generic_minimal_mdp Hm)
    (generic_list_deduction (generic_minimal_mdp Hm)
      (generic_minimal_K Hm) (generic_minimal_S Hm) dnnf)).
Defined.

Arguments generic_intuitionistic_double_neg_imp_converse_raw
  {S F E C s} _ _ _.

(** * Finite disjunction elimination *)

Fixpoint generic_intuitionistic_list_disj2_nonempty_elim_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    (head : F) (tail : list F) (goal : F)
    (branch : forall p, generic_raw_list_member p (head :: tail) ->
      generic_proof E s (generic_imp C p goal)) {struct tail} :
    generic_proof E s
      (generic_imp C (generic_list_disj2 C (head :: tail)) goal).
Proof.
  destruct tail as [|next rest].
  - exact (branch head (GRLM_here [])).
  - apply (generic_minimal_or_elim_raw
      (generic_intuitionistic_minimal H) head
      (generic_list_disj2 C (next :: rest)) goal).
    + exact (branch head (GRLM_here (next :: rest))).
    + apply (@generic_intuitionistic_list_disj2_nonempty_elim_raw
        S F E C s H next rest goal).
      intros p hp. exact (branch p (GRLM_there head hp)).
Defined.

Arguments generic_intuitionistic_list_disj2_nonempty_elim_raw
  {S F E C s} _ _ _ _ _.

Definition generic_intuitionistic_list_disj2_elim_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    (gamma : list F) (goal : F)
    (branch : forall p, generic_raw_list_member p gamma ->
      generic_proof E s (generic_imp C p goal)) :
    generic_proof E s
      (generic_imp C (generic_list_disj2 C gamma) goal) :=
  match gamma as xs return
    (forall p, generic_raw_list_member p xs ->
      generic_proof E s (generic_imp C p goal)) ->
    generic_proof E s
      (generic_imp C (generic_list_disj2 C xs) goal)
  with
  | [] => fun _ => generic_efq_raw
      (generic_intuitionistic_has_efq H) goal
  | head :: tail => fun branches =>
      generic_intuitionistic_list_disj2_nonempty_elim_raw
        H head tail goal branches
  end branch.

Arguments generic_intuitionistic_list_disj2_elim_raw {S F E C s}
  _ _ _ _.

Definition generic_intuitionistic_list_disj2_append_to_or_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    (gamma delta : list F) :
    generic_proof E s
      (generic_imp C (generic_list_disj2 C (gamma ++ delta))
        (generic_or C (generic_list_disj2 C gamma)
          (generic_list_disj2 C delta))) :=
  generic_intuitionistic_list_disj2_elim_raw H (gamma ++ delta) _
    (fun p hp =>
      match @generic_raw_list_member_app_split F p gamma delta hp with
      | inl hl => generic_minimal_imp_trans_raw
          (generic_intuitionistic_minimal H) p
          (generic_list_disj2 C gamma) _
          (generic_minimal_list_disj2_intro_raw
            (generic_intuitionistic_minimal H) hl)
          (generic_minimal_or1 (generic_intuitionistic_minimal H)
            (generic_list_disj2 C gamma) (generic_list_disj2 C delta))
      | inr hr => generic_minimal_imp_trans_raw
          (generic_intuitionistic_minimal H) p
          (generic_list_disj2 C delta) _
          (generic_minimal_list_disj2_intro_raw
            (generic_intuitionistic_minimal H) hr)
          (generic_minimal_or2 (generic_intuitionistic_minimal H)
            (generic_list_disj2 C gamma) (generic_list_disj2 C delta))
      end).

Arguments generic_intuitionistic_list_disj2_append_to_or_raw {S F E C s}
  _ _ _.

Definition generic_intuitionistic_or_to_list_disj2_append_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    (gamma delta : list F) :
    generic_proof E s
      (generic_imp C
        (generic_or C (generic_list_disj2 C gamma)
          (generic_list_disj2 C delta))
        (generic_list_disj2 C (gamma ++ delta))) :=
  generic_minimal_or_elim_raw (generic_intuitionistic_minimal H)
    (generic_list_disj2 C gamma) (generic_list_disj2 C delta)
    (generic_list_disj2 C (gamma ++ delta))
    (generic_intuitionistic_list_disj2_elim_raw H gamma _
      (fun p hp => generic_minimal_list_disj2_intro_raw
        (generic_intuitionistic_minimal H)
        (generic_raw_list_member_app_left delta hp)))
    (generic_intuitionistic_list_disj2_elim_raw H delta _
      (fun p hp => generic_minimal_list_disj2_intro_raw
        (generic_intuitionistic_minimal H)
        (generic_raw_list_member_app_right gamma hp))).

Arguments generic_intuitionistic_or_to_list_disj2_append_raw {S F E C s}
  _ _ _.

Definition generic_intuitionistic_list_disj2_append_iff_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    (gamma delta : list F) :
    generic_proof E s
      (generic_formula_iff C (generic_list_disj2 C (gamma ++ delta))
        (generic_or C (generic_list_disj2 C gamma)
          (generic_list_disj2 C delta))) :=
  generic_minimal_iff_intro_raw (generic_intuitionistic_minimal H) _ _
    (generic_intuitionistic_list_disj2_append_to_or_raw H gamma delta)
    (generic_intuitionistic_or_to_list_disj2_append_raw H gamma delta).

Arguments generic_intuitionistic_list_disj2_append_iff_raw {S F E C s}
  _ _ _.

Definition generic_intuitionistic_list_disj2_unique_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s) (p : F)
    (gamma : list F)
    (same : forall q, generic_raw_list_member q gamma -> q = p) :
    generic_proof E s
      (generic_imp C (generic_list_disj2 C gamma) p).
Proof.
  apply (generic_intuitionistic_list_disj2_elim_raw H gamma p).
  intros q hq. destruct (same q hq).
  exact (generic_minimal_identity_raw
    (generic_intuitionistic_minimal H) q).
Defined.

Arguments generic_intuitionistic_list_disj2_unique_raw {S F E C s}
  _ _ _ _.

Definition generic_intuitionistic_list_disj2_cons_iff_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s) (p : F)
    (gamma : list F) :
    generic_proof E s
      (generic_formula_iff C (generic_list_disj2 C (p :: gamma))
        (generic_or C p (generic_list_disj2 C gamma))) :=
  generic_intuitionistic_list_disj2_append_iff_raw H [p] gamma.

Arguments generic_intuitionistic_list_disj2_cons_iff_raw {S F E C s}
  _ _ _.

(** * Positional disjunction removal and monotonicity *)

Definition generic_intuitionistic_insert_member_to_or_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    (gamma delta : list F) (p : F) {q : F}
    (hq : generic_raw_list_member q (gamma ++ p :: delta)) :
    generic_proof E s
      (generic_imp C q
        (generic_or C p (generic_list_disj2 C (gamma ++ delta)))).
Proof.
  set (Hm := generic_intuitionistic_minimal H).
  destruct (@generic_raw_list_member_app_split F q gamma (p :: delta) hq)
    as [hl | hr].
  - exact (generic_minimal_imp_trans_raw Hm q
      (generic_list_disj2 C (gamma ++ delta)) _
      (generic_minimal_list_disj2_intro_raw Hm
        (generic_raw_list_member_app_left delta hl))
      (generic_minimal_or2 Hm p
        (generic_list_disj2 C (gamma ++ delta)))).
  - dependent destruction hr.
    + exact (generic_minimal_or1 Hm p
        (generic_list_disj2 C (gamma ++ delta))).
    + exact (generic_minimal_imp_trans_raw Hm q
        (generic_list_disj2 C (gamma ++ delta)) _
        (generic_minimal_list_disj2_intro_raw Hm
          (generic_raw_list_member_app_right gamma hr))
        (generic_minimal_or2 Hm p
          (generic_list_disj2 C (gamma ++ delta)))).
Defined.

Arguments generic_intuitionistic_insert_member_to_or_raw {S F E C s}
  _ _ _ _ {q} _.

Definition generic_intuitionistic_list_disj2_insert_to_or_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    (gamma delta : list F) (p : F) :
    generic_proof E s
      (generic_imp C (generic_list_disj2 C (gamma ++ p :: delta))
        (generic_or C p (generic_list_disj2 C (gamma ++ delta)))) :=
  generic_intuitionistic_list_disj2_elim_raw H
    (gamma ++ p :: delta) _
    (fun q hq => generic_intuitionistic_insert_member_to_or_raw
      H gamma delta p hq).

Arguments generic_intuitionistic_list_disj2_insert_to_or_raw {S F E C s}
  _ _ _ _.

Definition generic_intuitionistic_or_to_list_disj2_insert_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    (gamma delta : list F) (p : F) :
    generic_proof E s
      (generic_imp C
        (generic_or C p (generic_list_disj2 C (gamma ++ delta)))
        (generic_list_disj2 C (gamma ++ p :: delta))) :=
  let Hm := generic_intuitionistic_minimal H in
  generic_minimal_or_elim_raw Hm p
    (generic_list_disj2 C (gamma ++ delta))
    (generic_list_disj2 C (gamma ++ p :: delta))
    (generic_minimal_list_disj2_intro_raw Hm
      (generic_raw_list_member_app_right gamma (GRLM_here delta)))
    (generic_intuitionistic_list_disj2_elim_raw H (gamma ++ delta) _
      (fun q hq => generic_minimal_list_disj2_intro_raw Hm
        (@generic_raw_list_member_skip_insert F p q gamma delta hq))).

Arguments generic_intuitionistic_or_to_list_disj2_insert_raw {S F E C s}
  _ _ _ _.

Definition generic_intuitionistic_list_disj2_insert_iff_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    (gamma delta : list F) (p : F) :
    generic_proof E s
      (generic_formula_iff C
        (generic_list_disj2 C (gamma ++ p :: delta))
        (generic_or C p (generic_list_disj2 C (gamma ++ delta)))) :=
  generic_minimal_iff_intro_raw (generic_intuitionistic_minimal H) _ _
    (generic_intuitionistic_list_disj2_insert_to_or_raw H gamma delta p)
    (generic_intuitionistic_or_to_list_disj2_insert_raw H gamma delta p).

Arguments generic_intuitionistic_list_disj2_insert_iff_raw {S F E C s}
  _ _ _ _.

Definition generic_intuitionistic_list_disj2_subset_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    (gamma delta : list F)
    (incl : forall p, generic_raw_list_member p gamma ->
      generic_raw_list_member p delta) :
    generic_proof E s
      (generic_imp C (generic_list_disj2 C gamma)
        (generic_list_disj2 C delta)) :=
  generic_intuitionistic_list_disj2_elim_raw H gamma _
    (fun p hp => generic_minimal_list_disj2_intro_raw
      (generic_intuitionistic_minimal H) (incl p hp)).

Arguments generic_intuitionistic_list_disj2_subset_raw {S F E C s}
  _ _ _ _.

(** * Finite De Morgan equivalence *)

Definition generic_intuitionistic_neg_disj2_to_conj2_neg_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s) (gamma : list F) :
    generic_proof E s
      (generic_imp C (generic_neg C (generic_list_disj2 C gamma))
        (generic_list_conj_map C (generic_neg C) gamma)) :=
  let Hm := generic_intuitionistic_minimal H in
  generic_minimal_list_conj_map_right_intro_raw Hm
    (generic_neg C (generic_list_disj2 C gamma))
    (generic_neg C) gamma
    (fun p hp => generic_minimal_contraposition_raw Hm p
      (generic_list_disj2 C gamma)
      (generic_minimal_list_disj2_intro_raw Hm hp)).

Arguments generic_intuitionistic_neg_disj2_to_conj2_neg_raw
  {S F E C s} _ _.

Definition generic_intuitionistic_conj2_neg_to_neg_disj2_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s) (gamma : list F) :
    generic_proof E s
      (generic_imp C (generic_list_conj_map C (generic_neg C) gamma)
        (generic_neg C (generic_list_disj2 C gamma))).
Proof.
  set (Hm := generic_intuitionistic_minimal H).
  set (a := generic_list_conj_map C (generic_neg C) gamma).
  set (d := generic_list_disj2 C gamma).
  assert (branches : forall p, generic_raw_list_member p gamma ->
      generic_proof E s (generic_imp C p
        (generic_imp C a (generic_bottom C)))).
  { intros p hp.
    apply (@generic_minimal_imp_swap_raw S F E C s Hm
      a p (generic_bottom C)).
    exact (generic_minimal_imp_trans_raw Hm a (generic_neg C p)
      (generic_imp C p (generic_bottom C))
      (generic_minimal_list_conj_map_elim_raw Hm (generic_neg C) hp)
      (generic_minimal_iff_elim_left_raw Hm _ _
        (generic_minimal_neg_equiv Hm p))). }
  pose (ddab := generic_intuitionistic_list_disj2_elim_raw H gamma
    (generic_imp C a (generic_bottom C)) branches).
  pose (dadb := @generic_minimal_imp_swap_raw S F E C s Hm
    d a (generic_bottom C) ddab).
  exact (generic_minimal_imp_trans_raw Hm a
    (generic_imp C d (generic_bottom C)) (generic_neg C d) dadb
    (generic_minimal_iff_elim_right_raw Hm _ _
      (generic_minimal_neg_equiv Hm d))).
Defined.

Arguments generic_intuitionistic_conj2_neg_to_neg_disj2_raw
  {S F E C s} _ _.

Definition generic_intuitionistic_neg_disj2_iff_conj2_neg_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s) (gamma : list F) :
    generic_proof E s
      (generic_formula_iff C
        (generic_neg C (generic_list_disj2 C gamma))
        (generic_list_conj_map C (generic_neg C) gamma)) :=
  generic_minimal_iff_intro_raw (generic_intuitionistic_minimal H) _ _
    (generic_intuitionistic_neg_disj2_to_conj2_neg_raw H gamma)
    (generic_intuitionistic_conj2_neg_to_neg_disj2_raw H gamma).

Arguments generic_intuitionistic_neg_disj2_iff_conj2_neg_raw
  {S F E C s} _ _.
