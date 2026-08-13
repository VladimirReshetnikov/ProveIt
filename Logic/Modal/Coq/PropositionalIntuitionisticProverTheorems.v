(** Mathematical theorem wrappers used by Foundation's intuitionistic prover.

    This module ports exactly the namespace [IntProver.Theorems] from
    [Foundation/Meta/IntProver.lean].  It deliberately excludes Lean's
    quotation, elaborator, and proof-search implementation.  The source
    prover keeps the active sequent at the end of a tableau while the generic
    tableau rules consume it at the head; proof-relevant list inclusions
    implement that rotation without formula or sequent equality decisions.

    Raw witnesses remain in [Type].  Public theoremhood and validity views
    use [inhabited], and no public proof witness is selected into [Type]. *)

From Stdlib Require Import Lists.List.
From FoundationModal Require Import
  GenericSemantics GenericEntailment GenericLogicSymbol GenericCalculus
  PropositionalEntailmentAxioms PropositionalEntailmentMinimal
  PropositionalEntailmentInt PropositionalTwoSided
  PropositionalTwoSidedTableau.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Singleton projection *)

(** Source declaration [IntProver.Theorems.to_twoSided]. *)
Definition generic_intuitionistic_prover_to_two_sided_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {gamma delta : list F}
    (v : generic_two_sided_tableau_validity E s C
      [GTS_mk gamma delta]) :
    generic_two_sided_derivation E s C gamma delta.
Proof.
  exact ((match v in generic_two_sided_tableau_validity _ _ _ tau return
      match tau with
      | [] => unit
      | q :: rest =>
          (generic_two_sided_sequent_derivation E s C q ->
           match rest with
           | [] => generic_two_sided_derivation E s C gamma delta
           | _ => unit
           end) ->
          match rest with
          | [] => generic_two_sided_derivation E s C gamma delta
          | _ => unit
          end
      end
    with
    | GTTV_head d => fun K => K d
    | GTTV_tail vt =>
        fun _ =>
          match vt in generic_two_sided_tableau_validity _ _ _ tau return
            match tau with
            | [] => generic_two_sided_derivation E s C gamma delta
            | _ => unit
            end
          with
          | GTTV_head _ => tt
          | GTTV_tail _ => tt
          end
    end) (fun d => d)).
Defined.

Lemma generic_intuitionistic_prover_to_two_sided :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta,
    generic_two_sided_tableau_valid E s C [GTS_mk gamma delta] ->
    generic_two_sided_derivable E s C gamma delta.
Proof.
  intros S F E C s gamma delta [v]. constructor.
  exact (generic_intuitionistic_prover_to_two_sided_raw v).
Qed.

(** Source declaration [IntProver.Theorems.to_provable]. *)
Definition generic_intuitionistic_prover_to_proof_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s) {p : F}
    (v : generic_two_sided_tableau_validity E s C [GTS_mk [] [p]]) :
    generic_proof E s p :=
  generic_two_sided_tableau_valid_to_proof_raw H v.

Lemma generic_intuitionistic_prover_to_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_intuitionistic_entailment E C s -> forall p,
    generic_two_sided_tableau_valid E s C [GTS_mk [] [p]] ->
    generic_provable E s p.
Proof.
  intros S F E C s H p [v]. constructor.
  exact (generic_intuitionistic_prover_to_proof_raw H v).
Qed.

(** Source declaration [IntProver.Theorems.add_hyp].  The raw form accepts
    the already-transported target proof.  The public source-faithful form
    transports inhabited provability through [generic_weaker_than] while its
    goal remains in [Prop], so it needs no choice principle. *)
Definition generic_intuitionistic_prover_add_hyp_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F}
    (dp : generic_proof E s p)
    (v : generic_two_sided_tableau_validity E s C
      [GTS_mk (p :: gamma) delta]) :
    generic_two_sided_tableau_validity E s C [GTS_mk gamma delta] :=
  generic_two_sided_tableau_valid_of_single_uppercedent_raw
    (generic_two_sided_add_hyp_raw H dp) v.

Lemma generic_intuitionistic_prover_add_hyp :
  forall (SS S F : Type)
         (ES : generic_entailment SS F) (E : generic_entailment S F)
         (C : generic_connectives F) (ss : SS) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p,
    generic_weaker_than ES E ss s ->
    generic_provable ES ss p ->
    generic_two_sided_tableau_valid E s C
      [GTS_mk (p :: gamma) delta] ->
    generic_two_sided_tableau_valid E s C [GTS_mk gamma delta].
Proof.
  intros SS S F ES E C ss s H gamma delta p Hweak Hp.
  apply generic_two_sided_tableau_valid_of_single_uppercedent.
  intros Hd. exact (generic_two_sided_add_hyp H Hweak Hp Hd).
Qed.

(** * Closed branches and tableau organization *)

(** Source declaration [IntProver.Theorems.right_closed]. *)
Definition generic_intuitionistic_prover_right_closed_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F} (T : generic_two_sided_tableau F)
    (hp : generic_raw_list_member p gamma) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (p :: delta) :: T) :=
  generic_two_sided_tableau_valid_right_closed_raw H T hp.

Lemma generic_intuitionistic_prover_right_closed :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p T,
    generic_raw_list_member p gamma ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (p :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p T hp. constructor.
  exact (generic_intuitionistic_prover_right_closed_raw H T hp).
Qed.

(** Source declaration [IntProver.Theorems.left_closed]. *)
Definition generic_intuitionistic_prover_left_closed_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F} (T : generic_two_sided_tableau F)
    (hp : generic_raw_list_member p delta) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (p :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_left_closed_raw H T hp.

Lemma generic_intuitionistic_prover_left_closed :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p T,
    generic_raw_list_member p delta ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (p :: gamma) delta :: T).
Proof.
  intros S F E C s H gamma delta p T hp. constructor.
  exact (generic_intuitionistic_prover_left_closed_raw H T hp).
Qed.

(** Source declaration [IntProver.Theorems.remove]. *)
Definition generic_intuitionistic_prover_remove_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (gamma delta : list F) {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C T) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma delta :: T) :=
  generic_two_sided_tableau_valid_remove_raw gamma delta v.

Lemma generic_intuitionistic_prover_remove :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta T,
    generic_two_sided_tableau_valid E s C T ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma delta :: T).
Proof.
  intros S F E C s gamma delta T [v]. constructor.
  exact (generic_intuitionistic_prover_remove_raw gamma delta v).
Qed.

(** Source declaration [IntProver.Theorems.rotate]. *)
Definition generic_intuitionistic_prover_rotate_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {gamma delta : list F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (T ++ [GTS_mk gamma delta])) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma delta :: T) :=
  generic_two_sided_tableau_valid_of_subset_raw v
    (generic_raw_list_subset_append_singleton_to_cons
      (GTS_mk gamma delta) T).

Lemma generic_intuitionistic_prover_rotate :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta T,
    generic_two_sided_tableau_valid E s C
      (T ++ [GTS_mk gamma delta]) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma delta :: T).
Proof.
  intros S F E C s gamma delta T [v]. constructor.
  exact (generic_intuitionistic_prover_rotate_raw v).
Qed.

(** * Right rules over append-oriented prover tableaux *)

(** Source declaration [IntProver.Theorems.remove_right]. *)
Definition generic_intuitionistic_prover_remove_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (T ++ [GTS_mk gamma delta])) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (p :: delta) :: T) :=
  generic_two_sided_tableau_valid_remove_right_raw H
    (generic_intuitionistic_prover_rotate_raw v).

Lemma generic_intuitionistic_prover_remove_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p T,
    generic_two_sided_tableau_valid E s C
      (T ++ [GTS_mk gamma delta]) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (p :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p T [v]. constructor.
  exact (generic_intuitionistic_prover_remove_right_raw H v).
Qed.

(** Source declaration [IntProver.Theorems.rotate_right]. *)
Definition generic_intuitionistic_prover_rotate_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (T ++ [GTS_mk gamma (delta ++ [p])])) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (p :: delta) :: T) :=
  generic_two_sided_tableau_valid_rotate_right_raw H
    (generic_intuitionistic_prover_rotate_raw v).

Lemma generic_intuitionistic_prover_rotate_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p T,
    generic_two_sided_tableau_valid E s C
      (T ++ [GTS_mk gamma (delta ++ [p])]) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (p :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p T [v]. constructor.
  exact (generic_intuitionistic_prover_rotate_right_raw H v).
Qed.

(** Source declaration [IntProver.Theorems.verum_right]. *)
Definition generic_intuitionistic_prover_verum_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    (gamma delta : list F) (T : generic_two_sided_tableau F) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_top C :: delta) :: T) :=
  generic_two_sided_tableau_valid_verum_right_raw H gamma delta T.

Lemma generic_intuitionistic_prover_verum_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_top C :: delta) :: T).
Proof.
  intros S F E C s H gamma delta T. constructor.
  exact (generic_intuitionistic_prover_verum_right_raw H gamma delta T).
Qed.

(** Source declaration [IntProver.Theorems.falsum_right]. *)
Definition generic_intuitionistic_prover_falsum_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (T ++ [GTS_mk gamma delta])) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_bottom C :: delta) :: T) :=
  generic_two_sided_tableau_valid_falsum_right_raw H
    (generic_intuitionistic_prover_rotate_raw v).

Lemma generic_intuitionistic_prover_falsum_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta T,
    generic_two_sided_tableau_valid E s C
      (T ++ [GTS_mk gamma delta]) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_bottom C :: delta) :: T).
Proof.
  intros S F E C s H gamma delta T [v]. constructor.
  exact (generic_intuitionistic_prover_falsum_right_raw H v).
Qed.

(** Source declaration [IntProver.Theorems.and_right]. *)
Definition generic_intuitionistic_prover_and_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (vp : generic_two_sided_tableau_validity E s C
      (T ++ [GTS_mk gamma (delta ++ [p])]))
    (vq : generic_two_sided_tableau_validity E s C
      (T ++ [GTS_mk gamma (delta ++ [q])])) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_and C p q :: delta) :: T) :=
  generic_two_sided_tableau_valid_and_right_raw H
    (generic_intuitionistic_prover_rotate_raw vp)
    (generic_intuitionistic_prover_rotate_raw vq).

Lemma generic_intuitionistic_prover_and_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q T,
    generic_two_sided_tableau_valid E s C
      (T ++ [GTS_mk gamma (delta ++ [p])]) ->
    generic_two_sided_tableau_valid E s C
      (T ++ [GTS_mk gamma (delta ++ [q])]) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_and C p q :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p q T [vp] [vq]. constructor.
  exact (generic_intuitionistic_prover_and_right_raw H vp vq).
Qed.

(** Source declaration [IntProver.Theorems.or_right]. *)
Definition generic_intuitionistic_prover_or_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (T ++ [GTS_mk gamma (delta ++ [p; q])])) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_or C p q :: delta) :: T) :=
  generic_two_sided_tableau_valid_or_right_raw H
    (generic_intuitionistic_prover_rotate_raw v).

Lemma generic_intuitionistic_prover_or_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q T,
    generic_two_sided_tableau_valid E s C
      (T ++ [GTS_mk gamma (delta ++ [p; q])]) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_or C p q :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p q T [v]. constructor.
  exact (generic_intuitionistic_prover_or_right_raw H v).
Qed.

(** Source declaration [IntProver.Theorems.neg_right]. *)
Definition generic_intuitionistic_prover_neg_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      ((T ++ [GTS_mk (gamma ++ [p]) []]) ++ [GTS_mk gamma delta])) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_neg C p :: delta) :: T) :=
  generic_two_sided_tableau_valid_neg_right_prime_raw H
    (@generic_intuitionistic_prover_rotate_raw
      S F E C s (gamma ++ [p]) [] (GTS_mk gamma delta :: T)
      (@generic_intuitionistic_prover_rotate_raw
        S F E C s gamma delta
        (T ++ [GTS_mk (gamma ++ [p]) []]) v)).

Lemma generic_intuitionistic_prover_neg_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p T,
    generic_two_sided_tableau_valid E s C
      ((T ++ [GTS_mk (gamma ++ [p]) []]) ++ [GTS_mk gamma delta]) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_neg C p :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p T [v]. constructor.
  exact (generic_intuitionistic_prover_neg_right_raw H v).
Qed.

(** Source declaration [IntProver.Theorems.imply_right]. *)
Definition generic_intuitionistic_prover_imply_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      ((T ++ [GTS_mk (gamma ++ [p]) [q]]) ++ [GTS_mk gamma delta])) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_imp C p q :: delta) :: T) :=
  generic_two_sided_tableau_valid_imply_right_prime_raw H
    (@generic_intuitionistic_prover_rotate_raw
      S F E C s (gamma ++ [p]) [q] (GTS_mk gamma delta :: T)
      (@generic_intuitionistic_prover_rotate_raw
        S F E C s gamma delta
        (T ++ [GTS_mk (gamma ++ [p]) [q]]) v)).

Lemma generic_intuitionistic_prover_imply_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_intuitionistic_entailment E C s -> forall gamma delta p q T,
    generic_two_sided_tableau_valid E s C
      ((T ++ [GTS_mk (gamma ++ [p]) [q]]) ++ [GTS_mk gamma delta]) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_imp C p q :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p q T [v]. constructor.
  exact (generic_intuitionistic_prover_imply_right_raw H v).
Qed.

(** Source declaration [IntProver.Theorems.iff_right]. *)
Definition generic_intuitionistic_prover_iff_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (vpq : generic_two_sided_tableau_validity E s C
      (T ++ [GTS_mk gamma (delta ++ [generic_imp C p q])]))
    (vqp : generic_two_sided_tableau_validity E s C
      (T ++ [GTS_mk gamma (delta ++ [generic_imp C q p])])) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_formula_iff C p q :: delta) :: T) :=
  generic_two_sided_tableau_valid_and_right_raw H
    (generic_intuitionistic_prover_rotate_raw vpq)
    (generic_intuitionistic_prover_rotate_raw vqp).

Lemma generic_intuitionistic_prover_iff_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q T,
    generic_two_sided_tableau_valid E s C
      (T ++ [GTS_mk gamma (delta ++ [generic_imp C p q])]) ->
    generic_two_sided_tableau_valid E s C
      (T ++ [GTS_mk gamma (delta ++ [generic_imp C q p])]) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_formula_iff C p q :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p q T [vpq] [vqp]. constructor.
  exact (generic_intuitionistic_prover_iff_right_raw H vpq vqp).
Qed.

(** * Left rules *)

(** Source declaration [IntProver.Theorems.remove_left]. *)
Definition generic_intuitionistic_prover_remove_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {gamma delta : list F} {p : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk gamma delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (p :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_remove_left_raw v.

Lemma generic_intuitionistic_prover_remove_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta p T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (p :: gamma) delta :: T).
Proof.
  intros S F E C s gamma delta p T [v]. constructor.
  exact (generic_intuitionistic_prover_remove_left_raw v).
Qed.

(** Source declaration [IntProver.Theorems.rotate_left]. *)
Definition generic_intuitionistic_prover_rotate_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {gamma delta : list F} {p : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [p]) delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (p :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_rotate_left_raw v.

Lemma generic_intuitionistic_prover_rotate_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta p T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [p]) delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (p :: gamma) delta :: T).
Proof.
  intros S F E C s gamma delta p T [v]. constructor.
  exact (generic_intuitionistic_prover_rotate_left_raw v).
Qed.

(** Source declaration [IntProver.Theorems.verum_left]. *)
Definition generic_intuitionistic_prover_verum_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {gamma delta : list F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk gamma delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (generic_top C :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_verum_left_raw v.

Lemma generic_intuitionistic_prover_verum_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (generic_top C :: gamma) delta :: T).
Proof.
  intros S F E C s gamma delta T [v]. constructor.
  exact (generic_intuitionistic_prover_verum_left_raw v).
Qed.

(** Source declaration [IntProver.Theorems.falsum_left]. *)
Definition generic_intuitionistic_prover_falsum_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    (gamma delta : list F) (T : generic_two_sided_tableau F) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (generic_bottom C :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_falsum_left_raw H gamma delta T.

Lemma generic_intuitionistic_prover_falsum_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_intuitionistic_entailment E C s -> forall gamma delta T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (generic_bottom C :: gamma) delta :: T).
Proof.
  intros S F E C s H gamma delta T. constructor.
  exact (generic_intuitionistic_prover_falsum_left_raw H gamma delta T).
Qed.

(** Source declaration [IntProver.Theorems.or_left]. *)
Definition generic_intuitionistic_prover_or_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (vp : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [p]) delta :: T))
    (vq : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [q]) delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (generic_or C p q :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_or_left_raw H vp vq.

Lemma generic_intuitionistic_prover_or_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [p]) delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [q]) delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (generic_or C p q :: gamma) delta :: T).
Proof.
  intros S F E C s H gamma delta p q T [vp] [vq]. constructor.
  exact (generic_intuitionistic_prover_or_left_raw H vp vq).
Qed.

(** Source declaration [IntProver.Theorems.and_left]. *)
Definition generic_intuitionistic_prover_and_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [p; q]) delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (generic_and C p q :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_and_left_raw H v.

Lemma generic_intuitionistic_prover_and_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [p; q]) delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (generic_and C p q :: gamma) delta :: T).
Proof.
  intros S F E C s H gamma delta p q T [v]. constructor.
  exact (generic_intuitionistic_prover_and_left_raw H v).
Qed.

(** Source declaration [IntProver.Theorems.neg_left]. *)
Definition generic_intuitionistic_prover_neg_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [generic_neg C p]) (delta ++ [p]) :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (generic_neg C p :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_neg_left_raw H v.

Lemma generic_intuitionistic_prover_neg_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [generic_neg C p]) (delta ++ [p]) :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (generic_neg C p :: gamma) delta :: T).
Proof.
  intros S F E C s H gamma delta p T [v]. constructor.
  exact (generic_intuitionistic_prover_neg_left_raw H v).
Qed.

(** Source declaration [IntProver.Theorems.imply_left]. *)
Definition generic_intuitionistic_prover_imply_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (vp : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [generic_imp C p q]) (delta ++ [p]) :: T))
    (vq : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [q]) delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (generic_imp C p q :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_imply_left_raw H vp vq.

Lemma generic_intuitionistic_prover_imply_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [generic_imp C p q]) (delta ++ [p]) :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [q]) delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (generic_imp C p q :: gamma) delta :: T).
Proof.
  intros S F E C s H gamma delta p q T [vp] [vq]. constructor.
  exact (generic_intuitionistic_prover_imply_left_raw H vp vq).
Qed.

(** Source declaration [IntProver.Theorems.iff_left]. *)
Definition generic_intuitionistic_prover_iff_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk
        (gamma ++ [generic_imp C p q; generic_imp C q p]) delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (generic_formula_iff C p q :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_and_left_raw H v.

Lemma generic_intuitionistic_prover_iff_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk
        (gamma ++ [generic_imp C p q; generic_imp C q p]) delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (generic_formula_iff C p q :: gamma) delta :: T).
Proof.
  intros S F E C s H gamma delta p q T [v]. constructor.
  exact (generic_intuitionistic_prover_iff_left_raw H v).
Qed.
