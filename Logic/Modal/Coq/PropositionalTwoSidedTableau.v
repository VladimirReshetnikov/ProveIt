(** Proof-relevant validity for finite tableaux of two-sided sequents.

    This module ports the [Tableaux.Sequent] and [Tableaux.Valid] half of
    [Foundation/Meta/TwoSided.lean].  A raw validity witness records the
    position of a derivable sequent in a tableau and retains its raw
    derivation in [Type].  The public proposition is the inhabited view of
    that raw witness.

    Positional membership and inclusion avoid formula or sequent equality
    decisions, preserve duplicates, and keep every raw construction fully
    constructive. *)

From Stdlib Require Import Lists.List Program.Equality.
From FoundationModal Require Import
  GenericSemantics GenericEntailment GenericLogicSymbol GenericCalculus
  PropositionalEntailmentAxioms PropositionalEntailmentMinimal
  PropositionalEntailmentInt PropositionalEntailmentClassical
  PropositionalTwoSided.

Import ListNotations.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Sequents, tableaux, and raw validity *)

Record generic_two_sided_sequent@{u} (F : Type@{u}) : Type@{u} := GTS_mk {
  generic_two_sided_antecedent : list F;
  generic_two_sided_succedent : list F
}.

Arguments GTS_mk {F} _ _.
Arguments generic_two_sided_antecedent {F} _.
Arguments generic_two_sided_succedent {F} _.

Definition generic_two_sided_tableau (F : Type) : Type :=
  list (generic_two_sided_sequent F).

Definition generic_two_sided_sequent_derivation {S F : Type}
    (E : generic_entailment S F) (s : S) (C : generic_connectives F)
    (q : generic_two_sided_sequent F) : Type :=
  generic_two_sided_derivation E s C
    (generic_two_sided_antecedent q)
    (generic_two_sided_succedent q).

Inductive generic_two_sided_tableau_validity {S F : Type}
    (E : generic_entailment S F) (s : S) (C : generic_connectives F) :
    generic_two_sided_tableau F -> Type :=
| GTTV_head : forall gamma delta tau,
    generic_two_sided_derivation E s C gamma delta ->
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma delta :: tau)
| GTTV_tail : forall q tau,
    generic_two_sided_tableau_validity E s C tau ->
    generic_two_sided_tableau_validity E s C (q :: tau).

Arguments GTTV_head {S F E s C gamma delta tau} _.
Arguments GTTV_tail {S F E s C q tau} _.

Definition generic_two_sided_tableau_valid {S F : Type}
    (E : generic_entailment S F) (s : S) (C : generic_connectives F)
    (tau : generic_two_sided_tableau F) : Prop :=
  inhabited (generic_two_sided_tableau_validity E s C tau).

Lemma generic_two_sided_tableau_valid_head :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta tau,
    generic_two_sided_derivable E s C gamma delta ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma delta :: tau).
Proof.
  intros S F E C s gamma delta tau [d]. constructor.
  exact (GTTV_head d).
Qed.

Lemma generic_two_sided_tableau_valid_tail :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) q tau,
    generic_two_sided_tableau_valid E s C tau ->
    generic_two_sided_tableau_valid E s C (q :: tau).
Proof.
  intros S F E C s q tau [v]. constructor.
  exact (GTTV_tail v).
Qed.

(** * Structural validity operations *)

Definition generic_two_sided_tableau_validity_nil_elim {S F A : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (v : generic_two_sided_tableau_validity E s C []) : A.
Proof.
  exact (match v in generic_two_sided_tableau_validity _ _ _ tau return
    match tau with
    | [] => A
    | _ => unit
    end
  with
  | GTTV_head _ => tt
  | GTTV_tail _ => tt
  end).
Defined.

Lemma generic_two_sided_tableau_valid_not_nil :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    ~ generic_two_sided_tableau_valid E s C [].
Proof.
  intros S F E C s [v].
  exact (generic_two_sided_tableau_validity_nil_elim v).
Qed.

Fixpoint generic_two_sided_tableau_valid_of_member_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {gamma delta : list F} {tau : generic_two_sided_tableau F}
    (d : generic_two_sided_derivation E s C gamma delta)
    (h : generic_raw_list_member (GTS_mk gamma delta) tau) {struct h} :
    generic_two_sided_tableau_validity E s C tau.
Proof.
  dependent destruction h.
  - exact (GTTV_head d).
  - exact (GTTV_tail
      (@generic_two_sided_tableau_valid_of_member_raw
        S F E C s gamma delta _ d h)).
Defined.

Lemma generic_two_sided_tableau_valid_of_member :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta tau,
    generic_two_sided_derivable E s C gamma delta ->
    generic_raw_list_member (GTS_mk gamma delta) tau ->
    generic_two_sided_tableau_valid E s C tau.
Proof.
  intros S F E C s gamma delta tau [d] h. constructor.
  exact (generic_two_sided_tableau_valid_of_member_raw d h).
Qed.

Fixpoint generic_two_sided_tableau_valid_of_subset_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {sigma tau : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C sigma)
    (incl : generic_raw_list_subset sigma tau) {struct v} :
    generic_two_sided_tableau_validity E s C tau.
Proof.
  destruct v as [gamma delta rest d | q rest vrest].
  - exact (generic_two_sided_tableau_valid_of_member_raw d
      (incl (GTS_mk gamma delta) (GRLM_here rest))).
  - apply (@generic_two_sided_tableau_valid_of_subset_raw
      S F E C s rest tau vrest).
    intros r hr. exact (incl r (GRLM_there q hr)).
Defined.

Lemma generic_two_sided_tableau_valid_of_subset :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) sigma tau,
    generic_two_sided_tableau_valid E s C sigma ->
    generic_raw_list_subset sigma tau ->
    generic_two_sided_tableau_valid E s C tau.
Proof.
  intros S F E C s sigma tau [v] incl. constructor.
  exact (generic_two_sided_tableau_valid_of_subset_raw v incl).
Qed.

Definition generic_two_sided_tableau_valid_of_single_uppercedent_raw
    {S F : Type} {E : generic_entailment S F}
    {C : generic_connectives F} {s : S}
    {gamma delta xi lambda : list F}
    {T : generic_two_sided_tableau F}
    (H : generic_two_sided_derivation E s C gamma delta ->
         generic_two_sided_derivation E s C xi lambda)
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk gamma delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk xi lambda :: T).
Proof.
  exact ((match v in generic_two_sided_tableau_validity _ _ _ tau return
      match tau with
      | [] => unit
      | q :: rest =>
          (generic_two_sided_sequent_derivation E s C q ->
           generic_two_sided_derivation E s C xi lambda) ->
          generic_two_sided_tableau_validity E s C
            (GTS_mk xi lambda :: rest)
      end
    with
    | GTTV_head d => fun K => GTTV_head (K d)
    | GTTV_tail vt => fun _ => GTTV_tail vt
    end) H).
Defined.

Lemma generic_two_sided_tableau_valid_of_single_uppercedent :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S)
         gamma delta xi lambda T,
    (generic_two_sided_derivable E s C gamma delta ->
     generic_two_sided_derivable E s C xi lambda) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk xi lambda :: T).
Proof.
  intros S F E C s gamma delta xi lambda T H [v].
  refine (match v in generic_two_sided_tableau_validity _ _ _ tau return
      match tau with
      | [] => True
      | q :: rest =>
          (generic_two_sided_derivable E s C
             (generic_two_sided_antecedent q)
             (generic_two_sided_succedent q) ->
           generic_two_sided_derivable E s C xi lambda) ->
          generic_two_sided_tableau_valid E s C
            (GTS_mk xi lambda :: rest)
      end
    with
    | GTTV_head d => fun K => _
    | GTTV_tail vt => fun _ => inhabits (GTTV_tail vt)
    end H).
  destruct (K (inhabits d)) as [d']. exact (inhabits (GTTV_head d')).
Qed.

Definition generic_two_sided_tableau_valid_of_double_uppercedent_raw
    {S F : Type} {E : generic_entailment S F}
    {C : generic_connectives F} {s : S}
    {gamma1 delta1 gamma2 delta2 xi lambda : list F}
    {T : generic_two_sided_tableau F}
    (H : generic_two_sided_derivation E s C gamma1 delta1 ->
         generic_two_sided_derivation E s C gamma2 delta2 ->
         generic_two_sided_derivation E s C xi lambda)
    (v1 : generic_two_sided_tableau_validity E s C
      (GTS_mk gamma1 delta1 :: T))
    (v2 : generic_two_sided_tableau_validity E s C
      (GTS_mk gamma2 delta2 :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk xi lambda :: T).
Proof.
  exact ((match v1 in generic_two_sided_tableau_validity _ _ _ tau return
      match tau with
      | [] => unit
      | q1 :: rest =>
          generic_two_sided_tableau_validity E s C
            (GTS_mk gamma2 delta2 :: rest) ->
          (generic_two_sided_sequent_derivation E s C q1 ->
           generic_two_sided_tableau_validity E s C
             (GTS_mk gamma2 delta2 :: rest) ->
           generic_two_sided_tableau_validity E s C
             (GTS_mk xi lambda :: rest)) ->
          generic_two_sided_tableau_validity E s C
            (GTS_mk xi lambda :: rest)
      end
    with
    | GTTV_head d1 => fun w2 K => K d1 w2
    | GTTV_tail vt => fun _ _ => GTTV_tail vt
    end) v2
    (fun d1 w2 =>
      (match w2 in generic_two_sided_tableau_validity _ _ _ tau return
         match tau with
         | [] => unit
         | q2 :: rest =>
             (generic_two_sided_sequent_derivation E s C q2 ->
              generic_two_sided_tableau_validity E s C
                (GTS_mk xi lambda :: rest)) ->
             generic_two_sided_tableau_validity E s C
               (GTS_mk xi lambda :: rest)
         end
       with
       | GTTV_head d2 => fun K => K d2
       | GTTV_tail vt => fun _ => GTTV_tail vt
       end) (fun d2 => GTTV_head (H d1 d2)))).
Defined.

Lemma generic_two_sided_tableau_valid_of_double_uppercedent :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S)
         gamma1 delta1 gamma2 delta2 xi lambda T,
    (generic_two_sided_derivable E s C gamma1 delta1 ->
     generic_two_sided_derivable E s C gamma2 delta2 ->
     generic_two_sided_derivable E s C xi lambda) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma1 delta1 :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma2 delta2 :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk xi lambda :: T).
Proof.
  intros S F E C s gamma1 delta1 gamma2 delta2 xi lambda T
    H [v1] [v2].
  refine ((match v1 in generic_two_sided_tableau_validity _ _ _ tau return
      match tau with
      | [] => True
      | q1 :: rest =>
          generic_two_sided_tableau_validity E s C
            (GTS_mk gamma2 delta2 :: rest) ->
          (generic_two_sided_derivable E s C
             (generic_two_sided_antecedent q1)
             (generic_two_sided_succedent q1) ->
           generic_two_sided_tableau_validity E s C
             (GTS_mk gamma2 delta2 :: rest) ->
           generic_two_sided_tableau_valid E s C
             (GTS_mk xi lambda :: rest)) ->
          generic_two_sided_tableau_valid E s C
            (GTS_mk xi lambda :: rest)
      end
    with
    | GTTV_head d1 => fun w2 K => K (inhabits d1) w2
    | GTTV_tail vt => fun _ _ => inhabits (GTTV_tail vt)
    end) v2 _).
  intros hd1 w2.
  refine ((match w2 in generic_two_sided_tableau_validity _ _ _ tau return
      match tau with
      | [] => True
      | q2 :: rest =>
          (generic_two_sided_derivable E s C
             (generic_two_sided_antecedent q2)
             (generic_two_sided_succedent q2) ->
           generic_two_sided_tableau_valid E s C
             (GTS_mk xi lambda :: rest)) ->
          generic_two_sided_tableau_valid E s C
            (GTS_mk xi lambda :: rest)
      end
    with
    | GTTV_head d2 => fun K => K (inhabits d2)
    | GTTV_tail vt => fun _ => inhabits (GTTV_tail vt)
    end) _).
  intro hd2. destruct (H hd1 hd2) as [d].
  exact (inhabits (GTTV_head d)).
Qed.

Definition generic_two_sided_tableau_valid_remove_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (gamma delta : list F) {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C T) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma delta :: T) :=
  GTTV_tail v.

Lemma generic_two_sided_tableau_valid_remove :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta T,
    generic_two_sided_tableau_valid E s C T ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma delta :: T).
Proof.
  intros S F E C s gamma delta T [v]. constructor.
  exact (generic_two_sided_tableau_valid_remove_raw gamma delta v).
Qed.

Definition generic_two_sided_tableau_valid_to_proof_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s) {p : F}
    (v : generic_two_sided_tableau_validity E s C [GTS_mk [] [p]]) :
    generic_proof E s p.
Proof.
  exact ((match v in generic_two_sided_tableau_validity _ _ _ tau return
      match tau with
      | [] => unit
      | q :: rest =>
          (generic_two_sided_sequent_derivation E s C q ->
           match rest with [] => generic_proof E s p | _ => unit end) ->
          match rest with [] => generic_proof E s p | _ => unit end
      end
    with
    | GTTV_head d => fun K => K d
    | GTTV_tail vt =>
        fun _ =>
          match vt in generic_two_sided_tableau_validity _ _ _ tau return
            match tau with [] => generic_proof E s p | _ => unit end
          with
          | GTTV_head _ => tt
          | GTTV_tail _ => tt
          end
    end) (fun d => generic_two_sided_to_proof_raw H d)).
Defined.

Lemma generic_two_sided_tableau_valid_to_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_intuitionistic_entailment E C s -> forall p,
    generic_two_sided_tableau_valid E s C [GTS_mk [] [p]] ->
    generic_provable E s p.
Proof.
  intros S F E C s H p [v]. constructor.
  exact (generic_two_sided_tableau_valid_to_proof_raw H v).
Qed.

(** A common traversal for source rules whose tableau premise has two
    distinguished leading sequents. *)
Definition generic_two_sided_tableau_valid_of_either_uppercedent_raw
    {S F : Type} {E : generic_entailment S F}
    {C : generic_connectives F} {s : S}
    {agamma adelta bgamma bdelta cgamma cdelta : list F}
    {T : generic_two_sided_tableau F}
    (Ha : generic_two_sided_derivation E s C agamma adelta ->
          generic_two_sided_derivation E s C cgamma cdelta)
    (Hb : generic_two_sided_derivation E s C bgamma bdelta ->
          generic_two_sided_derivation E s C cgamma cdelta)
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk agamma adelta :: GTS_mk bgamma bdelta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk cgamma cdelta :: T).
Proof.
  exact ((match v in generic_two_sided_tableau_validity _ _ _ tau return
      match tau with
      | [] => unit
      | q :: rest =>
          (generic_two_sided_sequent_derivation E s C q ->
           generic_two_sided_derivation E s C cgamma cdelta) ->
          match rest with
          | [] => Type
          | r :: tail =>
              (generic_two_sided_sequent_derivation E s C r ->
               generic_two_sided_derivation E s C cgamma cdelta) ->
              generic_two_sided_tableau_validity E s C
                (GTS_mk cgamma cdelta :: tail)
          end
      end
    with
    | @GTTV_head _ _ _ _ _ gx gd rest dx =>
        fun Kx =>
          match rest as rest0 return
            match rest0 with
            | [] => Type
            | r :: tail =>
                (generic_two_sided_sequent_derivation E s C r ->
                 generic_two_sided_derivation E s C cgamma cdelta) ->
                generic_two_sided_tableau_validity E s C
                  (GTS_mk cgamma cdelta :: tail)
            end
          with
          | [] => unit
          | _ :: _ => fun _ => GTTV_head (Kx dx)
          end
    | GTTV_tail vr =>
        fun _ =>
          match vr in generic_two_sided_tableau_validity _ _ _ tau return
            match tau with
            | [] => Type
            | r :: tail =>
                (generic_two_sided_sequent_derivation E s C r ->
                 generic_two_sided_derivation E s C cgamma cdelta) ->
                generic_two_sided_tableau_validity E s C
                  (GTS_mk cgamma cdelta :: tail)
            end
          with
          | GTTV_head dr => fun Kr => GTTV_head (Kr dr)
          | GTTV_tail vt => fun _ => GTTV_tail vt
          end
    end) Ha Hb).
Defined.

(** * Lifted structural and connective rules *)

Definition generic_two_sided_tableau_valid_right_closed_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F} (T : generic_two_sided_tableau F)
    (hp : generic_raw_list_member p gamma) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (p :: delta) :: T) :=
  GTTV_head (generic_two_sided_right_closed_raw H hp).

Lemma generic_two_sided_tableau_valid_right_closed :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p T,
    generic_raw_list_member p gamma ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (p :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p T hp. constructor.
  exact (generic_two_sided_tableau_valid_right_closed_raw H T hp).
Qed.

Definition generic_two_sided_tableau_valid_left_closed_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F} (T : generic_two_sided_tableau F)
    (hp : generic_raw_list_member p delta) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (p :: gamma) delta :: T) :=
  GTTV_head (generic_two_sided_left_closed_raw H hp).

Lemma generic_two_sided_tableau_valid_left_closed :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p T,
    generic_raw_list_member p delta ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (p :: gamma) delta :: T).
Proof.
  intros S F E C s H gamma delta p T hp. constructor.
  exact (generic_two_sided_tableau_valid_left_closed_raw H T hp).
Qed.

Definition generic_two_sided_tableau_valid_remove_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk gamma delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (p :: delta) :: T) :=
  generic_two_sided_tableau_valid_of_single_uppercedent_raw
    (generic_two_sided_remove_right_raw H p) v.

Lemma generic_two_sided_tableau_valid_remove_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (p :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p T [v]. constructor.
  exact (generic_two_sided_tableau_valid_remove_right_raw H v).
Qed.

Definition generic_two_sided_tableau_valid_remove_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {gamma delta : list F} {p : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk gamma delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (p :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_of_single_uppercedent_raw
    (generic_two_sided_remove_left_raw p) v.

Lemma generic_two_sided_tableau_valid_remove_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta p T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (p :: gamma) delta :: T).
Proof.
  intros S F E C s gamma delta p T [v]. constructor.
  exact (generic_two_sided_tableau_valid_remove_left_raw v).
Qed.

Definition generic_two_sided_tableau_valid_rotate_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (delta ++ [p]) :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (p :: delta) :: T) :=
  generic_two_sided_tableau_valid_of_single_uppercedent_raw
    (generic_two_sided_rotate_right_raw H) v.

Lemma generic_two_sided_tableau_valid_rotate_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (delta ++ [p]) :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (p :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p T [v]. constructor.
  exact (generic_two_sided_tableau_valid_rotate_right_raw H v).
Qed.

Definition generic_two_sided_tableau_valid_rotate_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {gamma delta : list F} {p : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [p]) delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (p :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_of_single_uppercedent_raw
    generic_two_sided_rotate_left_raw v.

Lemma generic_two_sided_tableau_valid_rotate_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta p T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [p]) delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (p :: gamma) delta :: T).
Proof.
  intros S F E C s gamma delta p T [v]. constructor.
  exact (generic_two_sided_tableau_valid_rotate_left_raw v).
Qed.

Definition generic_two_sided_tableau_valid_verum_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    (gamma delta : list F) (T : generic_two_sided_tableau F) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_top C :: delta) :: T) :=
  GTTV_head (generic_two_sided_verum_right_raw H gamma delta).

Lemma generic_two_sided_tableau_valid_verum_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_top C :: delta) :: T).
Proof.
  intros S F E C s H gamma delta T. constructor.
  exact (generic_two_sided_tableau_valid_verum_right_raw H gamma delta T).
Qed.

Definition generic_two_sided_tableau_valid_falsum_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    (gamma delta : list F) (T : generic_two_sided_tableau F) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (generic_bottom C :: gamma) delta :: T) :=
  GTTV_head (generic_two_sided_falsum_left_raw H gamma delta).

Lemma generic_two_sided_tableau_valid_falsum_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_intuitionistic_entailment E C s -> forall gamma delta T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (generic_bottom C :: gamma) delta :: T).
Proof.
  intros S F E C s H gamma delta T. constructor.
  exact (generic_two_sided_tableau_valid_falsum_left_raw H gamma delta T).
Qed.

Definition generic_two_sided_tableau_valid_falsum_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk gamma delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_bottom C :: delta) :: T) :=
  generic_two_sided_tableau_valid_of_single_uppercedent_raw
    (generic_two_sided_falsum_right_raw H) v.

Lemma generic_two_sided_tableau_valid_falsum_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_bottom C :: delta) :: T).
Proof.
  intros S F E C s H gamma delta T [v]. constructor.
  exact (generic_two_sided_tableau_valid_falsum_right_raw H v).
Qed.

Definition generic_two_sided_tableau_valid_verum_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    {gamma delta : list F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk gamma delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (generic_top C :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_of_single_uppercedent_raw
    generic_two_sided_verum_left_raw v.

Lemma generic_two_sided_tableau_valid_verum_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S) gamma delta T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (generic_top C :: gamma) delta :: T).
Proof.
  intros S F E C s gamma delta T [v]. constructor.
  exact (generic_two_sided_tableau_valid_verum_left_raw v).
Qed.

Definition generic_two_sided_tableau_valid_and_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (vp : generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (delta ++ [p]) :: T))
    (vq : generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (delta ++ [q]) :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_and C p q :: delta) :: T) :=
  generic_two_sided_tableau_valid_of_double_uppercedent_raw
    (generic_two_sided_and_right_raw H) vp vq.

Lemma generic_two_sided_tableau_valid_and_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (delta ++ [p]) :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (delta ++ [q]) :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_and C p q :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p q T [vp] [vq]. constructor.
  exact (generic_two_sided_tableau_valid_and_right_raw H vp vq).
Qed.

Definition generic_two_sided_tableau_valid_or_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (vp : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [p]) delta :: T))
    (vq : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [q]) delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (generic_or C p q :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_of_double_uppercedent_raw
    (generic_two_sided_or_left_raw H) vp vq.

Lemma generic_two_sided_tableau_valid_or_left :
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
  exact (generic_two_sided_tableau_valid_or_left_raw H vp vq).
Qed.

Definition generic_two_sided_tableau_valid_or_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (delta ++ [p; q]) :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_or C p q :: delta) :: T) :=
  generic_two_sided_tableau_valid_of_single_uppercedent_raw
    (generic_two_sided_or_right_raw H) v.

Lemma generic_two_sided_tableau_valid_or_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (delta ++ [p; q]) :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_or C p q :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p q T [v]. constructor.
  exact (generic_two_sided_tableau_valid_or_right_raw H v).
Qed.

Definition generic_two_sided_tableau_valid_and_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [p; q]) delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (generic_and C p q :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_of_single_uppercedent_raw
    (generic_two_sided_and_left_raw H) v.

Lemma generic_two_sided_tableau_valid_and_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p q T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [p; q]) delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (generic_and C p q :: gamma) delta :: T).
Proof.
  intros S F E C s H gamma delta p q T [v]. constructor.
  exact (generic_two_sided_tableau_valid_and_left_raw H v).
Qed.

Definition generic_two_sided_tableau_valid_neg_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [p]) [] ::
       GTS_mk gamma (delta ++ [generic_neg C p]) :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_neg C p :: delta) :: T) :=
  @generic_two_sided_tableau_valid_of_either_uppercedent_raw
    S F E C s
    (gamma ++ [p]) [] gamma (delta ++ [generic_neg C p])
    gamma (generic_neg C p :: delta) T
    (fun d => generic_two_sided_neg_right_int_raw H d)
    (fun d => generic_two_sided_rotate_right_raw H d) v.

Lemma generic_two_sided_tableau_valid_neg_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [p]) [] ::
       GTS_mk gamma (delta ++ [generic_neg C p]) :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_neg C p :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p T [v]. constructor.
  exact (generic_two_sided_tableau_valid_neg_right_raw H v).
Qed.

Definition generic_two_sided_tableau_valid_neg_right_prime_raw
    {S F : Type} {E : generic_entailment S F}
    {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [p]) [] :: GTS_mk gamma delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_neg C p :: delta) :: T) :=
  @generic_two_sided_tableau_valid_of_either_uppercedent_raw
    S F E C s
    (gamma ++ [p]) [] gamma delta
    gamma (generic_neg C p :: delta) T
    (fun d => generic_two_sided_neg_right_int_raw H d)
    (fun d => generic_two_sided_remove_right_raw H (generic_neg C p) d) v.

Lemma generic_two_sided_tableau_valid_neg_right_prime :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [p]) [] :: GTS_mk gamma delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_neg C p :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p T [v]. constructor.
  exact (generic_two_sided_tableau_valid_neg_right_prime_raw H v).
Qed.

Definition generic_two_sided_tableau_valid_neg_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [generic_neg C p]) (delta ++ [p]) :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (generic_neg C p :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_of_single_uppercedent_raw
    (generic_two_sided_neg_left_int_raw H) v.

Lemma generic_two_sided_tableau_valid_neg_left :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_minimal_entailment E C s -> forall gamma delta p T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [generic_neg C p]) (delta ++ [p]) :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk (generic_neg C p :: gamma) delta :: T).
Proof.
  intros S F E C s H gamma delta p T [v]. constructor.
  exact (generic_two_sided_tableau_valid_neg_left_raw H v).
Qed.

Definition generic_two_sided_tableau_valid_imply_right_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [p]) [q] ::
       GTS_mk gamma (delta ++ [generic_imp C p q]) :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_imp C p q :: delta) :: T) :=
  @generic_two_sided_tableau_valid_of_either_uppercedent_raw
    S F E C s
    (gamma ++ [p]) [q] gamma (delta ++ [generic_imp C p q])
    gamma (generic_imp C p q :: delta) T
    (fun d => generic_two_sided_imply_right_int_raw H d)
    (fun d => generic_two_sided_rotate_right_raw
      (generic_intuitionistic_minimal H) d) v.

Lemma generic_two_sided_tableau_valid_imply_right :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_intuitionistic_entailment E C s ->
    forall gamma delta p q T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [p]) [q] ::
       GTS_mk gamma (delta ++ [generic_imp C p q]) :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_imp C p q :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p q T [v]. constructor.
  exact (generic_two_sided_tableau_valid_imply_right_raw H v).
Qed.

Definition generic_two_sided_tableau_valid_imply_right_prime_raw
    {S F : Type} {E : generic_entailment S F}
    {C : generic_connectives F} {s : S}
    (H : generic_intuitionistic_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (v : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [p]) [q] :: GTS_mk gamma delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk gamma (generic_imp C p q :: delta) :: T) :=
  @generic_two_sided_tableau_valid_of_either_uppercedent_raw
    S F E C s
    (gamma ++ [p]) [q] gamma delta
    gamma (generic_imp C p q :: delta) T
    (fun d => generic_two_sided_imply_right_int_raw H d)
    (fun d => generic_two_sided_remove_right_raw
      (generic_intuitionistic_minimal H) (generic_imp C p q) d) v.

Lemma generic_two_sided_tableau_valid_imply_right_prime :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_intuitionistic_entailment E C s ->
    forall gamma delta p q T,
    generic_two_sided_tableau_valid E s C
      (GTS_mk (gamma ++ [p]) [q] :: GTS_mk gamma delta :: T) ->
    generic_two_sided_tableau_valid E s C
      (GTS_mk gamma (generic_imp C p q :: delta) :: T).
Proof.
  intros S F E C s H gamma delta p q T [v]. constructor.
  exact (generic_two_sided_tableau_valid_imply_right_prime_raw H v).
Qed.

Definition generic_two_sided_tableau_valid_imply_left_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (H : generic_minimal_entailment E C s)
    {gamma delta : list F} {p q : F} {T : generic_two_sided_tableau F}
    (vp : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [generic_imp C p q]) (delta ++ [p]) :: T))
    (vq : generic_two_sided_tableau_validity E s C
      (GTS_mk (gamma ++ [q]) delta :: T)) :
    generic_two_sided_tableau_validity E s C
      (GTS_mk (generic_imp C p q :: gamma) delta :: T) :=
  generic_two_sided_tableau_valid_of_double_uppercedent_raw
    (generic_two_sided_imply_left_int_raw H) vp vq.

Lemma generic_two_sided_tableau_valid_imply_left :
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
  exact (generic_two_sided_tableau_valid_imply_left_raw H vp vq).
Qed.
