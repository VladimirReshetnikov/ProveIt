(** Standalone propositional axiom capabilities.

    This module ports the small [Entailment/Axiom{DNE,EFQ,ElimContra,LEM,
    Peirce}.lean] family and [Entailment/Int/DNE_of_LEM.lean].  Each source
    typeclass becomes an explicit raw-proof capability, with its
    inhabited-provability view factored once.  The final transport definitions
    generalize both finite and predicate context instances: any
    formula-uniform proof embedding preserves every capability.
*)

From FoundationModal Require Import
  GenericSemantics GenericEntailment GenericCalculus.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Formula schemata *)

Definition generic_axiom_efq {F : Type}
    (C : generic_connectives F) (p : F) : F :=
  generic_imp C (generic_bottom C) p.

Definition generic_axiom_lem {F : Type}
    (C : generic_connectives F) (p : F) : F :=
  generic_or C p (generic_neg C p).

Definition generic_axiom_elim_contra {F : Type}
    (C : generic_connectives F) (p q : F) : F :=
  generic_imp C
    (generic_imp C (generic_neg C q) (generic_neg C p))
    (generic_imp C p q).

Definition generic_axiom_peirce {F : Type}
    (C : generic_connectives F) (p q : F) : F :=
  generic_imp C (generic_imp C (generic_imp C p q) p) p.

(** [generic_axiom_dne] is shared with the classical-calculus interface in
    [GenericCalculus]. *)

(** * Independent raw-proof capabilities *)

Record generic_has_axiom_dne {S F : Type}
    (E : generic_entailment S F) (C : generic_connectives F) (s : S) : Type := {
  generic_dne_raw : forall p,
    generic_proof E s (generic_axiom_dne C p)
}.

Record generic_has_axiom_efq {S F : Type}
    (E : generic_entailment S F) (C : generic_connectives F) (s : S) : Type := {
  generic_efq_raw : forall p,
    generic_proof E s (generic_axiom_efq C p)
}.

Record generic_has_axiom_elim_contra {S F : Type}
    (E : generic_entailment S F) (C : generic_connectives F) (s : S) : Type := {
  generic_elim_contra_raw : forall p q,
    generic_proof E s (generic_axiom_elim_contra C p q)
}.

Record generic_has_axiom_lem {S F : Type}
    (E : generic_entailment S F) (C : generic_connectives F) (s : S) : Type := {
  generic_lem_raw : forall p,
    generic_proof E s (generic_axiom_lem C p)
}.

Record generic_has_axiom_peirce {S F : Type}
    (E : generic_entailment S F) (C : generic_connectives F) (s : S) : Type := {
  generic_peirce_raw : forall p q,
    generic_proof E s (generic_axiom_peirce C p q)
}.

Arguments generic_dne_raw {S F E C s} _ _.
Arguments generic_efq_raw {S F E C s} _ _.
Arguments generic_elim_contra_raw {S F E C s} _ _ _.
Arguments generic_lem_raw {S F E C s} _ _.
Arguments generic_peirce_raw {S F E C s} _ _ _.

(** * Inhabited theorem views *)

Lemma generic_dne_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_has_axiom_dne E C s ->
    forall p, generic_provable E s (generic_axiom_dne C p).
Proof. intros S F E C s H p; constructor; exact (generic_dne_raw H p). Qed.

Lemma generic_efq_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_has_axiom_efq E C s ->
    forall p, generic_provable E s (generic_axiom_efq C p).
Proof. intros S F E C s H p; constructor; exact (generic_efq_raw H p). Qed.

Lemma generic_elim_contra_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_has_axiom_elim_contra E C s ->
    forall p q, generic_provable E s (generic_axiom_elim_contra C p q).
Proof.
  intros S F E C s H p q; constructor; exact (generic_elim_contra_raw H p q).
Qed.

Lemma generic_lem_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_has_axiom_lem E C s ->
    forall p, generic_provable E s (generic_axiom_lem C p).
Proof. intros S F E C s H p; constructor; exact (generic_lem_raw H p). Qed.

Lemma generic_peirce_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_has_axiom_peirce E C s ->
    forall p q, generic_provable E s (generic_axiom_peirce C p q).
Proof.
  intros S F E C s H p q; constructor; exact (generic_peirce_raw H p q).
Qed.

(** * Elimination consequences *)

Definition generic_double_negation_elim_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (Hmp : generic_modus_ponens E C s)
    (Hdne : generic_has_axiom_dne E C s) (p : F)
    (b : generic_proof E s (generic_neg C (generic_neg C p))) :
    generic_proof E s p :=
  generic_modus_ponens_raw Hmp
    (generic_neg C (generic_neg C p)) p (generic_dne_raw Hdne p) b.

Lemma generic_double_negation_elim_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_modus_ponens E C s -> generic_has_axiom_dne E C s ->
    forall p,
      generic_provable E s (generic_neg C (generic_neg C p)) ->
      generic_provable E s p.
Proof.
  intros S F E C s Hmp Hdne p [b]. constructor.
  exact (@generic_double_negation_elim_raw S F E C s Hmp Hdne p b).
Qed.

Definition generic_efq_elim_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (Hmp : generic_modus_ponens E C s)
    (Hefq : generic_has_axiom_efq E C s) (p : F)
    (b : generic_proof E s (generic_bottom C)) : generic_proof E s p :=
  generic_modus_ponens_raw Hmp (generic_bottom C) p
    (generic_efq_raw Hefq p) b.

Lemma generic_efq_elim_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_modus_ponens E C s -> generic_has_axiom_efq E C s ->
    generic_provable E s (generic_bottom C) ->
    forall p, generic_provable E s p.
Proof.
  intros S F E C s Hmp Hefq [b] p. constructor.
  exact (@generic_efq_elim_raw S F E C s Hmp Hefq p b).
Qed.

Definition generic_deductive_explosion_of_efq {S F : Type}
    (E : generic_entailment S F) (C : generic_connectives F)
    (Hmp : forall s, generic_modus_ponens E C s)
    (Hefq : forall s, generic_has_axiom_efq E C s) :
    generic_deductive_explosion E (generic_bottom C).
Proof.
  constructor. intros s b p.
  exact (@generic_efq_elim_raw S F E C s (Hmp s) (Hefq s) p b).
Defined.

(** * Shared implicational combinators *)

Definition generic_imp_identity_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (Hmp : generic_modus_ponens E C s)
    (HK : forall p q, generic_proof E s (generic_axiom_K C p q))
    (HS : forall p q r, generic_proof E s (generic_axiom_S C p q r))
    (p : F) : generic_proof E s (generic_imp C p p) :=
  generic_modus_ponens_raw Hmp _ _
    (generic_modus_ponens_raw Hmp _ _
      (HS p (generic_imp C p p) p)
      (HK p (generic_imp C p p)))
    (HK p p).

Definition generic_dhyp_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (Hmp : generic_modus_ponens E C s)
    (HK : forall p q, generic_proof E s (generic_axiom_K C p q))
    (p q : F) (d : generic_proof E s p) :
    generic_proof E s (generic_imp C q p) :=
  generic_modus_ponens_raw Hmp _ _ (HK p q) d.

Definition generic_under_apply_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (Hmp : generic_modus_ponens E C s)
    (HS : forall p q r, generic_proof E s (generic_axiom_S C p q r))
    (a b c : F)
    (df : generic_proof E s
      (generic_imp C a (generic_imp C b c)))
    (dx : generic_proof E s (generic_imp C a b)) :
    generic_proof E s (generic_imp C a c) :=
  generic_modus_ponens_raw Hmp _ _
    (generic_modus_ponens_raw Hmp _ _ (HS a b c) df) dx.

Definition generic_imp_trans_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (Hmp : generic_modus_ponens E C s)
    (HK : forall p q, generic_proof E s (generic_axiom_K C p q))
    (HS : forall p q r, generic_proof E s (generic_axiom_S C p q r))
    (a b c : F)
    (dab : generic_proof E s (generic_imp C a b))
    (dbc : generic_proof E s (generic_imp C b c)) :
    generic_proof E s (generic_imp C a c) :=
  @generic_under_apply_raw S F E C s Hmp HS a b c
    (@generic_dhyp_raw S F E C s Hmp HK
      (generic_imp C b c) a dbc) dab.

(** Foundation proves this through finite-context deduction and assumes full
    intuitionistic entailment plus decidable formula equality.  The following
    direct Hilbert derivation needs only the rules it actually invokes. *)
Definition generic_dne_of_lem_efq_raw {S F : Type}
    {E : generic_entailment S F} {C : generic_connectives F} {s : S}
    (Hmp : generic_modus_ponens E C s)
    (HK : forall p q, generic_proof E s (generic_axiom_K C p q))
    (HS : forall p q r, generic_proof E s (generic_axiom_S C p q r))
    (Hor3 : forall p q r, generic_proof E s (generic_axiom_or3 C p q r))
    (Hlem : generic_has_axiom_lem E C s)
    (Hefq : generic_has_axiom_efq E C s)
    (Hneg_to_imp : forall p, generic_proof E s
      (generic_imp C (generic_neg C p)
        (generic_imp C p (generic_bottom C))))
    (p : F) : generic_proof E s (generic_axiom_dne C p).
Proof.
  set (n := generic_neg C p).
  set (nn := generic_neg C n).
  pose (defq := generic_efq_raw Hefq p).
  pose (dn_to_p := generic_modus_ponens_raw Hmp _ _
    (HS n (generic_bottom C) p)
    (@generic_dhyp_raw S F E C s Hmp HK
      (generic_imp C (generic_bottom C) p) n defq)).
  pose (dbranch := @generic_imp_trans_raw S F E C s Hmp HK HS nn
    (generic_imp C n (generic_bottom C)) (generic_imp C n p)
    (Hneg_to_imp n) dn_to_p).
  pose (dcases := Hor3 p n p).
  pose (d0 := @generic_dhyp_raw S F E C s Hmp HK _ nn dcases).
  pose (did := @generic_imp_identity_raw S F E C s Hmp HK HS p).
  pose (d1 := @generic_under_apply_raw S F E C s Hmp HS nn
    (generic_imp C p p)
    (generic_imp C (generic_imp C n p)
      (generic_imp C (generic_or C p n) p))
    d0 (@generic_dhyp_raw S F E C s Hmp HK _ nn did)).
  pose (d2 := @generic_under_apply_raw S F E C s Hmp HS nn
    (generic_imp C n p) (generic_imp C (generic_or C p n) p)
    d1 dbranch).
  pose (d3 := @generic_under_apply_raw S F E C s Hmp HS nn
    (generic_or C p n) p d2
    (@generic_dhyp_raw S F E C s Hmp HK _ nn
      (generic_lem_raw Hlem p))).
  exact d3.
Defined.

Lemma generic_dne_of_lem_efq_provable :
  forall (S F : Type) (E : generic_entailment S F)
         (C : generic_connectives F) (s : S),
    generic_modus_ponens E C s ->
    (forall p q, generic_proof E s (generic_axiom_K C p q)) ->
    (forall p q r, generic_proof E s (generic_axiom_S C p q r)) ->
    (forall p q r, generic_proof E s (generic_axiom_or3 C p q r)) ->
    generic_has_axiom_lem E C s -> generic_has_axiom_efq E C s ->
    (forall p, generic_proof E s
      (generic_imp C (generic_neg C p)
        (generic_imp C p (generic_bottom C)))) ->
    forall p, generic_provable E s (generic_axiom_dne C p).
Proof.
  intros S F E C s Hmp HK HS Hor3 Hlem Hefq Hneg p. constructor.
  exact (@generic_dne_of_lem_efq_raw S F E C s
    Hmp HK HS Hor3 Hlem Hefq Hneg p).
Qed.

(** * Formula-uniform transport

    This single abstraction subsumes the source's duplicate finite-context
    and predicate-context instances, and also permits transport between
    entirely different proof-system representations. *)

Definition generic_raw_proof_translation {S T F : Type}
    (ES : generic_entailment S F) (ET : generic_entailment T F)
    (s : S) (t : T) : Type :=
  forall p, generic_proof ES s p -> generic_proof ET t p.

Definition generic_has_axiom_dne_map {S T F : Type}
    {ES : generic_entailment S F} {ET : generic_entailment T F}
    {C : generic_connectives F} {s : S} {t : T}
    (f : generic_raw_proof_translation ES ET s t)
    (H : generic_has_axiom_dne ES C s) : generic_has_axiom_dne ET C t :=
  {| generic_dne_raw := fun p => f _ (generic_dne_raw H p) |}.

Definition generic_has_axiom_efq_map {S T F : Type}
    {ES : generic_entailment S F} {ET : generic_entailment T F}
    {C : generic_connectives F} {s : S} {t : T}
    (f : generic_raw_proof_translation ES ET s t)
    (H : generic_has_axiom_efq ES C s) : generic_has_axiom_efq ET C t :=
  {| generic_efq_raw := fun p => f _ (generic_efq_raw H p) |}.

Definition generic_has_axiom_elim_contra_map {S T F : Type}
    {ES : generic_entailment S F} {ET : generic_entailment T F}
    {C : generic_connectives F} {s : S} {t : T}
    (f : generic_raw_proof_translation ES ET s t)
    (H : generic_has_axiom_elim_contra ES C s) :
    generic_has_axiom_elim_contra ET C t :=
  {| generic_elim_contra_raw :=
       fun p q => f _ (generic_elim_contra_raw H p q) |}.

Definition generic_has_axiom_lem_map {S T F : Type}
    {ES : generic_entailment S F} {ET : generic_entailment T F}
    {C : generic_connectives F} {s : S} {t : T}
    (f : generic_raw_proof_translation ES ET s t)
    (H : generic_has_axiom_lem ES C s) : generic_has_axiom_lem ET C t :=
  {| generic_lem_raw := fun p => f _ (generic_lem_raw H p) |}.

Definition generic_has_axiom_peirce_map {S T F : Type}
    {ES : generic_entailment S F} {ET : generic_entailment T F}
    {C : generic_connectives F} {s : S} {t : T}
    (f : generic_raw_proof_translation ES ET s t)
    (H : generic_has_axiom_peirce ES C s) : generic_has_axiom_peirce ET C t :=
  {| generic_peirce_raw :=
       fun p q => f _ (generic_peirce_raw H p q) |}.
