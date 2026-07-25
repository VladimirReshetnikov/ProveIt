(**
  The Hilbert calculus for classical normal modal logic K.

  Foundation presents normal modal Hilbert systems over the classical
  Lukasiewicz basis [K, S, elimination of contraposition], with modus ponens,
  necessitation, and substituted modal axiom instances.  Since this file is
  specifically the system K, its modal axiom is already a schema and no
  separate collection of named axioms is needed.

  The second half of the file gives a one-sided consequence relation over
  predicate-valued theories.  Necessitation deliberately remains a rule only
  for theorems: unrestricted necessitation in a context would invalidate the
  deduction theorem.  The contextual necessitation lemma at the end instead
  boxes every hypothesis, exactly as normal modal logic requires.
*)

From FoundationModal Require Import Syntax Axioms.

Set Implicit Arguments.
Unset Strict Implicit.

(** The three schemata of the classical Lukasiewicz basis.  Their names are
    prefixed to distinguish propositional K from the modal axiom [K]. *)
Definition Hilbert_imply_K {AtomType} (p q : formula AtomType)
    : formula AtomType :=
  Imp p (Imp q p).

Definition Hilbert_imply_S {AtomType} (p q r : formula AtomType)
    : formula AtomType :=
  Imp (Imp p (Imp q r)) (Imp (Imp p q) (Imp p r)).

Definition Hilbert_elim_contra {AtomType} (p q : formula AtomType)
    : formula AtomType :=
  Imp (Imp (Neg q) (Neg p)) (Imp p q).

(** The theoremhood judgement for K. *)
Inductive K_proves {AtomType : Type} : formula AtomType -> Prop :=
| Kp_imply_K : forall p q,
    K_proves (Hilbert_imply_K p q)
| Kp_imply_S : forall p q r,
    K_proves (Hilbert_imply_S p q r)
| Kp_elim_contra : forall p q,
    K_proves (Hilbert_elim_contra p q)
| Kp_modal_K : forall p q,
    K_proves (K p q)
| Kp_mp : forall p q,
    K_proves (Imp p q) -> K_proves p -> K_proves q
| Kp_nec : forall p,
    K_proves p -> K_proves (Box p).

Arguments Kp_imply_K {AtomType} p q.
Arguments Kp_imply_S {AtomType} p q r.
Arguments Kp_elim_contra {AtomType} p q.
Arguments Kp_modal_K {AtomType} p q.
Arguments Kp_mp {AtomType p q} _ _.
Arguments Kp_nec {AtomType p} _.

(** A recursor whose premises correspond directly to the semantic obligations
    in a soundness proof. *)
Lemma K_proves_fold :
  forall (AtomType : Type) (P : formula AtomType -> Prop),
    (forall p q, P (Hilbert_imply_K p q)) ->
    (forall p q r, P (Hilbert_imply_S p q r)) ->
    (forall p q, P (Hilbert_elim_contra p q)) ->
    (forall p q, P (K p q)) ->
    (forall p q, P (Imp p q) -> P p -> P q) ->
    (forall p, P p -> P (Box p)) ->
    forall p, K_proves p -> P p.
Proof.
  intros AtomType P HK HS HEC HM Hmp Hnec p Hp.
  induction Hp; eauto.
Qed.

(** The calculus is structural under arbitrary substitutions of atoms. *)
Lemma K_proves_substitute :
  forall (A B : Type) (sigma : A -> formula B) (p : formula A),
    K_proves p -> K_proves (substitute sigma p).
Proof.
  intros A B sigma p Hp; induction Hp; simpl.
  - apply Kp_imply_K.
  - apply Kp_imply_S.
  - apply Kp_elim_contra.
  - apply Kp_modal_K.
  - eapply Kp_mp; eauto.
  - apply Kp_nec; assumption.
Qed.

Definition K_proves_substitution := K_proves_substitute.

(** Basic implicational proof combinators. *)
Lemma K_proves_identity :
  forall (AtomType : Type) (p : formula AtomType),
    K_proves (Imp p p).
Proof.
  intros AtomType p.
  eapply Kp_mp.
  - eapply Kp_mp.
    + exact (Kp_imply_S p (Imp p p) p).
    + exact (Kp_imply_K p (Imp p p)).
  - exact (Kp_imply_K p p).
Qed.

Lemma K_proves_imply_intro :
  forall (AtomType : Type) (p q : formula AtomType),
    K_proves q -> K_proves (Imp p q).
Proof.
  intros AtomType p q Hq.
  eapply Kp_mp; [exact (Kp_imply_K q p) | exact Hq].
Qed.

Lemma K_proves_under_mp :
  forall (AtomType : Type) (p q r : formula AtomType),
    K_proves (Imp p (Imp q r)) ->
    K_proves (Imp p q) ->
    K_proves (Imp p r).
Proof.
  intros AtomType p q r Hqr Hq.
  eapply Kp_mp.
  - eapply Kp_mp; [exact (Kp_imply_S p q r) | exact Hqr].
  - exact Hq.
Qed.

Lemma K_proves_imp_trans :
  forall (AtomType : Type) (p q r : formula AtomType),
    K_proves (Imp p q) ->
    K_proves (Imp q r) ->
    K_proves (Imp p r).
Proof.
  intros AtomType p q r Hpq Hqr.
  eapply K_proves_under_mp; [apply K_proves_imply_intro; exact Hqr | exact Hpq].
Qed.

Lemma K_proves_box_mp :
  forall (AtomType : Type) (p q : formula AtomType),
    K_proves (Box (Imp p q)) ->
    K_proves (Box p) ->
    K_proves (Box q).
Proof.
  intros AtomType p q Hpq Hp.
  eapply Kp_mp.
  - eapply Kp_mp; [exact (Kp_modal_K p q) | exact Hpq].
  - exact Hp.
Qed.

Lemma K_proves_box_regularity :
  forall (AtomType : Type) (p q : formula AtomType),
    K_proves (Imp p q) -> K_proves (Imp (Box p) (Box q)).
Proof.
  intros AtomType p q H.
  eapply Kp_mp; [exact (Kp_modal_K p q) | now apply Kp_nec].
Qed.

(** Classical consequences of elimination of contraposition.  The proof of
    DNE follows Foundation's short Lukasiewicz derivation; DNI then follows by
    one more instance of the classical schema. *)
Lemma K_proves_dne :
  forall (AtomType : Type) (p : formula AtomType),
    K_proves (Imp (Neg (Neg p)) p).
Proof.
  intros AtomType p.
  pose proof
    (K_proves_imply_intro (Neg (Neg p))
       (Kp_elim_contra (Neg p) (Neg (Neg (Neg p))))) as H1.
  pose proof
    (Kp_imply_K (Neg (Neg p)) (Neg (Neg (Neg (Neg p))))) as H2.
  pose proof
    (K_proves_imply_intro (Neg (Neg p))
       (Kp_elim_contra (Neg (Neg p)) p)) as H3.
  pose proof (K_proves_under_mp H1 H2) as H4.
  pose proof (K_proves_under_mp H3 H4) as H5.
  exact (K_proves_under_mp H5 (K_proves_identity (Neg (Neg p)))).
Qed.

Lemma K_proves_dni :
  forall (AtomType : Type) (p : formula AtomType),
    K_proves (Imp p (Neg (Neg p))).
Proof.
  intros AtomType p.
  eapply Kp_mp.
  - exact (Kp_elim_contra p (Neg (Neg p))).
  - exact (K_proves_dne (Neg p)).
Qed.

Lemma K_proves_ex_falso :
  forall (AtomType : Type) (p : formula AtomType),
    K_proves (Imp Bottom p).
Proof.
  intros AtomType p.
  eapply Kp_mp.
  - exact (Kp_elim_contra Bottom p).
  - apply K_proves_imply_intro.
    apply K_proves_identity.
Qed.

Lemma K_proves_explosion :
  forall (AtomType : Type) (p q : formula AtomType),
    K_proves p -> K_proves (Neg p) -> K_proves q.
Proof.
  intros AtomType p q Hp Hnp.
  apply (Kp_mp (K_proves_ex_falso q)).
  exact (Kp_mp Hnp Hp).
Qed.

(** Predicate-valued theories keep the consequence relation independent of
    decidable equality on atoms or formulae. *)
Definition theory (AtomType : Type) : Type := formula AtomType -> Prop.

Definition empty_theory {AtomType} : theory AtomType := fun _ => False.

Definition theory_insert {AtomType}
    (Gamma : theory AtomType) (p : formula AtomType) : theory AtomType :=
  fun q => q = p \/ Gamma q.

Definition theory_included {AtomType}
    (Gamma Delta : theory AtomType) : Prop :=
  forall p, Gamma p -> Delta p.

Inductive K_derives {AtomType : Type} (Gamma : theory AtomType)
    : formula AtomType -> Prop :=
| Kd_assumption : forall p, Gamma p -> K_derives Gamma p
| Kd_theorem : forall p, K_proves p -> K_derives Gamma p
| Kd_mp : forall p q,
    K_derives Gamma (Imp p q) ->
    K_derives Gamma p ->
    K_derives Gamma q.

Arguments Kd_assumption {AtomType Gamma p} _.
Arguments Kd_theorem {AtomType Gamma p} _.
Arguments Kd_mp {AtomType Gamma p q} _ _.

Lemma K_derives_weaken :
  forall (AtomType : Type) (Gamma Delta : theory AtomType) p,
    theory_included Gamma Delta ->
    K_derives Gamma p -> K_derives Delta p.
Proof.
  intros AtomType Gamma Delta p Hin Hp.
  induction Hp.
  - apply Kd_assumption; auto.
  - apply Kd_theorem; assumption.
  - eapply Kd_mp; eauto.
Qed.

Lemma K_derives_theorem :
  forall (AtomType : Type) (Gamma : theory AtomType) p,
    K_proves p -> K_derives Gamma p.
Proof. intros; now apply Kd_theorem. Qed.

Lemma K_derives_empty_iff :
  forall (AtomType : Type) (p : formula AtomType),
    K_derives empty_theory p <-> K_proves p.
Proof.
  intros AtomType p; split.
  - intro Hp; induction Hp.
    + contradiction.
    + assumption.
    + eapply Kp_mp; eauto.
  - now apply Kd_theorem.
Qed.

Lemma K_derives_imply_intro :
  forall (AtomType : Type) (Gamma : theory AtomType) p q,
    K_derives Gamma q -> K_derives Gamma (Imp p q).
Proof.
  intros AtomType Gamma p q Hq.
  eapply Kd_mp.
  - apply Kd_theorem; exact (Kp_imply_K q p).
  - exact Hq.
Qed.

Lemma K_derives_under_mp :
  forall (AtomType : Type) (Gamma : theory AtomType) p q r,
    K_derives Gamma (Imp p (Imp q r)) ->
    K_derives Gamma (Imp p q) ->
    K_derives Gamma (Imp p r).
Proof.
  intros AtomType Gamma p q r Hqr Hq.
  eapply Kd_mp.
  - eapply Kd_mp.
    + apply Kd_theorem; exact (Kp_imply_S p q r).
    + exact Hqr.
  - exact Hq.
Qed.

(** Deduction is constructive: necessitation never appears in a contextual
    derivation, and theoremhood is lifted under an antecedent using axiom K. *)
Lemma K_derives_deduction :
  forall (AtomType : Type) (Gamma : theory AtomType) p q,
    K_derives (theory_insert Gamma p) q ->
    K_derives Gamma (Imp p q).
Proof.
  intros AtomType Gamma p q Hq.
  induction Hq as [r Hr | r Hr | r s Hrs IHrs Hr IHr].
  - destruct Hr as [-> | Hr].
    + apply Kd_theorem; apply K_proves_identity.
    + apply K_derives_imply_intro; now apply Kd_assumption.
  - apply K_derives_imply_intro; now apply Kd_theorem.
  - exact (K_derives_under_mp IHrs IHr).
Qed.

Lemma K_derives_undeduction :
  forall (AtomType : Type) (Gamma : theory AtomType) p q,
    K_derives Gamma (Imp p q) ->
    K_derives (theory_insert Gamma p) q.
Proof.
  intros AtomType Gamma p q Hpq.
  eapply Kd_mp.
  - eapply K_derives_weaken; [|exact Hpq].
    intros r Hr; now right.
  - apply Kd_assumption; now left.
Qed.

Lemma K_derives_deduction_iff :
  forall (AtomType : Type) (Gamma : theory AtomType) p q,
    K_derives (theory_insert Gamma p) q <->
    K_derives Gamma (Imp p q).
Proof.
  intros; split; [apply K_derives_deduction | apply K_derives_undeduction].
Qed.

Lemma K_derives_dni :
  forall (AtomType : Type) (Gamma : theory AtomType) p,
    K_derives Gamma p -> K_derives Gamma (Neg (Neg p)).
Proof.
  intros AtomType Gamma p Hp.
  eapply Kd_mp; [apply Kd_theorem; apply K_proves_dni | exact Hp].
Qed.

Lemma K_derives_dne :
  forall (AtomType : Type) (Gamma : theory AtomType) p,
    K_derives Gamma (Neg (Neg p)) -> K_derives Gamma p.
Proof.
  intros AtomType Gamma p Hp.
  eapply Kd_mp; [apply Kd_theorem; apply K_proves_dne | exact Hp].
Qed.

Lemma K_derives_ex_falso :
  forall (AtomType : Type) (Gamma : theory AtomType) p,
    K_derives Gamma Bottom -> K_derives Gamma p.
Proof.
  intros AtomType Gamma p Hbot.
  eapply Kd_mp; [apply Kd_theorem; apply K_proves_ex_falso | exact Hbot].
Qed.

Definition theory_consistent {AtomType} (Gamma : theory AtomType) : Prop :=
  ~ K_derives Gamma Bottom.

Definition theory_inconsistent {AtomType} (Gamma : theory AtomType) : Prop :=
  K_derives Gamma Bottom.

Lemma theory_consistent_insert_iff :
  forall (AtomType : Type) (Gamma : theory AtomType) p,
    theory_consistent (theory_insert Gamma p) <->
    ~ K_derives Gamma (Neg p).
Proof.
  intros AtomType Gamma p; split.
  - intros Hconsistent Hneg.
    apply Hconsistent.
    exact (K_derives_undeduction Hneg).
  - intros Hnot Hbottom.
    apply Hnot.
    exact (K_derives_deduction Hbottom).
Qed.

(** The form used when extending a consistent theory with a negative
    formula: adding [~p] is consistent exactly when [p] was not derivable. *)
Lemma theory_consistent_insert_neg_iff :
  forall (AtomType : Type) (Gamma : theory AtomType) p,
    theory_consistent (theory_insert Gamma (Neg p)) <->
    ~ K_derives Gamma p.
Proof.
  intros AtomType Gamma p; split.
  - intros Hconsistent Hp.
    apply Hconsistent.
    eapply Kd_mp.
    + apply Kd_assumption; now left.
    + eapply K_derives_weaken; [|exact Hp].
      intros r Hr; now right.
  - intros Hnot Hbottom.
    apply Hnot.
    apply K_derives_dne.
    exact (K_derives_deduction Hbottom).
Qed.

(** Box every member of a theory. *)
Definition boxed_theory {AtomType} (Gamma : theory AtomType)
    : theory AtomType :=
  fun p => exists q, Gamma q /\ p = Box q.

(** Contextual necessitation: a derivation from [Gamma] lifts to a derivation
    from the pointwise boxed theory. *)
Lemma K_derives_boxed :
  forall (AtomType : Type) (Gamma : theory AtomType) p,
    K_derives Gamma p -> K_derives (boxed_theory Gamma) (Box p).
Proof.
  intros AtomType Gamma p Hp; induction Hp.
  - apply Kd_assumption. exists p; now split.
  - apply Kd_theorem. now apply Kp_nec.
  - eapply Kd_mp.
    + eapply Kd_mp.
      * apply Kd_theorem; exact (Kp_modal_K p q).
      * exact IHHp1.
    + exact IHHp2.
Qed.

(** A particularly useful canonical-model form: if formulas whose boxes lie
    in [Gamma] derive [p], then [Gamma] derives [box p]. *)
Lemma K_derives_box_from_unboxed :
  forall (AtomType : Type) (Gamma : theory AtomType) p,
    K_derives (fun q => Gamma (Box q)) p ->
    K_derives Gamma (Box p).
Proof.
  intros AtomType Gamma p Hp.
  assert (Hincl : theory_included
      (boxed_theory (fun q => Gamma (Box q))) Gamma).
  { intros r Hr.
    destruct Hr as [q [Hq Heq]].
    now subst r. }
  exact (@K_derives_weaken AtomType
           (boxed_theory (fun q => Gamma (Box q))) Gamma (Box p)
           Hincl (K_derives_boxed Hp)).
Qed.

(** If every assumption's box is already a theorem, contextual necessitation
    produces theoremhood rather than merely another contextual derivation. *)
Lemma K_proves_box_of_derives :
  forall (AtomType : Type) (Gamma : theory AtomType) p,
    K_derives Gamma p ->
    (forall q, Gamma q -> K_proves (Box q)) ->
    K_proves (Box p).
Proof.
  intros AtomType Gamma p Hp Hbox.
  induction Hp.
  - now apply Hbox.
  - now apply Kp_nec.
  - eapply K_proves_box_mp; eauto.
Qed.
