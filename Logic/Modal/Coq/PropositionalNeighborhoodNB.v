(** Rooted neighborhood semantics for propositional Hilbert WF.

    This ports the active mathematical surface of
    Foundation/Propositional/Neighborhood/NB/{Basic,Hilbert/Basic,
    Hilbert/WF}.lean.  Foundation stores an admissible carrier [X] together
    with closure proofs.  Those fields force [X] to contain every world:
    monotonicity validates [empty -> empty] everywhere, while implication
    closure places that truth set inside [X].  We therefore use the equivalent
    and smaller presentation in which truth sets are arbitrary predicates.

    Neighborhoods consume predicates extensionally.  Recording that law
    directly avoids quotienting predicates or importing functional and
    propositional extensionality.  The development is polymorphic in atoms
    and worlds; only the three two-world independence models use nat atoms. *)

From Stdlib Require Import
  Bool.Bool Logic.Classical_Prop Logic.Classical_Pred_Type.
From FoundationModal Require Import
  PropositionalFormula PropositionalHilbert PropositionalKripke2
  PropositionalKripke2Hilbert PropositionalHilbertVF
  PropositionalHilbertFExtensions PropositionalHilbertWF.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Predicate sets and rooted frames *)

Definition nb_subset {W : Type} (X Y : W -> Prop) : Prop :=
  forall w, X w -> Y w.

Definition nb_set_equiv {W : Type} (X Y : W -> Prop) : Prop :=
  forall w, X w <-> Y w.

Lemma nb_set_equiv_refl : forall (W : Type) (X : W -> Prop),
  nb_set_equiv X X.
Proof. firstorder. Qed.

Lemma nb_set_equiv_sym : forall (W : Type) (X Y : W -> Prop),
  nb_set_equiv X Y -> nb_set_equiv Y X.
Proof. firstorder. Qed.

Lemma nb_subset_equiv : forall (W : Type) (X X' Y Y' : W -> Prop),
  nb_set_equiv X X' -> nb_set_equiv Y Y' ->
  (nb_subset X Y <-> nb_subset X' Y').
Proof. unfold nb_set_equiv, nb_subset; firstorder. Qed.

Record nb_frame : Type := {
  nb_world : Type;
  nb_neighborhood :
    nb_world -> (nb_world -> Prop) -> (nb_world -> Prop) -> Prop;
  nb_neighborhood_inclusion : forall w X Y,
    nb_subset X Y -> nb_neighborhood w X Y;
  nb_neighborhood_extensional : forall w X X' Y Y',
    nb_set_equiv X X' -> nb_set_equiv Y Y' ->
    (nb_neighborhood w X Y <-> nb_neighborhood w X' Y');
  nb_root : nb_world;
  nb_rooted : forall X Y,
    nb_neighborhood nb_root X Y <-> nb_subset X Y
}.

Arguments nb_world _ : clear implicits.
Arguments nb_neighborhood _ _ _ _ : clear implicits.
Arguments nb_neighborhood_inclusion _ _ _ _ _ : clear implicits.
Arguments nb_neighborhood_extensional _ _ _ _ _ _ _ _ : clear implicits.
Arguments nb_root _ : clear implicits.
Arguments nb_rooted _ _ _ : clear implicits.

(** * Models, truth sets, and forcing *)

Record nb_model (Atom : Type) : Type := {
  nb_model_frame : nb_frame;
  nb_valuation : Atom -> nb_world nb_model_frame -> Prop
}.

Arguments nb_model_frame {Atom} _.
Arguments nb_valuation {Atom} _ _ _.

Fixpoint nb_truthset {Atom : Type} (M : nb_model Atom)
    (p : pformula Atom) : nb_world (nb_model_frame M) -> Prop :=
  match p with
  | PAtom a => nb_valuation M a
  | PFalsum => fun _ => False
  | PAnd q r => fun w =>
      @nb_truthset Atom M q w /\ @nb_truthset Atom M r w
  | POr q r => fun w =>
      @nb_truthset Atom M q w \/ @nb_truthset Atom M r w
  | PImp q r => fun w =>
      nb_neighborhood (nb_model_frame M) w
        (@nb_truthset Atom M q) (@nb_truthset Atom M r)
  end.

Arguments nb_truthset Atom M p w : clear implicits.
Arguments nb_truthset {Atom} M p w.

Definition nb_forces {Atom : Type} (M : nb_model Atom)
    (w : nb_world (nb_model_frame M)) (p : pformula Atom) : Prop :=
  nb_truthset M p w.

Arguments nb_forces Atom M w p : clear implicits.
Arguments nb_forces {Atom} M w p.

Definition nb_model_valid {Atom : Type}
    (M : nb_model Atom) (p : pformula Atom) : Prop :=
  forall w, nb_forces M w p.

Arguments nb_model_valid Atom M p : clear implicits.
Arguments nb_model_valid {Atom} M p.

Definition nb_frame_valid {Atom : Type}
    (F : nb_frame) (p : pformula Atom) : Prop :=
  forall V : Atom -> nb_world F -> Prop,
    nb_model_valid {| nb_model_frame := F; nb_valuation := V |} p.

Definition nb_frame_class_valid {Atom : Type}
    (C : nb_frame -> Prop) (p : pformula Atom) : Prop :=
  forall F, C F -> nb_frame_valid F p.

Definition nb_model_class_valid {Atom : Type}
    (C : nb_model Atom -> Prop) (p : pformula Atom) : Prop :=
  forall M, C M -> nb_model_valid M p.

Lemma nb_forces_atom : forall (Atom : Type) (M : nb_model Atom) w a,
  nb_forces M w (PAtom a) <-> nb_valuation M a w.
Proof. reflexivity. Qed.

Lemma nb_not_forces_bottom : forall (Atom : Type) (M : nb_model Atom) w,
  ~ nb_forces M w PFalsum.
Proof. firstorder. Qed.

Lemma nb_forces_and : forall (Atom : Type) (M : nb_model Atom) w p q,
  nb_forces M w (PAnd p q) <->
  nb_forces M w p /\ nb_forces M w q.
Proof. reflexivity. Qed.

Lemma nb_forces_or : forall (Atom : Type) (M : nb_model Atom) w p q,
  nb_forces M w (POr p q) <->
  nb_forces M w p \/ nb_forces M w q.
Proof. reflexivity. Qed.

Lemma nb_forces_imp : forall (Atom : Type) (M : nb_model Atom) w p q,
  nb_forces M w (PImp p q) <->
  nb_neighborhood (nb_model_frame M) w
    (nb_truthset M p) (nb_truthset M q).
Proof. reflexivity. Qed.

Lemma nb_forces_top : forall (Atom : Type) (M : nb_model Atom) w,
  nb_forces M w ptop.
Proof.
  intros Atom M w. apply nb_neighborhood_inclusion.
  unfold nb_subset; firstorder.
Qed.

Lemma nb_forces_neg : forall (Atom : Type) (M : nb_model Atom) w p,
  nb_forces M w (pneg p) <->
  nb_neighborhood (nb_model_frame M) w
    (nb_truthset M p) (fun _ => False).
Proof. reflexivity. Qed.

Lemma nb_forces_iff : forall (Atom : Type) (M : nb_model Atom) w p q,
  nb_forces M w (phwf_iff p q) <->
  nb_neighborhood (nb_model_frame M) w
    (nb_truthset M p) (nb_truthset M q) /\
  nb_neighborhood (nb_model_frame M) w
    (nb_truthset M q) (nb_truthset M p).
Proof. reflexivity. Qed.

(** Global validity of an implication is exactly inclusion of truth sets.
    The forward direction needs only the distinguished root; the reverse
    direction is the frame's monotonicity law. *)
Lemma nb_model_valid_imp_iff :
  forall (Atom : Type) (M : nb_model Atom) p q,
    nb_model_valid M (PImp p q) <->
    nb_subset (nb_truthset M p) (nb_truthset M q).
Proof.
  intros Atom M p q; split.
  - intro H. apply (proj1 (nb_rooted (nb_model_frame M)
      (nb_truthset M p) (nb_truthset M q))).
    apply H.
  - intros H w. now apply nb_neighborhood_inclusion.
Qed.

Lemma nb_model_valid_iff_iff :
  forall (Atom : Type) (M : nb_model Atom) p q,
    nb_model_valid M (phwf_iff p q) <->
    nb_set_equiv (nb_truthset M p) (nb_truthset M q).
Proof.
  intros Atom M p q. unfold phwf_iff, phf_iff, nb_model_valid.
  split.
  - intro H. unfold nb_set_equiv. intro w; split.
    + apply (proj1 (nb_model_valid_imp_iff M p q)).
      intro x; exact (proj1 (H x)).
    + apply (proj1 (nb_model_valid_imp_iff M q p)).
      intro x; exact (proj2 (H x)).
  - intro H. intro w; split.
    + apply nb_neighborhood_inclusion. unfold nb_subset.
      intros x Hx. now apply (proj1 (H x)).
    + apply nb_neighborhood_inclusion. unfold nb_subset.
      intros x Hx. now apply (proj2 (H x)).
Qed.

(** * Universally valid positive schemata and WF rules *)

Lemma nb_valid_and1 : forall (Atom : Type) (M : nb_model Atom) p q,
  nb_model_valid M (ph_axiom_and1 p q).
Proof.
  intros. apply (proj2 (nb_model_valid_imp_iff M _ _)).
  unfold nb_subset; cbn; firstorder.
Qed.

Lemma nb_valid_and2 : forall (Atom : Type) (M : nb_model Atom) p q,
  nb_model_valid M (ph_axiom_and2 p q).
Proof.
  intros. apply (proj2 (nb_model_valid_imp_iff M _ _)).
  unfold nb_subset; cbn; firstorder.
Qed.

Lemma nb_valid_or1 : forall (Atom : Type) (M : nb_model Atom) p q,
  nb_model_valid M (ph_axiom_or1 p q).
Proof.
  intros. apply (proj2 (nb_model_valid_imp_iff M _ _)).
  unfold nb_subset; cbn; firstorder.
Qed.

Lemma nb_valid_or2 : forall (Atom : Type) (M : nb_model Atom) p q,
  nb_model_valid M (ph_axiom_or2 p q).
Proof.
  intros. apply (proj2 (nb_model_valid_imp_iff M _ _)).
  unfold nb_subset; cbn; firstorder.
Qed.

Lemma nb_valid_distribute_and_or :
  forall (Atom : Type) (M : nb_model Atom) p q r,
    nb_model_valid M (phvf_distribute_and_or p q r).
Proof.
  intros. apply (proj2 (nb_model_valid_imp_iff M _ _)).
  unfold nb_subset; cbn; firstorder.
Qed.

Lemma nb_valid_identity : forall (Atom : Type) (M : nb_model Atom) p,
  nb_model_valid M (PImp p p).
Proof.
  intros. apply (proj2 (nb_model_valid_imp_iff M _ _)).
  unfold nb_subset; firstorder.
Qed.

Lemma nb_valid_efq : forall (Atom : Type) (M : nb_model Atom) p,
  nb_model_valid M (ph_axiom_efq p).
Proof.
  intros. apply (proj2 (nb_model_valid_imp_iff M _ _)).
  unfold nb_subset; cbn; firstorder.
Qed.

Lemma nb_valid_modus_ponens :
  forall (Atom : Type) (M : nb_model Atom) p q,
    nb_model_valid M (PImp p q) -> nb_model_valid M p ->
    nb_model_valid M q.
Proof.
  intros Atom M p q Hpq Hp w.
  apply (proj1 (nb_model_valid_imp_iff M p q)) in Hpq.
  exact (Hpq w (Hp w)).
Qed.

Lemma nb_valid_fortiori :
  forall (Atom : Type) (M : nb_model Atom) p q,
    nb_model_valid M p -> nb_model_valid M (PImp q p).
Proof.
  intros Atom M p q Hp. apply (proj2 (nb_model_valid_imp_iff M _ _)).
  unfold nb_subset; intros w _. apply Hp.
Qed.

Lemma nb_valid_and_rule :
  forall (Atom : Type) (M : nb_model Atom) p q,
    nb_model_valid M p -> nb_model_valid M q ->
    nb_model_valid M (PAnd p q).
Proof. firstorder. Qed.

Lemma nb_valid_rule_C :
  forall (Atom : Type) (M : nb_model Atom) p q r,
    nb_model_valid M (PImp p q) ->
    nb_model_valid M (PImp p r) ->
    nb_model_valid M (PImp p (PAnd q r)).
Proof.
  intros Atom M p q r Hq Hr.
  apply (proj2 (nb_model_valid_imp_iff M _ _)).
  apply (proj1 (nb_model_valid_imp_iff M p q)) in Hq.
  apply (proj1 (nb_model_valid_imp_iff M p r)) in Hr.
  unfold nb_subset; cbn; firstorder.
Qed.

Lemma nb_valid_rule_D :
  forall (Atom : Type) (M : nb_model Atom) p q r,
    nb_model_valid M (PImp p r) ->
    nb_model_valid M (PImp q r) ->
    nb_model_valid M (PImp (POr p q) r).
Proof.
  intros Atom M p q r Hp Hq.
  apply (proj2 (nb_model_valid_imp_iff M _ _)).
  apply (proj1 (nb_model_valid_imp_iff M p r)) in Hp.
  apply (proj1 (nb_model_valid_imp_iff M q r)) in Hq.
  unfold nb_subset; cbn; firstorder.
Qed.

Lemma nb_valid_rule_I :
  forall (Atom : Type) (M : nb_model Atom) p q r,
    nb_model_valid M (PImp p q) ->
    nb_model_valid M (PImp q r) ->
    nb_model_valid M (PImp p r).
Proof.
  intros Atom M p q r Hpq Hqr.
  apply (proj2 (nb_model_valid_imp_iff M _ _)).
  apply (proj1 (nb_model_valid_imp_iff M p q)) in Hpq.
  apply (proj1 (nb_model_valid_imp_iff M q r)) in Hqr.
  unfold nb_subset; firstorder.
Qed.

Lemma nb_valid_rule_E :
  forall (Atom : Type) (M : nb_model Atom) p q r s,
    nb_model_valid M (phwf_iff p q) ->
    nb_model_valid M (phwf_iff r s) ->
    nb_model_valid M (phwf_iff (PImp p r) (PImp q s)).
Proof.
  intros Atom M p q r s Hpq Hrs.
  apply (proj2 (nb_model_valid_iff_iff M _ _)).
  apply (proj1 (nb_model_valid_iff_iff M p q)) in Hpq.
  apply (proj1 (nb_model_valid_iff_iff M r s)) in Hrs.
  unfold nb_set_equiv. intro w. cbn.
  apply nb_neighborhood_extensional; assumption.
Qed.

(** * Hilbert soundness, consistency, and semantic comparison *)

Fixpoint nb_phwf_proof_sound {Atom : Type} {H : phwf_hilbert Atom}
    (M : nb_model Atom)
    (Hschema : forall p, phwf_schema H p -> nb_model_valid M p)
    {p : pformula Atom} (d : phwf_proof H p) : nb_model_valid M p.
Proof.
  destruct d.
  - now apply Hschema.
  - apply nb_valid_and1.
  - apply nb_valid_and2.
  - apply nb_valid_or1.
  - apply nb_valid_or2.
  - apply nb_valid_distribute_and_or.
  - apply nb_valid_identity.
  - apply nb_valid_efq.
  - eapply nb_valid_modus_ponens.
    + exact (@nb_phwf_proof_sound Atom H M Hschema _ d1).
    + exact (@nb_phwf_proof_sound Atom H M Hschema _ d2).
  - apply nb_valid_fortiori.
    exact (@nb_phwf_proof_sound Atom H M Hschema _ d).
  - apply nb_valid_and_rule.
    + exact (@nb_phwf_proof_sound Atom H M Hschema _ d1).
    + exact (@nb_phwf_proof_sound Atom H M Hschema _ d2).
  - apply nb_valid_rule_C.
    + exact (@nb_phwf_proof_sound Atom H M Hschema _ d1).
    + exact (@nb_phwf_proof_sound Atom H M Hschema _ d2).
  - apply nb_valid_rule_D.
    + exact (@nb_phwf_proof_sound Atom H M Hschema _ d1).
    + exact (@nb_phwf_proof_sound Atom H M Hschema _ d2).
  - eapply nb_valid_rule_I.
    + exact (@nb_phwf_proof_sound Atom H M Hschema _ d1).
    + exact (@nb_phwf_proof_sound Atom H M Hschema _ d2).
  - apply nb_valid_rule_E.
    + exact (@nb_phwf_proof_sound Atom H M Hschema _ d1).
    + exact (@nb_phwf_proof_sound Atom H M Hschema _ d2).
Defined.

Definition nb_phwf_frame_schema_valid {Atom : Type}
    (H : phwf_hilbert Atom) (C : nb_frame -> Prop) : Prop :=
  forall p, phwf_schema H p -> nb_frame_class_valid C p.

Definition nb_phwf_model_schema_valid {Atom : Type}
    (H : phwf_hilbert Atom) (C : nb_model Atom -> Prop) : Prop :=
  forall p, phwf_schema H p -> nb_model_class_valid C p.

Definition nb_phwf_frame_sound {Atom : Type}
    (H : phwf_hilbert Atom) (C : nb_frame -> Prop) : Prop :=
  forall p, phwf_provable H p -> nb_frame_class_valid C p.

Definition nb_phwf_model_sound {Atom : Type}
    (H : phwf_hilbert Atom) (C : nb_model Atom -> Prop) : Prop :=
  forall p, phwf_provable H p -> nb_model_class_valid C p.

Definition nb_phwf_frame_complete {Atom : Type}
    (H : phwf_hilbert Atom) (C : nb_frame -> Prop) : Prop :=
  forall p, nb_frame_class_valid C p -> phwf_provable H p.

Theorem nb_phwf_soundness_frame_class :
  forall (Atom : Type) (H : phwf_hilbert Atom) (C : nb_frame -> Prop),
    nb_phwf_frame_schema_valid H C -> nb_phwf_frame_sound H C.
Proof.
  intros Atom H C Hschema p [d] F HF V.
  exact (@nb_phwf_proof_sound Atom H
    {| nb_model_frame := F; nb_valuation := V |}
    (fun q Hq => Hschema q Hq F HF V) p d).
Qed.

Theorem nb_phwf_soundness_model_class :
  forall (Atom : Type) (H : phwf_hilbert Atom)
      (C : nb_model Atom -> Prop),
    nb_phwf_model_schema_valid H C -> nb_phwf_model_sound H C.
Proof.
  intros Atom H C Hschema p [d] M HM.
  exact (@nb_phwf_proof_sound Atom H M
    (fun q Hq => Hschema q Hq M HM) p d).
Qed.

Definition nb_phwf_consistent {Atom : Type} (H : phwf_hilbert Atom) : Prop :=
  ~ phwf_provable H PFalsum.

Theorem nb_phwf_consistent_of_frame_sound :
  forall (Atom : Type) (H : phwf_hilbert Atom) (C : nb_frame -> Prop),
    nb_phwf_frame_sound H C ->
    (exists F, C F) -> nb_phwf_consistent H.
Proof.
  intros Atom H C Hsound [F HF] Hbot.
  specialize (Hsound PFalsum Hbot F HF
    (fun _ _ => False) (nb_root F)).
  exact Hsound.
Qed.

Theorem nb_phwf_consistent_of_model_sound :
  forall (Atom : Type) (H : phwf_hilbert Atom)
      (C : nb_model Atom -> Prop),
    nb_phwf_model_sound H C ->
    (exists M, C M) -> nb_phwf_consistent H.
Proof.
  intros Atom H C Hsound [M HM] Hbot.
  exact (Hsound PFalsum Hbot M HM (nb_root (nb_model_frame M))).
Qed.

Theorem nb_phwf_weaker_of_frame_classes :
  forall (Atom : Type) (H1 H2 : phwf_hilbert Atom)
      (C1 C2 : nb_frame -> Prop),
    (forall F, C2 F -> C1 F) ->
    nb_phwf_frame_sound H1 C1 -> nb_phwf_frame_complete H2 C2 ->
    phwf_logic_included H1 H2.
Proof.
  intros Atom H1 H2 C1 C2 HC Hsound Hcomplete p Hp.
  apply Hcomplete. intros F HF.
  exact (Hsound p Hp F (HC F HF)).
Qed.

(** Counterexample equivalences match the source class-level API. *)
Lemma nb_model_not_valid_iff :
  forall (Atom : Type) (M : nb_model Atom) p,
    ~ nb_model_valid M p <-> exists w, ~ nb_forces M w p.
Proof.
  intros; unfold nb_model_valid; split; [apply not_all_ex_not | firstorder].
Qed.

Lemma nb_frame_not_valid_iff :
  forall (Atom : Type) (F : nb_frame) p,
    ~ nb_frame_valid F p <->
    exists V : Atom -> nb_world F -> Prop, ~ nb_model_valid
      {| nb_model_frame := F; nb_valuation := V |} p.
Proof.
  intros; unfold nb_frame_valid; split; [apply not_all_ex_not | firstorder].
Qed.

Lemma nb_frame_class_not_valid_iff_frame :
  forall (Atom : Type) (C : nb_frame -> Prop) (p : pformula Atom),
    ~ nb_frame_class_valid C p <->
    exists F, C F /\ ~ nb_frame_valid F p.
Proof.
  intros; unfold nb_frame_class_valid; split.
  - intro H. apply not_all_ex_not in H. destruct H as [F HF].
    exists F. destruct (classic (C F)); tauto.
  - firstorder.
Qed.

Lemma nb_frame_class_not_valid_iff_model :
  forall (Atom : Type) (C : nb_frame -> Prop) (p : pformula Atom),
    ~ nb_frame_class_valid C p <->
    exists M : nb_model Atom,
      C (nb_model_frame M) /\ ~ nb_model_valid M p.
Proof.
  intros Atom C p. rewrite nb_frame_class_not_valid_iff_frame; split.
  - intros [F [HF H]]. apply nb_frame_not_valid_iff in H.
    destruct H as [V HV].
    now exists {| nb_model_frame := F; nb_valuation := V |}.
  - intros [[F V] [HF H]]. exists F; split; [exact HF |].
    apply nb_frame_not_valid_iff. now exists V.
Qed.

Lemma nb_frame_class_not_valid_iff_model_world :
  forall (Atom : Type) (C : nb_frame -> Prop) (p : pformula Atom),
    ~ nb_frame_class_valid C p <->
    exists (M : nb_model Atom) w,
      C (nb_model_frame M) /\ ~ nb_forces M w p.
Proof.
  intros Atom C p. rewrite nb_frame_class_not_valid_iff_model; split.
  - intros [M [HM H]]. apply nb_model_not_valid_iff in H.
    destruct H as [w Hw]. now exists M, w.
  - intros [M [w [HM Hw]]]. exists M; split; [exact HM |].
    apply nb_model_not_valid_iff. now exists w.
Qed.

Lemma nb_model_class_not_valid_iff_model :
  forall (Atom : Type) (C : nb_model Atom -> Prop) (p : pformula Atom),
    ~ nb_model_class_valid C p <->
    exists M, C M /\ ~ nb_model_valid M p.
Proof.
  intros; unfold nb_model_class_valid; split.
  - intro H. apply not_all_ex_not in H. destruct H as [M HM].
    exists M. destruct (classic (C M)); tauto.
  - firstorder.
Qed.

Lemma nb_model_class_not_valid_iff_world :
  forall (Atom : Type) (C : nb_model Atom -> Prop) (p : pformula Atom),
    ~ nb_model_class_valid C p <->
    exists M w, C M /\ ~ nb_forces M w p.
Proof.
  intros Atom C p. rewrite nb_model_class_not_valid_iff_model; split.
  - intros [M [HM H]]. apply nb_model_not_valid_iff in H.
    destruct H as [w Hw]. now exists M, w.
  - intros [M [w [HM Hw]]]. exists M; split; [exact HM |].
    apply nb_model_not_valid_iff. now exists w.
Qed.

(** * The universal WF frame class *)

Definition nb_trivial_neighborhood (_ : unit)
    (X Y : unit -> Prop) : Prop := nb_subset X Y.

Definition nb_trivial_frame : nb_frame.
Proof.
  refine {| nb_world := unit;
    nb_neighborhood := nb_trivial_neighborhood;
    nb_root := tt |}.
  - intros; assumption.
  - intros w X X' Y Y' HX HY.
    now apply nb_subset_equiv.
  - reflexivity.
Defined.

Theorem phwf_WF_nb_frame_sound : forall Atom : Type,
  nb_phwf_frame_sound (phwf_hilbert_WF Atom) (fun _ => True).
Proof.
  intro Atom. apply nb_phwf_soundness_frame_class.
  intros p Hschema; contradiction.
Qed.

Theorem phwf_WF_nb_model_sound : forall Atom : Type,
  nb_phwf_model_sound (phwf_hilbert_WF Atom) (fun _ => True).
Proof.
  intro Atom. apply nb_phwf_soundness_model_class.
  intros p Hschema; contradiction.
Qed.

Theorem phwf_WF_consistent : forall Atom : Type,
  nb_phwf_consistent (phwf_hilbert_WF Atom).
Proof.
  intro Atom. eapply nb_phwf_consistent_of_frame_sound.
  - apply phwf_WF_nb_frame_sound.
  - exists nb_trivial_frame; exact I.
Qed.

(** * A factored two-world counterframe *)

Definition nb_extra_extensional
    (E : (bool -> Prop) -> (bool -> Prop) -> Prop) : Prop :=
  forall X X' Y Y', nb_set_equiv X X' -> nb_set_equiv Y Y' ->
    (E X Y <-> E X' Y').

Definition nb_two_neighborhood
    (E : (bool -> Prop) -> (bool -> Prop) -> Prop)
    (w : bool) (X Y : bool -> Prop) : Prop :=
  if w then nb_subset X Y \/ E X Y else nb_subset X Y.

Lemma nb_two_neighborhood_inclusion : forall E w X Y,
  nb_subset X Y -> nb_two_neighborhood E w X Y.
Proof. intros E [] X Y H; cbn; tauto. Qed.

Lemma nb_two_neighborhood_extensional :
  forall E, nb_extra_extensional E -> forall w X X' Y Y',
    nb_set_equiv X X' -> nb_set_equiv Y Y' ->
    (nb_two_neighborhood E w X Y <->
     nb_two_neighborhood E w X' Y').
Proof.
  intros E HE [] X X' Y Y' HX HY; cbn [nb_two_neighborhood].
  - rewrite (nb_subset_equiv HX HY), (HE X X' Y Y' HX HY).
    reflexivity.
  - now apply nb_subset_equiv.
Qed.

Definition nb_two_frame
    (E : (bool -> Prop) -> (bool -> Prop) -> Prop)
    (HE : nb_extra_extensional E) : nb_frame.
Proof.
  refine {| nb_world := bool;
    nb_neighborhood := nb_two_neighborhood E;
    nb_root := false |}.
  - apply nb_two_neighborhood_inclusion.
  - now apply nb_two_neighborhood_extensional.
  - reflexivity.
Defined.

Definition nb_bool_all : bool -> Prop := fun _ => True.
Definition nb_bool_none : bool -> Prop := fun _ => False.
Definition nb_bool_singleton (b : bool) : bool -> Prop := fun w => w = b.

Definition nb_C_extra (X Y : bool -> Prop) : Prop :=
  (nb_set_equiv X nb_bool_all /\
   nb_set_equiv Y (nb_bool_singleton false)) \/
  (nb_set_equiv X nb_bool_all /\
   nb_set_equiv Y (nb_bool_singleton true)).

Lemma nb_C_extra_extensional : nb_extra_extensional nb_C_extra.
Proof. unfold nb_extra_extensional, nb_C_extra, nb_set_equiv; firstorder. Qed.

Definition nb_C_frame : nb_frame :=
  @nb_two_frame nb_C_extra nb_C_extra_extensional.

Definition nb_C_valuation (a : nat) : bool -> Prop :=
  match a with
  | 0 => nb_bool_all
  | 1 => nb_bool_singleton true
  | 2 => nb_bool_singleton false
  | _ => nb_bool_none
  end.

Definition nb_C_model : nb_model nat :=
  {| nb_model_frame := nb_C_frame; nb_valuation := nb_C_valuation |}.

Definition nb_axiom_C : pformula nat :=
  pk2_axiom_C (PAtom 0) (PAtom 1) (PAtom 2).

Lemma nb_C_countermodel : ~ nb_model_valid nb_C_model nb_axiom_C.
Proof.
  intro H. specialize (H false). cbn [nb_forces nb_truthset nb_axiom_C
    pk2_axiom_C nb_C_model nb_C_frame nb_C_valuation nb_two_frame
    nb_two_neighborhood nb_subset] in H.
  apply (proj1 (nb_rooted (nb_model_frame nb_C_model) _ _)) in H.
  assert (Hante : nb_forces nb_C_model true
      (PAnd (PImp (PAtom 0) (PAtom 1))
        (PImp (PAtom 0) (PAtom 2)))).
  { change (nb_two_neighborhood nb_C_extra true nb_bool_all
        (nb_bool_singleton true) /\
      nb_two_neighborhood nb_C_extra true nb_bool_all
        (nb_bool_singleton false)).
    split.
    - right. right. split.
      + unfold nb_set_equiv; tauto.
      + unfold nb_set_equiv; tauto.
    - right. left. split.
      + unfold nb_set_equiv; tauto.
      + unfold nb_set_equiv; tauto. }
  specialize (H true Hante); clear Hante.
  change (nb_two_neighborhood nb_C_extra true nb_bool_all
    (fun w => nb_bool_singleton true w /\
      nb_bool_singleton false w)) in H.
  cbn [nb_two_neighborhood] in H.
  destruct H as [Hsub | [[_ HY] | [_ HY]]].
  - specialize (Hsub true I). destruct Hsub as [_ Hfalse]. discriminate.
  - specialize (HY false). destruct HY as [_ HY].
    destruct (HY eq_refl) as [Hbad _]. discriminate.
  - specialize (HY true). destruct HY as [_ HY].
    destruct (HY eq_refl) as [_ Hbad]. discriminate.
Qed.

Theorem phwf_WF_unprovable_axiom_C :
  ~ phwf_provable (phwf_hilbert_WF nat) nb_axiom_C.
Proof.
  intro Hp. apply nb_C_countermodel.
  exact (@phwf_WF_nb_model_sound nat nb_axiom_C Hp nb_C_model I).
Qed.

Definition nb_D_extra (X Y : bool -> Prop) : Prop :=
  nb_set_equiv X (nb_bool_singleton false) /\
  nb_set_equiv Y (nb_bool_singleton true).

Lemma nb_D_extra_extensional : nb_extra_extensional nb_D_extra.
Proof. unfold nb_extra_extensional, nb_D_extra, nb_set_equiv; firstorder. Qed.

Definition nb_D_frame : nb_frame :=
  @nb_two_frame nb_D_extra nb_D_extra_extensional.

Definition nb_D_valuation (a : nat) : bool -> Prop :=
  match a with
  | 0 => nb_bool_singleton true
  | 1 => nb_bool_singleton false
  | 2 => nb_bool_singleton true
  | _ => nb_bool_none
  end.

Definition nb_D_model : nb_model nat :=
  {| nb_model_frame := nb_D_frame; nb_valuation := nb_D_valuation |}.

Definition nb_axiom_D : pformula nat :=
  pk2_axiom_D (PAtom 0) (PAtom 1) (PAtom 2).

Lemma nb_D_countermodel : ~ nb_model_valid nb_D_model nb_axiom_D.
Proof.
  intro H. specialize (H false).
  cbn [nb_forces nb_truthset nb_axiom_D pk2_axiom_D] in H.
  apply (proj1 (nb_rooted (nb_model_frame nb_D_model) _ _)) in H.
  assert (Hante : nb_forces nb_D_model true
      (PAnd (PImp (PAtom 0) (PAtom 2))
        (PImp (PAtom 1) (PAtom 2)))).
  { change (nb_two_neighborhood nb_D_extra true
        (nb_bool_singleton true) (nb_bool_singleton true) /\
      nb_two_neighborhood nb_D_extra true
        (nb_bool_singleton false) (nb_bool_singleton true)).
    split.
    - left. unfold nb_subset; tauto.
    - right. split; unfold nb_set_equiv; tauto. }
  specialize (H true Hante); clear Hante.
  change (nb_two_neighborhood nb_D_extra true
    (fun w => nb_bool_singleton true w \/
      nb_bool_singleton false w)
    (nb_bool_singleton true)) in H.
  cbn [nb_two_neighborhood] in H.
  destruct H as [Hsub | [HX _]].
  - specialize (Hsub false (or_intror eq_refl)). discriminate.
  - specialize (HX true). destruct HX as [HX _].
    specialize (HX (or_introl eq_refl)). discriminate.
Qed.

Theorem phwf_WF_unprovable_axiom_D :
  ~ phwf_provable (phwf_hilbert_WF nat) nb_axiom_D.
Proof.
  intro Hp. apply nb_D_countermodel.
  exact (@phwf_WF_nb_model_sound nat nb_axiom_D Hp nb_D_model I).
Qed.

Definition nb_I_extra (X Y : bool -> Prop) : Prop :=
  (nb_set_equiv X (nb_bool_singleton true) /\
   nb_set_equiv Y (nb_bool_singleton false)) \/
  (nb_set_equiv X (nb_bool_singleton false) /\
   nb_set_equiv Y nb_bool_none).

Lemma nb_I_extra_extensional : nb_extra_extensional nb_I_extra.
Proof. unfold nb_extra_extensional, nb_I_extra, nb_set_equiv; firstorder. Qed.

Definition nb_I_frame : nb_frame :=
  @nb_two_frame nb_I_extra nb_I_extra_extensional.

Definition nb_I_valuation (a : nat) : bool -> Prop :=
  match a with
  | 0 => nb_bool_singleton true
  | 1 => nb_bool_singleton false
  | 2 => nb_bool_none
  | _ => nb_bool_none
  end.

Definition nb_I_model : nb_model nat :=
  {| nb_model_frame := nb_I_frame; nb_valuation := nb_I_valuation |}.

Definition nb_axiom_I : pformula nat :=
  pk2_axiom_I (PAtom 0) (PAtom 1) (PAtom 2).

Lemma nb_I_countermodel : ~ nb_model_valid nb_I_model nb_axiom_I.
Proof.
  intro H. specialize (H false).
  cbn [nb_forces nb_truthset nb_axiom_I pk2_axiom_I] in H.
  apply (proj1 (nb_rooted (nb_model_frame nb_I_model) _ _)) in H.
  assert (Hante : nb_forces nb_I_model true
      (PAnd (PImp (PAtom 0) (PAtom 1))
        (PImp (PAtom 1) (PAtom 2)))).
  { change (nb_two_neighborhood nb_I_extra true
        (nb_bool_singleton true) (nb_bool_singleton false) /\
      nb_two_neighborhood nb_I_extra true
        (nb_bool_singleton false) nb_bool_none).
    split.
    - right. left. split; unfold nb_set_equiv; tauto.
    - right. right. split; unfold nb_set_equiv; tauto. }
  specialize (H true Hante); clear Hante.
  change (nb_two_neighborhood nb_I_extra true
    (nb_bool_singleton true) nb_bool_none) in H.
  cbn [nb_two_neighborhood] in H.
  destruct H as [Hsub | [[_ HY] | [HX _]]].
  - exact (Hsub true eq_refl).
  - specialize (HY false). destruct HY as [_ HY].
    exact (HY eq_refl).
  - specialize (HX true). destruct HX as [HX _].
    specialize (HX eq_refl). discriminate.
Qed.

Theorem phwf_WF_unprovable_axiom_I :
  ~ phwf_provable (phwf_hilbert_WF nat) nb_axiom_I.
Proof.
  intro Hp. apply nb_I_countermodel.
  exact (@phwf_WF_nb_model_sound nat nb_axiom_I Hp nb_I_model I).
Qed.

(** The source concludes with strict inclusion of WF in F.  Axiom C is the
    shortest of the three available witnesses. *)
Definition phwf_phf_strictly_included {Atom : Type}
    (Hw : phwf_hilbert Atom) (Hf : phf_hilbert Atom) : Prop :=
  phwf_phf_included Hw Hf /\
  exists p, phf_provable Hf p /\ ~ phwf_provable Hw p.

Theorem phwf_WF_strictly_included_phf_F :
  phwf_phf_strictly_included
    (phwf_hilbert_WF nat) (phf_hilbert_F nat).
Proof.
  split.
  - apply phwf_WF_included_phf_F.
  - exists nb_axiom_C. split.
    + constructor. unfold nb_axiom_C. apply PHFPAxiomC.
    + apply phwf_WF_unprovable_axiom_C.
Qed.
