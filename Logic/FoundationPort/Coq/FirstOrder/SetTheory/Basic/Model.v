(** Representation-independent membership structures.

    Foundation's set-theory model layer defines internal subset, emptiness,
    nonemptiness, strict subset, and the membership relation inherited by a
    subtype.  None of those laws depends on first-order syntax or on a set
    theory axiom, so the Coq port exposes their mathematical core for an
    arbitrary carrier and membership relation.

    Extensionality is kept as an explicit property.  Likewise, the one
    classically valid implication from non-emptiness failure to a witness is
    parameterized by excluded middle instead of importing a global axiom. *)

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record membership_structure : Type := {
  membership_carrier : Type;
  membership_rel : membership_carrier -> membership_carrier -> Prop
}.

Arguments membership_carrier _ : clear implicits.
Arguments membership_rel {m} _ _.

Definition set_model_subset {m : membership_structure}
    (x y : membership_carrier m) : Prop :=
  forall z, membership_rel z x -> membership_rel z y.

Definition set_model_is_empty {m : membership_structure}
    (x : membership_carrier m) : Prop :=
  forall z, ~ membership_rel z x.

Definition set_model_is_nonempty {m : membership_structure}
    (x : membership_carrier m) : Prop :=
  exists z, membership_rel z x.

Definition set_model_strict_subset {m : membership_structure}
    (x y : membership_carrier m) : Prop :=
  set_model_subset x y /\ x <> y.

Definition membership_extensional (m : membership_structure) : Prop :=
  forall x y : membership_carrier m,
    (forall z : membership_carrier m,
      membership_rel z x <-> membership_rel z y) -> x = y.

Lemma set_model_subset_def : forall m (x y : membership_carrier m),
  set_model_subset x y <->
  forall z, membership_rel z x -> membership_rel z y.
Proof. intros; split; trivial. Qed.

Lemma set_model_subset_refl : forall m (x : membership_carrier m),
  set_model_subset x x.
Proof. firstorder. Qed.

Lemma set_model_subset_trans : forall m (x y z : membership_carrier m),
  set_model_subset x y -> set_model_subset y z -> set_model_subset x z.
Proof. firstorder. Qed.

Lemma set_model_subset_antisym : forall m,
  membership_extensional m ->
  forall x y : membership_carrier m,
    set_model_subset x y -> set_model_subset y x -> x = y.
Proof.
  intros m Hext x y Hxy Hyx. apply Hext. intro z.
  split; [apply Hxy | apply Hyx].
Qed.

Lemma set_model_empty_not_nonempty : forall m (x : membership_carrier m),
  set_model_is_empty x -> ~ set_model_is_nonempty x.
Proof. firstorder. Qed.

Lemma set_model_nonempty_not_empty : forall m (x : membership_carrier m),
  set_model_is_nonempty x -> ~ set_model_is_empty x.
Proof. firstorder. Qed.

Lemma set_model_not_nonempty_iff_empty : forall m
    (x : membership_carrier m),
  ~ set_model_is_nonempty x <-> set_model_is_empty x.
Proof. firstorder. Qed.

Lemma set_model_not_empty_iff_nonempty :
  (forall P : Prop, P \/ ~ P) ->
  forall m (x : membership_carrier m),
    ~ set_model_is_empty x <-> set_model_is_nonempty x.
Proof.
  intros Hem m x. split.
  - intro Hnotempty.
    destruct (Hem (set_model_is_nonempty x)) as [H | H]; [exact H |].
    exfalso. apply Hnotempty.
    apply (proj1 (@set_model_not_nonempty_iff_empty m x)). exact H.
  - apply set_model_nonempty_not_empty.
Qed.

Lemma set_model_strict_subset_def : forall m
    (x y : membership_carrier m),
  set_model_strict_subset x y <-> set_model_subset x y /\ x <> y.
Proof. intros; split; trivial. Qed.

Lemma set_model_strict_subset_irrefl : forall m
    (x : membership_carrier m),
  ~ set_model_strict_subset x x.
Proof. firstorder. Qed.

Lemma set_model_strict_subset_subset : forall m
    (x y : membership_carrier m),
  set_model_strict_subset x y -> set_model_subset x y.
Proof. firstorder. Qed.

Lemma set_model_strict_subset_asym : forall m,
  membership_extensional m ->
  forall x y : membership_carrier m,
    set_model_strict_subset x y -> ~ set_model_strict_subset y x.
Proof.
  intros m Hext x y [Hxy Hneq] [Hyx _].
  apply Hneq. now apply (set_model_subset_antisym Hext).
Qed.

Lemma set_model_strict_subset_trans : forall m,
  membership_extensional m ->
  forall x y z : membership_carrier m,
    set_model_strict_subset x y ->
    set_model_strict_subset y z ->
    set_model_strict_subset x z.
Proof.
  intros m Hext x y z [Hxy Hxny] [Hyz Hynz]. split.
  - exact (@set_model_subset_trans m x y z Hxy Hyz).
  - intro Hxz. apply Hxny.
    apply (set_model_subset_antisym Hext); [exact Hxy |].
    rewrite Hxz. exact Hyz.
Qed.

(** The source's subtype model, generalized from set-valued predicates to
    every predicate on the carrier. *)
Definition membership_submodel (m : membership_structure)
    (U : membership_carrier m -> Prop) : membership_structure :=
  {| membership_carrier := {x : membership_carrier m | U x};
     membership_rel := fun x y => membership_rel (proj1_sig x) (proj1_sig y) |}.

Arguments membership_submodel m U : clear implicits.

Lemma membership_submodel_rel_iff : forall m U
    (x y : membership_carrier (membership_submodel m U)),
  @membership_rel (membership_submodel m U) x y <->
  @membership_rel m (proj1_sig x) (proj1_sig y).
Proof. intros; split; trivial. Qed.

Lemma membership_submodel_subset_iff : forall m U
    (x y : membership_carrier (membership_submodel m U)),
  @set_model_subset (membership_submodel m U) x y <->
  forall z : membership_carrier (membership_submodel m U),
    @membership_rel m (proj1_sig z) (proj1_sig x) ->
    @membership_rel m (proj1_sig z) (proj1_sig y).
Proof. intros; split; trivial. Qed.

Lemma membership_submodel_empty_iff : forall m U
    (x : membership_carrier (membership_submodel m U)),
  @set_model_is_empty (membership_submodel m U) x <->
  forall z : membership_carrier (membership_submodel m U),
    ~ @membership_rel m (proj1_sig z) (proj1_sig x).
Proof. intros; split; trivial. Qed.

Lemma membership_submodel_nonempty_iff : forall m U
    (x : membership_carrier (membership_submodel m U)),
  @set_model_is_nonempty (membership_submodel m U) x <->
  exists z : membership_carrier (membership_submodel m U),
    @membership_rel m (proj1_sig z) (proj1_sig x).
Proof. intros; split; trivial. Qed.

Print Assumptions set_model_not_empty_iff_nonempty.
Print Assumptions set_model_strict_subset_trans.
