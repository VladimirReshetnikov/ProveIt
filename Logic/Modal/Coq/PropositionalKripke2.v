(** Rooted arbitrary-relation semantics for propositional implication.

    This ports Foundation/Propositional/Kripke2/Basic.  Unlike ordinary
    intuitionistic Kripke semantics, valuations need not be persistent and
    the accessibility relation need not be reflexive or transitive.  A
    distinguished root sees every world; that single hypothesis is exactly
    what global modus ponens consumes.  Atoms and substitution are generalized
    heterogeneously. *)

From Stdlib Require Import
  Logic.Classical_Prop Logic.Classical_Pred_Type.
From FoundationModal Require Import
  PropositionalFormula PropositionalHilbert.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Record pk2_frame : Type := {
  pk2_world : Type;
  pk2_access : pk2_world -> pk2_world -> Prop;
  pk2_root : pk2_world;
  pk2_root_access : forall w, pk2_access pk2_root w
}.

Arguments pk2_world _ : clear implicits.
Arguments pk2_access _ _ _ : clear implicits.
Arguments pk2_root _ : clear implicits.
Arguments pk2_root_access _ _ : clear implicits.

Definition pk2_valuation (Atom : Type) (F : pk2_frame) : Type :=
  Atom -> pk2_world F -> Prop.

Record pk2_model (Atom : Type) : Type := {
  pk2_model_frame : pk2_frame;
  pk2_model_valuation : pk2_valuation Atom pk2_model_frame
}.

Arguments pk2_model_frame {Atom} _.
Arguments pk2_model_valuation {Atom} _ _ _.

Fixpoint pk2_forces {Atom : Type} (M : pk2_model Atom)
    (w : pk2_world (pk2_model_frame M)) (p : pformula Atom) : Prop :=
  match p with
  | PAtom a => pk2_model_valuation M a w
  | PFalsum => False
  | PAnd q r => @pk2_forces Atom M w q /\ @pk2_forces Atom M w r
  | POr q r => @pk2_forces Atom M w q \/ @pk2_forces Atom M w r
  | PImp q r => forall v,
      pk2_access (pk2_model_frame M) w v ->
      @pk2_forces Atom M v q -> @pk2_forces Atom M v r
  end.

Arguments pk2_forces {Atom} M w p.

Lemma pk2_forces_atom :
  forall (Atom : Type) (M : pk2_model Atom) w a,
    pk2_forces M w (PAtom a) <-> pk2_model_valuation M a w.
Proof. reflexivity. Qed.

Lemma pk2_forces_bottom :
  forall (Atom : Type) (M : pk2_model Atom) w,
    ~ pk2_forces M w (@PFalsum Atom).
Proof. intros; exact (fun H => H). Qed.

Lemma pk2_forces_top :
  forall (Atom : Type) (M : pk2_model Atom) w,
    pk2_forces M w (@ptop Atom).
Proof. intros Atom M w v _ H; exact H. Qed.

Lemma pk2_forces_and :
  forall (Atom : Type) (M : pk2_model Atom) w p q,
    pk2_forces M w (PAnd p q) <->
    pk2_forces M w p /\ pk2_forces M w q.
Proof. reflexivity. Qed.

Lemma pk2_not_forces_and :
  forall (Atom : Type) (M : pk2_model Atom) w p q,
    ~ pk2_forces M w (PAnd p q) <->
    ~ pk2_forces M w p \/ ~ pk2_forces M w q.
Proof.
  intros Atom M w p q; cbn. destruct (classic (pk2_forces M w p)); tauto.
Qed.

Lemma pk2_forces_or :
  forall (Atom : Type) (M : pk2_model Atom) w p q,
    pk2_forces M w (POr p q) <->
    pk2_forces M w p \/ pk2_forces M w q.
Proof. reflexivity. Qed.

Lemma pk2_not_forces_or :
  forall (Atom : Type) (M : pk2_model Atom) w p q,
    ~ pk2_forces M w (POr p q) <->
    ~ pk2_forces M w p /\ ~ pk2_forces M w q.
Proof. intros; cbn; tauto. Qed.

Lemma pk2_forces_imp :
  forall (Atom : Type) (M : pk2_model Atom) w p q,
    pk2_forces M w (PImp p q) <->
    (forall v, pk2_access (pk2_model_frame M) w v ->
      pk2_forces M v p -> pk2_forces M v q).
Proof. reflexivity. Qed.

Lemma pk2_not_forces_imp :
  forall (Atom : Type) (M : pk2_model Atom) w p q,
    ~ pk2_forces M w (PImp p q) <->
    exists v, pk2_access (pk2_model_frame M) w v /\
      pk2_forces M v p /\ ~ pk2_forces M v q.
Proof.
  intros Atom M w p q; cbn; split.
  - intro Hnot. apply not_all_ex_not in Hnot.
    destruct Hnot as [v Hv]. exists v.
    destruct (classic (pk2_access (pk2_model_frame M) w v));
      destruct (classic (pk2_forces M v p)); tauto.
  - intros [v [Rwv [Hp Hq]]] Hall. exact (Hq (Hall v Rwv Hp)).
Qed.

Lemma pk2_forces_neg :
  forall (Atom : Type) (M : pk2_model Atom) w p,
    pk2_forces M w (pneg p) <->
    (forall v, pk2_access (pk2_model_frame M) w v ->
      ~ pk2_forces M v p).
Proof. reflexivity. Qed.

Lemma pk2_not_forces_neg :
  forall (Atom : Type) (M : pk2_model Atom) w p,
    ~ pk2_forces M w (pneg p) <->
    exists v, pk2_access (pk2_model_frame M) w v /\
      pk2_forces M v p.
Proof.
  intros Atom M w p. unfold pneg. rewrite pk2_not_forces_imp. cbn.
  firstorder.
Qed.

(** * Heterogeneous substitution *)

Definition pk2_substitution_model {A B : Type}
    (M : pk2_model B) (sigma : psubstitution A B) : pk2_model A :=
  {| pk2_model_frame := pk2_model_frame M;
     pk2_model_valuation := fun a w => pk2_forces M w (sigma a) |}.

Lemma pk2_forces_substitute :
  forall (A B : Type) (M : pk2_model B) (sigma : psubstitution A B)
         (p : pformula A) w,
    pk2_forces (pk2_substitution_model M sigma) w p <->
    pk2_forces M w (pformula_substitute sigma p).
Proof.
  intros A B M sigma p; induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq]; intro w; cbn.
  - reflexivity.
  - reflexivity.
  - now rewrite IHp, IHq.
  - now rewrite IHp, IHq.
  - split; intros H v Rwv Hv.
    + apply (proj1 (IHq v)), H with (v := v); [exact Rwv |].
      now apply (proj2 (IHp v)).
    + apply (proj2 (IHq v)), H with (v := v); [exact Rwv |].
      now apply (proj1 (IHp v)).
Qed.

(** * Model, frame, and class validity *)

Definition pk2_model_valid {Atom : Type}
    (M : pk2_model Atom) (p : pformula Atom) : Prop :=
  forall w, pk2_forces M w p.

Definition pk2_frame_valid {Atom : Type}
    (F : pk2_frame) (p : pformula Atom) : Prop :=
  forall V : pk2_valuation Atom F,
    pk2_model_valid {| pk2_model_frame := F;
      pk2_model_valuation := V |} p.

Definition pk2_frame_class_valid {Atom : Type}
    (C : pk2_frame -> Prop) (p : pformula Atom) : Prop :=
  forall F, C F -> pk2_frame_valid F p.

Definition pk2_model_class_valid {Atom : Type}
    (C : pk2_model Atom -> Prop) (p : pformula Atom) : Prop :=
  forall M, C M -> pk2_model_valid M p.

Lemma pk2_model_not_valid_iff :
  forall (Atom : Type) (M : pk2_model Atom) p,
    ~ pk2_model_valid M p <-> exists w, ~ pk2_forces M w p.
Proof.
  intros Atom M p; unfold pk2_model_valid; split.
  - apply not_all_ex_not.
  - intros [w Hw] Hall; exact (Hw (Hall w)).
Qed.

Lemma pk2_frame_not_valid_iff_model :
  forall (Atom : Type) (F : pk2_frame) p,
    ~ pk2_frame_valid F p <->
    exists V : pk2_valuation Atom F,
      ~ pk2_model_valid {| pk2_model_frame := F;
        pk2_model_valuation := V |} p.
Proof.
  intros Atom F p; unfold pk2_frame_valid; split.
  - apply not_all_ex_not.
  - intros [V HV] Hall; exact (HV (Hall V)).
Qed.

Lemma pk2_frame_not_valid_iff_world :
  forall (Atom : Type) (F : pk2_frame) p,
    ~ pk2_frame_valid F p <->
    exists (V : pk2_valuation Atom F) (w : pk2_world F),
      ~ pk2_forces {| pk2_model_frame := F;
        pk2_model_valuation := V |} w p.
Proof.
  intros Atom F p. rewrite pk2_frame_not_valid_iff_model.
  split.
  - intros [V HV]. apply pk2_model_not_valid_iff in HV.
    destruct HV as [w Hw]. now exists V, w.
  - intros [V [w Hw]]. exists V. apply pk2_model_not_valid_iff.
    now exists w.
Qed.

Lemma pk2_frame_valid_substitute :
  forall (A B : Type) (F : pk2_frame) (p : pformula A),
    pk2_frame_valid F p -> forall sigma : psubstitution A B,
    pk2_frame_valid F (pformula_substitute sigma p).
Proof.
  intros A B F p Hp sigma V w.
  apply (proj1 (@pk2_forces_substitute A B
    {| pk2_model_frame := F; pk2_model_valuation := V |}
    sigma p w)).
  apply Hp.
Qed.

Lemma pk2_frame_class_not_valid_iff_frame :
  forall (Atom : Type) (C : pk2_frame -> Prop) (p : pformula Atom),
    ~ pk2_frame_class_valid C p <->
    exists F, C F /\ ~ pk2_frame_valid F p.
Proof.
  intros Atom C p; unfold pk2_frame_class_valid; split.
  - intro Hnot. apply not_all_ex_not in Hnot. destruct Hnot as [F HF].
    exists F. destruct (classic (C F)); tauto.
  - intros [F [HF Hinvalid]] Hall. exact (Hinvalid (Hall F HF)).
Qed.

Lemma pk2_frame_class_not_valid_iff_model :
  forall (Atom : Type) (C : pk2_frame -> Prop) (p : pformula Atom),
    ~ pk2_frame_class_valid C p <->
    exists M : pk2_model Atom,
      C (pk2_model_frame M) /\ ~ pk2_model_valid M p.
Proof.
  intros Atom C p. rewrite pk2_frame_class_not_valid_iff_frame.
  split.
  - intros [F [HF Hinvalid]].
    apply pk2_frame_not_valid_iff_model in Hinvalid.
    destruct Hinvalid as [V HV].
    exists {| pk2_model_frame := F; pk2_model_valuation := V |}; auto.
  - intros [[F V] [HF Hinvalid]]. exists F; split; [exact HF |].
    apply pk2_frame_not_valid_iff_model. now exists V.
Qed.

Lemma pk2_frame_class_not_valid_iff_model_world :
  forall (Atom : Type) (C : pk2_frame -> Prop) (p : pformula Atom),
    ~ pk2_frame_class_valid C p <->
    exists (M : pk2_model Atom)
      (w : pk2_world (pk2_model_frame M)),
      C (pk2_model_frame M) /\ ~ pk2_forces M w p.
Proof.
  intros Atom C p. rewrite pk2_frame_class_not_valid_iff_model.
  split.
  - intros [M [HM Hinvalid]]. apply pk2_model_not_valid_iff in Hinvalid.
    destruct Hinvalid as [w Hw]. now exists M, w.
  - intros [M [w [HM Hw]]]. exists M; split; [exact HM |].
    apply pk2_model_not_valid_iff. now exists w.
Qed.

Lemma pk2_model_class_not_valid_iff_model :
  forall (Atom : Type) (C : pk2_model Atom -> Prop) (p : pformula Atom),
    ~ pk2_model_class_valid C p <->
    exists M, C M /\ ~ pk2_model_valid M p.
Proof.
  intros Atom C p; unfold pk2_model_class_valid; split.
  - intro Hnot. apply not_all_ex_not in Hnot. destruct Hnot as [M HM].
    exists M. destruct (classic (C M)); tauto.
  - intros [M [HM Hinvalid]] Hall. exact (Hinvalid (Hall M HM)).
Qed.

Lemma pk2_model_class_not_valid_iff_world :
  forall (Atom : Type) (C : pk2_model Atom -> Prop) (p : pformula Atom),
    ~ pk2_model_class_valid C p <->
    exists (M : pk2_model Atom)
      (w : pk2_world (pk2_model_frame M)),
      C M /\ ~ pk2_forces M w p.
Proof.
  intros Atom C p. rewrite pk2_model_class_not_valid_iff_model.
  split.
  - intros [M [HM Hinvalid]]. apply pk2_model_not_valid_iff in Hinvalid.
    destruct Hinvalid as [w Hw]. now exists M, w.
  - intros [M [w [HM Hw]]]. exists M; split; [exact HM |].
    apply pk2_model_not_valid_iff. now exists w.
Qed.

(** * Universally valid positive schemata and rules *)

Definition pk2_axiom_C {Atom : Type} (p q r : pformula Atom) :=
  PImp (PAnd (PImp p q) (PImp p r)) (PImp p (PAnd q r)).

Definition pk2_axiom_D {Atom : Type} (p q r : pformula Atom) :=
  PImp (PAnd (PImp p r) (PImp q r)) (PImp (POr p q) r).

Definition pk2_distribute_and_or {Atom : Type} (p q r : pformula Atom) :=
  PImp (PAnd p (POr q r)) (POr (PAnd p q) (PAnd p r)).

Definition pk2_axiom_I {Atom : Type} (p q r : pformula Atom) :=
  PImp (PAnd (PImp p q) (PImp q r)) (PImp p r).

Lemma pk2_valid_and1 :
  forall (Atom : Type) (M : pk2_model Atom) p q,
    pk2_model_valid M (ph_axiom_and1 p q).
Proof. intros Atom M p q x y _ [Hp _]; exact Hp. Qed.

Lemma pk2_valid_and2 :
  forall (Atom : Type) (M : pk2_model Atom) p q,
    pk2_model_valid M (ph_axiom_and2 p q).
Proof. intros Atom M p q x y _ [_ Hq]; exact Hq. Qed.

Lemma pk2_valid_axiom_C :
  forall (Atom : Type) (M : pk2_model Atom) p q r,
    pk2_model_valid M (pk2_axiom_C p q r).
Proof.
  intros Atom M p q r x y _ [Hpq Hpr] z Ryz Hp.
  split; [exact (Hpq z Ryz Hp) | exact (Hpr z Ryz Hp)].
Qed.

Lemma pk2_valid_or1 :
  forall (Atom : Type) (M : pk2_model Atom) p q,
    pk2_model_valid M (ph_axiom_or1 p q).
Proof. intros Atom M p q x y _ Hp; now left. Qed.

Lemma pk2_valid_or2 :
  forall (Atom : Type) (M : pk2_model Atom) p q,
    pk2_model_valid M (ph_axiom_or2 p q).
Proof. intros Atom M p q x y _ Hq; now right. Qed.

Lemma pk2_valid_axiom_D :
  forall (Atom : Type) (M : pk2_model Atom) p q r,
    pk2_model_valid M (pk2_axiom_D p q r).
Proof.
  intros Atom M p q r x y _ [Hpr Hqr] z Ryz [Hp | Hq].
  - exact (Hpr z Ryz Hp).
  - exact (Hqr z Ryz Hq).
Qed.

Lemma pk2_valid_distribute_and_or :
  forall (Atom : Type) (M : pk2_model Atom) p q r,
    pk2_model_valid M (pk2_distribute_and_or p q r).
Proof.
  intros Atom M p q r x y _ [Hp [Hq | Hr]].
  - left; now split.
  - right; now split.
Qed.

Lemma pk2_valid_axiom_I :
  forall (Atom : Type) (M : pk2_model Atom) p q r,
    pk2_model_valid M (pk2_axiom_I p q r).
Proof.
  intros Atom M p q r x y _ [Hpq Hqr] z Ryz Hp.
  exact (Hqr z Ryz (Hpq z Ryz Hp)).
Qed.

Lemma pk2_valid_identity :
  forall (Atom : Type) (M : pk2_model Atom) p,
    pk2_model_valid M (PImp p p).
Proof. intros Atom M p x y _ Hp; exact Hp. Qed.

Lemma pk2_valid_efq :
  forall (Atom : Type) (M : pk2_model Atom) p,
    pk2_model_valid M (ph_axiom_efq p).
Proof. intros Atom M p x y _ Hfalse; contradiction. Qed.

Lemma pk2_valid_afortiori :
  forall (Atom : Type) (M : pk2_model Atom) p q,
    pk2_model_valid M p -> pk2_model_valid M (PImp q p).
Proof. intros Atom M p q Hp x y _ _; apply Hp. Qed.

Lemma pk2_valid_conjunction_rule :
  forall (Atom : Type) (M : pk2_model Atom) p q,
    pk2_model_valid M p -> pk2_model_valid M q ->
    pk2_model_valid M (PAnd p q).
Proof. intros Atom M p q Hp Hq x; split; [apply Hp | apply Hq]. Qed.

Lemma pk2_valid_modus_ponens :
  forall (Atom : Type) (M : pk2_model Atom) p q,
    pk2_model_valid M (PImp p q) -> pk2_model_valid M p ->
    pk2_model_valid M q.
Proof.
  intros Atom M p q Hpq Hp x.
  exact (Hpq (pk2_root (pk2_model_frame M)) x
    (pk2_root_access (pk2_model_frame M) x) (Hp x)).
Qed.

(** The a-fortiori schema [p -> q -> p] is not valid without transitivity. *)
Inductive pk2_K_counter_world :=
| PK2KRoot
| PK2KOne
| PK2KTwo.

Definition pk2_K_counter_access (x y : pk2_K_counter_world) : Prop :=
  x = PK2KRoot \/ (x = PK2KOne /\ y = PK2KTwo).

Definition pk2_K_counter_frame : pk2_frame :=
  {| pk2_world := pk2_K_counter_world;
     pk2_access := pk2_K_counter_access;
     pk2_root := PK2KRoot;
     pk2_root_access := fun w => or_introl eq_refl |}.

Definition pk2_K_counter_valuation : pk2_valuation nat pk2_K_counter_frame :=
  fun a x =>
    match a with
    | 0 => x = PK2KOne
    | 1 => x = PK2KRoot \/ x = PK2KTwo
    | _ => False
    end.

Theorem pk2_K_counter_frame_refutes_K :
  ~ pk2_frame_valid pk2_K_counter_frame
      (ph_axiom_K (PAtom 0) (PAtom 1)).
Proof.
  apply pk2_frame_not_valid_iff_world.
  exists pk2_K_counter_valuation, PK2KRoot. cbn.
  intro Hvalid.
  specialize (Hvalid PK2KOne (or_introl eq_refl) eq_refl).
  specialize (Hvalid PK2KTwo (or_intror (conj eq_refl eq_refl))).
  pose proof (Hvalid (or_intror eq_refl)) as Habsurd.
  discriminate Habsurd.
Qed.
