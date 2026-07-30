(** Frame correspondences for rooted arbitrary-relation propositional
    semantics.

    This ports Foundation/Propositional/Kripke2/Axiom/{Corfl,Hrd,PSCon,
    Rfl,Ser,Sym,Tra}.  The soundness statements are atom-polymorphic, while
    the converses retain the source's small nat-atom test formulas.  Common
    relation predicates and axiom formulas are factored here rather than
    repeated across one-file correspondence proofs.

    Foundation's PCon module admits its only theorem with [sorry].  That
    statement is false for Kripke2's unrestricted valuations: the universal
    relation on two worlds is piecewise connected but refutes Dummett.  The
    formula family and an independently checked counterexample are included
    below instead of turning the admitted result into a Coq axiom. *)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  PropositionalFormula PropositionalHilbert PropositionalKripke2.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * Shared frame and model properties *)

Definition pk2_frame_coreflexive (F : pk2_frame) : Prop :=
  forall x y, pk2_access F x y -> x = y.

Definition pk2_frame_reflexive (F : pk2_frame) : Prop :=
  forall x, pk2_access F x x.

Definition pk2_frame_serial (F : pk2_frame) : Prop :=
  forall x, exists y, pk2_access F x y.

Definition pk2_frame_symmetric (F : pk2_frame) : Prop :=
  forall x y, pk2_access F x y -> pk2_access F y x.

Definition pk2_frame_transitive (F : pk2_frame) : Prop :=
  forall x y z,
    pk2_access F x y -> pk2_access F y z -> pk2_access F x z.

Definition pk2_frame_piecewise_connected (F : pk2_frame) : Prop :=
  forall x y z,
    pk2_access F x y -> pk2_access F x z ->
    pk2_access F y z \/ y = z \/ pk2_access F z y.

Definition pk2_frame_piecewise_strongly_connected (F : pk2_frame) : Prop :=
  forall x y z,
    pk2_access F x y -> pk2_access F x z ->
    pk2_access F y z \/ pk2_access F z y.

Definition pk2_model_hereditary {Atom : Type} (M : pk2_model Atom) : Prop :=
  forall a x y,
    pk2_model_valuation M a x ->
    pk2_access (pk2_model_frame M) x y ->
    pk2_model_valuation M a y.

Lemma pk2_reflexive_serial :
  forall F, pk2_frame_reflexive F -> pk2_frame_serial F.
Proof. intros F H x; exists x; apply H. Qed.

Lemma pk2_symmetric_serial :
  forall F, pk2_frame_symmetric F -> pk2_frame_serial F.
Proof.
  intros F Hsym x. exists (pk2_root F).
  apply Hsym, pk2_root_access.
Qed.

(** * Corsi axiom formulas *)

Definition pk2_axiom_rfl {Atom : Type} (p q : pformula Atom) :=
  PImp (PAnd p (PImp p q)) q.

Definition pk2_axiom_corefl {Atom : Type} (p q : pformula Atom) :=
  PAnd (PImp p (PImp q p)) (POr p (pneg p)).

Definition pk2_axiom_tra1 {Atom : Type} (p q r : pformula Atom) :=
  PImp (PImp p q) (PImp r (PImp p q)).

Definition pk2_axiom_tra2 {Atom : Type} (p q r : pformula Atom) :=
  PImp (PImp p q) (PImp (PImp q r) (PImp p r)).

Definition pk2_axiom_sym {Atom : Type} (p q : pformula Atom) :=
  PImp p (POr q (pneg (PImp p q))).

Definition pk2_axiom_ser {Atom : Type} : pformula Atom :=
  pneg (pneg ptop).

Definition pk2_axiom_hrd {Atom : Type} (p : pformula Atom) :=
  PImp p (PImp ptop p).

(** * Coreflexivity *)

Theorem pk2_valid_corefl_of_coreflexive :
  forall (Atom : Type) (F : pk2_frame),
    pk2_frame_coreflexive F -> forall p q : pformula Atom,
    pk2_frame_valid F (pk2_axiom_corefl p q).
Proof.
  intros Atom F Hcore p q V x; split.
  - intros y _ Hp z Ryz _. now rewrite <- (Hcore y z Ryz).
  - destruct (classic (pk2_forces
        {| pk2_model_frame := F; pk2_model_valuation := V |} x p))
      as [Hp | Hnp]; [now left | right].
    intros y Rxy Hp. apply Hnp.
    now rewrite (Hcore x y Rxy).
Qed.

Theorem pk2_coreflexive_of_valid_corefl :
  forall F : pk2_frame,
    pk2_frame_valid F
      (pk2_axiom_corefl (PAtom 0) (PAtom 1)) ->
    pk2_frame_coreflexive F.
Proof.
  intros F Hvalid x y Rxy.
  set (V := fun a w =>
    match a with
    | 0 => w = x
    | 1 => w = y
    | _ => False
    end : Prop).
  specialize (Hvalid V (pk2_root F)).
  destruct Hvalid as [Himp [Hroot | Hneg]].
  - specialize (Himp x (pk2_root_access F x) eq_refl).
    specialize (Himp y Rxy eq_refl). exact (eq_sym Himp).
  - exfalso. exact (Hneg x (pk2_root_access F x) eq_refl).
Qed.

Corollary pk2_coreflexive_iff_valid_corefl :
  forall F : pk2_frame,
    pk2_frame_coreflexive F <->
    pk2_frame_valid F
      (pk2_axiom_corefl (PAtom 0) (PAtom 1)).
Proof.
  intro F; split; [intro H; now apply pk2_valid_corefl_of_coreflexive |
    apply pk2_coreflexive_of_valid_corefl].
Qed.

(** * Atomic heredity *)

Theorem pk2_valid_hrd_of_hereditary :
  forall (Atom : Type) (M : pk2_model Atom),
    pk2_model_hereditary M -> forall a,
    pk2_model_valid M (pk2_axiom_hrd (PAtom a)).
Proof.
  intros Atom M Hher a x y _ Ha z Ryz _.
  exact (Hher a y z Ha Ryz).
Qed.

Theorem pk2_hereditary_of_valid_hrd :
  forall (Atom : Type) (M : pk2_model Atom),
    (forall a, pk2_model_valid M (pk2_axiom_hrd (PAtom a))) ->
    pk2_model_hereditary M.
Proof.
  intros Atom M Hvalid a x y Ha Rxy.
  specialize (Hvalid a (pk2_root (pk2_model_frame M))).
  specialize (Hvalid x (pk2_root_access (pk2_model_frame M) x) Ha).
  exact (Hvalid y Rxy (@pk2_forces_top Atom M y)).
Qed.

Corollary pk2_hereditary_iff_valid_hrd :
  forall (Atom : Type) (M : pk2_model Atom),
    pk2_model_hereditary M <->
    (forall a, pk2_model_valid M (pk2_axiom_hrd (PAtom a))).
Proof.
  intros Atom M; split; [apply pk2_valid_hrd_of_hereditary |
    apply pk2_hereditary_of_valid_hrd].
Qed.

(** * Reflexivity *)

Theorem pk2_valid_rfl_of_reflexive :
  forall (Atom : Type) (F : pk2_frame),
    pk2_frame_reflexive F -> forall p q : pformula Atom,
    pk2_frame_valid F (pk2_axiom_rfl p q).
Proof.
  intros Atom F Hrefl p q V x y _ [Hp Hpq].
  exact (Hpq y (Hrefl y) Hp).
Qed.

Theorem pk2_reflexive_of_valid_rfl :
  forall F : pk2_frame,
    pk2_frame_valid F (pk2_axiom_rfl (PAtom 0) (PAtom 1)) ->
    pk2_frame_reflexive F.
Proof.
  intros F Hvalid x.
  set (V := fun a w =>
    match a with
    | 0 => w = x
    | 1 => pk2_access F x w
    | _ => False
    end : Prop).
  specialize (Hvalid V (pk2_root F) x (pk2_root_access F x)).
  apply Hvalid; split; [reflexivity |].
  intros y Rxy _. exact Rxy.
Qed.

Corollary pk2_reflexive_iff_valid_rfl :
  forall F : pk2_frame,
    pk2_frame_reflexive F <->
    pk2_frame_valid F (pk2_axiom_rfl (PAtom 0) (PAtom 1)).
Proof.
  intro F; split; [intro H; now apply pk2_valid_rfl_of_reflexive |
    apply pk2_reflexive_of_valid_rfl].
Qed.

(** * Seriality *)

Theorem pk2_valid_ser_of_serial :
  forall (Atom : Type) (F : pk2_frame),
    pk2_frame_serial F -> pk2_frame_valid F (@pk2_axiom_ser Atom).
Proof.
  intros Atom F Hserial V x y _ Hneg.
  destruct (Hserial y) as [z Ryz].
  exact (Hneg z Ryz (@pk2_forces_top Atom
    {| pk2_model_frame := F; pk2_model_valuation := V |} z)).
Qed.

Theorem pk2_serial_of_valid_ser :
  forall (Atom : Type) (F : pk2_frame),
    pk2_frame_valid F (@pk2_axiom_ser Atom) -> pk2_frame_serial F.
Proof.
  intros Atom F Hvalid x. apply NNPP; intro Hnone.
  specialize (Hvalid (fun _ _ => True) (pk2_root F)
    x (pk2_root_access F x)).
  apply Hvalid. intros y Rxy _.
  apply Hnone. now exists y.
Qed.

Corollary pk2_serial_iff_valid_ser :
  forall (Atom : Type) (F : pk2_frame),
    pk2_frame_serial F <-> pk2_frame_valid F (@pk2_axiom_ser Atom).
Proof.
  intros Atom F; split; [apply pk2_valid_ser_of_serial |
    apply pk2_serial_of_valid_ser].
Qed.

(** * Symmetry *)

Theorem pk2_valid_sym_of_symmetric :
  forall (Atom : Type) (F : pk2_frame),
    pk2_frame_symmetric F -> forall p q : pformula Atom,
    pk2_frame_valid F (pk2_axiom_sym p q).
Proof.
  intros Atom F Hsym p q V x y _ Hp.
  destruct (classic (pk2_forces
      {| pk2_model_frame := F; pk2_model_valuation := V |} y q))
    as [Hq | Hnq]; [now left | right].
  intros z Ryz Hpq. apply Hnq.
  exact (Hpq y (Hsym y z Ryz) Hp).
Qed.

Theorem pk2_symmetric_of_valid_sym :
  forall F : pk2_frame,
    pk2_frame_valid F (pk2_axiom_sym (PAtom 0) (PAtom 1)) ->
    pk2_frame_symmetric F.
Proof.
  intros F Hvalid x y Rxy.
  set (V := fun a w =>
    match a with
    | 0 => w = x
    | 1 => pk2_access F y w
    | _ => False
    end : Prop).
  specialize (Hvalid V (pk2_root F) x
    (pk2_root_access F x) eq_refl).
  destruct Hvalid as [Hyx | Hneg]; [exact Hyx |].
  exfalso. apply (Hneg y Rxy).
  intros z Ryz _. exact Ryz.
Qed.

Corollary pk2_symmetric_iff_valid_sym :
  forall F : pk2_frame,
    pk2_frame_symmetric F <->
    pk2_frame_valid F (pk2_axiom_sym (PAtom 0) (PAtom 1)).
Proof.
  intro F; split; [intro H; now apply pk2_valid_sym_of_symmetric |
    apply pk2_symmetric_of_valid_sym].
Qed.

(** * Transitivity *)

Theorem pk2_valid_tra1_of_transitive :
  forall (Atom : Type) (F : pk2_frame),
    pk2_frame_transitive F -> forall p q r : pformula Atom,
    pk2_frame_valid F (pk2_axiom_tra1 p q r).
Proof.
  intros Atom F Htrans p q r V x y _ Hpq z Ryz _ v Rzv Hp.
  exact (Hpq v (Htrans y z v Ryz Rzv) Hp).
Qed.

Theorem pk2_transitive_of_valid_tra1 :
  forall F : pk2_frame,
    pk2_frame_valid F
      (pk2_axiom_tra1 (PAtom 0) (PAtom 1) (PAtom 2)) ->
    pk2_frame_transitive F.
Proof.
  intros F Hvalid x y z Rxy Ryz.
  set (V := fun a w =>
    match a with
    | 0 => pk2_access F y w
    | 1 => pk2_access F x w
    | 2 => pk2_access F x w
    | _ => False
    end : Prop).
  specialize (Hvalid V (pk2_root F) x (pk2_root_access F x)).
  apply (Hvalid (fun u Rxu _ => Rxu) y Rxy Rxy z Ryz Ryz).
Qed.

Theorem pk2_valid_tra2_of_transitive :
  forall (Atom : Type) (F : pk2_frame),
    pk2_frame_transitive F -> forall p q r : pformula Atom,
    pk2_frame_valid F (pk2_axiom_tra2 p q r).
Proof.
  intros Atom F Htrans p q r V x y _ Hpq z Ryz Hqr v Rzv Hp.
  exact (Hqr v Rzv (Hpq v (Htrans y z v Ryz Rzv) Hp)).
Qed.

Theorem pk2_transitive_of_valid_tra2 :
  forall F : pk2_frame,
    pk2_frame_valid F
      (pk2_axiom_tra2 (PAtom 0) (PAtom 1) (PAtom 2)) ->
    pk2_frame_transitive F.
Proof.
  intros F Hvalid x y z Rxy Ryz.
  set (V := fun a w =>
    match a with
    | 0 => w = z
    | 1 => pk2_access F x w
    | 2 => pk2_access F x w
    | _ => False
    end : Prop).
  specialize (Hvalid V (pk2_root F) x (pk2_root_access F x)).
  apply (Hvalid (fun u Rxu _ => Rxu)
    y Rxy (fun u _ Hu => Hu) z Ryz eq_refl).
Qed.

Corollary pk2_transitive_iff_valid_tra1 :
  forall F : pk2_frame,
    pk2_frame_transitive F <->
    pk2_frame_valid F
      (pk2_axiom_tra1 (PAtom 0) (PAtom 1) (PAtom 2)).
Proof.
  intro F; split; [intro H; now apply pk2_valid_tra1_of_transitive |
    apply pk2_transitive_of_valid_tra1].
Qed.

Corollary pk2_transitive_iff_valid_tra2 :
  forall F : pk2_frame,
    pk2_frame_transitive F <->
    pk2_frame_valid F
      (pk2_axiom_tra2 (PAtom 0) (PAtom 1) (PAtom 2)).
Proof.
  intro F; split; [intro H; now apply pk2_valid_tra2_of_transitive |
    apply pk2_transitive_of_valid_tra2].
Qed.

Corollary pk2_valid_tra1_iff_valid_tra2 :
  forall F : pk2_frame,
    pk2_frame_valid F
      (pk2_axiom_tra1 (PAtom 0) (PAtom 1) (PAtom 2)) <->
    pk2_frame_valid F
      (pk2_axiom_tra2 (PAtom 0) (PAtom 1) (PAtom 2)).
Proof.
  intro F; rewrite <- pk2_transitive_iff_valid_tra1.
  apply pk2_transitive_iff_valid_tra2.
Qed.

(** * Piecewise strong connectedness *)

Definition pk2_axiom_pscon {Atom : Type}
    (p q r s : pformula Atom) :=
  POr (PImp (PAnd r (PImp p q)) s)
      (PImp (PAnd p (PImp r s)) q).

Theorem pk2_valid_pscon_of_piecewise_strongly_connected :
  forall (Atom : Type) (F : pk2_frame),
    pk2_frame_piecewise_strongly_connected F ->
    forall p q r s : pformula Atom,
    pk2_frame_valid F (pk2_axiom_pscon p q r s).
Proof.
  intros Atom F Hconn p q r s V x. apply NNPP; intro Hnot.
  apply pk2_not_forces_or in Hnot. destruct Hnot as [Hleft Hright].
  apply pk2_not_forces_imp in Hleft.
  destruct Hleft as [y [Rxy [[Hr Hpq] Hns]]].
  apply pk2_not_forces_imp in Hright.
  destruct Hright as [z [Rxz [[Hp Hrs] Hnq]]].
  destruct (Hconn x y z Rxy Rxz) as [Ryz | Rzy].
  - exact (Hnq (Hpq z Ryz Hp)).
  - exact (Hns (Hrs y Rzy Hr)).
Qed.

(** * Piecewise-connected formulas and the admitted-source counterexample *)

Definition pk2_axiom_pcon1 {Atom : Type} (p q : pformula Atom) :=
  ph_axiom_dummett p q.

Definition pk2_axiom_pcon2 {Atom : Type} (p q : pformula Atom) :=
  PImp (PImp p q) (PImp (PImp p q) p).

Definition pk2_axiom_pcon3 {Atom : Type} (p q : pformula Atom) :=
  PImp (PImp p q) (PImp (PImp p q) q).

Definition pk2_axiom_pcon4 {Atom : Type}
    (p q r : pformula Atom) :=
  PImp (PImp p (POr q r)) (POr (PImp p q) (PImp p r)).

Definition pk2_axiom_pcon5 {Atom : Type}
    (p q r : pformula Atom) :=
  PImp (POr (PAnd p q) r) (POr (PImp p r) (PImp p q)).

Definition pk2_axiom_pcon6 {Atom : Type} (p q : pformula Atom) :=
  PImp (PAnd (PImp (PImp p q) q) (PImp (PImp q p) p))
    (POr p q).

Inductive pk2_pcon_counter_world :=
| PK2PConLeft
| PK2PConRight.

Definition pk2_pcon_counter_frame : pk2_frame :=
  {| pk2_world := pk2_pcon_counter_world;
     pk2_access := fun _ _ => True;
     pk2_root := PK2PConLeft;
     pk2_root_access := fun _ => I |}.

Definition pk2_pcon_counter_valuation :
    pk2_valuation nat pk2_pcon_counter_frame :=
  fun a w =>
    match a with
    | 0 => w = PK2PConLeft
    | 1 => w = PK2PConRight
    | _ => False
    end.

Lemma pk2_pcon_counter_piecewise_strongly_connected :
  pk2_frame_piecewise_strongly_connected pk2_pcon_counter_frame.
Proof. intros; now left. Qed.

Lemma pk2_pcon_counter_piecewise_connected :
  pk2_frame_piecewise_connected pk2_pcon_counter_frame.
Proof. intros; now left. Qed.

Theorem pk2_pcon1_not_valid_on_piecewise_connected_frame :
  ~ pk2_frame_valid pk2_pcon_counter_frame
      (pk2_axiom_pcon1 (PAtom 0) (PAtom 1)).
Proof.
  apply pk2_frame_not_valid_iff_world.
  exists pk2_pcon_counter_valuation, PK2PConLeft.
  intros [Hpq | Hqp].
  - specialize (Hpq PK2PConLeft I eq_refl). discriminate Hpq.
  - specialize (Hqp PK2PConRight I eq_refl). discriminate Hqp.
Qed.
