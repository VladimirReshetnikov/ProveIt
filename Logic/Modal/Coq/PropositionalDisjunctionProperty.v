(** The disjunction property of intuitionistic propositional logic.

    This ports Foundation's [Propositional/Kripke/Hilbert/Int/DP.lean].
    Two pointed countermodels are placed below a fresh root.  Formula truth
    on either component is preserved exactly, so a disjunction true at the
    new root would make one of the selected counterexamples true. *)

From Stdlib Require Import Logic.Classical_Prop.
From FoundationModal Require Import
  PropositionalFormula PropositionalHilbert PropositionalKripke
  PropositionalKripkeCanonical.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Inductive pkripke_dp_world (W1 W2 : Type) : Type :=
| PKDP_root
| PKDP_left (w : W1)
| PKDP_right (w : W2).

Arguments PKDP_root {W1 W2}.
Arguments PKDP_left {W1 W2} _.
Arguments PKDP_right {W1 W2} _.

Definition pkripke_dp_access (F1 F2 : pkripke_frame)
    (w1 : pkripke_world F1) (w2 : pkripke_world F2)
    (x y : pkripke_dp_world (pkripke_world F1) (pkripke_world F2)) : Prop :=
  match x, y with
  | PKDP_root, PKDP_root => True
  | PKDP_root, PKDP_left y => pkripke_access F1 w1 y
  | PKDP_root, PKDP_right y => pkripke_access F2 w2 y
  | PKDP_left x, PKDP_left y => pkripke_access F1 x y
  | PKDP_right x, PKDP_right y => pkripke_access F2 x y
  | _, _ => False
  end.

Arguments pkripke_dp_access F1 F2 w1 w2 x y : clear implicits.

Lemma pkripke_dp_access_refl :
  forall F1 F2 w1 w2 x,
    pkripke_dp_access F1 F2 w1 w2 x x.
Proof.
  intros F1 F2 w1 w2 [|x|x]; cbn [pkripke_dp_access].
  - exact I.
  - apply pkripke_access_refl.
  - apply pkripke_access_refl.
Qed.

Lemma pkripke_dp_access_trans :
  forall F1 F2 w1 w2 x y z,
    pkripke_dp_access F1 F2 w1 w2 x y ->
    pkripke_dp_access F1 F2 w1 w2 y z ->
    pkripke_dp_access F1 F2 w1 w2 x z.
Proof.
  intros F1 F2 w1 w2 [|x|x] [|y|y] [|z|z] Hxy Hyz;
    cbn [pkripke_dp_access] in *;
    try contradiction; try exact I; try assumption;
    eauto using pkripke_access_trans.
Qed.

Definition pkripke_dp_frame (F1 F2 : pkripke_frame)
    (w1 : pkripke_world F1) (w2 : pkripke_world F2) : pkripke_frame :=
  {| pkripke_world :=
       pkripke_dp_world (pkripke_world F1) (pkripke_world F2);
     pkripke_access := pkripke_dp_access F1 F2 w1 w2;
     pkripke_access_refl := @pkripke_dp_access_refl F1 F2 w1 w2;
     pkripke_access_trans := @pkripke_dp_access_trans F1 F2 w1 w2 |}.

Arguments pkripke_dp_frame F1 F2 w1 w2 : clear implicits.

Definition pkripke_dp_valuation {Atom : Type}
    (M1 M2 : pkripke_model Atom)
    (w1 : pkripke_world (pkripke_model_frame M1))
    (w2 : pkripke_world (pkripke_model_frame M2)) :
    pkripke_valuation Atom
      (pkripke_dp_frame (pkripke_model_frame M1)
        (pkripke_model_frame M2) w1 w2).
Proof.
  refine (@Build_pkripke_valuation Atom
    (pkripke_dp_frame (pkripke_model_frame M1)
      (pkripke_model_frame M2) w1 w2)
    (fun (a : Atom)
      (x : pkripke_dp_world
        (pkripke_world (pkripke_model_frame M1))
        (pkripke_world (pkripke_model_frame M2))) =>
      match x with
      | PKDP_root => False
      | PKDP_left x =>
          pkripke_atom_value (pkripke_model_valuation M1) a x
      | PKDP_right x =>
          pkripke_atom_value (pkripke_model_valuation M2) a x
      end) _).
  intros a [|x|x] [|y|y] Rxy Hx;
    cbn [pkripke_dp_frame pkripke_dp_access] in *;
    try contradiction.
  - exact (@pkripke_atom_persistent Atom (pkripke_model_frame M1)
      (pkripke_model_valuation M1) a x y Rxy Hx).
  - exact (@pkripke_atom_persistent Atom (pkripke_model_frame M2)
      (pkripke_model_valuation M2) a x y Rxy Hx).
Defined.

Arguments pkripke_dp_valuation {Atom} M1 M2 w1 w2.

Definition pkripke_dp_model {Atom : Type}
    (M1 M2 : pkripke_model Atom)
    (w1 : pkripke_world (pkripke_model_frame M1))
    (w2 : pkripke_world (pkripke_model_frame M2)) :
    pkripke_model Atom :=
  {| pkripke_model_frame :=
       pkripke_dp_frame (pkripke_model_frame M1)
         (pkripke_model_frame M2) w1 w2;
     pkripke_model_valuation := pkripke_dp_valuation M1 M2 w1 w2 |}.

Arguments pkripke_dp_model {Atom} M1 M2 w1 w2.

Theorem pkripke_dp_forces_left_iff :
  forall (Atom : Type) (M1 M2 : pkripke_model Atom)
      (w1 : pkripke_world (pkripke_model_frame M1))
      (w2 : pkripke_world (pkripke_model_frame M2))
      (p : pformula Atom) x,
    pkripke_forces M1 x p <->
    pkripke_forces (pkripke_dp_model M1 M2 w1 w2) (PKDP_left x) p.
Proof.
  intros Atom M1 M2 w1 w2 p; induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq]; intro x; cbn.
  - reflexivity.
  - reflexivity.
  - now rewrite IHp, IHq.
  - now rewrite IHp, IHq.
  - split.
    + intros H u R Hup. destruct u as [|y|y];
        cbn [pkripke_dp_model pkripke_dp_frame pkripke_dp_access] in R;
        try contradiction.
      apply (proj1 (IHq y)), H with (v := y); [exact R |].
      now apply (proj2 (IHp y)).
    + intros H y R Hpy. apply (proj2 (IHq y)).
      apply (H (PKDP_left y));
        cbn [pkripke_dp_model pkripke_dp_frame pkripke_dp_access].
      * exact R.
      * now apply (proj1 (IHp y)).
Qed.

Theorem pkripke_dp_forces_right_iff :
  forall (Atom : Type) (M1 M2 : pkripke_model Atom)
      (w1 : pkripke_world (pkripke_model_frame M1))
      (w2 : pkripke_world (pkripke_model_frame M2))
      (p : pformula Atom) x,
    pkripke_forces M2 x p <->
    pkripke_forces (pkripke_dp_model M1 M2 w1 w2) (PKDP_right x) p.
Proof.
  intros Atom M1 M2 w1 w2 p; induction p as
      [a| |p IHp q IHq|p IHp q IHq|p IHp q IHq]; intro x; cbn.
  - reflexivity.
  - reflexivity.
  - now rewrite IHp, IHq.
  - now rewrite IHp, IHq.
  - split.
    + intros H u R Hup. destruct u as [|y|y];
        cbn [pkripke_dp_model pkripke_dp_frame pkripke_dp_access] in R;
        try contradiction.
      apply (proj1 (IHq y)), H with (v := y); [exact R |].
      now apply (proj2 (IHp y)).
    + intros H y R Hpy. apply (proj2 (IHq y)).
      apply (H (PKDP_right y));
        cbn [pkripke_dp_model pkripke_dp_frame pkripke_dp_access].
      * exact R.
      * now apply (proj1 (IHp y)).
Qed.

Theorem ph_hilbert_int_disjunction_property :
  forall p q : pformula nat,
    ph_hilbert_provable (ph_hilbert_int nat) (POr p q) ->
    ph_hilbert_provable (ph_hilbert_int nat) p \/
    ph_hilbert_provable (ph_hilbert_int nat) q.
Proof.
  intros p q Hor.
  destruct (classic (ph_hilbert_provable (ph_hilbert_int nat) p))
    as [Hp | Hnp]; [now left |].
  destruct (classic (ph_hilbert_provable (ph_hilbert_int nat) q))
    as [Hq | Hnq]; [now right |].
  exfalso.
  destruct (pki_unprovable_has_canonical_countermodel
    pki_int_has_efq Hnp) as [w1 Hfailp].
  destruct (pki_unprovable_has_canonical_countermodel
    pki_int_has_efq Hnq) as [w2 Hfailq].
  set (C := pki_canonical_model (ph_hilbert_int nat)).
  set (M := pkripke_dp_model C C w1 w2).
  assert (Hroot : ~ pkripke_forces M PKDP_root (POr p q)).
  { intros [Hrootp | Hrootq].
    - apply Hfailp, (proj2 (@pkripke_dp_forces_left_iff nat
        C C w1 w2 p w1)).
      apply (@pkripke_forces_persistent nat M p
        PKDP_root (PKDP_left w1)); [| exact Hrootp].
      change (pkripke_access (pkripke_model_frame C) w1 w1).
      apply pkripke_access_refl.
    - apply Hfailq, (proj2 (@pkripke_dp_forces_right_iff nat
        C C w1 w2 q w2)).
      apply (@pkripke_forces_persistent nat M q
        PKDP_root (PKDP_right w2)); [| exact Hrootq].
      change (pkripke_access (pkripke_model_frame C) w2 w2).
      apply pkripke_access_refl. }
  apply Hroot.
  exact (@ph_hilbert_int_pkripke_sound nat (POr p q) Hor
    (pkripke_model_frame M) I (pkripke_model_valuation M) PKDP_root).
Qed.
