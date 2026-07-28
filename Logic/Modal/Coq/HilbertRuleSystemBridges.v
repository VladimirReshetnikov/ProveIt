(**
  Syntactic bridges between the exact raw rule calculi and the established
  concrete presentations used by the GL equivalence development.

  [with_henkin_K4] and [with_loeb_K4_proves] instantiate the pinned
  Foundation raw-axiom calculi with exactly the two atomic K/Four templates.
  [K4Henkin_proves] and [K4Loeb_proves] instead close the existing schema
  presentation [K4_proves] under the corresponding rule.  The proofs below
  translate every constructor in both directions.  The final GL corollaries
  only compose these translations with the already checked concrete iff
  theorems; no semantics or completeness theorem is used here.
*)

From Stdlib Require Import Arith.PeanoNat.
From FoundationModal Require Import
  Syntax Axioms NormalHilbert EntailmentExtensions HilbertWithHenkin
  HilbertWithLoeb GLAlternativeSystems.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

(** * K4 with the Henkin rule *)

(** The normal K4 base embeds in the exact raw K/Four Henkin calculus. *)
Local Lemma K4_weaker_than_with_henkin_K4 :
  forall p : formula nat, K4_proves p -> with_henkin_K4 p.
Proof.
  intros p Hp; unfold with_henkin_K4; induction Hp.
  - apply WH_imply_K.
  - apply WH_imply_S.
  - apply WH_elim_contra.
  - exact
      (has_K_axiom
        (with_henkin_has_K Nat.eq_dec with_henkin_K4_axioms_has_K)
        p q).
  - destruct H as [q ->].
    exact
      (has_Four_axiom
        (with_henkin_has_Four Nat.eq_dec
          with_henkin_K4_axioms_has_Four) q).
  - exact (WH_mp IHHp1 IHHp2).
  - exact (WH_nec IHHp).
Qed.

Theorem with_henkin_K4_weaker_than_K4Henkin :
  forall p : formula nat,
    with_henkin_K4 p -> K4Henkin_proves p.
Proof.
  intros p Hp; unfold with_henkin_K4 in Hp; induction Hp.
  - unfold with_henkin_K4_axioms in H.
    destruct H as [-> | ->]; simpl.
    + apply K4Henkin_base, Np_modal_K.
    + apply K4Henkin_base, Np_extra. now exists (sigma 0).
  - exact (K4Henkin_mp IHHp1 IHHp2).
  - exact (K4Henkin_nec IHHp).
  - exact (K4Henkin_henkin IHHp).
  - apply K4Henkin_base, Np_imply_K.
  - apply K4Henkin_base, Np_imply_S.
  - apply K4Henkin_base, Np_elim_contra.
Qed.

Theorem K4Henkin_weaker_than_with_henkin_K4 :
  forall p : formula nat,
    K4Henkin_proves p -> with_henkin_K4 p.
Proof.
  intros p Hp; induction Hp.
  - now apply K4_weaker_than_with_henkin_K4.
  - exact (WH_mp IHHp1 IHHp2).
  - exact (WH_nec IHHp).
  - exact (WH_henkin IHHp).
Qed.

Theorem provable_with_henkin_K4_K4Henkin_iff :
  forall p : formula nat,
    with_henkin_K4 p <-> K4Henkin_proves p.
Proof.
  intro p; split.
  - apply with_henkin_K4_weaker_than_K4Henkin.
  - apply K4Henkin_weaker_than_with_henkin_K4.
Qed.

Theorem provable_GL_with_henkin_K4_iff :
  forall p : formula nat,
    GL_proves p <-> with_henkin_K4 p.
Proof.
  intro p; split; intro Hp.
  - apply K4Henkin_weaker_than_with_henkin_K4.
    exact (proj1 (provable_GL_K4Henkin_iff p) Hp).
  - apply (proj2 (provable_GL_K4Henkin_iff p)).
    now apply with_henkin_K4_weaker_than_K4Henkin.
Qed.

(** * K4 with Loeb's rule *)

(** The normal K4 base embeds in the exact raw K/Four Loeb calculus. *)
Local Lemma K4_weaker_than_with_loeb_K4 :
  forall p : formula nat, K4_proves p -> with_loeb_K4_proves p.
Proof.
  intros p Hp; unfold with_loeb_K4_proves; induction Hp.
  - apply WL_imply_K.
  - apply WL_imply_S.
  - apply WL_elim_contra.
  - exact
      (has_K_axiom
        (with_loeb_has_K Nat.eq_dec with_loeb_K4_axioms_has_K)
        p q).
  - destruct H as [q ->].
    exact
      (has_Four_axiom
        (with_loeb_has_Four Nat.eq_dec
          with_loeb_K4_axioms_has_Four) q).
  - exact (WL_mp IHHp1 IHHp2).
  - exact (WL_nec IHHp).
Qed.

Theorem with_loeb_K4_weaker_than_K4Loeb :
  forall p : formula nat,
    with_loeb_K4_proves p -> K4Loeb_proves p.
Proof.
  intros p Hp; unfold with_loeb_K4_proves in Hp; induction Hp.
  - unfold with_loeb_K4_axioms in H.
    destruct H as [-> | ->]; simpl.
    + apply K4Loeb_base, Np_modal_K.
    + apply K4Loeb_base, Np_extra. now exists (sigma 0).
  - exact (K4Loeb_mp IHHp1 IHHp2).
  - exact (K4Loeb_nec IHHp).
  - exact (K4Loeb_loeb IHHp).
  - apply K4Loeb_base, Np_imply_K.
  - apply K4Loeb_base, Np_imply_S.
  - apply K4Loeb_base, Np_elim_contra.
Qed.

Theorem K4Loeb_weaker_than_with_loeb_K4 :
  forall p : formula nat,
    K4Loeb_proves p -> with_loeb_K4_proves p.
Proof.
  intros p Hp; induction Hp.
  - now apply K4_weaker_than_with_loeb_K4.
  - exact (WL_mp IHHp1 IHHp2).
  - exact (WL_nec IHHp).
  - exact (WL_loeb IHHp).
Qed.

Theorem provable_with_loeb_K4_K4Loeb_iff :
  forall p : formula nat,
    with_loeb_K4_proves p <-> K4Loeb_proves p.
Proof.
  intro p; split.
  - apply with_loeb_K4_weaker_than_K4Loeb.
  - apply K4Loeb_weaker_than_with_loeb_K4.
Qed.

Theorem provable_GL_with_loeb_K4_iff :
  forall p : formula nat,
    GL_proves p <-> with_loeb_K4_proves p.
Proof.
  intro p; split; intro Hp.
  - apply K4Loeb_weaker_than_with_loeb_K4.
    exact (proj1 (provable_GL_K4Loeb_iff p) Hp).
  - apply (proj2 (provable_GL_K4Loeb_iff p)).
    now apply with_loeb_K4_weaker_than_K4Loeb.
Qed.
