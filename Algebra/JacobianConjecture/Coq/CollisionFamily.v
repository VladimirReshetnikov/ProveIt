From Stdlib Require Import Reals Ring Field Psatz.
From Coquelicot Require Import Complex.
From JacobianConjecture Require Import Counterexample Scaling.

Open Scope C_scope.
Import LeanProofs.JacobianCounterexample.
Import Scaling.

(**
  The rational one-parameter family of collisions, as a torus orbit.

  The parameter-[t] member of the family is the weighted scaling by [1 / t]
  of the mirrored integral collision.  Once that identification is made
  ([collision_family_*_eq_scale] below, the only computations in this file),
  every property of the family — the common values, the collision itself,
  and the closure under the mirror symmetry with parameter action
  [t |-> - t] — follows by rewriting from the torus action of [Scaling.v]
  and the single integral collision of [Counterexample.v].
*)

Module CollisionFamily.

Definition collision_family_0 (t : C) : Point3 :=
  point3 t (-c1 / t) (c5 / (t * t)).

Definition collision_family_1 (t : C) : Point3 :=
  point3 c0 (c2 / t) (-c16 / (t * t)).

Definition collision_family_value (t : C) : Point3 :=
  point3 c0 (c2 / t) c0.

(** Unfold the family points on top of the shared unfolding tactic. *)
Ltac family_c :=
  cbv [collision_family_0 collision_family_1 collision_family_value
       scale_source scale_target];
  eval_c.

(** **The family is a torus orbit.**  These three identifications are the
    only computations in this file. *)

Lemma collision_family_0_eq_scale (t : C) (ht : t <> c0) :
  collision_family_0 t =
  scale_source (c1 / t) (flip_source integral_collision_0).
Proof.
  apply point3_ext; family_c; field; repeat split; try exact ht; try exact c1_neq_0.
Qed.

Lemma collision_family_1_eq_scale (t : C) (ht : t <> c0) :
  collision_family_1 t =
  scale_source (c1 / t) (flip_source integral_collision_1).
Proof.
  apply point3_ext; family_c; field; repeat split; try exact ht; try exact c1_neq_0.
Qed.

Lemma collision_family_value_eq_scale (t : C) (ht : t <> c0) :
  collision_family_value t =
  scale_target (c1 / t) (flip_target integral_collision_value).
Proof.
  apply point3_ext; family_c; field; repeat split; try exact ht; try exact c1_neq_0.
Qed.

(** The scaling parameter of the orbit is nonzero. *)
Lemma inv_param_neq_0 (t : C) (ht : t <> c0) : c1 / t <> c0.
Proof. exact (neq_0_div c1 t c1_neq_0 ht). Qed.

(** The family values, by rewriting alone. *)
Theorem collision_family_0_value (t : C) (ht : t <> c0) :
  eval_map counterexample (collision_family_0 t) = collision_family_value t.
Proof.
  rewrite (collision_family_0_eq_scale t ht).
  rewrite (counterexample_scaling _ (inv_param_neq_0 t ht)).
  rewrite counterexample_equivariant, integral_collision_0_value.
  rewrite (collision_family_value_eq_scale t ht).
  reflexivity.
Qed.

Theorem collision_family_1_value (t : C) (ht : t <> c0) :
  eval_map counterexample (collision_family_1 t) = collision_family_value t.
Proof.
  rewrite (collision_family_1_eq_scale t ht).
  rewrite (counterexample_scaling _ (inv_param_neq_0 t ht)).
  rewrite counterexample_equivariant, integral_collision_1_value.
  rewrite (collision_family_value_eq_scale t ht).
  reflexivity.
Qed.

Theorem collision_family (t : C) (ht : t <> c0) :
  eval_map counterexample (collision_family_0 t) =
  eval_map counterexample (collision_family_1 t).
Proof.
  rewrite collision_family_0_value by exact ht.
  rewrite collision_family_1_value by exact ht.
  reflexivity.
Qed.

Theorem collision_family_points_distinct (t : C) (ht : t <> c0) :
  collision_family_0 t <> collision_family_1 t.
Proof.
  intro h.
  apply (f_equal xcoord) in h.
  cbv [collision_family_0 collision_family_1 xcoord] in h.
  exact (ht h).
Qed.

(** **Equivariance of the family.**  The source involution sends the
    parameter-[t] member to the parameter-[-t] member: compose the
    [s = -1] slice with the orbit parametrization. *)
Theorem collision_family_0_mirror (t : C) (ht : t <> c0) :
  flip_source (collision_family_0 t) = collision_family_0 (- t).
Proof.
  rewrite (collision_family_0_eq_scale t ht).
  rewrite flip_source_eq_scale.
  rewrite (scale_source_comp _ _
    (neq_0_opp c1 c1_neq_0) (inv_param_neq_0 t ht)).
  replace (- c1 * (c1 / t)) with (c1 / - t) by (cbv [c1]; field; exact ht).
  rewrite <- (collision_family_0_eq_scale (- t) (neq_0_opp t ht)).
  reflexivity.
Qed.

Theorem collision_family_1_mirror (t : C) (ht : t <> c0) :
  flip_source (collision_family_1 t) = collision_family_1 (- t).
Proof.
  rewrite (collision_family_1_eq_scale t ht).
  rewrite flip_source_eq_scale.
  rewrite (scale_source_comp _ _
    (neq_0_opp c1 c1_neq_0) (inv_param_neq_0 t ht)).
  replace (- c1 * (c1 / t)) with (c1 / - t) by (cbv [c1]; field; exact ht).
  rewrite <- (collision_family_1_eq_scale (- t) (neq_0_opp t ht)).
  reflexivity.
Qed.

Theorem collision_family_value_mirror (t : C) (ht : t <> c0) :
  flip_target (collision_family_value t) = collision_family_value (- t).
Proof.
  rewrite (collision_family_value_eq_scale t ht).
  rewrite flip_target_eq_scale.
  rewrite (scale_target_comp _ _
    (neq_0_opp c1 c1_neq_0) (inv_param_neq_0 t ht)).
  replace (- c1 * (c1 / t)) with (c1 / - t) by (cbv [c1]; field; exact ht).
  rewrite <- (collision_family_value_eq_scale (- t) (neq_0_opp t ht)).
  reflexivity.
Qed.

(** Scaling the parameter-[t] member by [t] recovers the mirrored integral
    collision: the orbit parametrization inverted. *)
Theorem scale_collision_family_0 (t : C) (ht : t <> c0) :
  scale_source t (collision_family_0 t) = flip_source integral_collision_0.
Proof.
  rewrite (collision_family_0_eq_scale t ht).
  rewrite (scale_source_comp _ _ ht (inv_param_neq_0 t ht)).
  replace (t * (c1 / t)) with c1 by (cbv [c1]; field; exact ht).
  exact (scale_source_one _).
Qed.

Theorem scale_collision_family_1 (t : C) (ht : t <> c0) :
  scale_source t (collision_family_1 t) = flip_source integral_collision_1.
Proof.
  rewrite (collision_family_1_eq_scale t ht).
  rewrite (scale_source_comp _ _ ht (inv_param_neq_0 t ht)).
  replace (t * (c1 / t)) with c1 by (cbv [c1]; field; exact ht).
  exact (scale_source_one _).
Qed.

Theorem scale_collision_family_value (t : C) (ht : t <> c0) :
  scale_target t (collision_family_value t) =
  flip_target integral_collision_value.
Proof.
  rewrite (collision_family_value_eq_scale t ht).
  rewrite (scale_target_comp _ _ ht (inv_param_neq_0 t ht)).
  replace (t * (c1 / t)) with c1 by (cbv [c1]; field; exact ht).
  exact (scale_target_one _).
Qed.

(** **The integral collision is the [t = -1] member of the family.** *)
Theorem collision_family_0_at_minus_one :
  collision_family_0 (- c1) = integral_collision_0.
Proof.
  apply point3_ext; family_c; field;
    apply neq_0_opp; exact c1_neq_0.
Qed.

Theorem collision_family_1_at_minus_one :
  collision_family_1 (- c1) = integral_collision_1.
Proof.
  apply point3_ext; family_c; field;
    apply neq_0_opp; exact c1_neq_0.
Qed.

Theorem collision_family_value_at_minus_one :
  collision_family_value (- c1) = integral_collision_value.
Proof.
  apply point3_ext; family_c; field;
    apply neq_0_opp; exact c1_neq_0.
Qed.

End CollisionFamily.
