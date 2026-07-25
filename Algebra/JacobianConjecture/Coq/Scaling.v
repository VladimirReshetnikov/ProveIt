From Stdlib Require Import Reals Ring Field Psatz.
From Coquelicot Require Import Complex.
From JacobianConjecture Require Import Counterexample.

Open Scope C_scope.
Import LeanProofs.JacobianCounterexample.

(**
  The weighted torus action behind the discrete symmetry.

  Alpöge's map is homogeneous for the grading [weight (x, y, z) = (-1, 1, 2)]:
  for every nonzero scalar [s],

    [F (x / s, s y, s^2 z) = (s^2 P, s Q, R / s)].

  The flip involutions of [Counterexample.v] are the [s = -1] instance, and
  [CollisionFamily.v] derives the entire rational one-parameter family of
  collisions from this action and one integral collision.
*)

Module Scaling.

(** The weight [(-1, 1, 2)] source action. *)
Definition scale_source (s : C) (p : Point3) : Point3 :=
  point3 (xcoord p / s) (s * ycoord p) (s * s * zcoord p).

(** The weight [(2, 1, -1)] target action. *)
Definition scale_target (s : C) (p : Point3) : Point3 :=
  point3 (s * s * xcoord p) (s * ycoord p) (zcoord p / s).

(** **Weighted homogeneity.** *)
Theorem counterexample_scaling (s : C) (hs : s <> c0) (p : Point3) :
  eval_map counterexample (scale_source s p) =
  scale_target s (eval_map counterexample p).
Proof.
  destruct p as [x y z]; apply point3_ext;
    cbv [scale_source scale_target]; eval_c; field; exact hs.
Qed.

(** Scaling preserves collisions. *)
Theorem collision_scaling (s : C) (hs : s <> c0) (p q : Point3)
    (h : eval_map counterexample p = eval_map counterexample q) :
  eval_map counterexample (scale_source s p) =
  eval_map counterexample (scale_source s q).
Proof.
  rewrite !(counterexample_scaling s hs), h; reflexivity.
Qed.

(** The source action composes multiplicatively. *)
Theorem scale_source_comp (a b : C) (ha : a <> c0) (hb : b <> c0)
    (p : Point3) :
  scale_source a (scale_source b p) = scale_source (a * b) p.
Proof.
  apply point3_ext; cbv [scale_source]; eval_c; field; split; assumption.
Qed.

(** The target action composes multiplicatively. *)
Theorem scale_target_comp (a b : C) (ha : a <> c0) (hb : b <> c0)
    (p : Point3) :
  scale_target a (scale_target b p) = scale_target (a * b) p.
Proof.
  apply point3_ext; cbv [scale_target]; eval_c; field; split; assumption.
Qed.

(** The actions fix everything at [s = 1]. *)
Theorem scale_source_one (p : Point3) : scale_source c1 p = p.
Proof.
  apply point3_ext; cbv [scale_source]; eval_c; field; exact c1_neq_0.
Qed.

Theorem scale_target_one (p : Point3) : scale_target c1 p = p.
Proof.
  apply point3_ext; cbv [scale_target]; eval_c; field; exact c1_neq_0.
Qed.

(** The discrete flips are the [s = -1] instance of the action. *)
Theorem flip_source_eq_scale (p : Point3) :
  flip_source p = scale_source (- c1) p.
Proof.
  apply point3_ext; cbv [scale_source]; eval_c; field; re_neq.
Qed.

Theorem flip_target_eq_scale (p : Point3) :
  flip_target p = scale_target (- c1) p.
Proof.
  apply point3_ext; cbv [scale_target]; eval_c; field; re_neq.
Qed.

End Scaling.
