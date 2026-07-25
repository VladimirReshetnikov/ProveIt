From Stdlib Require Import Reals Ring Field Psatz.
From Coquelicot Require Import Complex.
From JacobianConjecture Require Export Common.

Open Scope C_scope.

(**
  A lower-degree stable counterexample.

  Alpöge's three-variable map has ordinary degree seven.  Introducing two
  variables and applying determinant-one triangular source and target shears
  gives the five-variable map below, whose coordinate degree profile is
  [(6,6,4,3,4)].  The formal five-by-five Jacobian determinant is still [-2],
  and an explicit integral collision rules out a polynomial inverse.

  As in [Counterexample.v], [Poly5] is a small syntax with formal
  differentiation.  The determinant and collision certificates are checked
  entirely by Coq's kernel.

  The stable shears preserve the equivariance of the three-variable map:
  negating [x, y, a, b] negates all image coordinates except the first
  ([simpler_counterexample_equivariant] below).
*)

Module LeanProofs.
Module JacobianSimplerCounterexample.

Inductive Var5 : Type := VX | VY | VZ | VA | VB.

Definition var5_eqb (i j : Var5) : bool :=
  match i, j with
  | VX, VX | VY, VY | VZ, VZ | VA, VA | VB, VB => true
  | _, _ => false
  end.

Inductive Poly5 : Type :=
| PConst (c : C)
| PVar (i : Var5)
| PAdd (p q : Poly5)
| PMul (p q : Poly5)
| POpp (p : Poly5).

Definition PSub (p q : Poly5) : Poly5 := PAdd p (POpp q).
Definition PSq (p : Poly5) : Poly5 := PMul p p.
Definition PCube (p : Poly5) : Poly5 := PMul (PMul p p) p.

Record Point5 : Type := point5 {
  xcoord5 : C;
  ycoord5 : C;
  zcoord5 : C;
  acoord5 : C;
  bcoord5 : C
}.

Definition coordinate5 (i : Var5) (p : Point5) : C :=
  match i with
  | VX => xcoord5 p
  | VY => ycoord5 p
  | VZ => zcoord5 p
  | VA => acoord5 p
  | VB => bcoord5 p
  end.

Fixpoint eval_poly5 (p : Poly5) (v : Point5) : C :=
  match p with
  | PConst c => c
  | PVar i => coordinate5 i v
  | PAdd p q => eval_poly5 p v + eval_poly5 q v
  | PMul p q => eval_poly5 p v * eval_poly5 q v
  | POpp p => - eval_poly5 p v
  end.

Fixpoint partial5 (i : Var5) (p : Poly5) : Poly5 :=
  match p with
  | PConst _ => PConst c0
  | PVar j => PConst (if var5_eqb i j then c1 else c0)
  | PAdd p q => PAdd (partial5 i p) (partial5 i q)
  | PMul p q => PAdd (PMul (partial5 i p) q) (PMul p (partial5 i q))
  | POpp p => POpp (partial5 i p)
  end.

(** A syntactic upper bound on ordinary total degree.  For the expanded
    coordinates below it is exact, and is independent of evaluation. *)
Fixpoint degree_bound (p : Poly5) : nat :=
  match p with
  | PConst _ => 0
  | PVar _ => 1
  | PAdd p q => Nat.max (degree_bound p) (degree_bound q)
  | PMul p q => degree_bound p + degree_bound q
  | POpp p => degree_bound p
  end.

Definition one := PConst c1.
Definition two := PConst c2.
Definition three := PConst c3.
Definition four := PConst c4.
Definition seven := PConst c7.
Definition px := PVar VX.
Definition py := PVar VY.
Definition pz := PVar VZ.
Definition pa := PVar VA.
Definition pb := PVar VB.

Definition base_u : Poly5 := PAdd one (PMul px py).

Definition base_P : Poly5 :=
  PAdd (PMul (PCube base_u) pz)
    (PMul (PMul (PSq py) base_u)
      (PAdd four (PMul three (PMul px py)))).

Definition base_Q : Poly5 :=
  PAdd py
    (PAdd (PMul (PMul three px) (PMul (PSq base_u) pz))
      (PMul (PMul (PMul three px) (PSq py))
        (PAdd four (PMul three (PMul px py))))).

Definition base_R : Poly5 :=
  PSub (PSub (PMul two px) (PMul (PMul three (PSq px)) py))
    (PMul (PCube px) pz).

Definition factor_p : Poly5 := PMul px (PSq py).
Definition factor_q : Poly5 := PMul (PMul (PSq px) py) pz.
Definition source_a : Poly5 := PAdd pa factor_p.
Definition source_b : Poly5 := PAdd pb factor_q.

(* The top degree-seven monomial of [base_P] cancels against
   [factor_p * factor_q].  Writing the result in expanded form makes the
   degree-six bound transparent. *)
Definition simpler_first : Poly5 :=
  PAdd (POpp (PMul pa pb))
  (PAdd (POpp (PMul pa factor_q))
  (PAdd (POpp (PMul pb factor_p))
  (PAdd (PMul three (PMul (PSq px) (PSq (PSq py))))
  (PAdd (PMul three (PMul (PMul (PSq px) (PSq py)) pz))
  (PAdd (PMul seven (PMul px (PCube py)))
  (PAdd (PMul three (PMul (PMul px py) pz))
  (PAdd (PMul four (PSq py)) pz))))))).

Record PolyMap5 : Type := poly_map5 {
  coord1 : Poly5;
  coord2 : Poly5;
  coord3 : Poly5;
  coord4 : Poly5;
  coord5 : Poly5
}.

Definition simpler_counterexample : PolyMap5 :=
  poly_map5
    simpler_first
    base_Q base_R source_a source_b.

Theorem simpler_counterexample_degree_profile :
  degree_bound (coord1 simpler_counterexample) = 6%nat /\
  degree_bound (coord2 simpler_counterexample) = 6%nat /\
  degree_bound (coord3 simpler_counterexample) = 4%nat /\
  degree_bound (coord4 simpler_counterexample) = 3%nat /\
  degree_bound (coord5 simpler_counterexample) = 4%nat.
Proof.
  repeat split; reflexivity.
Qed.

Definition poly_coordinate5 (f : PolyMap5) (i : Var5) : Poly5 :=
  match i with
  | VX => coord1 f
  | VY => coord2 f
  | VZ => coord3 f
  | VA => coord4 f
  | VB => coord5 f
  end.

Definition eval_map5 (f : PolyMap5) (p : Point5) : Point5 :=
  point5
    (eval_poly5 (coord1 f) p)
    (eval_poly5 (coord2 f) p)
    (eval_poly5 (coord3 f) p)
    (eval_poly5 (coord4 f) p)
    (eval_poly5 (coord5 f) p).

Definition det3m (M : Var5 -> Var5 -> Poly5)
    (r1 r2 r3 c1' c2' c3' : Var5) : Poly5 :=
  PAdd
    (PSub
      (PMul (M r1 c1')
        (PSub (PMul (M r2 c2') (M r3 c3'))
          (PMul (M r2 c3') (M r3 c2'))))
      (PMul (M r1 c2')
        (PSub (PMul (M r2 c1') (M r3 c3'))
          (PMul (M r2 c3') (M r3 c1')))))
    (PMul (M r1 c3')
      (PSub (PMul (M r2 c1') (M r3 c2'))
        (PMul (M r2 c2') (M r3 c1')))).

Definition det4m (M : Var5 -> Var5 -> Poly5)
    (r1 r2 r3 r4 c1' c2' c3' c4' : Var5) : Poly5 :=
  PSub
    (PAdd
      (PSub
        (PMul (M r1 c1') (det3m M r2 r3 r4 c2' c3' c4'))
        (PMul (M r1 c2') (det3m M r2 r3 r4 c1' c3' c4')))
      (PMul (M r1 c3') (det3m M r2 r3 r4 c1' c2' c4')))
    (PMul (M r1 c4') (det3m M r2 r3 r4 c1' c2' c3')).

Definition det5m (M : Var5 -> Var5 -> Poly5) : Poly5 :=
  PAdd
    (PSub
      (PAdd
        (PSub
          (PMul (M VX VX) (det4m M VY VZ VA VB VY VZ VA VB))
          (PMul (M VX VY) (det4m M VY VZ VA VB VX VZ VA VB)))
        (PMul (M VX VZ) (det4m M VY VZ VA VB VX VY VA VB)))
      (PMul (M VX VA) (det4m M VY VZ VA VB VX VY VZ VB)))
    (PMul (M VX VB) (det4m M VY VZ VA VB VX VY VZ VA)).

Definition jacobian_det5 (f : PolyMap5) : Poly5 :=
  det5m (fun i j => partial5 j (poly_coordinate5 f i)).

Lemma point5_ext (p q : Point5) :
  xcoord5 p = xcoord5 q -> ycoord5 p = ycoord5 q ->
  zcoord5 p = zcoord5 q -> acoord5 p = acoord5 q ->
  bcoord5 p = bcoord5 q -> p = q.
Proof.
  destruct p, q; cbn; intros; subst; reflexivity.
Qed.

(** Two points with different first coordinates are different. *)
Lemma point5_neq_x (p q : Point5) : xcoord5 p <> xcoord5 q -> p <> q.
Proof.
  intros hx h; apply hx; rewrite h; reflexivity.
Qed.

(** The source and target involutions of the equivariance below. *)
Definition flip5_source (p : Point5) : Point5 :=
  point5 (- xcoord5 p) (- ycoord5 p) (zcoord5 p) (- acoord5 p) (- bcoord5 p).

Definition flip5_target (p : Point5) : Point5 :=
  point5 (xcoord5 p) (- ycoord5 p) (- zcoord5 p) (- acoord5 p) (- bcoord5 p).

Definition collision0 : Point5 := point5 (-c1) c1 c5 c1 (-c5).
Definition collision1 : Point5 := point5 c0 (-c2) (-c16) c0 c0.
Definition collision_value : Point5 := point5 c0 (-c2) c0 c0 c0.

(** Unfold the polynomial syntax, its evaluators, and every named constant
    and point of this development, leaving only field arithmetic in [C]. *)
Ltac eval5_c :=
  cbv [eval_map5 jacobian_det5 det5m det4m det3m poly_coordinate5
       simpler_counterexample simpler_first
       base_P base_Q base_R base_u factor_p factor_q source_a source_b
       partial5 var5_eqb PSub PSq PCube eval_poly5 coordinate5
       one two three four seven px py pz pa pb
       coord1 coord2 coord3 coord4 coord5
       xcoord5 ycoord5 zcoord5 acoord5 bcoord5
       flip5_source flip5_target
       collision0 collision1 collision_value
       c0 c1 c2 c3 c4 c5 c7 c16].

Theorem simpler_first_stable_identity (point : Point5) :
  eval_poly5 simpler_first point =
  eval_poly5 (PSub base_P (PMul source_a source_b)) point.
Proof.
  destruct point as [x y z a b]; eval5_c; ring.
Qed.

Theorem jacobian_det5_is_minus_two (point : Point5) :
  eval_poly5 (jacobian_det5 simpler_counterexample) point = -c2.
Proof.
  destruct point as [x y z a b]; eval5_c; ring.
Qed.

(** **Equivariance.**  The triangular shears preserve the symmetry of the
    three-variable witness: negating [x, y, a, b] in the source negates every
    image coordinate except the first. *)
Theorem simpler_counterexample_equivariant (p : Point5) :
  eval_map5 simpler_counterexample (flip5_source p) =
  flip5_target (eval_map5 simpler_counterexample p).
Proof.
  destruct p as [x y z a b]; apply point5_ext; eval5_c; ring.
Qed.

Theorem collision0_value :
  eval_map5 simpler_counterexample collision0 = collision_value.
Proof.
  apply point5_ext; eval5_c; ring.
Qed.

Theorem collision1_value :
  eval_map5 simpler_counterexample collision1 = collision_value.
Proof.
  apply point5_ext; eval5_c; ring.
Qed.

Theorem collision_points_distinct : collision0 <> collision1.
Proof.
  apply point5_neq_x; re_neq.
Qed.

(** Mirroring the collision through the equivariance yields a second integral
    collision with no new polynomial evaluation. *)
Theorem mirrored_collision :
  eval_map5 simpler_counterexample (flip5_source collision0) =
  eval_map5 simpler_counterexample (flip5_source collision1).
Proof.
  rewrite !simpler_counterexample_equivariant,
    collision0_value, collision1_value.
  reflexivity.
Qed.

Definition PolynomialEq5 (p q : Poly5) : Prop :=
  forall point : Point5, eval_poly5 p point = eval_poly5 q point.

Definition HasNonzeroConstantJacobian5 (f : PolyMap5) : Prop :=
  exists c : C,
    c <> c0 /\ PolynomialEq5 (jacobian_det5 f) (PConst c).

Definition HasPolynomialInverse5 (f : PolyMap5) : Prop :=
  exists g : PolyMap5,
    (forall p : Point5, eval_map5 g (eval_map5 f p) = p) /\
    (forall p : Point5, eval_map5 f (eval_map5 g p) = p).

Definition JacobianConjectureInDimensionFiveOverC : Prop :=
  forall f : PolyMap5,
    HasNonzeroConstantJacobian5 f -> HasPolynomialInverse5 f.

Theorem simpler_counterexample_has_nonzero_constant_jacobian :
  HasNonzeroConstantJacobian5 simpler_counterexample.
Proof.
  exists (-c2).
  split.
  - re_neq.
  - intro p.
    cbn [eval_poly5].
    exact (jacobian_det5_is_minus_two p).
Qed.

Theorem simpler_counterexample_not_injective :
  ~ (forall p q : Point5,
       eval_map5 simpler_counterexample p =
       eval_map5 simpler_counterexample q -> p = q).
Proof.
  intro hinj.
  apply collision_points_distinct.
  apply hinj.
  rewrite collision0_value, collision1_value.
  reflexivity.
Qed.

Theorem simpler_counterexample_has_no_polynomial_inverse :
  ~ HasPolynomialInverse5 simpler_counterexample.
Proof.
  intros [g [hleft _]].
  apply collision_points_distinct.
  rewrite <- (hleft collision0), <- (hleft collision1).
  rewrite collision0_value, collision1_value.
  reflexivity.
Qed.

Theorem jacobian_conjecture_dimension_five_is_false :
  ~ JacobianConjectureInDimensionFiveOverC.
Proof.
  intro h.
  apply simpler_counterexample_has_no_polynomial_inverse.
  apply h.
  exact simpler_counterexample_has_nonzero_constant_jacobian.
Qed.

End JacobianSimplerCounterexample.
End LeanProofs.
