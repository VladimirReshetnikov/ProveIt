From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import CubicField.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * The literal root resolvents in Lazard's cubic discussion

    For a labelled root triple of [X^3 + p X + q], let

      [V = (x0-x1)(x1-x2)(x2-x0)] and [Delta = 4 p^3 + 27 q^2].

    The exact Vieta relations imply [V^2 = -Delta].  A genuine primitive
    cube root [j] satisfies [(j-j^2)^2 = -3], so the modified invariant
    [(j-j^2)V] has square [3 Delta].  This file derives both facts and then
    proves the actual two-factor polynomial and evaluation identities for
    [X^2 + Delta] and [X^2 - 3 Delta].  No resolvent identity is supplied as
    a certificate. *)
Module PolynomialFormulasLazardCubicRootResolvent.

Import GRing.Theory.
Local Open Scope ring_scope.

Module CF := PolynomialFormulasCubicField.

Section CubicRootResolvent.

Variable F : fieldType.

Record depressed_cubic_vieta_data
    (p q x0 x1 x2 : F) : Prop := {
  cubic_vieta_sum_zero : x0 + x1 + x2 = 0;
  cubic_vieta_pair_sum : x0 * x1 + x0 * x2 + x1 * x2 = p;
  cubic_vieta_product : x0 * x1 * x2 = - q
}.

Definition cubic_discriminant (p q : F) : F :=
  4%:R * p ^+ 3 + 27%:R * q ^+ 2.

Definition cubic_vandermonde (x0 x1 x2 : F) : F :=
  (x0 - x1) * (x1 - x2) * (x2 - x0).

Definition vandermonde_resolvent (p q : F) : {poly F} :=
  'X^2 + (cubic_discriminant p q)%:P.

Definition modified_invariant (j x0 x1 x2 : F) : F :=
  (j - j ^+ 2) * cubic_vandermonde x0 x1 x2.

Definition modified_resolvent (p q : F) : {poly F} :=
  'X^2 - (3%:R * cubic_discriminant p q)%:P.

(** Local bridge from MathComp's packed operations to Stdlib [ring]. *)
Let ring_carrier : Type := F.
Local Definition ring_zero : ring_carrier := @GRing.zero F.
Local Definition ring_one : ring_carrier := @GRing.one F.
Local Definition ring_add : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.add F.
Local Definition ring_mul : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.mul F.
Local Definition ring_sub : ring_carrier -> ring_carrier -> ring_carrier :=
  fun x y => x - y.
Local Definition ring_opp : ring_carrier -> ring_carrier := @GRing.opp F.
Local Definition ring_eq : ring_carrier -> ring_carrier -> Prop :=
  @eq ring_carrier.

Lemma cubic_resolvent_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma cubic_resolvent_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma cubic_resolvent_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma cubic_resolvent_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma cubic_resolvent_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma cubic_resolvent_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma cubic_resolvent_ring_theory :
  @ring_theory ring_carrier ring_zero ring_one ring_add ring_mul
    ring_sub ring_opp ring_eq.
Proof.
constructor; unfold ring_zero, ring_one, ring_add, ring_mul, ring_sub,
  ring_opp, ring_eq; intros.
- exact: add0r.
- exact: addrC.
- exact: addrA.
- exact: mul1r.
- exact: mulrC.
- exact: mulrA.
- exact: mulrDl.
- reflexivity.
- exact: addrN.
Qed.

Add Ring cubic_root_resolvent_ring : cubic_resolvent_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Lemma cubic_resolvent_three_natrE : (3%:R : F) = 1 + 1 + 1.
Proof.
have h2 : (2%:R : F) = 1 + 1 := @natrD F 1 1.
rewrite -h2.
exact: (@natrD F 2 1).
Qed.

Lemma cubic_resolvent_four_natrE : (4%:R : F) = 1 + 1 + 1 + 1.
Proof.
rewrite -cubic_resolvent_three_natrE.
exact: (@natrD F 3 1).
Qed.

Lemma cubic_resolvent_twenty_seven_natrE :
    (27%:R : F) =
      (1 + 1 + 1) * (1 + 1 + 1) * (1 + 1 + 1).
Proof.
have h9 : (9%:R : F) = 3%:R * 3%:R := @natrM F 3 3.
have h27 : (27%:R : F) = 3%:R * 9%:R := @natrM F 3 9.
rewrite h27 h9 !cubic_resolvent_three_natrE.
exact: mulrA _ _ _.
Qed.

Lemma cubic_resolvent_expr2 (x : F) : x ^+ 2 = x * x.
Proof. by rewrite expr2. Qed.

Lemma cubic_resolvent_expr3 (x : F) : x ^+ 3 = x * x * x.
Proof. by rewrite exprSr expr2. Qed.

Ltac finish_cubic_root_resolvent_ring :=
  repeat first
    [ rewrite cubic_resolvent_three_natrE
    | rewrite cubic_resolvent_four_natrE
    | rewrite cubic_resolvent_twenty_seven_natrE
    | rewrite cubic_resolvent_expr2
    | rewrite cubic_resolvent_expr3
    | rewrite cubic_resolvent_ring_addE
    | rewrite cubic_resolvent_ring_mulE
    | rewrite cubic_resolvent_ring_subE
    | rewrite cubic_resolvent_ring_oppE
    | rewrite cubic_resolvent_ring_zeroE
    | rewrite cubic_resolvent_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

(** The Vieta record also proves that its entries are the three labelled
    roots, via the exact linear factorization. *)
Lemma depressed_cubic_vieta_factorization p q x0 x1 x2 y
    (h : depressed_cubic_vieta_data p q x0 x1 x2) :
  CF.depressed_cubic_value p q y =
    (y - x0) * (y - x1) * (y - x2).
Proof.
exact: CF.depressed_cubic_factorization_of_vieta
  (cubic_vieta_sum_zero h) (cubic_vieta_pair_sum h)
  (cubic_vieta_product h).
Qed.

(** Direct derivation of the Vandermonde-square/discriminant identity. *)
Lemma cubic_vandermonde_square p q x0 x1 x2
    (h : depressed_cubic_vieta_data p q x0 x1 x2) :
  cubic_vandermonde x0 x1 x2 ^+ 2 = - cubic_discriminant p q.
Proof.
have hx2 : x2 = - (x0 + x1).
  apply: (addrI (x0 + x1)).
  by rewrite (cubic_vieta_sum_zero h) addrN.
have hp : p = x0 * x1 + x0 * x2 + x1 * x2 :=
  esym (cubic_vieta_pair_sum h).
have hq : q = - (x0 * x1 * x2).
  apply: oppr_inj.
  rewrite opprK.
  exact: esym (cubic_vieta_product h).
rewrite /cubic_vandermonde /cubic_discriminant hp hq hx2.
finish_cubic_root_resolvent_ring.
Qed.

(** A genuine primitive cube root supplies the exact scalar [-3].  The
    explicit nonvanishing of three records the corrected scope of the
    surrounding Cardano formula. *)
Lemma primitive_cube_root_difference_square j
    (three_neq0 : (3%:R : F) != 0)
    (j_primitive : 3.-primitive_root j) :
  (j - j ^+ 2) ^+ 2 = - (3%:R : F).
Proof.
have hj : j ^+ 2 + j + 1 = 0 :=
  CF.primitive_cube_root_quadratic j_primitive.
transitivity
  (- 3%:R +
    (j ^+ 2 - 3%:R * j + 3%:R) * (j ^+ 2 + j + 1)).
- finish_cubic_root_resolvent_ring.
- by rewrite hj mulr0 addr0.
Qed.

Lemma modified_invariant_square p q x0 x1 x2 j
    (three_neq0 : (3%:R : F) != 0)
    (j_primitive : 3.-primitive_root j)
    (h : depressed_cubic_vieta_data p q x0 x1 x2) :
  modified_invariant j x0 x1 x2 ^+ 2 =
    3%:R * cubic_discriminant p q.
Proof.
rewrite /modified_invariant exprMn
  (primitive_cube_root_difference_square three_neq0 j_primitive)
  (cubic_vandermonde_square h).
finish_cubic_root_resolvent_ring.
Qed.

(** Actual polynomial identity [X^2 + Delta = (X-V)(X+V)]. *)
Lemma vandermonde_resolvent_factorization p q x0 x1 x2
    (h : depressed_cubic_vieta_data p q x0 x1 x2) :
  vandermonde_resolvent p q =
    ('X - (cubic_vandermonde x0 x1 x2)%:P) *
      ('X + (cubic_vandermonde x0 x1 x2)%:P).
Proof.
rewrite /vandermonde_resolvent -subr_sqr -polyC_exp
  (cubic_vandermonde_square h) polyCN.
change ('X^2 + (cubic_discriminant p q)%:P =
  'X^2 + - (- (cubic_discriminant p q)%:P)).
by rewrite opprK.
Qed.

Lemma vandermonde_resolvent_horner p q x0 x1 x2 y
    (h : depressed_cubic_vieta_data p q x0 x1 x2) :
  (vandermonde_resolvent p q).[y] =
    (y - cubic_vandermonde x0 x1 x2) *
      (y + cubic_vandermonde x0 x1 x2).
Proof.
rewrite (vandermonde_resolvent_factorization h)
  !hornerM !hornerD !hornerN !hornerX !hornerC.
reflexivity.
Qed.

Lemma vandermonde_resolvent_signed_roots p q x0 x1 x2
    (h : depressed_cubic_vieta_data p q x0 x1 x2) :
  root (vandermonde_resolvent p q) (cubic_vandermonde x0 x1 x2) /\
  root (vandermonde_resolvent p q) (- cubic_vandermonde x0 x1 x2).
Proof.
split; rewrite rootE.
- rewrite (vandermonde_resolvent_horner
    (p := p) (q := q) (x0 := x0) (x1 := x1) (x2 := x2)
    (cubic_vandermonde x0 x1 x2) h).
  apply/eqP; finish_cubic_root_resolvent_ring.
- rewrite (vandermonde_resolvent_horner
    (p := p) (q := q) (x0 := x0) (x1 := x1) (x2 := x2)
    (- cubic_vandermonde x0 x1 x2) h).
  apply/eqP; finish_cubic_root_resolvent_ring.
Qed.

(** Actual polynomial identity [X^2 - 3 Delta = (X-W)(X+W)]. *)
Lemma modified_resolvent_factorization p q x0 x1 x2 j
    (three_neq0 : (3%:R : F) != 0)
    (j_primitive : 3.-primitive_root j)
    (h : depressed_cubic_vieta_data p q x0 x1 x2) :
  modified_resolvent p q =
    ('X - (modified_invariant j x0 x1 x2)%:P) *
      ('X + (modified_invariant j x0 x1 x2)%:P).
Proof.
rewrite /modified_resolvent -subr_sqr -polyC_exp
  (modified_invariant_square three_neq0 j_primitive h).
reflexivity.
Qed.

Lemma modified_resolvent_horner p q x0 x1 x2 j y
    (three_neq0 : (3%:R : F) != 0)
    (j_primitive : 3.-primitive_root j)
    (h : depressed_cubic_vieta_data p q x0 x1 x2) :
  (modified_resolvent p q).[y] =
    (y - modified_invariant j x0 x1 x2) *
      (y + modified_invariant j x0 x1 x2).
Proof.
rewrite (modified_resolvent_factorization three_neq0 j_primitive h)
  !hornerM !hornerD !hornerN !hornerX !hornerC.
reflexivity.
Qed.

Lemma modified_resolvent_signed_roots p q x0 x1 x2 j
    (three_neq0 : (3%:R : F) != 0)
    (j_primitive : 3.-primitive_root j)
    (h : depressed_cubic_vieta_data p q x0 x1 x2) :
  root (modified_resolvent p q) (modified_invariant j x0 x1 x2) /\
  root (modified_resolvent p q) (- modified_invariant j x0 x1 x2).
Proof.
split; rewrite rootE.
- rewrite (modified_resolvent_horner
    (p := p) (q := q) (x0 := x0) (x1 := x1) (x2 := x2) (j := j)
    (modified_invariant j x0 x1 x2) three_neq0 j_primitive h).
  apply/eqP; finish_cubic_root_resolvent_ring.
- rewrite (modified_resolvent_horner
    (p := p) (q := q) (x0 := x0) (x1 := x1) (x2 := x2) (j := j)
    (- modified_invariant j x0 x1 x2) three_neq0 j_primitive h).
  apply/eqP; finish_cubic_root_resolvent_ring.
Qed.

Lemma cubic_vandermonde_swap_last x0 x1 x2 :
  cubic_vandermonde x0 x2 x1 = - cubic_vandermonde x0 x1 x2.
Proof.
rewrite /cubic_vandermonde.
finish_cubic_root_resolvent_ring.
Qed.

Lemma primitive_cube_root_difference_square_conjugate (j : F)
    (j_primitive : 3.-primitive_root j) :
  j ^+ 2 - (j ^+ 2) ^+ 2 = - (j - j ^+ 2).
Proof.
have hj : j ^+ 2 + j + 1 = 0 :=
  CF.primitive_cube_root_quadratic j_primitive.
transitivity
  (- (j - j ^+ 2) - j * (j - 1) * (j ^+ 2 + j + 1)).
- finish_cubic_root_resolvent_ring.
- by rewrite hj mulr0 subr0.
Qed.

(** Simultaneously replacing [j] by [j^2] and swapping [x1,x2] fixes the
    modified invariant. *)
Lemma modified_invariant_simultaneous_action j x0 x1 x2
    (three_neq0 : (3%:R : F) != 0)
    (j_primitive : 3.-primitive_root j) :
  modified_invariant (j ^+ 2) x0 x2 x1 =
    modified_invariant j x0 x1 x2.
Proof.
rewrite /modified_invariant
  (primitive_cube_root_difference_square_conjugate j_primitive)
  cubic_vandermonde_swap_last.
finish_cubic_root_resolvent_ring.
Qed.

(** Paper-facing aggregate: both literal resolvents and the modified
    invariance are derived from Vieta data and primitivity. *)
Theorem literal_cubic_root_resolvent_bridge p q x0 x1 x2 j
    (three_neq0 : (3%:R : F) != 0)
    (j_primitive : 3.-primitive_root j)
    (h : depressed_cubic_vieta_data p q x0 x1 x2) :
  cubic_vandermonde x0 x1 x2 ^+ 2 = - cubic_discriminant p q /\
  modified_invariant j x0 x1 x2 ^+ 2 =
    3%:R * cubic_discriminant p q /\
  vandermonde_resolvent p q =
    ('X - (cubic_vandermonde x0 x1 x2)%:P) *
      ('X + (cubic_vandermonde x0 x1 x2)%:P) /\
  modified_resolvent p q =
    ('X - (modified_invariant j x0 x1 x2)%:P) *
      ('X + (modified_invariant j x0 x1 x2)%:P) /\
  modified_invariant (j ^+ 2) x0 x2 x1 =
    modified_invariant j x0 x1 x2.
Proof.
repeat split.
- exact: cubic_vandermonde_square h.
- exact: modified_invariant_square three_neq0 j_primitive h.
- exact: vandermonde_resolvent_factorization h.
- exact: modified_resolvent_factorization three_neq0 j_primitive h.
- exact: modified_invariant_simultaneous_action three_neq0 j_primitive.
Qed.

Print Assumptions cubic_vandermonde_square.
Print Assumptions primitive_cube_root_difference_square.
Print Assumptions vandermonde_resolvent_factorization.
Print Assumptions modified_resolvent_factorization.
Print Assumptions modified_invariant_simultaneous_action.
Print Assumptions literal_cubic_root_resolvent_bridge.

End CubicRootResolvent.

End PolynomialFormulasLazardCubicRootResolvent.
