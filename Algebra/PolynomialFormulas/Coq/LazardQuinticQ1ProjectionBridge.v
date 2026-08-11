From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticFourier LazardQuinticProjection LazardQuinticQuadratic
  LazardQuinticQ1Branches.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Section-7 normalization bridge from the standard projection equations
    to Lazard's Q1 branches, followed by the concrete specialization to the
    fifth powers of the four nonzero Fourier sums. *)
Module PolynomialFormulasLazardQuinticQ1ProjectionBridge.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticFourier.
Import PolynomialFormulasLazardQuinticProjection.
Import PolynomialFormulasLazardQuinticQuadratic.
Import PolynomialFormulasLazardQuinticQ1Branches.
Local Open Scope ring_scope.

Section Bridge.

Variable F : fieldType.

Definition lazard_section7_twenty_five : F := 5%:R * 5%:R.

(** Standard projections have respective Section-7 scales
    [5,5,25/2,25/2].  We use [2 P / 25] for the last two normalized values,
    avoiding a nested division while retaining the exact scale theorem
    below. *)
Definition lazard_section7_H epsilon t u (source : 'I_4 -> F) : F :=
  lazard_standard_projections epsilon t u source p0 / 5%:R.

Definition lazard_section7_I epsilon t u (source : 'I_4 -> F) : F :=
  lazard_standard_projections epsilon t u source p1 / 5%:R.

Definition lazard_section7_J epsilon t u (source : 'I_4 -> F) : F :=
  (2%:R * lazard_standard_projections epsilon t u source p2) /
    lazard_section7_twenty_five.

Definition lazard_section7_K epsilon t u (source : 'I_4 -> F) : F :=
  (2%:R * lazard_standard_projections epsilon t u source p3) /
    lazard_section7_twenty_five.

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

Lemma lazard_q1_bridge_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma lazard_q1_bridge_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma lazard_q1_bridge_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma lazard_q1_bridge_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma lazard_q1_bridge_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma lazard_q1_bridge_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma lazard_q1_bridge_ring_theory :
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

Add Ring lazard_q1_bridge_ring : lazard_q1_bridge_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Lemma lazard_q1_bridge_two_natrE : (2%:R : F) = 1 + 1.
Proof. exact: (@natrD F 1 1). Qed.

Lemma lazard_q1_bridge_four_natrE : (4%:R : F) = 1 + 1 + 1 + 1.
Proof.
have h3 : (3%:R : F) = 1 + 1 + 1.
  rewrite -lazard_q1_bridge_two_natrE.
  exact: (@natrD F 2 1).
rewrite -h3.
exact: (@natrD F 3 1).
Qed.

Lemma lazard_q1_bridge_five_natrE :
  (5%:R : F) = 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -lazard_q1_bridge_four_natrE.
exact: (@natrD F 4 1).
Qed.

Lemma lazard_q1_bridge_expr2 (x : F) : x ^+ 2 = x * x.
Proof. by rewrite expr2. Qed.

(** Unlike the general [unitRingType] lemma [invrM], multiplication of
    inverses is unconditional in a field: the zero cases reduce on both
    sides, and the nonzero case is the usual unit calculation. *)
Lemma lazard_q1_bridge_invM (x y : F) :
  (x * y)^-1 = x^-1 * y^-1.
Proof.
case: (boolP (x == 0)) => [/eqP -> | x_neq0].
- by rewrite mul0r invr0 mul0r.
case: (boolP (y == 0)) => [/eqP -> | y_neq0].
- by rewrite mulr0 invr0 mulr0.
rewrite invrM ?unitfE //.
exact: mulrC.
Qed.

Ltac finish_lazard_q1_bridge_ring :=
  repeat first
    [ rewrite lazard_q1_bridge_two_natrE
    | rewrite lazard_q1_bridge_four_natrE
    | rewrite lazard_q1_bridge_five_natrE
    | rewrite lazard_q1_bridge_expr2
    | rewrite lazard_q1_bridge_ring_addE
    | rewrite lazard_q1_bridge_ring_mulE
    | rewrite lazard_q1_bridge_ring_subE
    | rewrite lazard_q1_bridge_ring_oppE
    | rewrite lazard_q1_bridge_ring_zeroE
    | rewrite lazard_q1_bridge_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

Lemma lazard_section7_H_scaled epsilon t u source
    (five_neq0 : (5%:R : F) != 0) :
  5%:R * lazard_section7_H epsilon t u source =
    lazard_standard_projections epsilon t u source p0.
Proof.
rewrite /lazard_section7_H [5%:R * _]mulrC divfK //.
Qed.

Lemma lazard_section7_I_scaled epsilon t u source
    (five_neq0 : (5%:R : F) != 0) :
  5%:R * lazard_section7_I epsilon t u source =
    lazard_standard_projections epsilon t u source p1.
Proof.
rewrite /lazard_section7_I [5%:R * _]mulrC divfK //.
Qed.

Lemma lazard_section7_twenty_five_neq0
    (five_neq0 : (5%:R : F) != 0) :
  lazard_section7_twenty_five != 0.
Proof.
rewrite /lazard_section7_twenty_five.
exact (mulf_neq0 five_neq0 five_neq0).
Qed.

Lemma lazard_section7_J_scaled epsilon t u source
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0) :
  (lazard_section7_twenty_five / 2%:R) *
      lazard_section7_J epsilon t u source =
    lazard_standard_projections epsilon t u source p2.
Proof.
have h2 := mulVf two_neq0.
have h5 := mulVf five_neq0.
rewrite /lazard_section7_J /lazard_section7_twenty_five
  !lazard_q1_bridge_invM.
transitivity
  (((2%:R : F)^-1 * 2%:R) *
    (((5%:R : F)^-1 * 5%:R) *
      ((5%:R : F)^-1 * 5%:R)) *
    lazard_standard_projections epsilon t u source p2).
- finish_lazard_q1_bridge_ring.
- rewrite h2 !h5 !mul1r.
  reflexivity.
Qed.

Lemma lazard_section7_K_scaled epsilon t u source
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0) :
  (lazard_section7_twenty_five / 2%:R) *
      lazard_section7_K epsilon t u source =
    lazard_standard_projections epsilon t u source p3.
Proof.
have h2 := mulVf two_neq0.
have h5 := mulVf five_neq0.
rewrite /lazard_section7_K /lazard_section7_twenty_five
  !lazard_q1_bridge_invM.
transitivity
  (((2%:R : F)^-1 * 2%:R) *
    (((5%:R : F)^-1 * 5%:R) *
      ((5%:R : F)^-1 * 5%:R)) *
    lazard_standard_projections epsilon t u source p3).
- finish_lazard_q1_bridge_ring.
- rewrite h2 !h5 !mul1r.
  reflexivity.
Qed.

(** Three scalar normalization identities used to identify Q1 with the
    standard recovery expression. *)
Lemma lazard_five_quarter_H_normalize (x : F)
    (five_neq0 : (5%:R : F) != 0) :
  ((5%:R : F) / (4%:R : F)) * (x / 5%:R) = x / 4%:R.
Proof.
transitivity
  (((5%:R : F)^-1 * 5%:R) * ((4%:R : F)^-1 * x)).
- finish_lazard_q1_bridge_ring.
- rewrite (mulVf five_neq0) mul1r.
  finish_lazard_q1_bridge_ring.
Qed.

Lemma lazard_five_quarter_I_normalize (x epsilon : F)
    (five_neq0 : (5%:R : F) != 0) :
  ((5%:R : F) / (4%:R : F)) * ((x / 5%:R) / epsilon) =
    x / (4%:R * epsilon).
Proof.
rewrite lazard_q1_bridge_invM.
transitivity
  (((5%:R : F)^-1 * 5%:R) *
    ((4%:R : F)^-1 * epsilon^-1 * x)).
- finish_lazard_q1_bridge_ring.
- rewrite (mulVf five_neq0) mul1r.
  finish_lazard_q1_bridge_ring.
Qed.

Lemma lazard_five_quarter_JK_normalize t u p2v p3v E
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0) :
  ((5%:R : F) / (4%:R : F)) *
      ((t * ((2%:R * p2v) / (5%:R * 5%:R)) +
        u * ((2%:R * p3v) / (5%:R * 5%:R))) / E) =
    (t * p2v + u * p3v) / (2%:R * (5%:R * E)).
Proof.
rewrite (@natrM F 2 2) !lazard_q1_bridge_invM.
transitivity
  ((((5%:R : F)^-1 * 5%:R) *
      ((2%:R : F)^-1 * 2%:R)) *
    ((2%:R : F)^-1 * (5%:R : F)^-1 * E^-1 *
      (t * p2v + u * p3v))).
- finish_lazard_q1_bridge_ring.
- rewrite (mulVf five_neq0) (mulVf two_neq0) !mul1r.
  finish_lazard_q1_bridge_ring.
Qed.

(** Base-branch Q1 is exactly the already proved standard recovery formula. *)
Theorem lazard_section7_q1_base epsilon t u E source
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (E_neq0 : E != 0)
    (hsum : t ^+ 2 + u ^+ 2 = 5%:R * E) :
  lazard_q1_branch
      (lazard_section7_H epsilon t u source)
      (lazard_section7_I epsilon t u source)
      (lazard_section7_J epsilon t u source)
      (lazard_section7_K epsilon t u source) E
      (LazardQuadraticTriple epsilon t u) LazardBranchBase = source p0.
Proof.
have standard_denominator_neq0 : t ^+ 2 + u ^+ 2 != 0.
  rewrite hsum.
  exact (mulf_neq0 five_neq0 E_neq0).
transitivity
  (lazard_standard_recover epsilon t u
    (lazard_standard_projections epsilon t u source)).
- rewrite /lazard_q1_branch /lazard_branch_triple /=
    /lazard_q1 /lazard_q1_inner
    /lazard_section7_H /lazard_section7_I
    /lazard_section7_J /lazard_section7_K
    /lazard_section7_twenty_five.
  transitivity
    (((5%:R : F) / (4%:R : F)) *
        (lazard_standard_projections epsilon t u source p0 / 5%:R) +
     ((5%:R : F) / (4%:R : F)) *
        ((lazard_standard_projections epsilon t u source p1 / 5%:R) /
          epsilon) +
     ((5%:R : F) / (4%:R : F)) *
        ((t * ((2%:R * lazard_standard_projections epsilon t u source p2) /
                (5%:R * 5%:R)) +
          u * ((2%:R * lazard_standard_projections epsilon t u source p3) /
                (5%:R * 5%:R))) / E)).
  + finish_lazard_q1_bridge_ring.
  + rewrite lazard_five_quarter_H_normalize //
      lazard_five_quarter_I_normalize //
      lazard_five_quarter_JK_normalize //.
    rewrite -hsum.
    reflexivity.
- exact: @lazard_standard_recover_projections F epsilon t u source
    two_neq0 epsilon_neq0 standard_denominator_neq0.
Qed.

(** Source permutations corresponding to the three non-base sign branches. *)
Definition lazard_negate_source (source : 'I_4 -> F) (i : 'I_4) : F :=
  nth 0 [:: source p2; source p3; source p0; source p1] i.

Definition lazard_rotate_source (source : 'I_4 -> F) (i : 'I_4) : F :=
  nth 0 [:: source p3; source p0; source p1; source p2] i.

Definition lazard_rotate_negate_source
    (source : 'I_4 -> F) (i : 'I_4) : F :=
  nth 0 [:: source p1; source p2; source p3; source p0] i.

Lemma lazard_negate_projection0 epsilon t u source :
  lazard_standard_projections epsilon (- t) (- u)
      (lazard_negate_source source) p0 =
    lazard_standard_projections epsilon t u source p0.
Proof.
rewrite !lazard_standard_projection0 /lazard_negate_source
  /p0 /p1 /p2 /p3 /=.
finish_lazard_q1_bridge_ring.
Qed.

Lemma lazard_negate_projection1 epsilon t u source :
  lazard_standard_projections epsilon (- t) (- u)
      (lazard_negate_source source) p1 =
    lazard_standard_projections epsilon t u source p1.
Proof.
rewrite !lazard_standard_projection1 /lazard_negate_source
  /p0 /p1 /p2 /p3 /=.
finish_lazard_q1_bridge_ring.
Qed.

Lemma lazard_negate_projection2 epsilon t u source :
  lazard_standard_projections epsilon (- t) (- u)
      (lazard_negate_source source) p2 =
    lazard_standard_projections epsilon t u source p2.
Proof.
rewrite !lazard_standard_projection2 /lazard_negate_source
  /p0 /p1 /p2 /p3 /=.
finish_lazard_q1_bridge_ring.
Qed.

Lemma lazard_negate_projection3 epsilon t u source :
  lazard_standard_projections epsilon (- t) (- u)
      (lazard_negate_source source) p3 =
    lazard_standard_projections epsilon t u source p3.
Proof.
rewrite !lazard_standard_projection3 /lazard_negate_source
  /p0 /p1 /p2 /p3 /=.
finish_lazard_q1_bridge_ring.
Qed.

Lemma lazard_rotate_projection0 epsilon t u source :
  lazard_standard_projections (- epsilon) u (- t)
      (lazard_rotate_source source) p0 =
    lazard_standard_projections epsilon t u source p0.
Proof.
rewrite !lazard_standard_projection0 /lazard_rotate_source
  /p0 /p1 /p2 /p3 /=.
finish_lazard_q1_bridge_ring.
Qed.

Lemma lazard_rotate_projection1 epsilon t u source :
  lazard_standard_projections (- epsilon) u (- t)
      (lazard_rotate_source source) p1 =
    lazard_standard_projections epsilon t u source p1.
Proof.
rewrite !lazard_standard_projection1 /lazard_rotate_source
  /p0 /p1 /p2 /p3 /=.
finish_lazard_q1_bridge_ring.
Qed.

Lemma lazard_rotate_projection2 epsilon t u source :
  lazard_standard_projections (- epsilon) u (- t)
      (lazard_rotate_source source) p2 =
    lazard_standard_projections epsilon t u source p2.
Proof.
rewrite !lazard_standard_projection2 /lazard_rotate_source
  /p0 /p1 /p2 /p3 /=.
finish_lazard_q1_bridge_ring.
Qed.

Lemma lazard_rotate_projection3 epsilon t u source :
  lazard_standard_projections (- epsilon) u (- t)
      (lazard_rotate_source source) p3 =
    lazard_standard_projections epsilon t u source p3.
Proof.
rewrite !lazard_standard_projection3 /lazard_rotate_source
  /p0 /p1 /p2 /p3 /=.
finish_lazard_q1_bridge_ring.
Qed.

Lemma lazard_rotate_negate_projection0 epsilon t u source :
  lazard_standard_projections (- epsilon) (- u) t
      (lazard_rotate_negate_source source) p0 =
    lazard_standard_projections epsilon t u source p0.
Proof.
rewrite !lazard_standard_projection0 /lazard_rotate_negate_source
  /p0 /p1 /p2 /p3 /=.
finish_lazard_q1_bridge_ring.
Qed.

Lemma lazard_rotate_negate_projection1 epsilon t u source :
  lazard_standard_projections (- epsilon) (- u) t
      (lazard_rotate_negate_source source) p1 =
    lazard_standard_projections epsilon t u source p1.
Proof.
rewrite !lazard_standard_projection1 /lazard_rotate_negate_source
  /p0 /p1 /p2 /p3 /=.
finish_lazard_q1_bridge_ring.
Qed.

Lemma lazard_rotate_negate_projection2 epsilon t u source :
  lazard_standard_projections (- epsilon) (- u) t
      (lazard_rotate_negate_source source) p2 =
    lazard_standard_projections epsilon t u source p2.
Proof.
rewrite !lazard_standard_projection2 /lazard_rotate_negate_source
  /p0 /p1 /p2 /p3 /=.
finish_lazard_q1_bridge_ring.
Qed.

Lemma lazard_rotate_negate_projection3 epsilon t u source :
  lazard_standard_projections (- epsilon) (- u) t
      (lazard_rotate_negate_source source) p3 =
    lazard_standard_projections epsilon t u source p3.
Proof.
rewrite !lazard_standard_projection3 /lazard_rotate_negate_source
  /p0 /p1 /p2 /p3 /=.
finish_lazard_q1_bridge_ring.
Qed.

(** The remaining three branch values recover the corresponding permuted
    source coordinates. *)
Theorem lazard_section7_q1_negate epsilon t u E source
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (E_neq0 : E != 0)
    (hsum : t ^+ 2 + u ^+ 2 = 5%:R * E) :
  lazard_q1_branch
      (lazard_section7_H epsilon t u source)
      (lazard_section7_I epsilon t u source)
      (lazard_section7_J epsilon t u source)
      (lazard_section7_K epsilon t u source) E
      (LazardQuadraticTriple epsilon t u) LazardBranchNegateTU = source p2.
Proof.
have h := @lazard_section7_q1_base epsilon (- t) (- u) E
  (lazard_negate_source source) two_neq0 five_neq0 epsilon_neq0 E_neq0.
have hsum' : (- t) ^+ 2 + (- u) ^+ 2 = 5%:R * E.
  by rewrite !sqrrN.
move: (h hsum').
rewrite /lazard_section7_H /lazard_section7_I
  /lazard_section7_J /lazard_section7_K
  lazard_negate_projection0 lazard_negate_projection1
  lazard_negate_projection2 lazard_negate_projection3
  /lazard_q1_branch /lazard_branch_triple /=
  /lazard_negate_source /p0 /p2 /=.
by [].
Qed.

Theorem lazard_section7_q1_rotate epsilon t u E source
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (E_neq0 : E != 0)
    (hsum : t ^+ 2 + u ^+ 2 = 5%:R * E) :
  lazard_q1_branch
      (lazard_section7_H epsilon t u source)
      (lazard_section7_I epsilon t u source)
      (lazard_section7_J epsilon t u source)
      (lazard_section7_K epsilon t u source) E
      (LazardQuadraticTriple epsilon t u) LazardBranchRotate = source p3.
Proof.
have epsilon_neg_neq0 : - epsilon != 0 by rewrite oppr_eq0.
have h := @lazard_section7_q1_base (- epsilon) u (- t) E
  (lazard_rotate_source source) two_neq0 five_neq0
  epsilon_neg_neq0 E_neq0.
have hsum' : u ^+ 2 + (- t) ^+ 2 = 5%:R * E.
  by rewrite sqrrN addrC hsum.
move: (h hsum').
rewrite /lazard_section7_H /lazard_section7_I
  /lazard_section7_J /lazard_section7_K
  lazard_rotate_projection0 lazard_rotate_projection1
  lazard_rotate_projection2 lazard_rotate_projection3
  /lazard_q1_branch /lazard_branch_triple /=
  /lazard_rotate_source /p0 /p3 /=.
by [].
Qed.

Theorem lazard_section7_q1_rotate_negate epsilon t u E source
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (E_neq0 : E != 0)
    (hsum : t ^+ 2 + u ^+ 2 = 5%:R * E) :
  lazard_q1_branch
      (lazard_section7_H epsilon t u source)
      (lazard_section7_I epsilon t u source)
      (lazard_section7_J epsilon t u source)
      (lazard_section7_K epsilon t u source) E
      (LazardQuadraticTriple epsilon t u) LazardBranchRotateNegate = source p1.
Proof.
have epsilon_neg_neq0 : - epsilon != 0 by rewrite oppr_eq0.
have h := @lazard_section7_q1_base (- epsilon) (- u) t E
  (lazard_rotate_negate_source source) two_neq0 five_neq0
  epsilon_neg_neq0 E_neq0.
have hsum' : (- u) ^+ 2 + t ^+ 2 = 5%:R * E.
  by rewrite sqrrN addrC hsum.
move: (h hsum').
rewrite /lazard_section7_H /lazard_section7_I
  /lazard_section7_J /lazard_section7_K
  lazard_rotate_negate_projection0 lazard_rotate_negate_projection1
  lazard_rotate_negate_projection2 lazard_rotate_negate_projection3
  /lazard_q1_branch /lazard_branch_triple /=
  /lazard_rotate_negate_source /p0 /p1 /=.
by [].
Qed.

(** The fifth-power source in Lazard's orbit order [P1^5,P2^5,P4^5,P3^5]. *)
Definition lazard_fourier_fifth_power_source
    (omega : F) (roots : 5.-tuple F) (i : 'I_4) : F :=
  nth 0
    [:: lazard_fourier_sum omega roots o1 ^+ 5;
        lazard_fourier_sum omega roots o2 ^+ 5;
        lazard_fourier_sum omega roots o4 ^+ 5;
        lazard_fourier_sum omega roots o3 ^+ 5] i.

Definition lazard_fourier_q1_branch epsilon t u E omega roots branch : F :=
  lazard_q1_branch
    (lazard_section7_H epsilon t u
      (lazard_fourier_fifth_power_source omega roots))
    (lazard_section7_I epsilon t u
      (lazard_fourier_fifth_power_source omega roots))
    (lazard_section7_J epsilon t u
      (lazard_fourier_fifth_power_source omega roots))
    (lazard_section7_K epsilon t u
      (lazard_fourier_fifth_power_source omega roots)) E
    (LazardQuadraticTriple epsilon t u) branch.

Theorem lazard_fourier_q1_base epsilon t u E omega roots
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0) (E_neq0 : E != 0)
    (hsum : t ^+ 2 + u ^+ 2 = 5%:R * E) :
  lazard_fourier_q1_branch epsilon t u E omega roots LazardBranchBase =
    lazard_fourier_sum omega roots o1 ^+ 5.
Proof.
rewrite /lazard_fourier_q1_branch.
rewrite (@lazard_section7_q1_base epsilon t u E
  (lazard_fourier_fifth_power_source omega roots)
  two_neq0 five_neq0 epsilon_neq0 E_neq0 hsum).
by rewrite /lazard_fourier_fifth_power_source /p0 /=.
Qed.

Theorem lazard_fourier_q1_rotate_negate epsilon t u E omega roots
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0) (E_neq0 : E != 0)
    (hsum : t ^+ 2 + u ^+ 2 = 5%:R * E) :
  lazard_fourier_q1_branch epsilon t u E omega roots
      LazardBranchRotateNegate = lazard_fourier_sum omega roots o2 ^+ 5.
Proof.
rewrite /lazard_fourier_q1_branch.
rewrite (@lazard_section7_q1_rotate_negate epsilon t u E
  (lazard_fourier_fifth_power_source omega roots)
  two_neq0 five_neq0 epsilon_neq0 E_neq0 hsum).
by rewrite /lazard_fourier_fifth_power_source /p1 /=.
Qed.

Theorem lazard_fourier_q1_negate epsilon t u E omega roots
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0) (E_neq0 : E != 0)
    (hsum : t ^+ 2 + u ^+ 2 = 5%:R * E) :
  lazard_fourier_q1_branch epsilon t u E omega roots LazardBranchNegateTU =
    lazard_fourier_sum omega roots o4 ^+ 5.
Proof.
rewrite /lazard_fourier_q1_branch.
rewrite (@lazard_section7_q1_negate epsilon t u E
  (lazard_fourier_fifth_power_source omega roots)
  two_neq0 five_neq0 epsilon_neq0 E_neq0 hsum).
by rewrite /lazard_fourier_fifth_power_source /p2 /=.
Qed.

Theorem lazard_fourier_q1_rotate epsilon t u E omega roots
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0) (E_neq0 : E != 0)
    (hsum : t ^+ 2 + u ^+ 2 = 5%:R * E) :
  lazard_fourier_q1_branch epsilon t u E omega roots LazardBranchRotate =
    lazard_fourier_sum omega roots o3 ^+ 5.
Proof.
rewrite /lazard_fourier_q1_branch.
rewrite (@lazard_section7_q1_rotate epsilon t u E
  (lazard_fourier_fifth_power_source omega roots)
  two_neq0 five_neq0 epsilon_neq0 E_neq0 hsum).
by rewrite /lazard_fourier_fifth_power_source /p3 /=.
Qed.

(** Any nonzero one of the four Fourier components therefore supplies a
    nonzero coherent Q1 branch. *)
Theorem lazard_fourier_nonzero_gives_q1_branch epsilon t u E omega roots
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0) (E_neq0 : E != 0)
    (hsum : t ^+ 2 + u ^+ 2 = 5%:R * E)
    (hcomponent :
      lazard_fourier_sum omega roots o1 != 0 \/
      lazard_fourier_sum omega roots o2 != 0 \/
      lazard_fourier_sum omega roots o4 != 0 \/
      lazard_fourier_sum omega roots o3 != 0) :
  exists branch : lazard_sign_branch,
    lazard_fourier_q1_branch epsilon t u E omega roots branch != 0.
Proof.
destruct hcomponent as [h1 | [h2 | [h4 | h3]]].
- exists LazardBranchBase.
  rewrite lazard_fourier_q1_base //.
  exact: expf_neq0 5 h1.
- exists LazardBranchRotateNegate.
  rewrite lazard_fourier_q1_rotate_negate //.
  exact: expf_neq0 5 h2.
- exists LazardBranchNegateTU.
  rewrite lazard_fourier_q1_negate //.
  exact: expf_neq0 5 h4.
- exists LazardBranchRotate.
  rewrite lazard_fourier_q1_rotate //.
  exact: expf_neq0 5 h3.
Qed.

End Bridge.

End PolynomialFormulasLazardQuinticQ1ProjectionBridge.
