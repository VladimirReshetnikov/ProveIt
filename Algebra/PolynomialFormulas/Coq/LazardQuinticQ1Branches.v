From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import
  LazardQuinticProjection LazardQuinticQuadratic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The four coherent values of Lazard's first fifth-root radicand Q1.
    This layer is abstract in H/I/J/K and proves that the four sign branches
    cannot all vanish when the coefficient tuple and all relevant
    denominators are nondegenerate. *)
Module PolynomialFormulasLazardQuinticQ1Branches.

Import GRing.Theory.
Import PolynomialFormulasLazardQuinticProjection.
Import PolynomialFormulasLazardQuinticQuadratic.
Local Open Scope ring_scope.

Section Q1Branches.

Variable F : fieldType.

Definition lazard_q1_inner (H I J K E : F)
    (v : lazard_quadratic_triple F) : F :=
  H + I / lazard_epsilon v +
    (lazard_t v * J + lazard_u v * K) / E.

Definition lazard_q1 (H I J K E : F)
    (v : lazard_quadratic_triple F) : F :=
  ((5%:R : F) / (4%:R : F)) * lazard_q1_inner H I J K E v.

Definition lazard_q1_branch (H I J K E : F)
    (v : lazard_quadratic_triple F) (branch : lazard_sign_branch) : F :=
  lazard_q1 H I J K E (lazard_branch_triple v branch).

(** The coefficient common to each branch-pair sum and difference. *)
Definition lazard_q1_pair_scale : F :=
  2%:R * ((5%:R : F) / (4%:R : F)).

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

Lemma lazard_q1_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma lazard_q1_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma lazard_q1_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma lazard_q1_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma lazard_q1_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma lazard_q1_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma lazard_q1_ring_theory :
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

Add Ring lazard_q1_ring : lazard_q1_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Lemma lazard_q1_two_natrE : (2%:R : F) = 1 + 1.
Proof. exact: (@natrD F 1 1). Qed.

Lemma lazard_q1_four_natrE : (4%:R : F) = 1 + 1 + 1 + 1.
Proof.
have h3 : (3%:R : F) = 1 + 1 + 1.
  rewrite -lazard_q1_two_natrE.
  exact: (@natrD F 2 1).
rewrite -h3.
exact: (@natrD F 3 1).
Qed.

Lemma lazard_q1_five_natrE :
  (5%:R : F) = 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -lazard_q1_four_natrE.
exact: (@natrD F 4 1).
Qed.

Lemma lazard_q1_expr2 (x : F) : x ^+ 2 = x * x.
Proof. by rewrite expr2. Qed.

Ltac finish_lazard_q1_ring :=
  repeat first
    [ rewrite lazard_q1_two_natrE
    | rewrite lazard_q1_four_natrE
    | rewrite lazard_q1_five_natrE
    | rewrite lazard_q1_expr2
    | rewrite lazard_q1_ring_addE
    | rewrite lazard_q1_ring_mulE
    | rewrite lazard_q1_ring_subE
    | rewrite lazard_q1_ring_oppE
    | rewrite lazard_q1_ring_zeroE
    | rewrite lazard_q1_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

(** The base and simultaneous-negation branches have the same H/I part
    and opposite J/K parts. *)
Theorem lazard_q1_base_negate_sum H I J K E v :
  lazard_q1_branch H I J K E v LazardBranchBase +
      lazard_q1_branch H I J K E v LazardBranchNegateTU =
    lazard_q1_pair_scale * (H + I / lazard_epsilon v).
Proof.
rewrite /lazard_q1_branch /lazard_q1 /lazard_q1_inner
  /lazard_q1_pair_scale /lazard_branch_triple /=.
finish_lazard_q1_ring.
Qed.

Theorem lazard_q1_base_negate_difference H I J K E v :
  lazard_q1_branch H I J K E v LazardBranchBase -
      lazard_q1_branch H I J K E v LazardBranchNegateTU =
    lazard_q1_pair_scale *
      ((lazard_t v * J + lazard_u v * K) / E).
Proof.
rewrite /lazard_q1_branch /lazard_q1 /lazard_q1_inner
  /lazard_q1_pair_scale /lazard_branch_triple /=.
finish_lazard_q1_ring.
Qed.

(** Changing epsilon's sign exchanges the square branches; the rotated
    pair has opposite I parts and opposite rotated J/K parts. *)
Theorem lazard_q1_rotate_pair_sum H I J K E v :
  lazard_q1_branch H I J K E v LazardBranchRotate +
      lazard_q1_branch H I J K E v LazardBranchRotateNegate =
    lazard_q1_pair_scale * (H - I / lazard_epsilon v).
Proof.
rewrite /lazard_q1_branch /lazard_q1 /lazard_q1_inner
  /lazard_q1_pair_scale /lazard_branch_triple /=.
rewrite !invrN !mulrN.
finish_lazard_q1_ring.
Qed.

Theorem lazard_q1_rotate_pair_difference H I J K E v :
  lazard_q1_branch H I J K E v LazardBranchRotate -
      lazard_q1_branch H I J K E v LazardBranchRotateNegate =
    lazard_q1_pair_scale *
      ((lazard_u v * J - lazard_t v * K) / E).
Proof.
rewrite /lazard_q1_branch /lazard_q1 /lazard_q1_inner
  /lazard_q1_pair_scale /lazard_branch_triple /=.
rewrite !invrN !mulrN.
finish_lazard_q1_ring.
Qed.

(** Under characteristic not two, the raw pair scale is the conventional
    [5/2] coefficient. *)
Theorem lazard_q1_pair_scaleE
    (two_neq0 : (2%:R : F) != 0) :
  lazard_q1_pair_scale = (5%:R : F) / (2%:R : F).
Proof.
have four_neq0 := lazard_projection_four_neq0 two_neq0.
apply: (mulfI four_neq0).
transitivity
  ((((5%:R : F) / (4%:R : F)) * (4%:R : F)) * (2%:R : F)).
- rewrite /lazard_q1_pair_scale.
  finish_lazard_q1_ring.
- rewrite divfK //.
  transitivity
    ((((5%:R : F) / (2%:R : F)) * (2%:R : F)) * (2%:R : F)).
  + by rewrite divfK.
  + rewrite (@natrM F 2 2).
    finish_lazard_q1_ring.
Qed.

(** Multiplication by the Q1 denominator exposes the inner linear form.
    The characteristic-five exclusion is essential: otherwise the prefactor
    [5/4] vanishes identically. *)
Lemma lazard_q1_zero_inner H I J K E v
    (four_neq0 : (4%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (hq : lazard_q1 H I J K E v = 0) :
  lazard_q1_inner H I J K E v = 0.
Proof.
have hq4 : lazard_q1 H I J K E v * 4%:R = 0.
  by rewrite hq mul0r.
have hfive : (5%:R : F) * lazard_q1_inner H I J K E v = 0.
  have hcancel :
      (((5%:R : F) / (4%:R : F)) * (4%:R : F)) *
          lazard_q1_inner H I J K E v =
        (5%:R : F) * lazard_q1_inner H I J K E v.
    by rewrite divfK.
  rewrite -hcancel -hq4 /lazard_q1.
  finish_lazard_q1_ring.
apply: (mulfI five_neq0).
by rewrite mulr0 hfive.
Qed.

(** Two four-vectors whose standard projection equations reduce to the
    2-by-2 system in J and K. *)
Definition lazard_q1_J_source (J K : F) (i : 'I_4) : F :=
  nth 0 [:: J; - K; - J; K] i.

Definition lazard_q1_K_source (J K : F) (i : 'I_4) : F :=
  nth 0 [:: K; J; - K; - J] i.

(** The standard recovery theorem makes the kernel of
    [[t,u],[u,-t]] trivial when [t^2+u^2] is nonzero. *)
Lemma lazard_q1_standard_system_kernel (epsilon t u J K : F)
    (two_neq0 : (2%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (standard_denominator_neq0 : t ^+ 2 + u ^+ 2 != 0)
    (hfirst : t * J + u * K = 0)
    (hsecond : u * J - t * K = 0) :
  J = 0 /\ K = 0.
Proof.
have hJ0 : lazard_standard_projections epsilon t u
    (lazard_q1_J_source J K) p0 = 0.
  rewrite lazard_standard_projection0 /lazard_q1_J_source
    /p0 /p1 /p2 /p3 /=.
  finish_lazard_q1_ring.
have hJ1 : lazard_standard_projections epsilon t u
    (lazard_q1_J_source J K) p1 = 0.
  rewrite lazard_standard_projection1 /lazard_q1_J_source
    /p0 /p1 /p2 /p3 /=.
  finish_lazard_q1_ring.
have hJ2 : lazard_standard_projections epsilon t u
    (lazard_q1_J_source J K) p2 = 0.
  rewrite lazard_standard_projection2 /lazard_q1_J_source
    /p0 /p1 /p2 /p3 /=.
  transitivity (2%:R * (t * J + u * K)).
  + finish_lazard_q1_ring.
  + by rewrite hfirst mulr0.
have hJ3 : lazard_standard_projections epsilon t u
    (lazard_q1_J_source J K) p3 = 0.
  rewrite lazard_standard_projection3 /lazard_q1_J_source
    /p0 /p1 /p2 /p3 /=.
  transitivity (2%:R * (u * J - t * K)).
  + finish_lazard_q1_ring.
  + by rewrite hsecond mulr0.
have recoverJ := @lazard_standard_recover_projections F epsilon t u
  (lazard_q1_J_source J K) two_neq0 epsilon_neq0
  standard_denominator_neq0.
have hJ : J = 0.
  have recoverJ' :
      lazard_standard_recover epsilon t u
        (lazard_standard_projections epsilon t u
          (lazard_q1_J_source J K)) = J.
    move: recoverJ.
    by rewrite /lazard_q1_J_source /p0 /=.
  have hrecJ : 0 = J.
    rewrite -recoverJ' /lazard_standard_recover hJ0 hJ1 hJ2 hJ3.
    finish_lazard_q1_ring.
  exact: esym hrecJ.
have hK0 : lazard_standard_projections epsilon t u
    (lazard_q1_K_source J K) p0 = 0.
  rewrite lazard_standard_projection0 /lazard_q1_K_source
    /p0 /p1 /p2 /p3 /=.
  finish_lazard_q1_ring.
have hK1 : lazard_standard_projections epsilon t u
    (lazard_q1_K_source J K) p1 = 0.
  rewrite lazard_standard_projection1 /lazard_q1_K_source
    /p0 /p1 /p2 /p3 /=.
  finish_lazard_q1_ring.
have hK2 : lazard_standard_projections epsilon t u
    (lazard_q1_K_source J K) p2 = 0.
  rewrite lazard_standard_projection2 /lazard_q1_K_source
    /p0 /p1 /p2 /p3 /=.
  transitivity (- (2%:R * (u * J - t * K))).
  + finish_lazard_q1_ring.
  + by rewrite hsecond mulr0 oppr0.
have hK3 : lazard_standard_projections epsilon t u
    (lazard_q1_K_source J K) p3 = 0.
  rewrite lazard_standard_projection3 /lazard_q1_K_source
    /p0 /p1 /p2 /p3 /=.
  transitivity (2%:R * (t * J + u * K)).
  + finish_lazard_q1_ring.
  + by rewrite hfirst mulr0.
have recoverK := @lazard_standard_recover_projections F epsilon t u
  (lazard_q1_K_source J K) two_neq0 epsilon_neq0
  standard_denominator_neq0.
have hK : K = 0.
  have recoverK' :
      lazard_standard_recover epsilon t u
        (lazard_standard_projections epsilon t u
          (lazard_q1_K_source J K)) = K.
    move: recoverK.
    by rewrite /lazard_q1_K_source /p0 /=.
  have hrecK : 0 = K.
    rewrite -recoverK' /lazard_standard_recover hK0 hK1 hK2 hK3.
    finish_lazard_q1_ring.
  exact: esym hrecK.
exact: conj hJ hK.
Qed.

Definition lazard_q1_coefficients_zero (H I J K : F) : Prop :=
  H = 0 /\ I = 0 /\ J = 0 /\ K = 0.

(** If all four branch values vanish, the coefficient tuple is zero. *)
Theorem lazard_q1_all_branches_zero_coefficients H I J K E
    (v : lazard_quadratic_triple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : lazard_epsilon v != 0)
    (E_neq0 : E != 0)
    (standard_denominator_neq0 :
      lazard_t v ^+ 2 + lazard_u v ^+ 2 != 0)
    (hbase : lazard_q1_branch H I J K E v LazardBranchBase = 0)
    (hnegate :
      lazard_q1_branch H I J K E v LazardBranchNegateTU = 0)
    (hrotate : lazard_q1_branch H I J K E v LazardBranchRotate = 0)
    (hrotate_negate :
      lazard_q1_branch H I J K E v LazardBranchRotateNegate = 0) :
  lazard_q1_coefficients_zero H I J K.
Proof.
have four_neq0 := lazard_projection_four_neq0 two_neq0.
have hb : lazard_q1_inner H I J K E v = 0.
  exact: lazard_q1_zero_inner four_neq0 five_neq0 hbase.
have hn : lazard_q1_inner H I J K E
    (lazard_branch_triple v LazardBranchNegateTU) = 0.
  exact: lazard_q1_zero_inner four_neq0 five_neq0 hnegate.
have hr : lazard_q1_inner H I J K E
    (lazard_branch_triple v LazardBranchRotate) = 0.
  exact: lazard_q1_zero_inner four_neq0 five_neq0 hrotate.
have hrn : lazard_q1_inner H I J K E
    (lazard_branch_triple v LazardBranchRotateNegate) = 0.
  exact: lazard_q1_zero_inner four_neq0 five_neq0 hrotate_negate.
have hplus : H + I / lazard_epsilon v = 0.
  apply: (mulfI two_neq0).
  rewrite mulr0.
  transitivity
    (lazard_q1_inner H I J K E v +
      lazard_q1_inner H I J K E
        (lazard_branch_triple v LazardBranchNegateTU)).
  + rewrite /lazard_q1_inner /lazard_branch_triple /=.
    finish_lazard_q1_ring.
  + by rewrite hb hn add0r.
have hminus : H - I / lazard_epsilon v = 0.
  apply: (mulfI two_neq0).
  rewrite mulr0.
  transitivity
    (lazard_q1_inner H I J K E
        (lazard_branch_triple v LazardBranchRotate) +
      lazard_q1_inner H I J K E
        (lazard_branch_triple v LazardBranchRotateNegate)).
  + rewrite /lazard_q1_inner /lazard_branch_triple /=
      !invrN !mulrN.
    finish_lazard_q1_ring.
  + by rewrite hr hrn add0r.
have hH : H = 0.
  apply: (mulfI two_neq0).
  rewrite mulr0.
  transitivity
    ((H + I / lazard_epsilon v) +
      (H - I / lazard_epsilon v)).
  + finish_lazard_q1_ring.
  + by rewrite hplus hminus add0r.
have hIdiv : I / lazard_epsilon v = 0.
  apply: (mulfI two_neq0).
  rewrite mulr0.
  transitivity
    ((H + I / lazard_epsilon v) -
      (H - I / lazard_epsilon v)).
  + finish_lazard_q1_ring.
  + by rewrite hplus hminus subrr.
have hI : I = 0.
  have hcancelI : I / lazard_epsilon v * lazard_epsilon v = I :=
    divfK epsilon_neq0 I.
  by rewrite -hcancelI hIdiv mul0r.
have hfirst_div :
    (lazard_t v * J + lazard_u v * K) / E = 0.
  apply: (mulfI two_neq0).
  rewrite mulr0.
  transitivity
    (lazard_q1_inner H I J K E v -
      lazard_q1_inner H I J K E
        (lazard_branch_triple v LazardBranchNegateTU)).
  + rewrite /lazard_q1_inner /lazard_branch_triple /=.
    finish_lazard_q1_ring.
  + by rewrite hb hn subrr.
have hsecond_div :
    (lazard_u v * J - lazard_t v * K) / E = 0.
  apply: (mulfI two_neq0).
  rewrite mulr0.
  transitivity
    (lazard_q1_inner H I J K E
        (lazard_branch_triple v LazardBranchRotate) -
      lazard_q1_inner H I J K E
        (lazard_branch_triple v LazardBranchRotateNegate)).
  + rewrite /lazard_q1_inner /lazard_branch_triple /=
      !invrN !mulrN.
    finish_lazard_q1_ring.
  + by rewrite hr hrn subrr.
have hfirst : lazard_t v * J + lazard_u v * K = 0.
  have hcancel_first :
      (lazard_t v * J + lazard_u v * K) / E * E =
        lazard_t v * J + lazard_u v * K :=
    divfK E_neq0 (lazard_t v * J + lazard_u v * K).
  by rewrite -hcancel_first hfirst_div mul0r.
have hsecond : lazard_u v * J - lazard_t v * K = 0.
  have hcancel_second :
      (lazard_u v * J - lazard_t v * K) / E * E =
        lazard_u v * J - lazard_t v * K :=
    divfK E_neq0 (lazard_u v * J - lazard_t v * K).
  by rewrite -hcancel_second hsecond_div mul0r.
have hJK := @lazard_q1_standard_system_kernel
  (lazard_epsilon v) (lazard_t v) (lazard_u v) J K
  two_neq0 epsilon_neq0 standard_denominator_neq0 hfirst hsecond.
case: hJK=> hJ hK.
exact: conj hH (conj hI (conj hJ hK)).
Qed.

(** Hence a nonzero H/I/J/K tuple forces a nonzero Q1 value on at least
    one coherent branch. *)
Theorem lazard_q1_exists_nonzero_branch H I J K E
    (v : lazard_quadratic_triple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : lazard_epsilon v != 0)
    (E_neq0 : E != 0)
    (standard_denominator_neq0 :
      lazard_t v ^+ 2 + lazard_u v ^+ 2 != 0)
    (coefficients_nonzero : ~ lazard_q1_coefficients_zero H I J K) :
  exists branch : lazard_sign_branch,
    lazard_q1_branch H I J K E v branch != 0.
Proof.
case hbase: (lazard_q1_branch H I J K E v LazardBranchBase == 0).
- case hnegate:
    (lazard_q1_branch H I J K E v LazardBranchNegateTU == 0).
  + case hrotate:
      (lazard_q1_branch H I J K E v LazardBranchRotate == 0).
    * case hrotate_negate:
        (lazard_q1_branch H I J K E v LazardBranchRotateNegate == 0).
      -- exfalso; apply: coefficients_nonzero.
         apply: (@lazard_q1_all_branches_zero_coefficients
           H I J K E v two_neq0 five_neq0 epsilon_neq0 E_neq0
           standard_denominator_neq0).
         ++ exact/eqP.
         ++ exact/eqP.
         ++ exact/eqP.
         ++ exact/eqP.
      -- exists LazardBranchRotateNegate.
         by rewrite /negb hrotate_negate.
    * exists LazardBranchRotate.
      by rewrite /negb hrotate.
  + exists LazardBranchNegateTU.
    by rewrite /negb hnegate.
- exists LazardBranchBase.
  by rewrite /negb hbase.
Qed.

(** Variant taking nonsingularity of the standard matrix literally. *)
Corollary lazard_q1_exists_nonzero_branch_of_standard_det H I J K E
    (v : lazard_quadratic_triple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (epsilon_neq0 : lazard_epsilon v != 0)
    (E_neq0 : E != 0)
    (standard_det_neq0 :
      \det (lazard_standard_projection_matrix
        (lazard_epsilon v) (lazard_t v) (lazard_u v)) != 0)
    (coefficients_nonzero : ~ lazard_q1_coefficients_zero H I J K) :
  exists branch : lazard_sign_branch,
    lazard_q1_branch H I J K E v branch != 0.
Proof.
have standard_denominator_neq0 :
    lazard_t v ^+ 2 + lazard_u v ^+ 2 != 0.
  move: standard_det_neq0.
  rewrite lazard_standard_projection_matrix_det.
  apply: contra.
  by move/eqP=> ->; rewrite mulr0 eqxx.
exact: lazard_q1_exists_nonzero_branch two_neq0 five_neq0
  epsilon_neq0 E_neq0 standard_denominator_neq0 coefficients_nonzero.
Qed.

End Q1Branches.

End PolynomialFormulasLazardQuinticQ1Branches.
