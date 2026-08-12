From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticQuadratic LazardQuinticProjection
  LazardQuinticQ1ProjectionBridge
  LazardQuinticRootFourierNumeratorRing.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Coherent sign branches as honest reorderings of the five roots.
    Multiplication by two on the indices has order four; the four explicit
    tuples below are its powers [0,2,1,3] in Lazard's branch order. *)
Module PolynomialFormulasLazardQuinticRootBranchEquivariance.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticRootProjections.
Import PolynomialFormulasLazardQuinticQuadratic.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module P := PolynomialFormulasLazardQuinticProjection.
Module QB := PolynomialFormulasLazardQuinticQ1ProjectionBridge.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Local Open Scope ring_scope.

Section RootBranchEquivariance.

Variable F : fieldType.

Add Ring lazard_root_branch_equivariance_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_root_branch_equivariance_ring :=
  repeat first
    [ rewrite NR.lazard_numerator_expr4
    | rewrite NR.lazard_numerator_expr3
    | rewrite NR.lazard_numerator_expr2
    | rewrite expr1
    | rewrite NR.lazard_numerator_ring_addE
    | rewrite NR.lazard_numerator_ring_mulE
    | rewrite NR.lazard_numerator_ring_subE
    | rewrite NR.lazard_numerator_ring_oppE
    | rewrite NR.lazard_numerator_ring_zeroE
    | rewrite NR.lazard_numerator_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

Definition lazard_branch_index
    (branch : lazard_sign_branch) (i : 'I_5) : 'I_5 :=
  match branch with
  | LazardBranchBase => i
  | LazardBranchNegateTU => nth o0 [:: o0; o4; o3; o2; o1] i
  | LazardBranchRotate => nth o0 [:: o0; o2; o4; o1; o3] i
  | LazardBranchRotateNegate => nth o0 [:: o0; o3; o1; o4; o2] i
  end.

Definition lazard_roots_for_branch
    (roots : 5.-tuple F) (branch : lazard_sign_branch) : 5.-tuple F :=
  [tuple tnth roots (lazard_branch_index branch i) | i < 5].

Lemma lazard_roots_for_branch_tnth roots branch (i : 'I_5) :
  tnth (lazard_roots_for_branch roots branch) i =
    tnth roots (lazard_branch_index branch i).
Proof. by rewrite /lazard_roots_for_branch tnth_mktuple. Qed.

Definition lazard_root_quadratic_triple
    (omega : F) (roots : 5.-tuple F) : lazard_quadratic_triple F :=
  LazardQuadraticTriple
    (lazard_root_epsilon omega roots)
    (RR.lazard_root_T omega roots)
    (RR.lazard_root_formula_U omega roots).

(** Orbit order is [P1,P2,P4,P3], as in the Section-7 projection source. *)
Definition lazard_root_fourier_orbit
    (omega : F) (roots : 5.-tuple F) (i : 'I_4) : F :=
  nth 0
    [:: lazard_root_fourier_P1 omega roots;
        lazard_root_fourier_P2 omega roots;
        lazard_root_fourier_P4 omega roots;
        lazard_root_fourier_P3 omega roots] i.

Definition lazard_source_for_branch
    (source : 'I_4 -> F) (branch : lazard_sign_branch) : 'I_4 -> F :=
  match branch with
  | LazardBranchBase => source
  | LazardBranchNegateTU => QB.lazard_negate_source source
  | LazardBranchRotate => QB.lazard_rotate_source source
  | LazardBranchRotateNegate => QB.lazard_rotate_negate_source source
  end.

Lemma lazard_root_esymm1_roots_for_branch roots branch :
  lazard_root_esymm1 (lazard_roots_for_branch roots branch) =
    lazard_root_esymm1 roots.
Proof.
case: branch; rewrite /lazard_root_esymm1
  !lazard_roots_for_branch_tnth /lazard_branch_index
  /o0 /o1 /o2 /o3 /o4 /=;
  finish_lazard_root_branch_equivariance_ring.
Qed.

Lemma lazard_root_esymm2_roots_for_branch roots branch :
  lazard_root_esymm2 (lazard_roots_for_branch roots branch) =
    lazard_root_esymm2 roots.
Proof.
case: branch; rewrite /lazard_root_esymm2
  !lazard_roots_for_branch_tnth /lazard_branch_index
  /o0 /o1 /o2 /o3 /o4 /=;
  finish_lazard_root_branch_equivariance_ring.
Qed.

Lemma lazard_root_esymm3_roots_for_branch roots branch :
  lazard_root_esymm3 (lazard_roots_for_branch roots branch) =
    lazard_root_esymm3 roots.
Proof.
case: branch; rewrite /lazard_root_esymm3
  !lazard_roots_for_branch_tnth /lazard_branch_index
  /o0 /o1 /o2 /o3 /o4 /=;
  finish_lazard_root_branch_equivariance_ring.
Qed.

Lemma lazard_root_esymm4_roots_for_branch roots branch :
  lazard_root_esymm4 (lazard_roots_for_branch roots branch) =
    lazard_root_esymm4 roots.
Proof.
case: branch; rewrite /lazard_root_esymm4
  !lazard_roots_for_branch_tnth /lazard_branch_index
  /o0 /o1 /o2 /o3 /o4 /=;
  finish_lazard_root_branch_equivariance_ring.
Qed.

Lemma lazard_root_esymm5_roots_for_branch roots branch :
  lazard_root_esymm5 (lazard_roots_for_branch roots branch) =
    lazard_root_esymm5 roots.
Proof.
case: branch; rewrite /lazard_root_esymm5
  !lazard_roots_for_branch_tnth /lazard_branch_index
  /o0 /o1 /o2 /o3 /o4 /=;
  finish_lazard_root_branch_equivariance_ring.
Qed.

Lemma lazard_depressed_coefficients_ext
    (a b : LazardDepressedRootCoefficients F)
    (hp : lazard_root_p a = lazard_root_p b)
    (hq : lazard_root_q a = lazard_root_q b)
    (hr : lazard_root_r a = lazard_root_r b)
    (hs : lazard_root_s a = lazard_root_s b) : a = b.
Proof.
case: a hp hq hr hs=> ap aq ar asv /=.
case: b=> bp bq br bsv /=.
by move=> -> -> -> ->.
Qed.

Lemma lazard_depressed_of_roots_for_branch roots branch :
  lazard_depressed_of_roots (lazard_roots_for_branch roots branch) =
    lazard_depressed_of_roots roots.
Proof.
apply: lazard_depressed_coefficients_ext=> /=.
- exact: lazard_root_esymm2_roots_for_branch roots branch.
- by rewrite lazard_root_esymm3_roots_for_branch.
- exact: lazard_root_esymm4_roots_for_branch roots branch.
- by rewrite lazard_root_esymm5_roots_for_branch.
Qed.

Lemma lazard_root_invariants_ext (a b : LazardRootInvariants F)
    (h4 : lazard_root_i4 a = lazard_root_i4 b)
    (h5 : lazard_root_i5 a = lazard_root_i5 b)
    (h6 : lazard_root_i6 a = lazard_root_i6 b)
    (h7 : lazard_root_i7 a = lazard_root_i7 b)
    (h8 : lazard_root_i8 a = lazard_root_i8 b) : a = b.
Proof.
case: a h4 h5 h6 h7 h8=> a4 a5 a6 a7 a8 /=.
case: b=> b4 b5 b6 b7 b8 /=.
by move=> -> -> -> -> ->.
Qed.

Lemma lazard_root_invariants_roots_for_branch roots branch :
  lazard_root_invariants (lazard_roots_for_branch roots branch) =
    lazard_root_invariants roots.
Proof.
case: branch;
  apply: lazard_root_invariants_ext;
  rewrite /lazard_root_invariants /lazard_root_orbit_formula
    !lazard_roots_for_branch_tnth /lazard_branch_index
    /o0 /o1 /o2 /o3 /o4 /=;
  finish_lazard_root_branch_equivariance_ring.
Qed.

Lemma lazard_quadratic_triple_ext (a b : lazard_quadratic_triple F)
    (he : lazard_epsilon a = lazard_epsilon b)
    (ht : lazard_t a = lazard_t b)
    (hu : lazard_u a = lazard_u b) : a = b.
Proof.
case: a he ht hu=> ae atv au /=.
case: b=> be bt bu /=.
by move=> -> -> ->.
Qed.

Lemma lazard_root_quadratic_triple_roots_for_branch omega roots branch :
  lazard_root_quadratic_triple omega
      (lazard_roots_for_branch roots branch) =
    lazard_branch_triple (lazard_root_quadratic_triple omega roots) branch.
Proof.
case: branch;
  apply: lazard_quadratic_triple_ext;
  rewrite /lazard_root_quadratic_triple
    /lazard_branch_triple /= /lazard_root_epsilon
    /lazard_root_epsilon_product /RR.lazard_root_T
    /RR.lazard_root_formula_U /RR.lazard_root_printed_U
    /RR.lazard_root_T_prime /RR.lazard_root_U_prime
    !lazard_roots_for_branch_tnth /lazard_branch_index
    /o0 /o1 /o2 /o3 /o4 /=;
  finish_lazard_root_branch_equivariance_ring.
Qed.

Lemma lazard_root_fourier_orbit_roots_for_branch
    omega roots branch (i : 'I_4) :
  lazard_root_fourier_orbit omega (lazard_roots_for_branch roots branch) i =
    lazard_source_for_branch (lazard_root_fourier_orbit omega roots) branch i.
Proof.
case: branch;
  case: i=> [[|[|[|[|i]]]] hi] //=;
  rewrite /lazard_root_fourier_orbit /lazard_source_for_branch
    /QB.lazard_negate_source
    /QB.lazard_rotate_source /QB.lazard_rotate_negate_source
    /P.p0 /P.p1 /P.p2 /P.p3 /=
    /lazard_root_fourier_P1 /lazard_root_fourier_P2
    /lazard_root_fourier_P3 /lazard_root_fourier_P4
    !lazard_roots_for_branch_tnth /lazard_branch_index
    /o0 /o1 /o2 /o3 /o4 /=;
  finish_lazard_root_branch_equivariance_ring.
Qed.

(** The same identities after the two successive branch corrections used
    by Lazard's certificate construction. *)
Lemma lazard_root_esymm1_roots_for_two_branches roots first second :
  lazard_root_esymm1
      (lazard_roots_for_branch (lazard_roots_for_branch roots first) second) =
    lazard_root_esymm1 roots.
Proof. by rewrite !lazard_root_esymm1_roots_for_branch. Qed.

Lemma lazard_depressed_of_roots_for_two_branches roots first second :
  lazard_depressed_of_roots
      (lazard_roots_for_branch (lazard_roots_for_branch roots first) second) =
    lazard_depressed_of_roots roots.
Proof. by rewrite !lazard_depressed_of_roots_for_branch. Qed.

Lemma lazard_root_invariants_roots_for_two_branches roots first second :
  lazard_root_invariants
      (lazard_roots_for_branch (lazard_roots_for_branch roots first) second) =
    lazard_root_invariants roots.
Proof. by rewrite !lazard_root_invariants_roots_for_branch. Qed.

Lemma lazard_root_quadratic_triple_roots_for_two_branches
    omega roots first second :
  lazard_root_quadratic_triple omega
      (lazard_roots_for_branch (lazard_roots_for_branch roots first) second) =
    lazard_branch_triple
      (lazard_branch_triple (lazard_root_quadratic_triple omega roots) first)
      second.
Proof. by rewrite !lazard_root_quadratic_triple_roots_for_branch. Qed.

Lemma lazard_root_fourier_orbit_roots_for_two_branches
    omega roots first second (i : 'I_4) :
  lazard_root_fourier_orbit omega
      (lazard_roots_for_branch (lazard_roots_for_branch roots first) second) i =
    lazard_source_for_branch
      (lazard_source_for_branch (lazard_root_fourier_orbit omega roots) first)
      second i.
Proof.
rewrite lazard_root_fourier_orbit_roots_for_branch.
case: second;
  case: i=> [[|[|[|[|i]]]] hi] //=;
  rewrite /lazard_source_for_branch /QB.lazard_negate_source
    /QB.lazard_rotate_source /QB.lazard_rotate_negate_source
    /P.p0 /P.p1 /P.p2 /P.p3 /=;
  by rewrite !lazard_root_fourier_orbit_roots_for_branch.
Qed.

Lemma lazard_branch_epsilon_neq0 (v : lazard_quadratic_triple F) branch :
  lazard_epsilon v != 0 ->
  lazard_epsilon (lazard_branch_triple v branch) != 0.
Proof. by case: branch=> //=; rewrite oppr_eq0. Qed.

End RootBranchEquivariance.

End PolynomialFormulasLazardQuinticRootBranchEquivariance.
