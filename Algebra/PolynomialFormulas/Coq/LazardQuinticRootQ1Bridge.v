From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals LazardQuinticFourier
  LazardQuinticProjection LazardQuinticRootProjections
  LazardQuinticRootProjectionI LazardQuinticRootProjectionJKCommon
  LazardQuinticRootProjectionJ LazardQuinticRootProjectionK
  LazardQuinticQuadratic LazardQuinticQ1Branches
  LazardQuinticQ1ProjectionBridge.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Root-origin composition of the four proved projection identities with
    Lazard's Q1 recovery formula.  The coefficients H, I, J, and K below are
    computed directly from an ordered depressed root tuple.  Thus the four
    Q1 equalities at the end are derived from the roots; no Fourier or Vieta
    relation is accepted as certificate data. *)
Module PolynomialFormulasLazardQuinticRootQ1Bridge.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticFourier.
Import PolynomialFormulasLazardQuinticProjection.
Import PolynomialFormulasLazardQuinticQuadratic.
Import PolynomialFormulasLazardQuinticQ1Branches.
Local Open Scope ring_scope.

Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module RI := PolynomialFormulasLazardQuinticRootProjectionI.
Module RJK := PolynomialFormulasLazardQuinticRootProjectionJKCommon.
Module RJ := PolynomialFormulasLazardQuinticRootProjectionJ.
Module RK := PolynomialFormulasLazardQuinticRootProjectionK.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module QB := PolynomialFormulasLazardQuinticQ1ProjectionBridge.

Section RootQ1Bridge.

Variable F : fieldType.

(** The root-projection modules use explicit P1,...,P4 expressions, whereas
    the Q1 bridge uses the shared Fourier sum.  Primitive fifth-root
    reduction identifies the two four-vectors pointwise. *)
Lemma lazard_root_fourier_fifth_power_sourceE
    (omega : F) (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega) (j : 'I_4) :
  QB.lazard_fourier_fifth_power_source omega roots j =
    RP.lazard_root_fourier_fifth_orbit omega roots j.
Proof.
case: j=> [[|[|[|[|j]]]] hj].
- rewrite /QB.lazard_fourier_fifth_power_source
    /RP.lazard_root_fourier_fifth_orbit /=.
  by rewrite (@RP.lazard_root_fourier_P1E F omega roots).
- rewrite /QB.lazard_fourier_fifth_power_source
    /RP.lazard_root_fourier_fifth_orbit /=.
  by rewrite (@RP.lazard_root_fourier_P2E F omega roots omega_primitive).
- rewrite /QB.lazard_fourier_fifth_power_source
    /RP.lazard_root_fourier_fifth_orbit /=.
  by rewrite (@RP.lazard_root_fourier_P4E F omega roots omega_primitive).
- rewrite /QB.lazard_fourier_fifth_power_source
    /RP.lazard_root_fourier_fifth_orbit /=.
  by rewrite (@RP.lazard_root_fourier_P3E F omega roots omega_primitive).
- by move: hj.
Qed.

(** The zeroth projection does not depend on the matrix's epsilon, t, or u
    entries.  This generalizes the already proved H projection just enough
    to use the actual root epsilon in the common Section-7 tuple. *)
Lemma lazard_root_standard_projection_H_any_epsilon
    (epsilon omega t u : F) (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  lazard_standard_projections epsilon t u
      (RP.lazard_root_fourier_fifth_orbit omega roots) p0 =
    5%:R * RP.lazard_root_invariant_H
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots).
Proof.
rewrite lazard_standard_projection0.
have h := @RP.lazard_root_standard_projection_H F omega t u roots
  omega_primitive hsum.
by rewrite lazard_standard_projection0 in h.
Qed.

Definition lazard_root_section7_H
    (omega : F) (roots : 5.-tuple F) : F :=
  QB.lazard_section7_H (RP.lazard_root_epsilon omega roots)
    (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
    (QB.lazard_fourier_fifth_power_source omega roots).

Definition lazard_root_section7_I
    (omega : F) (roots : 5.-tuple F) : F :=
  QB.lazard_section7_I (RP.lazard_root_epsilon omega roots)
    (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
    (QB.lazard_fourier_fifth_power_source omega roots).

Definition lazard_root_section7_J
    (omega : F) (roots : 5.-tuple F) : F :=
  QB.lazard_section7_J (RP.lazard_root_epsilon omega roots)
    (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
    (QB.lazard_fourier_fifth_power_source omega roots).

Definition lazard_root_section7_K
    (omega : F) (roots : 5.-tuple F) : F :=
  QB.lazard_section7_K (RP.lazard_root_epsilon omega roots)
    (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
    (QB.lazard_fourier_fifth_power_source omega roots).

(** All four normalized Section-7 projection values are now consequences of
    their direct root identities. *)
Theorem lazard_root_section7_H_eq
    (omega : F) (roots : 5.-tuple F)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  lazard_root_section7_H omega roots =
    RP.lazard_root_invariant_H
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots).
Proof.
apply: (mulfI five_neq0).
rewrite /lazard_root_section7_H QB.lazard_section7_H_scaled //.
rewrite lazard_standard_projection0
  !(@lazard_root_fourier_fifth_power_sourceE omega roots omega_primitive).
have h := @lazard_root_standard_projection_H_any_epsilon
  (RP.lazard_root_epsilon omega roots) omega
  (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
  roots omega_primitive hsum.
by rewrite lazard_standard_projection0 in h.
Qed.

Theorem lazard_root_section7_I_eq
    (omega : F) (roots : 5.-tuple F)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  lazard_root_section7_I omega roots =
    RP.lazard_root_invariant_I
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots).
Proof.
apply: (mulfI five_neq0).
rewrite /lazard_root_section7_I QB.lazard_section7_I_scaled //.
rewrite lazard_standard_projection1
  !(@lazard_root_fourier_fifth_power_sourceE omega roots omega_primitive).
have h := @RI.lazard_root_standard_projection_I F omega
  (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
  roots omega_primitive hsum.
by rewrite lazard_standard_projection1 in h.
Qed.

Theorem lazard_root_section7_J_eq
    (omega : F) (roots : 5.-tuple F)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  lazard_root_section7_J omega roots =
    RJK.lazard_root_invariant_J
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots).
Proof.
have twenty_five_neq0 : (5%:R * 5%:R : F) != 0 :=
  mulf_neq0 five_neq0 five_neq0.
apply: (mulfI twenty_five_neq0).
rewrite /lazard_root_section7_J /QB.lazard_section7_J
  /QB.lazard_section7_twenty_five.
rewrite [((5%:R * 5%:R : F) * _)]mulrC divfK //.
rewrite lazard_standard_projection2
  !(@lazard_root_fourier_fifth_power_sourceE omega roots omega_primitive).
rewrite -(@RP.lazard_root_projection_twenty_five_natrE F).
have h := @RJ.lazard_root_standard_projection_J_scaled F omega roots
  omega_primitive hsum.
by rewrite lazard_standard_projection2 in h.
Qed.

Theorem lazard_root_section7_K_eq
    (omega : F) (roots : 5.-tuple F)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0) :
  lazard_root_section7_K omega roots =
    RJK.lazard_root_invariant_K
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots).
Proof.
have twenty_five_neq0 : (5%:R * 5%:R : F) != 0 :=
  mulf_neq0 five_neq0 five_neq0.
apply: (mulfI twenty_five_neq0).
rewrite /lazard_root_section7_K /QB.lazard_section7_K
  /QB.lazard_section7_twenty_five.
rewrite [((5%:R * 5%:R : F) * _)]mulrC divfK //.
rewrite lazard_standard_projection3
  !(@lazard_root_fourier_fifth_power_sourceE omega roots omega_primitive).
rewrite -(@RP.lazard_root_projection_twenty_five_natrE F).
have h := @RK.lazard_root_standard_projection_K_scaled F omega roots
  omega_primitive hsum.
by rewrite lazard_standard_projection3 in h.
Qed.

(** Q1 written solely with the coefficient invariants and the actual
    root-origin quadratic choices. *)
Definition lazard_root_q1_formula
    (omega : F) (roots : 5.-tuple F) (branch : lazard_sign_branch) : F :=
  lazard_q1_branch
    (RP.lazard_root_invariant_H
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots))
    (RP.lazard_root_invariant_I
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots))
    (RJK.lazard_root_invariant_J
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots))
    (RJK.lazard_root_invariant_K
      (RP.lazard_depressed_of_roots roots) (RP.lazard_root_invariants roots))
    (Q.lazard_root_E roots)
    (Q.LazardQuadraticTriple
      (RP.lazard_root_epsilon omega roots)
      (RR.lazard_root_T omega roots)
      (RR.lazard_root_formula_U omega roots)) branch.

Lemma lazard_root_TU_square_sum
    (omega : F) (roots : 5.-tuple F)
    (omega_primitive : 5.-primitive_root omega) :
  RR.lazard_root_T omega roots ^+ 2 +
      RR.lazard_root_formula_U omega roots ^+ 2 =
    5%:R * Q.lazard_root_E roots.
Proof.
exact: (@Q.lazard_root_E_identity F omega roots
  (@RR.lazard_primitive_fifth_root_cyclotomic F omega omega_primitive)).
Qed.

Theorem lazard_root_q1_formula_base
    (omega : F) (roots : 5.-tuple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 : Q.lazard_root_E roots != 0) :
  lazard_root_q1_formula omega roots LazardBranchBase =
    lazard_fourier_sum omega roots o1 ^+ 5.
Proof.
rewrite /lazard_root_q1_formula
  -(@lazard_root_section7_H_eq omega roots five_neq0 omega_primitive hsum)
  -(@lazard_root_section7_I_eq omega roots five_neq0 omega_primitive hsum)
  -(@lazard_root_section7_J_eq omega roots five_neq0 omega_primitive hsum)
  -(@lazard_root_section7_K_eq omega roots five_neq0 omega_primitive hsum).
change
  (QB.lazard_fourier_q1_branch
    (RP.lazard_root_epsilon omega roots)
    (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
    (Q.lazard_root_E roots) omega roots LazardBranchBase =
   lazard_fourier_sum omega roots o1 ^+ 5).
exact: (@QB.lazard_fourier_q1_base F
  (RP.lazard_root_epsilon omega roots)
  (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
  (Q.lazard_root_E roots) omega roots two_neq0 five_neq0
  epsilon_neq0 E_neq0 (@lazard_root_TU_square_sum omega roots omega_primitive)).
Qed.

Theorem lazard_root_q1_formula_rotate_negate
    (omega : F) (roots : 5.-tuple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 : Q.lazard_root_E roots != 0) :
  lazard_root_q1_formula omega roots LazardBranchRotateNegate =
    lazard_fourier_sum omega roots o2 ^+ 5.
Proof.
rewrite /lazard_root_q1_formula
  -(@lazard_root_section7_H_eq omega roots five_neq0 omega_primitive hsum)
  -(@lazard_root_section7_I_eq omega roots five_neq0 omega_primitive hsum)
  -(@lazard_root_section7_J_eq omega roots five_neq0 omega_primitive hsum)
  -(@lazard_root_section7_K_eq omega roots five_neq0 omega_primitive hsum).
change
  (QB.lazard_fourier_q1_branch
    (RP.lazard_root_epsilon omega roots)
    (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
    (Q.lazard_root_E roots) omega roots LazardBranchRotateNegate =
   lazard_fourier_sum omega roots o2 ^+ 5).
exact: (@QB.lazard_fourier_q1_rotate_negate F
  (RP.lazard_root_epsilon omega roots)
  (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
  (Q.lazard_root_E roots) omega roots two_neq0 five_neq0
  epsilon_neq0 E_neq0 (@lazard_root_TU_square_sum omega roots omega_primitive)).
Qed.

Theorem lazard_root_q1_formula_negate
    (omega : F) (roots : 5.-tuple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 : Q.lazard_root_E roots != 0) :
  lazard_root_q1_formula omega roots LazardBranchNegateTU =
    lazard_fourier_sum omega roots o4 ^+ 5.
Proof.
rewrite /lazard_root_q1_formula
  -(@lazard_root_section7_H_eq omega roots five_neq0 omega_primitive hsum)
  -(@lazard_root_section7_I_eq omega roots five_neq0 omega_primitive hsum)
  -(@lazard_root_section7_J_eq omega roots five_neq0 omega_primitive hsum)
  -(@lazard_root_section7_K_eq omega roots five_neq0 omega_primitive hsum).
change
  (QB.lazard_fourier_q1_branch
    (RP.lazard_root_epsilon omega roots)
    (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
    (Q.lazard_root_E roots) omega roots LazardBranchNegateTU =
   lazard_fourier_sum omega roots o4 ^+ 5).
exact: (@QB.lazard_fourier_q1_negate F
  (RP.lazard_root_epsilon omega roots)
  (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
  (Q.lazard_root_E roots) omega roots two_neq0 five_neq0
  epsilon_neq0 E_neq0 (@lazard_root_TU_square_sum omega roots omega_primitive)).
Qed.

Theorem lazard_root_q1_formula_rotate
    (omega : F) (roots : 5.-tuple F)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 : Q.lazard_root_E roots != 0) :
  lazard_root_q1_formula omega roots LazardBranchRotate =
    lazard_fourier_sum omega roots o3 ^+ 5.
Proof.
rewrite /lazard_root_q1_formula
  -(@lazard_root_section7_H_eq omega roots five_neq0 omega_primitive hsum)
  -(@lazard_root_section7_I_eq omega roots five_neq0 omega_primitive hsum)
  -(@lazard_root_section7_J_eq omega roots five_neq0 omega_primitive hsum)
  -(@lazard_root_section7_K_eq omega roots five_neq0 omega_primitive hsum).
change
  (QB.lazard_fourier_q1_branch
    (RP.lazard_root_epsilon omega roots)
    (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
    (Q.lazard_root_E roots) omega roots LazardBranchRotate =
   lazard_fourier_sum omega roots o3 ^+ 5).
exact: (@QB.lazard_fourier_q1_rotate F
  (RP.lazard_root_epsilon omega roots)
  (RR.lazard_root_T omega roots) (RR.lazard_root_formula_U omega roots)
  (Q.lazard_root_E roots) omega roots two_neq0 five_neq0
  epsilon_neq0 E_neq0 (@lazard_root_TU_square_sum omega roots omega_primitive)).
Qed.

Definition lazard_root_q1_target
    (omega : F) (roots : 5.-tuple F) (branch : lazard_sign_branch) : F :=
  match branch with
  | LazardBranchBase => lazard_fourier_sum omega roots o1 ^+ 5
  | LazardBranchNegateTU => lazard_fourier_sum omega roots o4 ^+ 5
  | LazardBranchRotate => lazard_fourier_sum omega roots o3 ^+ 5
  | LazardBranchRotateNegate => lazard_fourier_sum omega roots o2 ^+ 5
  end.

(** A single branch-indexed statement of actual-root Q1 correctness. *)
Theorem lazard_root_q1_formula_correct
    (omega : F) (roots : 5.-tuple F) (branch : lazard_sign_branch)
    (two_neq0 : (2%:R : F) != 0)
    (five_neq0 : (5%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (hsum : RP.lazard_root_esymm1 roots = 0)
    (epsilon_neq0 : RP.lazard_root_epsilon omega roots != 0)
    (E_neq0 : Q.lazard_root_E roots != 0) :
  lazard_root_q1_formula omega roots branch =
    lazard_root_q1_target omega roots branch.
Proof.
case: branch.
- exact: lazard_root_q1_formula_base.
- exact: lazard_root_q1_formula_negate.
- exact: lazard_root_q1_formula_rotate.
- exact: lazard_root_q1_formula_rotate_negate.
Qed.

End RootQ1Bridge.

End PolynomialFormulasLazardQuinticRootQ1Bridge.
