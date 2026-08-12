From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.
From PolynomialFormulas Require Import LazardQuinticRootRadicals.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Lazard's quadratic stage, separated from the later fifth-root formulas.
    The abstract record follows the Lean [QuadraticRelations] record, while
    the final section derives an instance directly from the already proved
    root-side E/F/G change-of-basis identities. *)
Module PolynomialFormulasLazardQuinticQuadratic.

Import GRing.Theory.
Import PolynomialFormulasLazardQuinticRootRadicals.
Local Open Scope ring_scope.

Section Quadratic.

Variable F : fieldType.

Record lazard_quadratic_triple := LazardQuadraticTriple {
  lazard_epsilon : F;
  lazard_t : F;
  lazard_u : F
}.

(** The four equations characterizing one coherent choice of the three
    quadratic-stage radicals. *)
Record lazard_quadratic_relations
    (D E Finvariant G : F) (v : lazard_quadratic_triple) : Prop := {
  lazard_epsilon_square :
    lazard_epsilon v ^+ 2 = 5%:R * D;
  lazard_t_square :
    lazard_t v ^+ 2 =
      ((5%:R : F) / (2%:R : F)) *
        (E + Finvariant / lazard_epsilon v);
  lazard_u_square :
    lazard_u v ^+ 2 =
      ((5%:R : F) / (2%:R : F)) *
        (E - Finvariant / lazard_epsilon v);
  lazard_t_u_epsilon_product :
    lazard_t v * lazard_u v * lazard_epsilon v = 5%:R * G
}.

Inductive lazard_sign_branch :=
| LazardBranchBase
| LazardBranchNegateTU
| LazardBranchRotate
| LazardBranchRotateNegate.

(** The four coherent sign choices in Lazard's construction. *)
Definition lazard_branch_triple
    (v : lazard_quadratic_triple) (branch : lazard_sign_branch) :
    lazard_quadratic_triple :=
  match branch with
  | LazardBranchBase => v
  | LazardBranchNegateTU =>
      LazardQuadraticTriple (lazard_epsilon v) (- lazard_t v) (- lazard_u v)
  | LazardBranchRotate =>
      LazardQuadraticTriple (- lazard_epsilon v) (lazard_u v) (- lazard_t v)
  | LazardBranchRotateNegate =>
      LazardQuadraticTriple (- lazard_epsilon v) (- lazard_u v) (lazard_t v)
  end.

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

Lemma lazard_quadratic_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma lazard_quadratic_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma lazard_quadratic_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma lazard_quadratic_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma lazard_quadratic_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma lazard_quadratic_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma lazard_quadratic_ring_theory :
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

Add Ring lazard_quadratic_ring : lazard_quadratic_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Lemma lazard_quadratic_two_natrE : (2%:R : F) = 1 + 1.
Proof. exact: (@natrD F 1 1). Qed.

Lemma lazard_quadratic_five_natrE :
  (5%:R : F) = 1 + 1 + 1 + 1 + 1.
Proof.
have h2 : (2%:R : F) = 1 + 1 := lazard_quadratic_two_natrE.
have h3 : (3%:R : F) = 1 + 1 + 1.
  rewrite -h2; exact: (@natrD F 2 1).
have h4 : (4%:R : F) = 1 + 1 + 1 + 1.
  rewrite -h3; exact: (@natrD F 3 1).
rewrite -h4.
exact: (@natrD F 4 1).
Qed.

Lemma lazard_quadratic_expr2 (x : F) : x ^+ 2 = x * x.
Proof. by rewrite expr2. Qed.

Ltac finish_lazard_quadratic_ring :=
  repeat first
    [ rewrite lazard_quadratic_two_natrE
    | rewrite lazard_quadratic_five_natrE
    | rewrite lazard_quadratic_expr2
    | rewrite lazard_quadratic_ring_addE
    | rewrite lazard_quadratic_ring_mulE
    | rewrite lazard_quadratic_ring_subE
    | rewrite lazard_quadratic_ring_oppE
    | rewrite lazard_quadratic_ring_zeroE
    | rewrite lazard_quadratic_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

(** Every coherent sign branch preserves all four equations.  No nonzero
    hypothesis is needed here: negation commutes with inversion in every
    field, including at zero. *)
Theorem lazard_quadratic_relations_branch
    D E Finvariant G v branch
    (h : lazard_quadratic_relations D E Finvariant G v) :
  lazard_quadratic_relations D E Finvariant G
    (lazard_branch_triple v branch).
Proof.
case: branch.
- exact h.
- case: h => he ht hu hp.
  constructor=> /=.
  + exact he.
  + by rewrite sqrrN.
  + by rewrite sqrrN.
  + rewrite -hp.
    finish_lazard_quadratic_ring.
- case: h => he ht hu hp.
  constructor=> /=.
  + by rewrite sqrrN.
  + rewrite invrN mulrN.
    exact hu.
  + rewrite sqrrN invrN mulrN ht.
    finish_lazard_quadratic_ring.
  + rewrite -hp.
    finish_lazard_quadratic_ring.
- case: h => he ht hu hp.
  constructor=> /=.
  + by rewrite sqrrN.
  + rewrite sqrrN invrN mulrN.
    exact hu.
  + rewrite invrN mulrN ht.
    finish_lazard_quadratic_ring.
  + rewrite -hp.
    finish_lazard_quadratic_ring.
Qed.

Corollary lazard_quadratic_relations_base D E Finvariant G v
    (h : lazard_quadratic_relations D E Finvariant G v) :
  lazard_quadratic_relations D E Finvariant G
    (lazard_branch_triple v LazardBranchBase).
Proof. exact: lazard_quadratic_relations_branch h. Qed.

Corollary lazard_quadratic_relations_negate_tu D E Finvariant G v
    (h : lazard_quadratic_relations D E Finvariant G v) :
  lazard_quadratic_relations D E Finvariant G
    (lazard_branch_triple v LazardBranchNegateTU).
Proof. exact: lazard_quadratic_relations_branch h. Qed.

Corollary lazard_quadratic_relations_rotate D E Finvariant G v
    (h : lazard_quadratic_relations D E Finvariant G v) :
  lazard_quadratic_relations D E Finvariant G
    (lazard_branch_triple v LazardBranchRotate).
Proof. exact: lazard_quadratic_relations_branch h. Qed.

Corollary lazard_quadratic_relations_rotate_negate D E Finvariant G v
    (h : lazard_quadratic_relations D E Finvariant G v) :
  lazard_quadratic_relations D E Finvariant G
    (lazard_branch_triple v LazardBranchRotateNegate).
Proof. exact: lazard_quadratic_relations_branch h. Qed.

(** Dividing the F identity is the sole point where epsilon must be
    nonzero. *)
Lemma lazard_EF_difference_divide (Finvariant epsilon t u : F)
    (epsilon_neq0 : epsilon != 0)
    (hdifference :
      epsilon * (t ^+ 2 - u ^+ 2) = 5%:R * Finvariant) :
  t ^+ 2 - u ^+ 2 = 5%:R * Finvariant / epsilon.
Proof.
apply: (mulfI epsilon_neq0).
rewrite hdifference [epsilon * _]mulrC divfK //.
Qed.

Lemma lazard_five_half_cancel (two_neq0 : (2%:R : F) != 0) :
  (2%:R : F) * ((5%:R : F) / (2%:R : F)) = (5%:R : F).
Proof.
by rewrite [2%:R * _]mulrC divfK.
Qed.

(** Adding the E and divided F identities gives the T-square equation. *)
Theorem lazard_t_square_of_EF E Finvariant epsilon t u
    (two_neq0 : (2%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (hsum : t ^+ 2 + u ^+ 2 = 5%:R * E)
    (hdifference :
      epsilon * (t ^+ 2 - u ^+ 2) = 5%:R * Finvariant) :
  t ^+ 2 =
    ((5%:R : F) / (2%:R : F)) * (E + Finvariant / epsilon).
Proof.
have hdiff := lazard_EF_difference_divide epsilon_neq0 hdifference.
apply: (mulfI two_neq0).
transitivity ((t ^+ 2 + u ^+ 2) + (t ^+ 2 - u ^+ 2)).
- finish_lazard_quadratic_ring.
- rewrite hsum hdiff.
  transitivity (5%:R * (E + Finvariant / epsilon)).
  + finish_lazard_quadratic_ring.
  + rewrite mulrA lazard_five_half_cancel //.
Qed.

(** Subtracting the divided F identity from E gives the U-square equation. *)
Theorem lazard_u_square_of_EF E Finvariant epsilon t u
    (two_neq0 : (2%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (hsum : t ^+ 2 + u ^+ 2 = 5%:R * E)
    (hdifference :
      epsilon * (t ^+ 2 - u ^+ 2) = 5%:R * Finvariant) :
  u ^+ 2 =
    ((5%:R : F) / (2%:R : F)) * (E - Finvariant / epsilon).
Proof.
have hdiff := lazard_EF_difference_divide epsilon_neq0 hdifference.
apply: (mulfI two_neq0).
transitivity ((t ^+ 2 + u ^+ 2) - (t ^+ 2 - u ^+ 2)).
- finish_lazard_quadratic_ring.
- rewrite hsum hdiff.
  transitivity (5%:R * (E - Finvariant / epsilon)).
  + finish_lazard_quadratic_ring.
  + rewrite mulrA lazard_five_half_cancel //.
Qed.

(** Package E/F/G identities, together with the D square identity, into the
    abstract quadratic-stage record. *)
Theorem lazard_quadratic_relations_of_EFG
    D E Finvariant G epsilon t u
    (two_neq0 : (2%:R : F) != 0)
    (epsilon_neq0 : epsilon != 0)
    (hepsilon_square : epsilon ^+ 2 = 5%:R * D)
    (hE : t ^+ 2 + u ^+ 2 = 5%:R * E)
    (hF : epsilon * (t ^+ 2 - u ^+ 2) = 5%:R * Finvariant)
    (hG : epsilon * t * u = 5%:R * G) :
  lazard_quadratic_relations D E Finvariant G
    (LazardQuadraticTriple epsilon t u).
Proof.
constructor=> /=.
- exact hepsilon_square.
- exact: lazard_t_square_of_EF two_neq0 epsilon_neq0 hE hF.
- exact: lazard_u_square_of_EF two_neq0 epsilon_neq0 hE hF.
- rewrite -hG.
  finish_lazard_quadratic_ring.
Qed.

(** Root-origin invariants in exactly the normalization occurring on the
    right sides of the already proved E/F/G identities. *)
Definition lazard_root_D (roots : 5.-tuple F) : F :=
  lazard_epsilon_product roots ^+ 2.

Definition lazard_root_E (roots : 5.-tuple F) : F :=
  - (lazard_root_T_prime roots ^+ 2 + lazard_root_U_prime roots ^+ 2).

Definition lazard_root_F (roots : 5.-tuple F) : F :=
  - lazard_epsilon_product roots *
    (lazard_root_T_prime roots ^+ 2 +
      4%:R * lazard_root_T_prime roots * lazard_root_U_prime roots -
      lazard_root_U_prime roots ^+ 2).

Definition lazard_root_G (roots : 5.-tuple F) : F :=
  lazard_epsilon_product roots *
    (lazard_root_T_prime roots ^+ 2 -
      lazard_root_T_prime roots * lazard_root_U_prime roots -
      lazard_root_U_prime roots ^+ 2).

Lemma lazard_root_epsilon_square omega roots
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_root_epsilon omega roots ^+ 2 =
    5%:R * lazard_root_D roots.
Proof.
rewrite /lazard_root_epsilon /lazard_root_D exprMn.
by rewrite lazard_fifth_root_discriminant_factor_sq_of_cyclotomic //.
Qed.

Lemma lazard_root_E_identity omega roots
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_root_T omega roots ^+ 2 +
      lazard_root_formula_U omega roots ^+ 2 =
    5%:R * lazard_root_E roots.
Proof.
rewrite (@lazard_root_E_change_of_basis F omega roots hcyclo)
  /lazard_root_E.
finish_lazard_quadratic_ring.
Qed.

Lemma lazard_root_F_identity omega roots
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_root_epsilon omega roots *
      (lazard_root_T omega roots ^+ 2 -
        lazard_root_formula_U omega roots ^+ 2) =
    5%:R * lazard_root_F roots.
Proof.
rewrite (@lazard_root_F_change_of_basis F omega roots hcyclo)
  /lazard_root_F.
finish_lazard_quadratic_ring.
Qed.

Lemma lazard_root_G_identity omega roots
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_root_epsilon omega roots * lazard_root_T omega roots *
      lazard_root_formula_U omega roots =
    5%:R * lazard_root_G roots.
Proof.
rewrite (@lazard_root_G_formula_change_of_basis F omega roots hcyclo)
  /lazard_root_G.
finish_lazard_quadratic_ring.
Qed.

Theorem lazard_root_T_square omega roots
    (two_neq0 : (2%:R : F) != 0)
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0)
    (epsilon_neq0 : lazard_root_epsilon omega roots != 0) :
  lazard_root_T omega roots ^+ 2 =
    ((5%:R : F) / (2%:R : F)) *
      (lazard_root_E roots +
        lazard_root_F roots / lazard_root_epsilon omega roots).
Proof.
exact (@lazard_t_square_of_EF
  (lazard_root_E roots) (lazard_root_F roots)
  (lazard_root_epsilon omega roots) (lazard_root_T omega roots)
  (lazard_root_formula_U omega roots) two_neq0 epsilon_neq0
  (@lazard_root_E_identity omega roots hcyclo)
  (@lazard_root_F_identity omega roots hcyclo)).
Qed.

Theorem lazard_root_U_square omega roots
    (two_neq0 : (2%:R : F) != 0)
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0)
    (epsilon_neq0 : lazard_root_epsilon omega roots != 0) :
  lazard_root_formula_U omega roots ^+ 2 =
    ((5%:R : F) / (2%:R : F)) *
      (lazard_root_E roots -
        lazard_root_F roots / lazard_root_epsilon omega roots).
Proof.
exact (@lazard_u_square_of_EF
  (lazard_root_E roots) (lazard_root_F roots)
  (lazard_root_epsilon omega roots) (lazard_root_T omega roots)
  (lazard_root_formula_U omega roots) two_neq0 epsilon_neq0
  (@lazard_root_E_identity omega roots hcyclo)
  (@lazard_root_F_identity omega roots hcyclo)).
Qed.

Theorem lazard_root_T_U_epsilon_product omega roots
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0) :
  lazard_root_T omega roots * lazard_root_formula_U omega roots *
      lazard_root_epsilon omega roots = 5%:R * lazard_root_G roots.
Proof.
rewrite -(@lazard_root_G_identity omega roots hcyclo).
finish_lazard_quadratic_ring.
Qed.

(** The existing root identities therefore supply an actual instance of
    the abstract quadratic-stage relations.  Epsilon nonvanishing is needed
    exactly to divide the F identity; characteristic not two is recorded
    separately by [two_neq0]. *)
Theorem lazard_root_quadratic_relations omega roots
    (two_neq0 : (2%:R : F) != 0)
    (hcyclo : lazard_root_fifth_cyclotomic_value omega = 0)
    (epsilon_neq0 : lazard_root_epsilon omega roots != 0) :
  lazard_quadratic_relations
    (lazard_root_D roots) (lazard_root_E roots)
    (lazard_root_F roots) (lazard_root_G roots)
    (LazardQuadraticTriple
      (lazard_root_epsilon omega roots)
      (lazard_root_T omega roots)
      (lazard_root_formula_U omega roots)).
Proof.
exact (@lazard_quadratic_relations_of_EFG
  (lazard_root_D roots) (lazard_root_E roots)
  (lazard_root_F roots) (lazard_root_G roots)
  (lazard_root_epsilon omega roots) (lazard_root_T omega roots)
  (lazard_root_formula_U omega roots) two_neq0 epsilon_neq0
  (@lazard_root_epsilon_square omega roots hcyclo)
  (@lazard_root_E_identity omega roots hcyclo)
  (@lazard_root_F_identity omega roots hcyclo)
  (@lazard_root_G_identity omega roots hcyclo)).
Qed.

Corollary lazard_root_quadratic_relations_primitive omega roots
    (two_neq0 : (2%:R : F) != 0)
    (omega_primitive : 5.-primitive_root omega)
    (epsilon_neq0 : lazard_root_epsilon omega roots != 0) :
  lazard_quadratic_relations
    (lazard_root_D roots) (lazard_root_E roots)
    (lazard_root_F roots) (lazard_root_G roots)
    (LazardQuadraticTriple
      (lazard_root_epsilon omega roots)
      (lazard_root_T omega roots)
      (lazard_root_formula_U omega roots)).
Proof.
exact (@lazard_root_quadratic_relations omega roots two_neq0
  (@lazard_primitive_fifth_root_cyclotomic F omega omega_primitive)
  epsilon_neq0).
Qed.

End Quadratic.

End PolynomialFormulasLazardQuinticQuadratic.
