From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import char0.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticGaloisAction
  QuinticRecursiveFactor QuinticCanonicalDecision
  LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticQuadratic LazardQuinticFourierNumerators
  LazardQuinticRootProjectionJKCommon
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticRootBranchEquivariance
  LazardQuinticRootInvariantENonzeroF20
  LazardQuinticRootInvariantF20 LazardQuinticInvariantDescentF20
  LazardQuinticRootCentering LazardQuinticCertificateRadicalTower
  LazardQuinticRootRadicalCertificate.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Automatic base-field membership for the root-origin Lazard
    certificate.

    The ten Fourier numerators and five of the eight radical invariants are
    polynomial expressions in the four depressed coefficients and the five
    metacyclic invariant coordinates.  Their membership proofs are therefore
    pure subfield closure.  The remaining root expressions [D], [F], and [G]
    are treated separately: they are proved invariant under the two
    generators of [F20], then descended through the canonical Galois action.

    This route deliberately does not identify the root expressions [D], [F],
    and [G] with Lazard's large displayed coefficient polynomials.  Those
    coefficient identities are independent formula-correctness statements;
    they are not needed for base-field membership of the root certificate. *)
Module PolynomialFormulasLazardQuinticRootMembershipDescent.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Module TV := PolynomialFormulasQuinticThetaValues.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module RJK := PolynomialFormulasLazardQuinticRootProjectionJKCommon.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module ENZ := PolynomialFormulasLazardQuinticRootInvariantENonzeroF20.
Module IF20 := PolynomialFormulasLazardQuinticRootInvariantF20.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.
Module RC := PolynomialFormulasLazardQuinticRootCentering.
Module CRT := PolynomialFormulasLazardQuinticCertificateRadicalTower.
Module RRC := PolynomialFormulasLazardQuinticRootRadicalCertificate.

Local Open Scope ring_scope.
Local Open Scope group_scope.

Section RootDFGInvariance.

Variable F : fieldType.

Add Ring lazard_membership_descent_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_membership_descent_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** The raw epsilon product commutes with scalar extension. *)
Lemma lazard_epsilon_product_map (E : fieldType)
    (h : {rmorphism F -> E}) (roots : 5.-tuple F) :
  h (RR.lazard_epsilon_product roots) =
    RR.lazard_epsilon_product (map_tuple h roots).
Proof.
by rewrite /RR.lazard_epsilon_product
  !rmorphM !rmorphD !rmorphB !tnth_map.
Qed.

(** Its two generator transformations are the missing sign bookkeeping for
    the root definitions of [D], [F], and [G]. *)
Lemma lazard_epsilon_product_five_cycle (roots : 5.-tuple F) :
  RR.lazard_epsilon_product
      (TV.permute_quintic_roots five_cycle roots) =
    RR.lazard_epsilon_product roots.
Proof.
rewrite /RR.lazard_epsilon_product
  !TV.tnth_permute_quintic_roots
  five_cycle_o0 five_cycle_o1 five_cycle_o2
  five_cycle_o3 five_cycle_o4.
finish_lazard_membership_descent_ring.
Qed.

Lemma lazard_epsilon_product_multiplier_two (roots : 5.-tuple F) :
  RR.lazard_epsilon_product
      (TV.permute_quintic_roots multiplier_two roots) =
    - RR.lazard_epsilon_product roots.
Proof.
rewrite /RR.lazard_epsilon_product
  !TV.tnth_permute_quintic_roots
  multiplier_two_o0 multiplier_two_o1 multiplier_two_o2
  multiplier_two_o3 multiplier_two_o4.
finish_lazard_membership_descent_ring.
Qed.

(** Scalar-extension identities for the three root expressions. *)
Lemma lazard_root_D_map (E : fieldType)
    (h : {rmorphism F -> E}) (roots : 5.-tuple F) :
  h (Q.lazard_root_D roots) = Q.lazard_root_D (map_tuple h roots).
Proof.
by rewrite /Q.lazard_root_D rmorphXn lazard_epsilon_product_map.
Qed.

Lemma lazard_root_F_map (E : fieldType)
    (h : {rmorphism F -> E}) (roots : 5.-tuple F) :
  h (Q.lazard_root_F roots) = Q.lazard_root_F (map_tuple h roots).
Proof.
by rewrite /Q.lazard_root_F rmorphN !rmorphM !rmorphD !rmorphB
  !rmorphXn lazard_epsilon_product_map
  ENZ.lazard_root_T_prime_map ENZ.lazard_root_U_prime_map.
Qed.

Lemma lazard_root_G_map (E : fieldType)
    (h : {rmorphism F -> E}) (roots : 5.-tuple F) :
  h (Q.lazard_root_G roots) = Q.lazard_root_G (map_tuple h roots).
Proof.
by rewrite /Q.lazard_root_G !rmorphM !rmorphD !rmorphB !rmorphXn
  lazard_epsilon_product_map
  ENZ.lazard_root_T_prime_map ENZ.lazard_root_U_prime_map.
Qed.

(** [D], [F], and [G] are fixed by the cyclic generator. *)
Lemma lazard_root_D_five_cycle (roots : 5.-tuple F) :
  Q.lazard_root_D (TV.permute_quintic_roots five_cycle roots) =
    Q.lazard_root_D roots.
Proof. by rewrite /Q.lazard_root_D lazard_epsilon_product_five_cycle. Qed.

Lemma lazard_root_F_five_cycle (roots : 5.-tuple F) :
  Q.lazard_root_F (TV.permute_quintic_roots five_cycle roots) =
    Q.lazard_root_F roots.
Proof.
by rewrite /Q.lazard_root_F lazard_epsilon_product_five_cycle
  ENZ.lazard_root_T_prime_five_cycle ENZ.lazard_root_U_prime_five_cycle.
Qed.

Lemma lazard_root_G_five_cycle (roots : 5.-tuple F) :
  Q.lazard_root_G (TV.permute_quintic_roots five_cycle roots) =
    Q.lazard_root_G roots.
Proof.
by rewrite /Q.lazard_root_G lazard_epsilon_product_five_cycle
  ENZ.lazard_root_T_prime_five_cycle ENZ.lazard_root_U_prime_five_cycle.
Qed.

(** They are also fixed by multiplication by two.  Here the three raw
    factors transform as [(epsilon,T',U') -> (-epsilon,U',-T')]. *)
Lemma lazard_root_D_multiplier_two (roots : 5.-tuple F) :
  Q.lazard_root_D (TV.permute_quintic_roots multiplier_two roots) =
    Q.lazard_root_D roots.
Proof.
rewrite /Q.lazard_root_D lazard_epsilon_product_multiplier_two.
finish_lazard_membership_descent_ring.
Qed.

Lemma lazard_root_F_multiplier_two (roots : 5.-tuple F) :
  Q.lazard_root_F (TV.permute_quintic_roots multiplier_two roots) =
    Q.lazard_root_F roots.
Proof.
rewrite /Q.lazard_root_F lazard_epsilon_product_multiplier_two
  ENZ.lazard_root_T_prime_multiplier_two
  ENZ.lazard_root_U_prime_multiplier_two.
finish_lazard_membership_descent_ring.
Qed.

Lemma lazard_root_G_multiplier_two (roots : 5.-tuple F) :
  Q.lazard_root_G (TV.permute_quintic_roots multiplier_two roots) =
    Q.lazard_root_G roots.
Proof.
rewrite /Q.lazard_root_G lazard_epsilon_product_multiplier_two
  ENZ.lazard_root_T_prime_multiplier_two
  ENZ.lazard_root_U_prime_multiplier_two.
finish_lazard_membership_descent_ring.
Qed.

(** Generator invariance extends uniformly to the whole standard [F20]. *)
Lemma lazard_root_function_expg (A : Type) (phi : 5.-tuple F -> A)
    (g : S5)
    (hg : forall roots : 5.-tuple F,
      phi (TV.permute_quintic_roots g roots) = phi roots)
    (n : nat) (roots : 5.-tuple F) :
  phi (TV.permute_quintic_roots (g ^+ n) roots) = phi roots.
Proof.
elim: n roots=> [|n ih] roots.
- by rewrite expg0 TV.permute_quintic_roots_one.
- rewrite expgS TV.permute_quintic_roots_mul.
  exact: eq_trans (ih _) (hg _).
Qed.

Theorem lazard_root_function_standard_F20
    (A : Type) (phi : 5.-tuple F -> A)
    (hcycle : forall roots,
      phi (TV.permute_quintic_roots five_cycle roots) = phi roots)
    (hmultiplier : forall roots,
      phi (TV.permute_quintic_roots multiplier_two roots) = phi roots)
    (roots : 5.-tuple F) (g : S5) :
  g \in standard_F20 ->
  phi (TV.permute_quintic_roots g roots) = phi roots.
Proof.
move=> hg.
have hnorm : standard_C4 \subset 'N(standard_C5).
  exact: standard_C4_sub_standard_F20.
have hjoin : (affine_F20 : {set S5}) =
    (standard_C5 * standard_C4)%g.
  exact: norm_joinEr hnorm.
have hgprod : g \in (standard_C5 * standard_C4)%g.
  by move: hg; rewrite -affine_F20E hjoin.
case/imset2P: hgprod=> u v hu hv ->.
move/cycleP: hu=> [m ->].
move/cycleP: hv=> [n ->].
rewrite TV.permute_quintic_roots_mul.
transitivity
  (phi (TV.permute_quintic_roots (multiplier_two ^+ n) roots)).
- exact: lazard_root_function_expg hcycle.
- exact: lazard_root_function_expg hmultiplier.
Qed.

Theorem lazard_root_D_standard_F20 (roots : 5.-tuple F) (g : S5) :
  g \in standard_F20 ->
  Q.lazard_root_D (TV.permute_quintic_roots g roots) =
    Q.lazard_root_D roots.
Proof.
exact: lazard_root_function_standard_F20
  lazard_root_D_five_cycle lazard_root_D_multiplier_two.
Qed.

Theorem lazard_root_F_standard_F20 (roots : 5.-tuple F) (g : S5) :
  g \in standard_F20 ->
  Q.lazard_root_F (TV.permute_quintic_roots g roots) =
    Q.lazard_root_F roots.
Proof.
exact: lazard_root_function_standard_F20
  lazard_root_F_five_cycle lazard_root_F_multiplier_two.
Qed.

Theorem lazard_root_G_standard_F20 (roots : 5.-tuple F) (g : S5) :
  g \in standard_F20 ->
  Q.lazard_root_G (TV.permute_quintic_roots g roots) =
    Q.lazard_root_G roots.
Proof.
exact: lazard_root_function_standard_F20
  lazard_root_G_five_cycle lazard_root_G_multiplier_two.
Qed.

End RootDFGInvariance.

Section DepressedCoefficientEquivariance.

Variable F : fieldType.

Add Ring lazard_depressed_membership_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_depressed_membership_ring :=
  lazard_numerator_prepare;
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** Coordinatewise scalar extension of the depressed coefficient record. *)
Definition lazard_depressed_coefficients_map (E : fieldType)
    (h : {rmorphism F -> E})
    (c : RP.LazardDepressedRootCoefficients F) :
    RP.LazardDepressedRootCoefficients E :=
  {| RP.lazard_root_p := h (RP.lazard_root_p c);
     RP.lazard_root_q := h (RP.lazard_root_q c);
     RP.lazard_root_r := h (RP.lazard_root_r c);
     RP.lazard_root_s := h (RP.lazard_root_s c) |}.

Lemma lazard_depressed_of_roots_map (E : fieldType)
    (h : {rmorphism F -> E}) (roots : 5.-tuple F) :
  lazard_depressed_coefficients_map h (RP.lazard_depressed_of_roots roots) =
    RP.lazard_depressed_of_roots (map_tuple h roots).
Proof.
apply: BE.lazard_depressed_coefficients_ext=> /=.
- by rewrite /RP.lazard_root_esymm2 !rmorphD !rmorphM !tnth_map.
- by rewrite /RP.lazard_root_esymm3 rmorphN !rmorphD !rmorphM !tnth_map.
- by rewrite /RP.lazard_root_esymm4 !rmorphD !rmorphM !tnth_map.
- by rewrite /RP.lazard_root_esymm5 rmorphN !rmorphM !tnth_map.
Qed.

(** The depressed coefficients are symmetric; checking the two [F20]
    generators is enough for the canonical descent below. *)
Lemma lazard_depressed_of_roots_five_cycle (roots : 5.-tuple F) :
  RP.lazard_depressed_of_roots
      (TV.permute_quintic_roots five_cycle roots) =
    RP.lazard_depressed_of_roots roots.
Proof.
apply: BE.lazard_depressed_coefficients_ext=> /=.
- rewrite /RP.lazard_root_esymm2
    !TV.tnth_permute_quintic_roots
    five_cycle_o0 five_cycle_o1 five_cycle_o2
    five_cycle_o3 five_cycle_o4.
  finish_lazard_depressed_membership_ring.
- rewrite /RP.lazard_root_esymm3
    !TV.tnth_permute_quintic_roots
    five_cycle_o0 five_cycle_o1 five_cycle_o2
    five_cycle_o3 five_cycle_o4.
  finish_lazard_depressed_membership_ring.
- rewrite /RP.lazard_root_esymm4
    !TV.tnth_permute_quintic_roots
    five_cycle_o0 five_cycle_o1 five_cycle_o2
    five_cycle_o3 five_cycle_o4.
  finish_lazard_depressed_membership_ring.
- rewrite /RP.lazard_root_esymm5
    !TV.tnth_permute_quintic_roots
    five_cycle_o0 five_cycle_o1 five_cycle_o2
    five_cycle_o3 five_cycle_o4.
  finish_lazard_depressed_membership_ring.
Qed.

Lemma lazard_depressed_of_roots_multiplier_two (roots : 5.-tuple F) :
  RP.lazard_depressed_of_roots
      (TV.permute_quintic_roots multiplier_two roots) =
    RP.lazard_depressed_of_roots roots.
Proof.
apply: BE.lazard_depressed_coefficients_ext=> /=.
- rewrite /RP.lazard_root_esymm2
    !TV.tnth_permute_quintic_roots
    multiplier_two_o0 multiplier_two_o1 multiplier_two_o2
    multiplier_two_o3 multiplier_two_o4.
  finish_lazard_depressed_membership_ring.
- rewrite /RP.lazard_root_esymm3
    !TV.tnth_permute_quintic_roots
    multiplier_two_o0 multiplier_two_o1 multiplier_two_o2
    multiplier_two_o3 multiplier_two_o4.
  finish_lazard_depressed_membership_ring.
- rewrite /RP.lazard_root_esymm4
    !TV.tnth_permute_quintic_roots
    multiplier_two_o0 multiplier_two_o1 multiplier_two_o2
    multiplier_two_o3 multiplier_two_o4.
  finish_lazard_depressed_membership_ring.
- rewrite /RP.lazard_root_esymm5
    !TV.tnth_permute_quintic_roots
    multiplier_two_o0 multiplier_two_o1 multiplier_two_o2
    multiplier_two_o3 multiplier_two_o4.
  finish_lazard_depressed_membership_ring.
Qed.

Theorem lazard_depressed_of_roots_standard_F20
    (roots : 5.-tuple F) (g : S5) :
  g \in standard_F20 ->
  RP.lazard_depressed_of_roots (TV.permute_quintic_roots g roots) =
    RP.lazard_depressed_of_roots roots.
Proof.
exact: lazard_root_function_standard_F20
  lazard_depressed_of_roots_five_cycle
  lazard_depressed_of_roots_multiplier_two.
Qed.

End DepressedCoefficientEquivariance.

Section BaseClosure.

Variables (F0 : fieldType) (L : fieldExtType F0).

(** The nine elementary base-membership facts from which all displayed
    coefficient expressions are built. *)
Record lazard_depressed_coefficients_in
    (B : {subfield L})
    (c : RP.LazardDepressedRootCoefficients L) : Prop :=
  LazardDepressedCoefficientsIn {
    lazard_depressed_p_in : RP.lazard_root_p c \in B;
    lazard_depressed_q_in : RP.lazard_root_q c \in B;
    lazard_depressed_r_in : RP.lazard_root_r c \in B;
    lazard_depressed_s_in : RP.lazard_root_s c \in B
  }.

Record lazard_invariant_coordinates_in
    (B : {subfield L}) (i : RP.LazardRootInvariants L) : Prop :=
  LazardInvariantCoordinatesIn {
    lazard_i4_in : RP.lazard_root_i4 i \in B;
    lazard_i5_in : RP.lazard_root_i5 i \in B;
    lazard_i6_in : RP.lazard_root_i6 i \in B;
    lazard_i7_in : RP.lazard_root_i7 i \in B;
    lazard_i8_in : RP.lazard_root_i8 i \in B
  }.

(** Recursive closure solver used only on the explicitly displayed
    polynomial expressions below. *)
Ltac solve_lazard_subfield_membership :=
  first
    [ assumption
    | apply: rpred_nat
    | apply: rpredN; solve_lazard_subfield_membership
    | apply: rpredD; solve_lazard_subfield_membership
    | apply: rpredB; solve_lazard_subfield_membership
    | apply: rpredM; solve_lazard_subfield_membership
    | apply: rpredX; solve_lazard_subfield_membership ].

(** Once [D], [F], and [G] have been descended, the other five radical
    invariants are automatic closure consequences. *)
Theorem lazard_radical_invariant_data_in_of_coordinates
    (B : {subfield L})
    (c : RP.LazardDepressedRootCoefficients L)
    (i : RP.LazardRootInvariants L) (D Finvariant G : L)
    (hD : D \in B) (hF : Finvariant \in B) (hG : G \in B)
    (hc : lazard_depressed_coefficients_in B c)
    (hi : lazard_invariant_coordinates_in B i) :
  @CRT.lazard_radical_invariant_data_in F0 L B c i
    D Finvariant G (RP.lazard_root_invariant_H c i)
    (RP.lazard_root_invariant_I c i)
    (RJK.lazard_root_invariant_J c i)
    (RJK.lazard_root_invariant_K c i).
Proof.
case: hc=> hp hq hr hs.
case: hi=> hi4 hi5 hi6 hi7 hi8.
constructor.
- exact: hD.
- rewrite /FN.lazard_invariant_E.
  solve_lazard_subfield_membership.
- exact: hF.
- exact: hG.
- rewrite /RP.lazard_root_invariant_H.
  solve_lazard_subfield_membership.
- rewrite /RP.lazard_root_invariant_I.
  solve_lazard_subfield_membership.
- rewrite /RJK.lazard_root_invariant_J.
  solve_lazard_subfield_membership.
- rewrite /RJK.lazard_root_invariant_K.
  solve_lazard_subfield_membership.
Qed.

(** All ten Fourier numerators are automatic from the same nine coordinate
    membership facts; no root or radical datum occurs in this proof. *)
Theorem lazard_fourier_numerator_data_in_of_coordinates
    (B : {subfield L})
    (c : RP.LazardDepressedRootCoefficients L)
    (i : RP.LazardRootInvariants L)
    (hc : lazard_depressed_coefficients_in B c)
    (hi : lazard_invariant_coordinates_in B i) :
  @CRT.lazard_fourier_numerator_data_in F0 L B c i.
Proof.
case: hc=> hp hq hr hs.
case: hi=> hi4 hi5 hi6 hi7 hi8.
constructor.
- rewrite /FN.lazard_p41.
  solve_lazard_subfield_membership.
- rewrite /FN.lazard_p42.
  solve_lazard_subfield_membership.
- rewrite /FN.lazard_p31.
  solve_lazard_subfield_membership.
- rewrite /FN.lazard_p32.
  solve_lazard_subfield_membership.
- rewrite /FN.lazard_p33.
  solve_lazard_subfield_membership.
- rewrite /FN.lazard_p34.
  solve_lazard_subfield_membership.
- rewrite /FN.lazard_p21.
  solve_lazard_subfield_membership.
- rewrite /FN.lazard_p22.
  solve_lazard_subfield_membership.
- rewrite /FN.lazard_p23.
  solve_lazard_subfield_membership.
- rewrite /FN.lazard_p24.
  solve_lazard_subfield_membership.
Qed.

End BaseClosure.

Section CanonicalMembership.

Variable f : QRF.monic_quintic.
Let p := CD.rational_monic_quintic f.
Let p_size : size p = 6%N := CD.size_rational_monic_quintic f.
Let L := numfield p.
Let ratrL : {rmorphism rat -> L} := char0_ratr (char_numfield p).
Let roots : 5.-tuple L := @GA.quintic_root_tuple p p_size.
Let ordered (i : 'I_6) : 5.-tuple L :=
  RC.lazard_centered_roots (ID.lazard_selected_roots i).

(** Every rational scalar belongs to every subfield of the canonical
    number field. *)
Lemma lazard_ratr_mem_subfield (B : {subfield L}) (a : rat) :
  ratrL a \in B.
Proof.
by rewrite /ratrL char0_ratrE -alg_num_field rpredZ ?mem1v.
Qed.

(** The centered depressed coefficient record is fixed by the complete
    canonical Galois action. *)
Lemma lazard_centered_selected_depressed_fixed
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q)
    (sigma : gal_of {:L}) :
  lazard_depressed_coefficients_map sigma
      (RP.lazard_depressed_of_roots (ordered i)) =
    RP.lazard_depressed_of_roots (ordered i).
Proof.
rewrite /ordered lazard_depressed_of_roots_map
  RC.lazard_centered_selected_roots_gal.
exact: lazard_depressed_of_roots_standard_F20
  (ID.lazard_selected_gal_perm_mem_standard_F20 p_irr hi sigma).
Qed.

(** Coefficient descent in the same bundled form already used for the five
    metacyclic invariants. *)
Theorem exists_rational_centered_depressed_coefficients_of_selected_root
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q) :
  exists c0 : RP.LazardDepressedRootCoefficients rat,
    lazard_depressed_coefficients_map ratrL c0 =
      RP.lazard_depressed_of_roots (ordered i).
Proof.
pose c := RP.lazard_depressed_of_roots (ordered i).
have hfixedp : forall sigma : gal_of {:L},
    sigma \in 'Gal({:L} / 1%AS)%G ->
    sigma (RP.lazard_root_p c) = RP.lazard_root_p c.
  move=> sigma _.
  have h := congr1 RP.lazard_root_p
    (lazard_centered_selected_depressed_fixed p_irr hi sigma).
  exact: h.
have hfixedq : forall sigma : gal_of {:L},
    sigma \in 'Gal({:L} / 1%AS)%G ->
    sigma (RP.lazard_root_q c) = RP.lazard_root_q c.
  move=> sigma _.
  have h := congr1 RP.lazard_root_q
    (lazard_centered_selected_depressed_fixed p_irr hi sigma).
  exact: h.
have hfixedr : forall sigma : gal_of {:L},
    sigma \in 'Gal({:L} / 1%AS)%G ->
    sigma (RP.lazard_root_r c) = RP.lazard_root_r c.
  move=> sigma _.
  have h := congr1 RP.lazard_root_r
    (lazard_centered_selected_depressed_fixed p_irr hi sigma).
  exact: h.
have hfixeds : forall sigma : gal_of {:L},
    sigma \in 'Gal({:L} / 1%AS)%G ->
    sigma (RP.lazard_root_s c) = RP.lazard_root_s c.
  move=> sigma _.
  have h := congr1 RP.lazard_root_s
    (lazard_centered_selected_depressed_fixed p_irr hi sigma).
  exact: h.
have [cp hcp] := @ID.lazard_numfield_fixed_is_rational p
  (RP.lazard_root_p c) hfixedp.
have [cq hcq] := @ID.lazard_numfield_fixed_is_rational p
  (RP.lazard_root_q c) hfixedq.
have [cr hcr] := @ID.lazard_numfield_fixed_is_rational p
  (RP.lazard_root_r c) hfixedr.
have [cs hcs] := @ID.lazard_numfield_fixed_is_rational p
  (RP.lazard_root_s c) hfixeds.
exists {| RP.lazard_root_p := cp;
          RP.lazard_root_q := cq;
          RP.lazard_root_r := cr;
          RP.lazard_root_s := cs |}.
apply: BE.lazard_depressed_coefficients_ext=> /=;
  first [exact: esym hcp | exact: esym hcq |
         exact: esym hcr | exact: esym hcs].
Qed.

(** The four depressed coefficients automatically belong to any chosen
    base subfield. *)
Theorem lazard_centered_selected_depressed_coefficients_in
    (B : {subfield L})
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q) :
  lazard_depressed_coefficients_in B
    (RP.lazard_depressed_of_roots (ordered i)).
Proof.
have [c0 hc0] :=
  exists_rational_centered_depressed_coefficients_of_selected_root p_irr hi.
have hp : ratrL (RP.lazard_root_p c0) =
    RP.lazard_root_p (RP.lazard_depressed_of_roots (ordered i)).
  exact: congr1 RP.lazard_root_p hc0.
have hq : ratrL (RP.lazard_root_q c0) =
    RP.lazard_root_q (RP.lazard_depressed_of_roots (ordered i)).
  exact: congr1 RP.lazard_root_q hc0.
have hr : ratrL (RP.lazard_root_r c0) =
    RP.lazard_root_r (RP.lazard_depressed_of_roots (ordered i)).
  exact: congr1 RP.lazard_root_r hc0.
have hs : ratrL (RP.lazard_root_s c0) =
    RP.lazard_root_s (RP.lazard_depressed_of_roots (ordered i)).
  exact: congr1 RP.lazard_root_s hc0.
constructor.
- rewrite -hp; exact: lazard_ratr_mem_subfield.
- rewrite -hq; exact: lazard_ratr_mem_subfield.
- rewrite -hr; exact: lazard_ratr_mem_subfield.
- rewrite -hs; exact: lazard_ratr_mem_subfield.
Qed.

(** The existing simultaneous invariant descent immediately gives the five
    coordinate membership facts. *)
Theorem lazard_centered_selected_invariant_coordinates_in
    (B : {subfield L})
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q) :
  lazard_invariant_coordinates_in B
    (RP.lazard_root_invariants (ordered i)).
Proof.
have [j hj] :=
  RC.exists_rational_centered_lazard_invariants_of_selected_root p_irr hi.
have h4 : ratrL (RP.lazard_root_i4 j) =
    RP.lazard_root_i4 (RP.lazard_root_invariants (ordered i)).
  exact: congr1 RP.lazard_root_i4 hj.
have h5 : ratrL (RP.lazard_root_i5 j) =
    RP.lazard_root_i5 (RP.lazard_root_invariants (ordered i)).
  exact: congr1 RP.lazard_root_i5 hj.
have h6 : ratrL (RP.lazard_root_i6 j) =
    RP.lazard_root_i6 (RP.lazard_root_invariants (ordered i)).
  exact: congr1 RP.lazard_root_i6 hj.
have h7 : ratrL (RP.lazard_root_i7 j) =
    RP.lazard_root_i7 (RP.lazard_root_invariants (ordered i)).
  exact: congr1 RP.lazard_root_i7 hj.
have h8 : ratrL (RP.lazard_root_i8 j) =
    RP.lazard_root_i8 (RP.lazard_root_invariants (ordered i)).
  exact: congr1 RP.lazard_root_i8 hj.
constructor.
- rewrite -h4; exact: lazard_ratr_mem_subfield.
- rewrite -h5; exact: lazard_ratr_mem_subfield.
- rewrite -h6; exact: lazard_ratr_mem_subfield.
- rewrite -h7; exact: lazard_ratr_mem_subfield.
- rewrite -h8; exact: lazard_ratr_mem_subfield.
Qed.

(** The three genuinely root-defined invariant expressions are fixed by
    Galois because their relabelling action lies in the selected [F20]. *)
Lemma lazard_centered_selected_root_D_fixed
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q)
    (sigma : gal_of {:L}) :
  sigma (Q.lazard_root_D (ordered i)) = Q.lazard_root_D (ordered i).
Proof.
rewrite /ordered lazard_root_D_map
  RC.lazard_centered_selected_roots_gal.
exact: lazard_root_D_standard_F20
  (ID.lazard_selected_gal_perm_mem_standard_F20 p_irr hi sigma).
Qed.

Lemma lazard_centered_selected_root_F_fixed
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q)
    (sigma : gal_of {:L}) :
  sigma (Q.lazard_root_F (ordered i)) = Q.lazard_root_F (ordered i).
Proof.
rewrite /ordered lazard_root_F_map
  RC.lazard_centered_selected_roots_gal.
exact: lazard_root_F_standard_F20
  (ID.lazard_selected_gal_perm_mem_standard_F20 p_irr hi sigma).
Qed.

Lemma lazard_centered_selected_root_G_fixed
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q)
    (sigma : gal_of {:L}) :
  sigma (Q.lazard_root_G (ordered i)) = Q.lazard_root_G (ordered i).
Proof.
rewrite /ordered lazard_root_G_map
  RC.lazard_centered_selected_roots_gal.
exact: lazard_root_G_standard_F20
  (ID.lazard_selected_gal_perm_mem_standard_F20 p_irr hi sigma).
Qed.

Lemma lazard_galois_fixed_mem_subfield
    (B : {subfield L}) (z : L)
    (hfixed : forall sigma : gal_of {:L},
      sigma \in 'Gal({:L} / 1%AS)%G -> sigma z = z) :
  z \in B.
Proof.
have [a ha] := @ID.lazard_numfield_fixed_is_rational p z hfixed.
rewrite ha.
exact: lazard_ratr_mem_subfield.
Qed.

Theorem lazard_centered_selected_root_D_in
    (B : {subfield L})
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q) :
  Q.lazard_root_D (ordered i) \in B.
Proof.
apply: lazard_galois_fixed_mem_subfield=> sigma _.
exact: lazard_centered_selected_root_D_fixed p_irr hi sigma.
Qed.

Theorem lazard_centered_selected_root_F_in
    (B : {subfield L})
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q) :
  Q.lazard_root_F (ordered i) \in B.
Proof.
apply: lazard_galois_fixed_mem_subfield=> sigma _.
exact: lazard_centered_selected_root_F_fixed p_irr hi sigma.
Qed.

Theorem lazard_centered_selected_root_G_in
    (B : {subfield L})
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q) :
  Q.lazard_root_G (ordered i) \in B.
Proof.
apply: lazard_galois_fixed_mem_subfield=> sigma _.
exact: lazard_centered_selected_root_G_fixed p_irr hi sigma.
Qed.

(** The two formerly supplied membership packages are now derived from the
    canonical rational resolvent witness alone.  The result is stated for an
    arbitrary subfield [B], hence specializes in particular to the rational
    bottom field [1%AS]. *)
Theorem lazard_centered_selected_root_membership_data
    (B : {subfield L})
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q) :
  RRC.lazard_root_radical_invariant_data_in B (ordered i) /\
  RRC.lazard_root_fourier_numerator_data_in B (ordered i).
Proof.
have hc := lazard_centered_selected_depressed_coefficients_in B p_irr hi.
have hinv := lazard_centered_selected_invariant_coordinates_in B p_irr hi.
have hD := lazard_centered_selected_root_D_in B p_irr hi.
have hF := lazard_centered_selected_root_F_in B p_irr hi.
have hG := lazard_centered_selected_root_G_in B p_irr hi.
split.
- rewrite /RRC.lazard_root_radical_invariant_data_in
    /RRC.lazard_root_H /RRC.lazard_root_I
    /RRC.lazard_root_J /RRC.lazard_root_K.
  exact: lazard_radical_invariant_data_in_of_coordinates
    hD hF hG hc hinv.
- rewrite /RRC.lazard_root_fourier_numerator_data_in.
  exact: lazard_fourier_numerator_data_in_of_coordinates hc hinv.
Qed.

Corollary lazard_centered_selected_root_membership_data_bot
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q) :
  RRC.lazard_root_radical_invariant_data_in
      (1%AS : {subfield L}) (ordered i) /\
  RRC.lazard_root_fourier_numerator_data_in
      (1%AS : {subfield L}) (ordered i).
Proof.
exact: lazard_centered_selected_root_membership_data p_irr hi.
Qed.

(** A rational root of the scalar resolvent supplies the selected index as
    well, so neither membership package nor an ordering certificate is an
    input to this wrapper. *)
Theorem exists_canonical_centered_root_membership_data
    (p_irr : irreducible_poly p) (q : rat)
    (hq : root (TV.quintic_scalar_resolvent roots) (ratrL q)) :
  exists (i : 'I_6) (ordered0 : 5.-tuple L),
    ordered0 = RC.lazard_centered_roots (ID.lazard_selected_roots i) /\
    RRC.lazard_root_radical_invariant_data_in
      (1%AS : {subfield L}) ordered0 /\
    RRC.lazard_root_fourier_numerator_data_in
      (1%AS : {subfield L}) ordered0.
Proof.
have [i hi] :=
  (proj1 (TV.quintic_scalar_resolvent_root_iff roots (ratrL q))) hq.
have hdata := lazard_centered_selected_root_membership_data_bot p_irr hi.
exists i, (ordered i).
split; first exact: erefl.
exact: hdata.
Qed.

End CanonicalMembership.

End PolynomialFormulasLazardQuinticRootMembershipDescent.
