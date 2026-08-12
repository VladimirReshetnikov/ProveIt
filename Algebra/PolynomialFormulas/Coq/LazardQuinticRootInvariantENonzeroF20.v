From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import map_gal char0 abel.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticGaloisAction
  QuinticRecursiveFactor QuinticCanonicalDecision
  LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticQuadratic LazardQuinticFourierNumerators
  LazardQuinticRootInvariantE
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticInvariantDescentF20.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Nonvanishing of Lazard's root-defined invariant [E] for the canonical
    [F20]-ordering.

    The argument is the one on p. 216 of Lazard's paper.  If

      [T'^2 + U'^2 = 0],

    then [T'/U'] is unchanged by the two generators of the standard
    Frobenius group.  Hence it is fixed by every splitting-field
    automorphism of the selected ordering, so it descends to a rational
    number.  Its square would be [-1], which is impossible over [rat].

    In particular, no separate [E != 0] certificate occurs in the public
    selected-root theorem below. *)
Module PolynomialFormulasLazardQuinticRootInvariantENonzeroF20.

Import GRing.Theory.
Import Num.Theory.
Import PolynomialFormulasQuinticF20Data.
Module TV := PolynomialFormulasQuinticThetaValues.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module RIE := PolynomialFormulasLazardQuinticRootInvariantE.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.

Section CyclicRatio.

Variable F : fieldType.

Add Ring lazard_root_E_nonzero_f20_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_root_E_nonzero_f20_ring :=
  repeat first
    [ rewrite NR.lazard_numerator_ring_addE
    | rewrite NR.lazard_numerator_ring_mulE
    | rewrite NR.lazard_numerator_ring_subE
    | rewrite NR.lazard_numerator_ring_oppE
    | rewrite NR.lazard_numerator_ring_zeroE
    | rewrite NR.lazard_numerator_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** The quotient used in the fixed-field argument. *)
Definition lazard_root_cyclic_ratio (roots : 5.-tuple F) : F :=
  RR.lazard_root_T_prime roots / RR.lazard_root_U_prime roots.

Lemma lazard_permute_quintic_roots_injective (roots : 5.-tuple F)
    (g : S5) :
  injective (tnth roots) ->
  injective (tnth (TV.permute_quintic_roots g roots)).
Proof.
move=> hroots i j.
rewrite !TV.tnth_permute_quintic_roots=> hij.
apply: perm_inj.
exact: hroots hij.
Qed.

Lemma lazard_root_T_prime_map (E : fieldType)
    (h : {rmorphism F -> E}) (roots : 5.-tuple F) :
  h (RR.lazard_root_T_prime roots) =
    RR.lazard_root_T_prime (map_tuple h roots).
Proof.
by rewrite /RR.lazard_root_T_prime
  !rmorphM !rmorphB !tnth_map.
Qed.

Lemma lazard_root_U_prime_map (E : fieldType)
    (h : {rmorphism F -> E}) (roots : 5.-tuple F) :
  h (RR.lazard_root_U_prime roots) =
    RR.lazard_root_U_prime (map_tuple h roots).
Proof.
by rewrite /RR.lazard_root_U_prime
  !rmorphM !rmorphB !tnth_map.
Qed.

(** The five-cycle fixes both cyclic difference products. *)
Lemma lazard_root_T_prime_five_cycle (roots : 5.-tuple F) :
  RR.lazard_root_T_prime
      (TV.permute_quintic_roots five_cycle roots) =
    RR.lazard_root_T_prime roots.
Proof.
rewrite /RR.lazard_root_T_prime
  !TV.tnth_permute_quintic_roots
  five_cycle_o0 five_cycle_o1 five_cycle_o2
  five_cycle_o3 five_cycle_o4.
finish_lazard_root_E_nonzero_f20_ring.
Qed.

Lemma lazard_root_U_prime_five_cycle (roots : 5.-tuple F) :
  RR.lazard_root_U_prime
      (TV.permute_quintic_roots five_cycle roots) =
    RR.lazard_root_U_prime roots.
Proof.
rewrite /RR.lazard_root_U_prime
  !TV.tnth_permute_quintic_roots
  five_cycle_o0 five_cycle_o1 five_cycle_o2
  five_cycle_o3 five_cycle_o4.
finish_lazard_root_E_nonzero_f20_ring.
Qed.

Lemma lazard_root_cyclic_ratio_five_cycle (roots : 5.-tuple F) :
  lazard_root_cyclic_ratio
      (TV.permute_quintic_roots five_cycle roots) =
    lazard_root_cyclic_ratio roots.
Proof.
by rewrite /lazard_root_cyclic_ratio
  lazard_root_T_prime_five_cycle lazard_root_U_prime_five_cycle.
Qed.

(** Multiplication by two sends [(T', U')] to [(U', -T')]. *)
Lemma lazard_root_T_prime_multiplier_two (roots : 5.-tuple F) :
  RR.lazard_root_T_prime
      (TV.permute_quintic_roots multiplier_two roots) =
    RR.lazard_root_U_prime roots.
Proof.
rewrite /RR.lazard_root_T_prime /RR.lazard_root_U_prime
  !TV.tnth_permute_quintic_roots
  multiplier_two_o0 multiplier_two_o1 multiplier_two_o2
  multiplier_two_o3 multiplier_two_o4.
finish_lazard_root_E_nonzero_f20_ring.
Qed.

Lemma lazard_root_U_prime_multiplier_two (roots : 5.-tuple F) :
  RR.lazard_root_U_prime
      (TV.permute_quintic_roots multiplier_two roots) =
    - RR.lazard_root_T_prime roots.
Proof.
rewrite /RR.lazard_root_T_prime /RR.lazard_root_U_prime
  !TV.tnth_permute_quintic_roots
  multiplier_two_o0 multiplier_two_o1 multiplier_two_o2
  multiplier_two_o3 multiplier_two_o4.
have h04 : tnth roots o0 - tnth roots o4 =
    - (tnth roots o4 - tnth roots o0) by rewrite opprB.
have h21 : tnth roots o2 - tnth roots o1 =
    - (tnth roots o1 - tnth roots o2) by rewrite opprB.
have h43 : tnth roots o4 - tnth roots o3 =
    - (tnth roots o3 - tnth roots o4) by rewrite opprB.
have h10 : tnth roots o1 - tnth roots o0 =
    - (tnth roots o0 - tnth roots o1) by rewrite opprB.
have h32 : tnth roots o3 - tnth roots o2 =
    - (tnth roots o2 - tnth roots o3) by rewrite opprB.
rewrite h04 h21 h43 h10 h32.
finish_lazard_root_E_nonzero_f20_ring.
Qed.

Lemma lazard_root_cyclic_sum_sq_multiplier_two
    (roots : 5.-tuple F) :
  RR.lazard_root_T_prime
      (TV.permute_quintic_roots multiplier_two roots) ^+ 2 +
    RR.lazard_root_U_prime
      (TV.permute_quintic_roots multiplier_two roots) ^+ 2 =
  RR.lazard_root_T_prime roots ^+ 2 +
    RR.lazard_root_U_prime roots ^+ 2.
Proof.
rewrite lazard_root_T_prime_multiplier_two
  lazard_root_U_prime_multiplier_two.
rewrite !expr2.
finish_lazard_root_E_nonzero_f20_ring.
Qed.

(** Under the temporary zero-sum-of-squares assumption, the multiplier-two
    generator fixes the quotient [T'/U']. *)
Lemma lazard_root_cyclic_ratio_multiplier_two
    (roots : 5.-tuple F) (hroots : injective (tnth roots))
    (hzero : RR.lazard_root_T_prime roots ^+ 2 +
      RR.lazard_root_U_prime roots ^+ 2 = 0) :
  lazard_root_cyclic_ratio
      (TV.permute_quintic_roots multiplier_two roots) =
    lazard_root_cyclic_ratio roots.
Proof.
have hT := RR.lazard_root_T_prime_neq0 hroots.
have hU := RR.lazard_root_U_prime_neq0 hroots.
have hNT : - RR.lazard_root_T_prime roots != 0.
  by rewrite oppr_eq0.
rewrite /lazard_root_cyclic_ratio
  lazard_root_T_prime_multiplier_two
  lazard_root_U_prime_multiplier_two.
apply/eqP.
rewrite (@eqr_div F
  (RR.lazard_root_U_prime roots)
  (- RR.lazard_root_T_prime roots)
  (RR.lazard_root_T_prime roots)
  (RR.lazard_root_U_prime roots)
  hNT hU) -subr_eq0.
have hid :
    RR.lazard_root_U_prime roots * RR.lazard_root_U_prime roots -
      RR.lazard_root_T_prime roots *
        (- RR.lazard_root_T_prime roots) =
      RR.lazard_root_T_prime roots ^+ 2 +
      RR.lazard_root_U_prime roots ^+ 2.
  rewrite !expr2.
  finish_lazard_root_E_nonzero_f20_ring.
by rewrite hid hzero eqxx.
Qed.

Lemma lazard_root_cyclic_ratio_five_cycle_expg
    (n : nat) (roots : 5.-tuple F) :
  lazard_root_cyclic_ratio
      (TV.permute_quintic_roots (five_cycle ^+ n) roots) =
    lazard_root_cyclic_ratio roots.
Proof.
elim: n roots=> [|n ih] roots.
- by rewrite expg0 TV.permute_quintic_roots_one.
- rewrite expgSr TV.permute_quintic_roots_mul ih.
  exact: lazard_root_cyclic_ratio_five_cycle.
Qed.

Lemma lazard_root_cyclic_ratio_multiplier_two_expg
    (n : nat) (roots : 5.-tuple F)
    (hroots : injective (tnth roots))
    (hzero : RR.lazard_root_T_prime roots ^+ 2 +
      RR.lazard_root_U_prime roots ^+ 2 = 0) :
  lazard_root_cyclic_ratio
      (TV.permute_quintic_roots (multiplier_two ^+ n) roots) =
    lazard_root_cyclic_ratio roots.
Proof.
elim: n roots hroots hzero=> [|n ih] roots hroots hzero.
- by rewrite expg0 TV.permute_quintic_roots_one.
- rewrite expgSr TV.permute_quintic_roots_mul.
  pose roots' := TV.permute_quintic_roots multiplier_two roots.
  have hroots' : injective (tnth roots').
    exact: lazard_permute_quintic_roots_injective hroots.
  have hzero' :
      RR.lazard_root_T_prime roots' ^+ 2 +
        RR.lazard_root_U_prime roots' ^+ 2 = 0.
    rewrite /roots' lazard_root_cyclic_sum_sq_multiplier_two.
    exact: hzero.
  rewrite (ih roots' hroots' hzero').
  exact: lazard_root_cyclic_ratio_multiplier_two hroots hzero.
Qed.

(** The quotient is fixed by every element of the standard [F20], derived
    solely from the two explicit generator calculations. *)
Theorem lazard_root_cyclic_ratio_standard_F20
    (roots : 5.-tuple F) (hroots : injective (tnth roots))
    (hzero : RR.lazard_root_T_prime roots ^+ 2 +
      RR.lazard_root_U_prime roots ^+ 2 = 0)
    (g : S5) : g \in standard_F20 ->
  lazard_root_cyclic_ratio (TV.permute_quintic_roots g roots) =
    lazard_root_cyclic_ratio roots.
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
rewrite TV.permute_quintic_roots_mul
  lazard_root_cyclic_ratio_five_cycle_expg.
exact: lazard_root_cyclic_ratio_multiplier_two_expg hroots hzero.
Qed.

End CyclicRatio.

Section CyclicRatioMap.

Variables (F E : fieldType).

(** The cyclic quotient commutes with field embeddings.  This statement is
    placed after [CyclicRatio] so both its source and target field arguments
    are generalized, rather than fixing the section's source field twice. *)
Lemma lazard_root_cyclic_ratio_map
    (h : {rmorphism F -> E}) (roots : 5.-tuple F) :
  h (@lazard_root_cyclic_ratio F roots) =
    @lazard_root_cyclic_ratio E (map_tuple h roots).
Proof.
by rewrite /lazard_root_cyclic_ratio fmorph_div
  lazard_root_T_prime_map lazard_root_U_prime_map.
Qed.

End CyclicRatioMap.

(* The remainder uses Galois groups only through explicitly scoped [%G]
   notation.  Keeping the action and group scopes open here makes standalone
   field quotients and powers elaborate as group/action operations. *)
Local Close Scope action_scope.
Local Close Scope group_scope.

Section FixedRatio.

Variable p : {poly rat}.
Let L := numfield p.
Let ratrL : {rmorphism rat -> L} := char0_ratr (char_numfield p).

(** A Galois-fixed quotient in a rational number field cannot square to
    [-1].  This is the fixed-field core, separated from the [F20] action. *)
Theorem lazard_sq_add_sq_neq0_of_galois_fixed_ratio
    (a b : L) (hb : b != 0)
    (hfixed : forall g : gal_of {:L},
      g \in 'Gal({:L} / 1%AS)%G ->
      (gal_repr g : {rmorphism L -> L}) ((a / b)%R) = (a / b)%R) :
  a ^+ 2 + b ^+ 2 != 0.
Proof.
apply/eqP=> hzero.
have [q hq] :=
  @ID.lazard_numfield_fixed_is_rational p ((a / b)%R) hfixed.
have hb2 : b ^+ 2 != 0 by exact: expf_neq0 2 hb.
have hratio : (a / b)%R ^+ 2 = - 1.
  rewrite expr_div_n.
  apply/eqP.
  rewrite -[(- 1 : L)]divr1
    (@eqr_div L (a ^+ 2) (b ^+ 2) (- 1) 1 hb2 (oner_neq0 L))
    mulr1 mulN1r -addr_eq0.
  apply/eqP.
  exact: hzero.
have hmapped : ratrL (q ^+ 2) = ratrL (- 1).
  rewrite rmorphXn rmorphN rmorph1 -hq.
  exact: hratio.
have hq2 : q ^+ 2 = - 1.
  exact: (fmorph_inj ratrL) hmapped.
have hge : (0 : rat) <= q ^+ 2 by exact: sqr_ge0 q.
by move: hge; rewrite hq2 ler0N1.
Qed.

(** Root tuples whose Galois action is through the standard [F20] have
    nonzero cyclic sum [T'^2 + U'^2]. *)
Theorem lazard_root_cyclic_sum_sq_neq0_of_standard_F20_action
    (roots : 5.-tuple L) (hroots : injective (tnth roots))
    (hgal : forall sigma : gal_of {:L}, exists g : S5,
      g \in standard_F20 /\
      map_tuple (gal_repr sigma : {rmorphism L -> L}) roots =
        TV.permute_quintic_roots g roots) :
  RR.lazard_root_T_prime roots ^+ 2 +
    RR.lazard_root_U_prime roots ^+ 2 != 0.
Proof.
apply/eqP=> hzero.
have hfixed : forall sigma : gal_of {:L},
    sigma \in 'Gal({:L} / 1%AS)%G ->
    (gal_repr sigma : {rmorphism L -> L})
      (lazard_root_cyclic_ratio roots) =
      lazard_root_cyclic_ratio roots.
  move=> sigma _.
  have [g [hg haction]] := hgal sigma.
  rewrite lazard_root_cyclic_ratio_map haction.
  exact: (@lazard_root_cyclic_ratio_standard_F20
    L roots hroots hzero g hg).
have hne := @lazard_sq_add_sq_neq0_of_galois_fixed_ratio
  (RR.lazard_root_T_prime roots) (RR.lazard_root_U_prime roots)
  (RR.lazard_root_U_prime_neq0 hroots) hfixed.
by move: hne; rewrite hzero eqxx.
Qed.

End FixedRatio.

Section CanonicalSelectedRoots.

Variable f : QRF.monic_quintic.
Let p := CD.rational_monic_quintic f.
Let p_size : size p = 6%N := CD.size_rational_monic_quintic f.
Let L := numfield p.
Let ratrL : {rmorphism rat -> L} := char0_ratr (char_numfield p).
Let roots : 5.-tuple L := @GA.quintic_root_tuple p p_size.

(** The selected ordering has nonzero [T'^2 + U'^2], with no nonzero
    certificate among the hypotheses. *)
Theorem lazard_selected_root_cyclic_sum_sq_neq0
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q) :
  RR.lazard_root_T_prime (ID.lazard_selected_roots f i) ^+ 2 +
    RR.lazard_root_U_prime (ID.lazard_selected_roots f i) ^+ 2 != 0.
Proof.
apply: (@lazard_root_cyclic_sum_sq_neq0_of_standard_F20_action p
  (ID.lazard_selected_roots f i)).
- exact: lazard_permute_quintic_roots_injective
    (@GA.quintic_root_tuple_injective p p_size p_irr).
- move=> sigma.
  exists (((@GA.quintic_gal_perm p p_size sigma) ^ representative i)%g).
  split.
  + exact: (@ID.lazard_selected_gal_perm_mem_standard_F20
      f p_irr i q hi sigma).
  + exact: (@ID.lazard_selected_roots_gal f i sigma).
Qed.

(** Therefore Lazard's root-defined [E = -(T'^2+U'^2)] is nonzero for
    the canonical [F20]-ordered roots. *)
Theorem lazard_selected_root_E_neq0
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q) :
  Q.lazard_root_E (ID.lazard_selected_roots f i) != 0.
Proof.
rewrite /Q.lazard_root_E oppr_eq0.
exact: (@lazard_selected_root_cyclic_sum_sq_neq0 p_irr i q hi).
Qed.

(** The same result in the displayed coefficient/invariant normalization.
    The sole extra premise is the depressed-root relation needed to identify
    that displayed polynomial with the root expression; nonvanishing itself
    is still derived rather than supplied. *)
Theorem lazard_selected_invariant_E_neq0
    (p_irr : irreducible_poly p) (i : 'I_6) (q : rat)
    (hi : TV.quintic_theta_value roots i = ratrL q)
    (hsum : RP.lazard_root_esymm1 (ID.lazard_selected_roots f i) = 0) :
  FN.lazard_invariant_E
      (RP.lazard_depressed_of_roots (ID.lazard_selected_roots f i))
      (RP.lazard_root_invariants (ID.lazard_selected_roots f i)) != 0.
Proof.
rewrite (RIE.lazard_root_invariant_E_eq hsum).
exact: (@lazard_selected_root_E_neq0 p_irr i q hi).
Qed.

End CanonicalSelectedRoots.

End PolynomialFormulasLazardQuinticRootInvariantENonzeroF20.
