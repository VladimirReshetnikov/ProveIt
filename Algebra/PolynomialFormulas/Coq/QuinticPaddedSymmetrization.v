From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticRecursiveFactor
  SexticSparsePolynomials SexticSparseResolvents
  SexticPowerSumSymmetric SexticNewtonPowerSums SexticResolventSymmetry
  SexticComputedResolvents.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A six-variable, executable presentation of the scalar Dummit resolvent.
    The sixth variable is deliberately unused.  Multiplication by the first
    five variables then turns six-variable Reynolds symmetrization into a
    five-variable symmetrization after the sixth root is set to zero. *)
Module PolynomialFormulasQuinticPaddedSymmetrization.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasQuinticThetaValues.
Import PolynomialFormulasQuinticRecursiveFactor.
Import PolynomialFormulasSexticSparsePolynomials.
Import PolynomialFormulasSexticSparseResolvents.
Import PolynomialFormulasSexticPowerSumSymmetric.
Import PolynomialFormulasSexticNewtonPowerSums.
Import PolynomialFormulasSexticResolventSymmetry.
Import PolynomialFormulasSexticComputedResolvents.

Local Open Scope ring_scope.
Local Open Scope group_scope.

Definition pad_quintic_exponent (d : quintic_exponent) : sparse_exponent :=
  [tuple if i == ord_max then 0%N else tnth d (inord i) | i < 6].

Definition quintic_sparse_monomial (d : quintic_exponent) :
    sparse_polynomial :=
  ([:: (1%Z, pad_quintic_exponent d)] : sparse_polynomial).

Definition quintic_sparse_table (table : seq quintic_exponent) :
    sparse_polynomial :=
  flatten (map quintic_sparse_monomial table).

Definition quintic_sparse_theta (i : 'I_6) : sparse_polynomial :=
  quintic_sparse_table
    (theta_table_image ((representative i)^-1)).

Definition quintic_sparse_theta_list : seq sparse_polynomial :=
  [seq quintic_sparse_theta i | i <- enum 'I_6].

(** Ascending coefficient list of the product over the six sparse theta
    values. *)
Definition quintic_sparse_resolvent : coefficient_list :=
  linear_product quintic_sparse_theta_list.

Definition quintic_sparse_resolvent_coefficient (i : 'I_7) :
    sparse_polynomial :=
  nth sparse_zero quintic_sparse_resolvent i.

Definition first_five_product : sparse_polynomial :=
  sparse_product [seq sparse_var (inord i) | i <- iota 0 5].

Definition weighted_quintic_coefficient (i : 'I_7) : sparse_polynomial :=
  sparse_mul first_five_product (quintic_sparse_resolvent_coefficient i).

Definition symmetrized_weighted_quintic_coefficient (i : 'I_7) :
    sparse_polynomial :=
  newton_symmetrize (weighted_quintic_coefficient i).

(** A fully executable integer coefficient list.  The quintic is embedded
    as [X * f], so its sixth root is zero and the six Vieta coordinates are
    exactly those expected by the padded symmetrization. *)
Definition quintic_scaled_resolvent_coefficient
    (f : monic_quintic) (i : 'I_7) : int :=
  sparse_eval_ring (R := int)
    (monic_elementary_values (quintic_sextic_embedding f))
    (symmetrized_weighted_quintic_coefficient i).

Definition quintic_scaled_resolvent (f : monic_quintic) : seq int :=
  [seq quintic_scaled_resolvent_coefficient f i | i <- enum 'I_7].

Lemma size_quintic_scaled_resolvent f :
  size (quintic_scaled_resolvent f) = 7%N.
Proof. by rewrite /quintic_scaled_resolvent size_map size_enum_ord. Qed.

Lemma nth_quintic_scaled_resolvent f (i : 'I_7) :
  nth 0 (quintic_scaled_resolvent f) i =
    quintic_scaled_resolvent_coefficient f i.
Proof.
by rewrite /quintic_scaled_resolvent (nth_map i) ?size_enum_ord //
  nth_ord_enum.
Qed.

(** The surviving assignments in the padded specialization are precisely
    the permutations fixing the last coordinate. *)
Definition fixed_last_group : {group {perm 'I_6}} :=
  'C[ord_max | perm_action 'I_6].

Lemma mem_fixed_last_group (g : {perm 'I_6}) :
  (g \in fixed_last_group) = (g ord_max == ord_max).
Proof.
rewrite /fixed_last_group.
apply/idP/idP.
- move/astab1P=> h.
  change (g ord_max = ord_max) in h.
  exact/eqP.
- move/eqP=> h; apply/astab1P.
  by change (g ord_max = ord_max).
Qed.

Lemma full_permutation_orbit_last :
  orbit (perm_action 'I_6) [set : {perm 'I_6}] ord_max = [set : 'I_6].
Proof.
apply/setP=> j; rewrite inE.
apply/orbitP.
exists (tperm ord_max j); first by rewrite inE.
change (tperm ord_max j ord_max = j).
by rewrite tpermL.
Qed.

Lemma card_fixed_last_group : #|fixed_last_group| = 120%N.
Proof.
have h := card_orbit_stab (perm_action 'I_6)
  [set : {perm 'I_6}] ord_max.
rewrite full_permutation_orbit_last cardsT card_ord cardsT card_Sn in h.
rewrite setTI in h.
change (6 * #|fixed_last_group| = 720)%N in h.
apply/eqP.
rewrite -(eqn_pmul2l (m := 6)) //.
apply/eqP.
change (6 * #|fixed_last_group| = 720)%N.
exact h.
Qed.

Definition permutation_assignment (g : {perm 'I_6}) : root_assignment :=
  finfun g.

Lemma permutation_assignment_injective : injective permutation_assignment.
Proof.
move=> g h e; apply/permP=> i.
have ei := congr1 (fun a : root_assignment => a i) e.
by move: ei; rewrite /permutation_assignment !ffunE.
Qed.

Definition fixed_injective_assignments : {set root_assignment} :=
  [set a : root_assignment | injectiveb a && (a ord_max == ord_max)].

Lemma fixed_injective_assignments_image :
  fixed_injective_assignments =
    [set permutation_assignment g | g in fixed_last_group].
Proof.
apply/setP=> a; apply/idP/idP.
- rewrite /fixed_injective_assignments inE.
  move/andP=> [hainj hlast].
  have hainjP : injective a := elimT (@injectiveP _ _ a) hainj.
  pose g : {perm 'I_6} := perm hainjP.
  apply/imsetP; exists g.
    rewrite mem_fixed_last_group /g permE.
    exact hlast.
  apply/ffunP=> i.
  by rewrite /permutation_assignment ffunE /g permE.
- move/imsetP=> [g hg ->].
  rewrite /fixed_injective_assignments inE.
  apply/andP; split.
  + apply/injectiveP=> x y.
    rewrite /permutation_assignment !ffunE.
    exact: perm_inj.
  + move: hg; rewrite mem_fixed_last_group
      /permutation_assignment ffunE.
    exact: id.
Qed.

Lemma card_fixed_injective_assignments :
  #|fixed_injective_assignments| = 120%N.
Proof.
rewrite fixed_injective_assignments_image
  (card_imset fixed_last_group permutation_assignment_injective)
  card_fixed_last_group.
by [].
Qed.

Lemma card_fixed_injective_assignments_pred :
  #|(fun a : root_assignment =>
      injectiveb a && (a ord_max == ord_max))| = 120%N.
Proof.
rewrite -card_fixed_injective_assignments.
apply: eq_card=> a.
by rewrite /fixed_injective_assignments inE.
Qed.

Lemma ordinal6_not_last_lt5 (j : 'I_6) :
  j != ord_max -> (j < 5)%N.
Proof.
move=> hj.
have hj6 : (j < 6)%N := ltn_ord j.
rewrite ltnS leq_eqVlt in hj6.
move/orP: hj6=> [/eqP h5|h5]; last exact h5.
have hjlast : j == ord_max by apply/eqP/val_inj; exact h5.
by move: hj; rewrite hjlast.
Qed.

Lemma inord5_widen (i : 'I_5) :
  (inord (val i) : 'I_5) = i.
Proof. exact: inord_val. Qed.

Lemma widen_ord5_neq_last (i : 'I_5) :
  widen_ord (leqnSn 5) i != (ord_max : 'I_6).
Proof.
apply/eqP=> h.
have hi : (widen_ord (leqnSn 5) i < 5)%N := ltn_ord i.
rewrite h in hi.
by move: hi; rewrite /ord_max /= ltnn.
Qed.

Lemma widen_inord5_not_last (j : 'I_6) (hj : j != ord_max) :
  widen_ord (leqnSn 5) (inord (val j) : 'I_5) = j.
Proof.
apply: val_inj.
have hj5 := ordinal6_not_last_lt5 hj.
have hk := @inordK 4 (val j) hj5.
exact hk.
Qed.

Local Close Scope group_scope.

Section Evaluation.

Variable R : comNzRingType.

Definition pad_quintic_roots (roots : 5.-tuple R) : 6.-tuple R :=
  [tuple if i == ord_max then 0 else tnth roots (inord i) | i < 6].

Definition take_quintic_roots (values : 6.-tuple R) : 5.-tuple R :=
  [tuple tnth values (widen_ord (leqnSn 5) i) | i < 5].

Definition restrict_assignment (a : root_assignment) (i : 'I_5) : 'I_5 :=
  inord (val (a (widen_ord (leqnSn 5) i))).

Lemma assignment_image_not_last (a : root_assignment)
    (hainj : injective a) (hlast : a ord_max = ord_max) (i : 'I_5) :
  a (widen_ord (leqnSn 5) i) != ord_max.
Proof.
apply/eqP=> hai.
have haw : a (widen_ord (leqnSn 5) i) = a ord_max.
  by rewrite hai hlast.
have hwi := hainj _ _ haw.
have hne := widen_ord5_neq_last i.
by move: hne; rewrite hwi eqxx.
Qed.

Lemma restrict_assignment_injective (a : root_assignment)
    (hainj : injective a) (hlast : a ord_max = ord_max) :
  injective (restrict_assignment a).
Proof.
move=> i j hij.
rewrite /restrict_assignment in hij.
have hi := assignment_image_not_last hainj hlast i.
have hj := assignment_image_not_last hainj hlast j.
have haw : a (widen_ord (leqnSn 5) i) =
    a (widen_ord (leqnSn 5) j).
  rewrite -(widen_inord5_not_last hi)
    -(widen_inord5_not_last hj).
  apply: f_equal.
  exact hij.
have hwij := hainj _ _ haw.
apply: val_inj.
have hv := congr1 (@nat_of_ord 6) hwij.
exact hv.
Qed.

Lemma tnth_pad_quintic_roots_in (roots : 5.-tuple R) (i : 'I_5) :
  tnth (pad_quintic_roots roots) (widen_ord (leqnSn 5) i) = tnth roots i.
Proof.
rewrite /pad_quintic_roots tnth_mktuple.
have hne : widen_ord (leqnSn 5) i != ord_max.
  apply/eqP=> h.
  have hi : (widen_ord (leqnSn 5) i < 5)%N := ltn_ord i.
  rewrite h in hi.
  by move: hi; rewrite /ord_max /= ltnn.
rewrite (negbTE hne).
rewrite inord_val.
congr (tnth roots _); exact: val_inj.
Qed.

Lemma tnth_pad_quintic_roots_last (roots : 5.-tuple R) :
  tnth (pad_quintic_roots roots) ord_max = 0.
Proof.
rewrite /pad_quintic_roots tnth_mktuple.
by rewrite eqxx.
Qed.

Lemma take_assignment_values_fixed roots (a : root_assignment)
    (hainj : injective a) (hlast : a ord_max = ord_max) :
  take_quintic_roots (assignment_values (pad_quintic_roots roots) a) =
    permute_quintic_roots
      (perm (restrict_assignment_injective hainj hlast)) roots.
Proof.
apply: eq_from_tnth=> i.
rewrite /take_quintic_roots /assignment_values
  /permute_quintic_roots !tnth_mktuple permE.
have hi := assignment_image_not_last hainj hlast i.
rewrite -(widen_inord5_not_last hi) /restrict_assignment.
have hne := widen_ord5_neq_last
  (inord (val (a (widen_ord (leqnSn 5) i))) : 'I_5).
rewrite (negbTE hne) inord_val.
congr (tnth roots _); exact: val_inj.
Qed.

Lemma quintic_product_permute (roots : 5.-tuple R) (s : S5) :
  \prod_(i : 'I_5) tnth (permute_quintic_roots s roots) i =
    \prod_(i : 'I_5) tnth roots i.
Proof.
under [LHS]eq_bigr=> i _ do rewrite tnth_permute_quintic_roots.
rewrite (reindex_inj (@perm_inj _ s^-1)) /=.
under [LHS]eq_bigr=> i _ do rewrite permKV.
by [].
Qed.

Lemma tnth_pad_quintic_exponent_in (d : quintic_exponent) (i : 'I_5) :
  tnth (pad_quintic_exponent d) (widen_ord (leqnSn 5) i) = tnth d i.
Proof.
rewrite /pad_quintic_exponent tnth_mktuple.
have hne : widen_ord (leqnSn 5) i != ord_max.
  apply/eqP=> h.
  have hi : (widen_ord (leqnSn 5) i < 5)%N := ltn_ord i.
  rewrite h in hi.
  by move: hi; rewrite /ord_max /= ltnn.
rewrite (negbTE hne).
rewrite inord_val.
congr (tnth d _); exact: val_inj.
Qed.

Lemma tnth_pad_quintic_exponent_last (d : quintic_exponent) :
  tnth (pad_quintic_exponent d) ord_max = 0%N.
Proof.
rewrite /pad_quintic_exponent tnth_mktuple.
by rewrite eqxx.
Qed.

Lemma exponent_value_ring_pad roots d :
  exponent_value_ring (pad_quintic_roots roots)
      (pad_quintic_exponent d) =
    \prod_(i : 'I_5) tnth roots i ^+ tnth d i.
Proof.
rewrite /exponent_value_ring.
rewrite big_ord_recr /= tnth_pad_quintic_roots_last
  tnth_pad_quintic_exponent_last expr0 mulr1.
apply: eq_bigr=> i _.
by rewrite tnth_pad_quintic_roots_in tnth_pad_quintic_exponent_in.
Qed.

Lemma exponent_value_ring_pad_exponent (values : 6.-tuple R) d :
  exponent_value_ring values (pad_quintic_exponent d) =
    \prod_(i : 'I_5)
      tnth values (widen_ord (leqnSn 5) i) ^+ tnth d i.
Proof.
rewrite /exponent_value_ring big_ord_recr /=
  tnth_pad_quintic_exponent_last expr0 mulr1.
apply: eq_bigr=> i _.
by rewrite tnth_pad_quintic_exponent_in.
Qed.

Lemma sparse_eval_ring_quintic_monomial roots d :
  sparse_eval_ring (pad_quintic_roots roots) (quintic_sparse_monomial d) =
    quintic_monomial_value roots d.
Proof.
by rewrite /sparse_eval_ring /quintic_sparse_monomial /quintic_monomial_value
  big_seq1 rmorph1 mul1r exponent_value_ring_pad.
Qed.

Lemma sparse_eval_ring_quintic_table roots table :
  sparse_eval_ring (pad_quintic_roots roots) (quintic_sparse_table table) =
    quintic_table_value roots table.
Proof.
rewrite /quintic_sparse_table /quintic_table_value
  sparse_eval_ring_sum big_map.
apply: eq_bigr=> d _.
exact: sparse_eval_ring_quintic_monomial.
Qed.

Lemma sparse_eval_ring_quintic_monomial_take (values : 6.-tuple R) d :
  sparse_eval_ring values (quintic_sparse_monomial d) =
    quintic_monomial_value (take_quintic_roots values) d.
Proof.
rewrite /sparse_eval_ring /quintic_sparse_monomial /quintic_monomial_value
  big_seq1 rmorph1 mul1r exponent_value_ring_pad_exponent.
apply: eq_bigr=> i _.
by rewrite /take_quintic_roots tnth_mktuple.
Qed.

Lemma sparse_eval_ring_quintic_table_take
    (values : 6.-tuple R) table :
  sparse_eval_ring values (quintic_sparse_table table) =
    quintic_table_value (take_quintic_roots values) table.
Proof.
rewrite /quintic_sparse_table /quintic_table_value
  sparse_eval_ring_sum big_map.
apply: eq_bigr=> d _.
exact: sparse_eval_ring_quintic_monomial_take.
Qed.

Lemma sparse_eval_ring_quintic_theta_take (values : 6.-tuple R) i :
  sparse_eval_ring values (quintic_sparse_theta i) =
    quintic_theta_value (take_quintic_roots values) i.
Proof. exact: sparse_eval_ring_quintic_table_take. Qed.

Lemma sparse_eval_ring_quintic_theta roots i :
  sparse_eval_ring (pad_quintic_roots roots) (quintic_sparse_theta i) =
    quintic_theta_value roots i.
Proof. exact: sparse_eval_ring_quintic_table. Qed.

Lemma size_quintic_sparse_resolvent :
  size quintic_sparse_resolvent = 7%N.
Proof.
by rewrite /quintic_sparse_resolvent size_linear_product
  /quintic_sparse_theta_list size_map size_enum_ord.
Qed.

Lemma coefficient_list_poly_quintic_resolvent roots :
  coefficient_list_poly (pad_quintic_roots roots)
      quintic_sparse_resolvent =
    quintic_scalar_resolvent roots.
Proof.
rewrite /quintic_sparse_resolvent coefficient_list_poly_linear_product
  /quintic_sparse_theta_list big_map big_enum.
rewrite PolynomialFormulasQuinticThetaValues.quintic_scalar_resolvent_index_product
  /PolynomialFormulasQuinticThetaValues.quintic_scalar_resolvent_by_index.
apply: eq_bigr=> i _.
by rewrite sparse_eval_ring_quintic_theta.
Qed.

Lemma coefficient_list_poly_quintic_resolvent_take
    (values : 6.-tuple R) :
  coefficient_list_poly values quintic_sparse_resolvent =
    quintic_scalar_resolvent (take_quintic_roots values).
Proof.
rewrite /quintic_sparse_resolvent coefficient_list_poly_linear_product
  /quintic_sparse_theta_list big_map big_enum.
rewrite PolynomialFormulasQuinticThetaValues.quintic_scalar_resolvent_index_product
  /PolynomialFormulasQuinticThetaValues.quintic_scalar_resolvent_by_index.
apply: eq_bigr=> i _.
by rewrite sparse_eval_ring_quintic_theta_take.
Qed.

Lemma sparse_eval_ring_quintic_resolvent_coefficient roots i :
  sparse_eval_ring (pad_quintic_roots roots)
      (quintic_sparse_resolvent_coefficient i) =
    (quintic_scalar_resolvent roots)`_i.
Proof.
rewrite /quintic_sparse_resolvent_coefficient.
rewrite -(coefficient_list_poly_coef
  (pad_quintic_roots roots) quintic_sparse_resolvent i).
by rewrite coefficient_list_poly_quintic_resolvent.
Qed.

Lemma sparse_eval_ring_quintic_resolvent_coefficient_take
    (values : 6.-tuple R) i :
  sparse_eval_ring values (quintic_sparse_resolvent_coefficient i) =
    (quintic_scalar_resolvent (take_quintic_roots values))`_i.
Proof.
rewrite /quintic_sparse_resolvent_coefficient.
rewrite -(coefficient_list_poly_coef values quintic_sparse_resolvent i).
by rewrite coefficient_list_poly_quintic_resolvent_take.
Qed.

Lemma sparse_eval_ring_first_five_product_take (values : 6.-tuple R) :
  sparse_eval_ring values first_five_product =
    \prod_(i : 'I_5) tnth (take_quintic_roots values) i.
Proof.
rewrite /first_five_product sparse_eval_ring_product big_map.
under [LHS]eq_bigr=> j hj do rewrite sparse_eval_ring_var.
rewrite -val_enum_ord big_map big_enum.
apply: eq_bigr=> i _.
have hinord : (inord (val i) : 'I_6) = widen_ord (leqnSn 5) i.
  apply: val_inj.
  have h :
      (inord (val (widen_ord (leqnSn 5) i)) : 'I_6) =
        widen_ord (leqnSn 5) i := inord_val _.
  have hv := congr1 (@nat_of_ord 6) h.
  exact hv.
by rewrite hinord /take_quintic_roots tnth_mktuple.
Qed.

Lemma sparse_eval_ring_weighted_quintic_coefficient_take
    (values : 6.-tuple R) i :
  sparse_eval_ring values (weighted_quintic_coefficient i) =
    (\prod_(j : 'I_5) tnth (take_quintic_roots values) j) *
      (quintic_scalar_resolvent (take_quintic_roots values))`_i.
Proof.
by rewrite /weighted_quintic_coefficient sparse_eval_ring_mul
  sparse_eval_ring_first_five_product_take
  sparse_eval_ring_quintic_resolvent_coefficient_take.
Qed.

Lemma sparse_eval_ring_first_five_product roots :
  sparse_eval_ring (pad_quintic_roots roots) first_five_product =
    \prod_(i : 'I_5) tnth roots i.
Proof.
rewrite /first_five_product sparse_eval_ring_product big_map.
under [LHS]eq_bigr=> j hj do rewrite sparse_eval_ring_var.
rewrite -val_enum_ord big_map big_enum.
apply: eq_bigr=> i _.
have hinord : (inord (val i) : 'I_6) = widen_ord (leqnSn 5) i.
  apply: val_inj.
  have h :
      (inord (val (widen_ord (leqnSn 5) i)) : 'I_6) =
        widen_ord (leqnSn 5) i := inord_val _.
  have hv := congr1 (@nat_of_ord 6) h.
  exact hv.
by rewrite hinord tnth_pad_quintic_roots_in.
Qed.

Lemma sparse_eval_ring_weighted_quintic_coefficient roots i :
  sparse_eval_ring (pad_quintic_roots roots)
      (weighted_quintic_coefficient i) =
    (\prod_(j : 'I_5) tnth roots j) *
      (quintic_scalar_resolvent roots)`_i.
Proof.
by rewrite /weighted_quintic_coefficient sparse_eval_ring_mul
  sparse_eval_ring_first_five_product
  sparse_eval_ring_quintic_resolvent_coefficient.
Qed.

Lemma weighted_assignment_fixed (roots : 5.-tuple R) (i : 'I_7)
    (a : root_assignment) (hainj : injective a)
    (hlast : a ord_max = ord_max) :
  sparse_eval_ring
      (assignment_values (pad_quintic_roots roots) a)
      (weighted_quintic_coefficient i) =
    (\prod_(j : 'I_5) tnth roots j) *
      (quintic_scalar_resolvent roots)`_i.
Proof.
rewrite sparse_eval_ring_weighted_quintic_coefficient_take.
rewrite (take_assignment_values_fixed roots hainj hlast).
rewrite quintic_product_permute quintic_scalar_resolvent_permute.
by [].
Qed.

Lemma weighted_assignment_nonfixed (roots : 5.-tuple R) (i : 'I_7)
    (a : root_assignment) (hainj : injective a)
    (hlast : a ord_max != ord_max) :
  sparse_eval_ring
      (assignment_values (pad_quintic_roots roots) a)
      (weighted_quintic_coefficient i) = 0.
Proof.
rewrite sparse_eval_ring_weighted_quintic_coefficient_take.
pose j := finv a ord_max.
have haj : a j = ord_max := f_finv hainj ord_max.
have hj : j != ord_max.
  apply/eqP=> hjlast.
  have heq : a ord_max = ord_max.
    by rewrite -hjlast haj.
  move: hlast.
  by rewrite heq eqxx.
pose k : 'I_5 := inord (val j).
have hw : widen_ord (leqnSn 5) k = j.
  exact: widen_inord5_not_last hj.
have hkzero :
    tnth (take_quintic_roots
      (assignment_values (pad_quintic_roots roots) a)) k = 0.
  by rewrite /take_quintic_roots tnth_mktuple
    /assignment_values tnth_mktuple hw haj
    tnth_pad_quintic_roots_last.
by rewrite (bigD1 k) //= hkzero mul0r mul0r.
Qed.

Lemma weighted_assignment_case (roots : 5.-tuple R) (i : 'I_7)
    (a : root_assignment) (hainj : injectiveb a) :
  sparse_eval_ring
      (assignment_values (pad_quintic_roots roots) a)
      (weighted_quintic_coefficient i) =
    if a ord_max == ord_max then
      (\prod_(j : 'I_5) tnth roots j) *
        (quintic_scalar_resolvent roots)`_i
    else 0.
Proof.
have hainjP : injective a := elimT (@injectiveP _ _ a) hainj.
case hfix: (a ord_max == ord_max).
- exact: weighted_assignment_fixed hainjP (eqP hfix).
- apply: (weighted_assignment_nonfixed roots i hainjP).
  by rewrite hfix.
Qed.

Theorem newton_symmetrized_weighted_coefficient_correct
    (roots : 5.-tuple R) (i : 'I_7) :
  sparse_eval_ring (elementary_values (pad_quintic_roots roots))
      (symmetrized_weighted_quintic_coefficient i) =
    120%:R * ((\prod_(j : 'I_5) tnth roots j) *
      (quintic_scalar_resolvent roots)`_i).
Proof.
rewrite /symmetrized_weighted_quintic_coefficient
  newton_symmetrize_correct /injective_assignment_polynomial_sum.
transitivity
  (\sum_(a : root_assignment |
      injectiveb a && (a ord_max == ord_max))
    ((\prod_(j : 'I_5) tnth roots j) *
      (quintic_scalar_resolvent roots)`_i)).
- rewrite [LHS]big_mkcond [RHS]big_mkcond.
  apply: eq_bigr=> a _.
  rewrite assignment_code_injectiveb.
  case hainj: (injectiveb a); last by rewrite /=.
  rewrite /= (weighted_assignment_case roots i hainj).
  by case: (a ord_max == ord_max).
- rewrite sumr_const.
  rewrite card_fixed_injective_assignments_pred.
  change
    (((\prod_(j : 'I_5) tnth roots j) *
        (quintic_scalar_resolvent roots)`_i) *+ 120 =
      120%:R * ((\prod_(j : 'I_5) tnth roots j) *
        (quintic_scalar_resolvent roots)`_i)).
  by rewrite mulr_natl.
Qed.

Theorem quintic_scaled_resolvent_coefficient_correct
    (roots : 5.-tuple R) (f : monic_quintic) (i : 'I_7) :
  @cast_int_values R
      (monic_elementary_values (quintic_sextic_embedding f)) =
      elementary_values (pad_quintic_roots roots) ->
  (quintic_scaled_resolvent_coefficient f i)%:~R =
    120%:R * ((\prod_(j : 'I_5) tnth roots j) *
      (quintic_scalar_resolvent roots)`_i).
Proof.
move=> hvieta.
rewrite /quintic_scaled_resolvent_coefficient
  sparse_eval_ring_cast hvieta.
exact: newton_symmetrized_weighted_coefficient_correct.
Qed.

End Evaluation.

End PolynomialFormulasQuinticPaddedSymmetrization.
