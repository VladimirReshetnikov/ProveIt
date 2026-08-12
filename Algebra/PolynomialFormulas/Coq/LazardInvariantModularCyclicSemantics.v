From Stdlib Require Import Lia.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.

From PolynomialFormulas Require Import
  LazardInvariantFiniteFree LazardInvariantMultinomials
  LazardInvariantSymmetricModule LazardInvariantSubgroupModule
  LazardInvariantHomogeneousCoordinates
  LazardInvariantModularCounterexample.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Polynomial semantics for the modular [C6] calculation.

    [LazardInvariantModularCounterexample] deliberately stops at the finite
    orbit/product matrix.  This file identifies those rows and columns with
    the actual degree-seven part of the invariant ring for the regular
    six-cycle over ['F_3].  It also transports the homogeneous-coordinate
    argument from the ambient symmetric module to an arbitrary raw
    homogeneous finite-free decomposition of the genuine invariant module.

    The only closed computations below concern finite lists of exponent
    vectors.  All statements involving an arbitrary polynomial or an
    arbitrary finite-free decomposition are proved from coefficients,
    homogeneity, invariance, reconstruction, and coordinate uniqueness. *)
Module PolynomialFormulasLazardInvariantModularCyclicSemantics.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.
Local Open Scope matrix_set_scope.

Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module SM := PolynomialFormulasLazardInvariantSymmetricModule.
Module SIM := PolynomialFormulasLazardInvariantSubgroupModule.
Module HC := PolynomialFormulasLazardInvariantHomogeneousCoordinates.
Module MC := PolynomialFormulasLazardInvariantModularCounterexample.

Local Notation F3 := 'F_3.
Local Notation Exponent := (6.-tuple nat).
Local Notation S6 := 'S_6.

(** * The genuine regular cyclic subgroup *)

Definition o0 : 'I_6 := @Ordinal 6 0 isT.
Definition o1 : 'I_6 := @Ordinal 6 1 isT.
Definition o2 : 'I_6 := @Ordinal 6 2 isT.
Definition o3 : 'I_6 := @Ordinal 6 3 isT.
Definition o4 : 'I_6 := @Ordinal 6 4 isT.
Definition o5 : 'I_6 := @Ordinal 6 5 isT.

(** This orientation agrees with [MC.rotate_exponent] after the inverse in
    [IM.mpoly_left_action] is taken into account. *)
Definition six_cycle : S6 :=
  (tperm o0 o1 * tperm o1 o2 * tperm o2 o3 *
    tperm o3 o4 * tperm o4 o5)%g.

Definition regular_C6 : {group S6} := <[six_cycle]>.

Definition six_cycle_in_regular : [subg regular_C6] :=
  Sub six_cycle (cycle_id six_cycle).

Lemma six_cycle_values :
  [tuple six_cycle o0; six_cycle o1; six_cycle o2;
    six_cycle o3; six_cycle o4; six_cycle o5] =
  [tuple o5; o0; o1; o2; o3; o4].
Proof. vm_compute. Qed.

(** The name [regular_C6] is semantic, not just mnemonic: its displayed
    generator has order six, and hence the generated subgroup has six
    elements.  Exporting these two facts keeps the scope of the modular
    counterexample explicit without making the later invariant calculation
    depend on them. *)
Lemma six_cycle_order : #[six_cycle] = 6.
Proof. vm_compute. Qed.

Lemma regular_C6_card : #|regular_C6| = 6.
Proof. by rewrite /regular_C6 -orderE six_cycle_order. Qed.

Lemma regular_C6_generated (g : [subg regular_C6]) :
  exists k, sgval g = six_cycle ^+ k.
Proof.
move: (valP g); rewrite /regular_C6.
by move/cycleP=> [k hk]; exists k.
Qed.

(** * Exponents and literal orbit sums *)

Definition exponent_monomial (a : Exponent) : 'X_{1..6} :=
  [multinom tnth a i | i < 6].

Definition monomial_exponent (m : 'X_{1..6}) : Exponent :=
  [tuple m i | i < 6].

Lemma exponent_monomialK : cancel exponent_monomial monomial_exponent.
Proof. by move=> a; apply/eq_from_tnth=> i; rewrite /monomial_exponent tnth_mktuple
  /exponent_monomial mnmE.
Qed.

Lemma monomial_exponentK : cancel monomial_exponent exponent_monomial.
Proof. by move=> m; apply/mnmP=> i; rewrite /exponent_monomial mnmE
  /monomial_exponent tnth_mktuple.
Qed.

Lemma exponent_monomial_injective : injective exponent_monomial.
Proof. exact: (can_inj exponent_monomialK). Qed.

Lemma exponent_monomial_degree a :
  mdeg (exponent_monomial a) = \sum_(i < 6) tnth a i.
Proof.
rewrite mdegE; apply: eq_bigr=> i _.
by rewrite /exponent_monomial mnmE.
Qed.

Lemma exponent_monomial_rotate_one a :
  exponent_monomial (MC.rotate_exponent a 1) =
    [multinom (exponent_monomial a) ((six_cycle^-1)%g i) | i < 6].
Proof.
apply/mnmP=> i; case: i=> [[|[|[|[|[|[|i]]]]]] hi] //=;
  vm_compute.
Qed.

(** Rotation is an honest cyclic action on exponent tuples.  Keeping this
    elementary identity separate prevents the later coefficient argument
    from depending on an executable fact that was never exported by the
    matrix-only counterexample file. *)
Lemma rotate_exponent_compose a k l :
  MC.rotate_exponent (MC.rotate_exponent a k) l =
    MC.rotate_exponent a (l + k).
Proof.
apply/eq_from_tnth=> i.
rewrite /MC.rotate_exponent !tnth_mktuple.
congr (tnth a _).
apply/val_inj=> /=.
rewrite !inordK ?ltn_mod //.
by rewrite modnDml addnA.
Qed.

Lemma rotate_exponent_zero a : MC.rotate_exponent a 0 = a.
Proof.
apply/eq_from_tnth=> i.
by rewrite /MC.rotate_exponent tnth_mktuple addn0 modn_small ?ltn_ord.
Qed.

Lemma cyclic_orbit_uniq a : uniq (MC.cyclic_orbit a).
Proof. exact: undup_uniq _. Qed.

Definition orbit_polynomial (a : Exponent) : {mpoly F3[6]} :=
  \sum_(b <- MC.cyclic_orbit a) 'X_[F3, exponent_monomial b].

Lemma mcoeff_orbit_polynomial a b :
  (orbit_polynomial a)@_(exponent_monomial b) =
    (count (pred1 b) (MC.cyclic_orbit a))%:R.
Proof.
rewrite /orbit_polynomial raddf_sum /=.
elim: (MC.cyclic_orbit a)=> [|c s ih] /=.
- by rewrite big_nil mcoeff0.
- rewrite big_cons mcoeffD mcoeffX
    (inj_eq exponent_monomial_injective) ih.
  by case: (c == b); rewrite /= ?addr0 ?add1n ?natrD.
Qed.

Lemma mcoeff_orbit_polynomial_monomial a m :
  (orbit_polynomial a)@_m =
    (count (pred1 (monomial_exponent m)) (MC.cyclic_orbit a))%:R.
Proof.
rewrite -[m]monomial_exponentK.
exact: mcoeff_orbit_polynomial.
Qed.

Definition orbit_index (d : nat) := 'I_(MC.invariant_orbit_count d).

Definition orbit_representative d (j : orbit_index d) : Exponent :=
  nth MC.zero_exponent (MC.orbit_representatives d) j.

Definition orbit_basis_polynomial d (j : orbit_index d) : {mpoly F3[6]} :=
  orbit_polynomial (orbit_representative j).

Definition orbit_coordinates d (p : {mpoly F3[6]}) :
    'rV[F3]_(MC.invariant_orbit_count d) :=
  \row_j p@_(exponent_monomial (orbit_representative j)).

Definition orbit_combination d
    (v : 'rV[F3]_(MC.invariant_orbit_count d)) : {mpoly F3[6]} :=
  \sum_(j < MC.invariant_orbit_count d)
    (v 0 j) *: orbit_basis_polynomial j.

(** Closed orbit-partition facts, isolated from the semantic arguments. *)
Lemma orbit_representative_separation (d : 'I_8)
    (i j : orbit_index d) :
  (orbit_representative j \in
      MC.cyclic_orbit (orbit_representative i)) = (i == j).
Proof.
have hclosed :
    [forall e : 'I_8,
      [forall r : orbit_index e,
        [forall s : orbit_index e,
          ((orbit_representative s \in
              MC.cyclic_orbit (orbit_representative r)) == (r == s))]]].
  vm_compute.
exact/eqP: (forallP (forallP (forallP hclosed d) i) j).
Qed.

Lemma orbit_representative_degree (d : 'I_8) (i : orbit_index d) :
  \sum_(k < 6) tnth (orbit_representative i) k = d.
Proof.
have hclosed :
    [forall e : 'I_8,
      [forall r : orbit_index e,
        (\sum_(k < 6) tnth (orbit_representative r) k == e)]].
  vm_compute.
exact/eqP: (forallP (forallP hclosed d) i).
Qed.

Lemma orbit_representative_rotation_degree (d : 'I_8)
    (i : orbit_index d) (k : 'I_6) :
  \sum_(j < 6) tnth
      (MC.rotate_exponent (orbit_representative i) k) j = d.
Proof.
have hclosed :
    [forall e : 'I_8,
      [forall r : orbit_index e,
        [forall s : 'I_6,
          (\sum_(j < 6) tnth
            (MC.rotate_exponent (orbit_representative r) s) j == e)]]].
  vm_compute.
exact/eqP: (forallP (forallP (forallP hclosed d) i) k).
Qed.

Lemma cyclic_orbit_representative_degree (d : 'I_8)
    (i : orbit_index d) a :
  a \in MC.cyclic_orbit (orbit_representative i) ->
  \sum_(j < 6) tnth a j = d.
Proof.
rewrite /MC.cyclic_orbit mem_undup mem_map=> /mapP [k hk ->].
have hk6 : k < 6 by move: hk; rewrite mem_iota add0n.
exact: orbit_representative_rotation_degree d i (Ordinal hk6).
Qed.

Lemma orbit_coordinates_combination (d : 'I_8)
    (v : 'rV[F3]_(MC.invariant_orbit_count d)) :
  orbit_coordinates d (orbit_combination d v) = v.
Proof.
apply/matrixP=> i j; rewrite !mxE /orbit_combination raddf_sum /=.
rewrite (bigD1 j) //= mcoeffZ mcoeff_orbit_polynomial.
rewrite count_uniq_mem ?cyclic_orbit_uniq // orbit_representative_separation
  eqxx mulr1.
rewrite big1 ?addr0 // => k hkj.
rewrite mcoeffZ mcoeff_orbit_polynomial count_uniq_mem
  ?cyclic_orbit_uniq // orbit_representative_separation.
by rewrite (negbTE hkj) mulr0.
Qed.

Lemma orbit_basis_homogeneous (d : 'I_8) (i : orbit_index d) :
  orbit_basis_polynomial i \is d.-homog.
Proof.
rewrite /orbit_basis_polynomial /orbit_polynomial rpred_sum //= => a ha.
rewrite dhomogX exponent_monomial_degree.
move: ha; rewrite mem_undup mem_map=> /mapP [k hk ->].
have hk6 : k < 6 by move: hk; rewrite mem_iota add0n.
exact: orbit_representative_rotation_degree d i (Ordinal hk6).
Qed.

Lemma orbit_basis_fixed_generator (d : 'I_8) (i : orbit_index d) :
  SM.symmetric_mpoly_left_action six_cycle (orbit_basis_polynomial i) =
    orbit_basis_polynomial i.
Proof.
have hclosed :
    [forall e : 'I_8,
      [forall r : orbit_index e,
        SM.symmetric_mpoly_left_action six_cycle
          (orbit_basis_polynomial r) == orbit_basis_polynomial r]].
  vm_compute.
exact/eqP: (forallP (forallP hclosed d) i).
Qed.

Lemma left_action_power_fixed p k :
  SM.symmetric_mpoly_left_action six_cycle p = p ->
  SM.symmetric_mpoly_left_action (six_cycle ^+ k) p = p.
Proof.
move=> hp; elim: k=> [|k ih].
- by rewrite expg0 SM.symmetric_mpoly_left_action1.
- by rewrite expgS SM.symmetric_mpoly_left_actionM hp ih.
Qed.

Lemma orbit_basis_fixed_regular (d : 'I_8) (i : orbit_index d)
    (g : [subg regular_C6]) :
  SM.symmetric_mpoly_left_action (sgval g) (orbit_basis_polynomial i) =
    orbit_basis_polynomial i.
Proof.
case: (regular_C6_generated g)=> k ->.
exact: left_action_power_fixed (orbit_basis_fixed_generator d i).
Qed.

Lemma orbit_combination_homogeneous (d : 'I_8)
    (v : 'rV[F3]_(MC.invariant_orbit_count d)) :
  orbit_combination d v \is d.-homog.
Proof.
rewrite /orbit_combination rpred_sum // => i _.
exact/rpredZ/orbit_basis_homogeneous.
Qed.

Lemma orbit_combination_fixed_regular (d : 'I_8)
    (v : 'rV[F3]_(MC.invariant_orbit_count d))
    (g : [subg regular_C6]) :
  SM.symmetric_mpoly_left_action (sgval g) (orbit_combination d v) =
    orbit_combination d v.
Proof.
rewrite /orbit_combination SM.symmetric_mpoly_left_action_sum.
apply: eq_bigr=> i _.
by rewrite SM.symmetric_mpoly_left_actionZ orbit_basis_fixed_regular.
Qed.

Definition orbit_combination_invariant (d : 'I_8)
    (v : 'rV[F3]_(MC.invariant_orbit_count d)) :
    SIM.lazard_subgroup_invariant_module F3 regular_C6.
Proof.
apply: SIM.LazardSubgroupInvariant.
apply/SIM.lazard_subgroup_invariantP=> g.
exact: orbit_combination_fixed_regular d v g.
Defined.

Lemma orbit_combination_invariant_val (d : 'I_8) v :
  SIM.lazard_subgroup_invariant_val
      (orbit_combination_invariant d v) = orbit_combination d v.
Proof. reflexivity. Qed.

(** Coefficients of a fixed polynomial are constant on the executable cyclic
    orbit.  This is the non-computational half of orbit reconstruction. *)
Lemma fixed_coefficient_rotate_one p a :
  SM.symmetric_mpoly_left_action six_cycle p = p ->
  p@_(exponent_monomial (MC.rotate_exponent a 1)) =
    p@_(exponent_monomial a).
Proof.
move=> hp.
have h := congr1 (fun q : {mpoly F3[6]} =>
  q@_(exponent_monomial a)) hp.
move: h; rewrite /SM.symmetric_mpoly_left_action
  /IM.mpoly_left_action mcoeff_sym.
by rewrite -exponent_monomial_rotate_one.
Qed.

Lemma fixed_coefficient_rotate p a k :
  SM.symmetric_mpoly_left_action six_cycle p = p ->
  p@_(exponent_monomial (MC.rotate_exponent a k)) =
    p@_(exponent_monomial a).
Proof.
move=> hp; elim: k=> [|k ih].
- by rewrite rotate_exponent_zero.
- have hcompose :
      MC.rotate_exponent (MC.rotate_exponent a k) 1 =
        MC.rotate_exponent a k.+1.
    by rewrite rotate_exponent_compose add1n.
  rewrite -hcompose.
  by rewrite (fixed_coefficient_rotate_one hp) ih.
Qed.

Definition bounded_degree_exponent (d : nat) := 6.-tuple 'I_d.+1.

Definition bounded_exponent_val d (a : bounded_degree_exponent d) : Exponent :=
  [tuple (tnth a i : nat) | i < 6].

Definition bounded_exponent_total d (a : bounded_degree_exponent d) : nat :=
  \sum_(i < 6) (tnth a i : nat).

(** The executable representatives really partition every degree at most
    seven.  Stating this on bounded exponent tuples makes it a genuinely
    finite closed fact. *)
Lemma bounded_degree_exponent_unique_orbit (d : 'I_8)
    (a : bounded_degree_exponent d) :
  bounded_exponent_total a = d ->
  exists2 i : orbit_index d,
    bounded_exponent_val a \in MC.cyclic_orbit (orbit_representative i) &
    forall j : orbit_index d,
      bounded_exponent_val a \in MC.cyclic_orbit (orbit_representative j) ->
      j = i.
Proof.
move=> hat.
have hclosed :
    [forall e : 'I_8,
      [forall b : bounded_degree_exponent e,
        (bounded_exponent_total b == e) ==>
          [exists r : orbit_index e,
            (bounded_exponent_val b \in
              MC.cyclic_orbit (orbit_representative r)) &&
            [forall s : orbit_index e,
              (bounded_exponent_val b \in
                MC.cyclic_orbit (orbit_representative s)) ==>
              (s == r)]]]].
  vm_compute.
have ha := forallP (forallP hclosed d) a.
rewrite hat eqxx /= in ha.
move/existsP: ha=> [i /andP [hai hui]].
exists i=> // j haj.
have hij := forallP hui j.
by rewrite haj /= in hij; exact/eqP: hij.
Qed.

Definition bound_monomial_of_degree (d : nat) (m : 'X_{1..6})
    (hm : mdeg m = d) : bounded_degree_exponent d :=
  [tuple inord (m i) | i < 6].

Lemma bounded_exponent_val_bound_monomial d m (hm : mdeg m = d) :
  bounded_exponent_val (bound_monomial_of_degree hm) = monomial_exponent m.
Proof.
apply/eq_from_tnth=> i.
rewrite /bounded_exponent_val /bound_monomial_of_degree
  /monomial_exponent !tnth_mktuple.
rewrite inordK // -ltnS -hm mdegE (bigD1 i) //=.
exact: leq_addr.
Qed.

Lemma bounded_exponent_total_bound_monomial d m hm :
  bounded_exponent_total (bound_monomial_of_degree hm) = d.
Proof.
have hentry i :
    (tnth (bound_monomial_of_degree hm) i : nat) = m i.
  have h := congr1 (fun a : Exponent => tnth a i)
    (bounded_exponent_val_bound_monomial hm).
  by move: h; rewrite /bounded_exponent_val /monomial_exponent !tnth_mktuple.
rewrite /bounded_exponent_total.
under eq_bigr=> i _ do rewrite hentry.
by rewrite -mdegE hm.
Qed.

Lemma invariant_fixed_generator
    (p : SIM.lazard_subgroup_invariant_module F3 regular_C6) :
  SM.symmetric_mpoly_left_action six_cycle
      (SIM.lazard_subgroup_invariant_val p) =
    SIM.lazard_subgroup_invariant_val p.
Proof. exact: SIM.lazard_subgroup_invariant_val_fixed p six_cycle_in_regular. Qed.

Theorem orbit_reconstruction (d : 'I_8)
    (p : SIM.lazard_subgroup_invariant_module F3 regular_C6) :
  SIM.lazard_invariant_homogeneous p d ->
  orbit_combination d
      (orbit_coordinates d (SIM.lazard_subgroup_invariant_val p)) =
    SIM.lazard_subgroup_invariant_val p.
Proof.
move=> hp; apply/mpolyP=> m.
case hmd: (mdeg m == d).
- have hm : mdeg m = d by exact/eqP.
  pose a := bound_monomial_of_degree hm.
  have hat := bounded_exponent_total_bound_monomial hm.
  case: (bounded_degree_exponent_unique_orbit d a hat)=> i hai hui.
  have hcoeff :
      (SIM.lazard_subgroup_invariant_val p)@_m =
      (SIM.lazard_subgroup_invariant_val p)@_
        (exponent_monomial (orbit_representative i)).
    move: hai; rewrite mem_undup mem_map=> /mapP [k hk hrot].
    have hmexp : exponent_monomial (bounded_exponent_val a) = m.
      by rewrite bounded_exponent_val_bound_monomial monomial_exponentK.
    rewrite -hmexp hrot.
    exact: fixed_coefficient_rotate (invariant_fixed_generator p).
  rewrite /orbit_combination raddf_sum /=.
  rewrite (bigD1 i) //= mcoeffZ mcoeff_orbit_polynomial_monomial.
  rewrite count_uniq_mem ?cyclic_orbit_uniq //.
  have himem : monomial_exponent m \in
      MC.cyclic_orbit (orbit_representative i).
    by rewrite -bounded_exponent_val_bound_monomial.
  rewrite himem mulr1.
  rewrite big1 ?addr0; first exact: hcoeff.
  move=> j hji; rewrite mcoeffZ mcoeff_orbit_polynomial_monomial.
  case hj : (monomial_exponent m \in MC.cyclic_orbit
      (orbit_representative j)).
  + have : j = i.
      apply: hui.
      by rewrite -bounded_exponent_val_bound_monomial.
    by move: hji; rewrite this eqxx.
  + rewrite count_uniq_mem ?cyclic_orbit_uniq // hj mulr0.
    reflexivity.
- have hzero : (SIM.lazard_subgroup_invariant_val p)@_m = 0.
    apply: dhomog_nemf_coeff hp.
    by rewrite hmd.
  rewrite /orbit_combination raddf_sum /= big1 ?hzero // => i _.
  rewrite mcoeffZ mcoeff_orbit_polynomial_monomial.
  have hnot : monomial_exponent m \notin
      MC.cyclic_orbit (orbit_representative i).
    apply/negP=> hmem.
    have hdegree : mdeg m = d.
      rewrite -[m]monomial_exponentK exponent_monomial_degree.
      move: hmem; rewrite mem_undup mem_map=> /mapP [k hk ->].
      have hk6 : k < 6 by move: hk; rewrite mem_iota add0n.
      exact: orbit_representative_rotation_degree d i (Ordinal hk6).
    by rewrite hdegree eqxx in hmd.
  by rewrite count_uniq_mem ?cyclic_orbit_uniq // hnot mulr0.
Qed.

(** * The literal 159 product rows *)

Definition literal_product_polynomial (r : 'I_(size (MC.product_sources 7))) :
    {mpoly F3[6]} :=
  let source := nth (1, MC.zero_exponent) (MC.product_sources 7) r in
  mesym 6 F3 source.1 * orbit_polynomial source.2.

Definition literal_product_matrix :
    'M[F3]_(size (MC.product_sources 7), MC.invariant_orbit_count 7) :=
  \matrix_(r, c)
    (literal_product_polynomial r)@_
      (exponent_monomial (orbit_representative c)).

(** This equality checks only the expansion of [mesym] times an orbit sum;
    it does not assert a rank and does not mention a hypothetical basis. *)
Lemma literal_product_matrixE :
  literal_product_matrix = MC.product_matrix 7.
Proof. vm_compute. Qed.

Lemma orbit_coordinates_literal_product r :
  orbit_coordinates 7 (literal_product_polynomial r) =
    row r (MC.product_matrix 7).
Proof.
apply/matrixP=> i c; rewrite !mxE.
exact: congr1 (fun M => M r c) literal_product_matrixE.
Qed.

Lemma literal_product_homogeneous r :
  literal_product_polynomial r \is 7.-homog.
Proof.
have hclosed :
    [forall s : 'I_(size (MC.product_sources 7)),
      literal_product_polynomial s \is 7.-homog].
  vm_compute.
exact: forallP hclosed r.
Qed.

Lemma literal_product_fixed_regular r (g : [subg regular_C6]) :
  SM.symmetric_mpoly_left_action (sgval g) (literal_product_polynomial r) =
    literal_product_polynomial r.
Proof.
rewrite /literal_product_polynomial SM.symmetric_mpoly_left_action_mul.
move/IM.full_symmetricP: (mesym_sym 6 F3
  (nth (1, MC.zero_exponent) (MC.product_sources 7) r).1)=> hsym.
rewrite hsym.
case: (regular_C6_generated g)=> k ->.
apply: congr1 (fun q => _ * q).
apply: left_action_power_fixed.
have hclosed :
    [forall s : 'I_(size (MC.product_sources 7)),
      SM.symmetric_mpoly_left_action six_cycle
        (orbit_polynomial
          (nth (1, MC.zero_exponent) (MC.product_sources 7) s).2) ==
      orbit_polynomial
        (nth (1, MC.zero_exponent) (MC.product_sources 7) s).2].
  vm_compute.
exact/eqP: (forallP hclosed r).
Qed.

End PolynomialFormulasLazardInvariantModularCyclicSemantics.
