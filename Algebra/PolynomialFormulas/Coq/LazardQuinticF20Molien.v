From Stdlib Require Import Lia Ring Field.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import QuinticF20Data.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The exact finite-group and rational-function calculation behind the
    Molien numerator in Lazard's Section 6.

    This file proves two algebraic facts:

      - the standard affine [F20] in [S5] has cycle-class sizes
        [1, 4, 5, 10] for types [1^5], [5], [1 2^2], [1 4];
      - the corresponding class sum has numerator
        [1 + t^4 + t^5 + t^6 + t^7 + t^8].

    The final equality is not advertised as a Hilbert-series theorem.  A
    formal Molien theorem connecting the class sum to the graded invariant
    ring is still needed, as is a proof identifying the concrete elements
    [1,i4,...,i8] with a free homogeneous module basis. *)
Module PolynomialFormulasLazardQuinticF20Molien.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.

Local Open Scope ring_scope.
Local Open Scope group_scope.

(** * The four cycle classes *)

(** Number of fixed letters of a permutation of five letters. *)
Definition f20_fixed_count (s : S5) : nat :=
  count [pred i : 'I_5 | s i == i] (enum 'I_5).

(** Exact bridge between a count over the canonical enumeration and the
    cardinality of its predicate.  This is just [cardE] plus [size_filter],
    exposed once so the fixed-point arguments below do not depend on the
    implementation shape of [enum]. *)
Lemma f20_count_enum_pred (T : finType) (P : pred T) :
  count P (enum T) = #|P|.
Proof. by rewrite enumT cardE size_filter. Qed.

(** These predicates encode the full cycle partition on five letters.
    MathComp does not package a cycle-type multiset, so we use fixed-point
    count together with the indicated power relation. *)
Definition f20_identity_classb (s : S5) : bool := s == 1%g.

Definition f20_five_cycle_classb (s : S5) : bool :=
  (f20_fixed_count s == 0%N) && (s ^+ 5 == 1%g).

Definition f20_one_two_two_classb (s : S5) : bool :=
  (f20_fixed_count s == 1%N) && (s ^+ 2 == 1%g).

Definition f20_one_four_classb (s : S5) : bool :=
  (f20_fixed_count s == 1%N) &&
  (s ^+ 4 == 1%g) && (s ^+ 2 != 1%g).

Definition f20_class (P : pred S5) : {set S5} :=
  [set s | normalizes_cycleb s && P s].

(** Fixed-point counts and the power tests used below are invariant under
    conjugation.  Packaging that once lets the class calculation work with
    the semidirect-product structure of [F20], instead of repeatedly
    enumerating all 120 elements of [S5]. *)
Lemma f20_fixed_count_conjugate s c :
  f20_fixed_count (s ^ c) = f20_fixed_count s.
Proof.
rewrite /f20_fixed_count !f20_count_enum_pred.
rewrite -(@cardsE 'I_5 [pred i : 'I_5 | (s ^ c) i == i]).
rewrite -(@cardsE 'I_5 [pred i : 'I_5 | s i == i]).
have hset :
    [set i : 'I_5 | (s ^ c) i == i] =
      [set i : 'I_5 | s (c^-1 i) == c^-1 i].
  apply/setP=> i; rewrite !inE.
  apply/eqP/eqP=> h.
  - have h' := congr1 c^-1 h.
    by move: h'; rewrite conjg_permE !permK.
  - by rewrite conjg_permE h permKV.
rewrite hset.
have hpre :
    [set i : 'I_5 | s (c^-1 i) == c^-1 i] =
      (fun i : 'I_5 => c^-1 i) @^-1:
        [set j : 'I_5 | s j == j].
  by apply/setP=> i; rewrite !inE.
rewrite hpre.
apply: card_preimset.
exact: perm_inj.
Qed.

Lemma f20_power_one_conjugate (s c : S5) (n : nat) :
  ((s ^ c) ^+ n == 1%g) = (s ^+ n == 1%g).
Proof.
rewrite -conjXg.
apply/eqP/eqP=> h.
- apply: (conjg_inj c).
  by rewrite h conj1g.
- by rewrite h conj1g.
Qed.

Lemma f20_identity_classb_conjugate s c :
  f20_identity_classb (s ^ c) = f20_identity_classb s.
Proof. by rewrite /f20_identity_classb conjg_eq1. Qed.

Lemma f20_five_cycle_classb_conjugate s c :
  f20_five_cycle_classb (s ^ c) = f20_five_cycle_classb s.
Proof.
by rewrite /f20_five_cycle_classb f20_fixed_count_conjugate
  f20_power_one_conjugate.
Qed.

Lemma f20_one_two_two_classb_conjugate s c :
  f20_one_two_two_classb (s ^ c) = f20_one_two_two_classb s.
Proof.
by rewrite /f20_one_two_two_classb f20_fixed_count_conjugate
  f20_power_one_conjugate.
Qed.

Lemma f20_one_four_classb_conjugate s c :
  f20_one_four_classb (s ^ c) = f20_one_four_classb s.
Proof.
by rewrite /f20_one_four_classb f20_fixed_count_conjugate
  !f20_power_one_conjugate.
Qed.

(** The distinguished five-cycle has no fixed letter. *)
Lemma five_cycle_no_fixed i : five_cycle i != i.
Proof.
case: i=> [[|[|[|[|[|i]]]]] hi].
- have -> : @Ordinal 5 0 hi = o0 by apply/val_inj.
  by rewrite five_cycle_o0.
- have -> : @Ordinal 5 1 hi = o1 by apply/val_inj.
  by rewrite five_cycle_o1.
- have -> : @Ordinal 5 2 hi = o2 by apply/val_inj.
  by rewrite five_cycle_o2.
- have -> : @Ordinal 5 3 hi = o3 by apply/val_inj.
  by rewrite five_cycle_o3.
- have -> : @Ordinal 5 4 hi = o4 by apply/val_inj.
  by rewrite five_cycle_o4.
- by move: hi.
Qed.

Lemma f20_fixed_count_five_cycle : f20_fixed_count five_cycle = 0%N.
Proof.
rewrite /f20_fixed_count f20_count_enum_pred -cardsE.
have -> : [set i : 'I_5 | five_cycle i == i] = set0.
  apply/setP=> i; rewrite !inE.
  exact: negPf (five_cycle_no_fixed i).
exact: cards0.
Qed.

(** The multiplier and its two nontrivial powers each fix exactly [o0]. *)
Lemma multiplier_two_fixedP i :
  (multiplier_two i == i) = (i == o0).
Proof.
case: i=> [[|[|[|[|[|i]]]]] hi].
- have -> : @Ordinal 5 0 hi = o0 by apply/val_inj.
  by rewrite multiplier_two_o0 !eqxx.
- have -> : @Ordinal 5 1 hi = o1 by apply/val_inj.
  by rewrite multiplier_two_o1.
- have -> : @Ordinal 5 2 hi = o2 by apply/val_inj.
  by rewrite multiplier_two_o2.
- have -> : @Ordinal 5 3 hi = o3 by apply/val_inj.
  by rewrite multiplier_two_o3.
- have -> : @Ordinal 5 4 hi = o4 by apply/val_inj.
  by rewrite multiplier_two_o4.
- by move: hi.
Qed.

Lemma multiplier_two_sq_fixedP i :
  (multiplier_two ^+ 2) i == i = (i == o0).
Proof.
case: i=> [[|[|[|[|[|i]]]]] hi].
- have -> : @Ordinal 5 0 hi = o0 by apply/val_inj.
  by rewrite expgS expg1 permM !multiplier_two_o0 !eqxx.
- have -> : @Ordinal 5 1 hi = o1 by apply/val_inj.
  by rewrite expgS expg1 permM multiplier_two_o1 multiplier_two_o2.
- have -> : @Ordinal 5 2 hi = o2 by apply/val_inj.
  by rewrite expgS expg1 permM multiplier_two_o2 multiplier_two_o4.
- have -> : @Ordinal 5 3 hi = o3 by apply/val_inj.
  by rewrite expgS expg1 permM multiplier_two_o3 multiplier_two_o1.
- have -> : @Ordinal 5 4 hi = o4 by apply/val_inj.
  by rewrite expgS expg1 permM multiplier_two_o4 multiplier_two_o3.
- by move: hi.
Qed.

Lemma multiplier_two_cube_fixedP i :
  (multiplier_two ^+ 3) i == i = (i == o0).
Proof.
case: i=> [[|[|[|[|[|i]]]]] hi].
- have -> : @Ordinal 5 0 hi = o0 by apply/val_inj.
  by rewrite expgS expgS expg1 permM permM multiplier_two_o0
    multiplier_two_o0 multiplier_two_o0 !eqxx.
- have -> : @Ordinal 5 1 hi = o1 by apply/val_inj.
  by rewrite expgS expgS expg1 permM permM multiplier_two_o1 multiplier_two_o2
    multiplier_two_o4.
- have -> : @Ordinal 5 2 hi = o2 by apply/val_inj.
  by rewrite expgS expgS expg1 permM permM multiplier_two_o2 multiplier_two_o4
    multiplier_two_o3.
- have -> : @Ordinal 5 3 hi = o3 by apply/val_inj.
  by rewrite expgS expgS expg1 permM permM multiplier_two_o3 multiplier_two_o1
    multiplier_two_o2.
- have -> : @Ordinal 5 4 hi = o4 by apply/val_inj.
  by rewrite expgS expgS expg1 permM permM multiplier_two_o4 multiplier_two_o3
    multiplier_two_o1.
- by move: hi.
Qed.

Lemma f20_fixed_count_multiplier_two :
  f20_fixed_count multiplier_two = 1%N.
Proof.
rewrite /f20_fixed_count f20_count_enum_pred -cardsE.
have -> : [set i : 'I_5 | multiplier_two i == i] = [set o0].
  by apply/setP=> i; rewrite !inE multiplier_two_fixedP.
exact: cards1.
Qed.

Lemma f20_fixed_count_multiplier_two_sq :
  f20_fixed_count (multiplier_two ^+ 2) = 1%N.
Proof.
rewrite /f20_fixed_count f20_count_enum_pred -cardsE.
have -> : [set i : 'I_5 | (multiplier_two ^+ 2) i == i] = [set o0].
  by apply/setP=> i; rewrite !inE multiplier_two_sq_fixedP.
exact: cards1.
Qed.

Lemma f20_fixed_count_multiplier_two_cube :
  f20_fixed_count (multiplier_two ^+ 3) = 1%N.
Proof.
rewrite /f20_fixed_count f20_count_enum_pred -cardsE.
have -> : [set i : 'I_5 | (multiplier_two ^+ 3) i == i] = [set o0].
  by apply/setP=> i; rewrite !inE multiplier_two_cube_fixedP.
exact: cards1.
Qed.

Lemma multiplier_two_sq_neq1 : multiplier_two ^+ 2 != 1%g.
Proof.
apply/eqP=> hm2.
have hpoint := congr1 (fun p : S5 => p o1) hm2.
by move: hpoint; rewrite expgS expg1 permM
  multiplier_two_o1 multiplier_two_o2 perm1.
Qed.

Lemma multiplier_two_cube_expg4 :
  (multiplier_two ^+ 3) ^+ 4 = 1%g.
Proof.
by rewrite -expgnA mulnC expgnA multiplier_two_expg4 expg1n.
Qed.

Lemma multiplier_two_cube_sq_neq1 :
  (multiplier_two ^+ 3) ^+ 2 != 1%g.
Proof.
apply/eqP=> hm32.
have hm31 : (multiplier_two ^+ 3) o1 = o3.
  by rewrite expgS expgS expg1 permM permM
    multiplier_two_o1 multiplier_two_o2 multiplier_two_o4.
have hm33 : (multiplier_two ^+ 3) o3 = o4.
  by rewrite expgS expgS expg1 permM permM
    multiplier_two_o3 multiplier_two_o1 multiplier_two_o2.
have hpoint := congr1 (fun p : S5 => p o1) hm32.
by move: hpoint; rewrite expgS expg1 permM hm31 hm33 perm1.
Qed.

Lemma five_cycle_classb_base : f20_five_cycle_classb five_cycle.
Proof.
have hc5 := expg_order five_cycle.
rewrite order_five_cycle in hc5.
by rewrite /f20_five_cycle_classb f20_fixed_count_five_cycle hc5 !eqxx.
Qed.

Lemma multiplier_two_one_four_base :
  f20_one_four_classb multiplier_two.
Proof.
by rewrite /f20_one_four_classb f20_fixed_count_multiplier_two
  multiplier_two_expg4 multiplier_two_sq_neq1 !eqxx.
Qed.

Lemma multiplier_two_sq_one_two_two_base :
  f20_one_two_two_classb (multiplier_two ^+ 2).
Proof.
have hm22 : (multiplier_two ^+ 2) ^+ 2 = 1%g.
  by rewrite -expgnA multiplier_two_expg4.
by rewrite /f20_one_two_two_classb f20_fixed_count_multiplier_two_sq
  hm22 !eqxx.
Qed.

Lemma multiplier_two_cube_one_four_base :
  f20_one_four_classb (multiplier_two ^+ 3).
Proof.
by rewrite /f20_one_four_classb f20_fixed_count_multiplier_two_cube
  multiplier_two_cube_expg4 multiplier_two_cube_sq_neq1 !eqxx.
Qed.

(** An element of the regular [C5] fixing [o0] is the identity. *)
Lemma standard_C5_fix_o0_identity s :
  s \in standard_C5 -> s o0 = o0 -> s = 1%g.
Proof.
move=> hs hfix.
case/cyclePmin: hs=> k hk hsE.
subst s.
rewrite order_five_cycle in hk.
case: k hk hfix=> [|[|[|[|[|k]]]]] hk hfix.
- by rewrite expg0.
- rewrite expg1 five_cycle_o0 in hfix.
  by move: hfix.
- rewrite expgS expg1 permM five_cycle_o0 five_cycle_o4 in hfix.
  by move: hfix.
- rewrite expgS expgS expg1 permM permM five_cycle_o0 five_cycle_o4
    five_cycle_o3 in hfix.
  by move: hfix.
- rewrite expgS expgS expgS expg1 permM permM permM five_cycle_o0 five_cycle_o4
    five_cycle_o3 five_cycle_o2 in hfix.
  by move: hfix.
- by move: hk.
Qed.

Lemma standard_C4_fix_o0 s : s \in standard_C4 -> s o0 = o0.
Proof.
move=> hs.
case/cyclePmin: hs=> k _ ->.
elim: k=> [|k IH].
- by rewrite expg0 perm1.
- by rewrite expgS permM multiplier_two_o0 IH.
Qed.

(** A multiplier power with unique fixed point [o0] has trivial
    centralizer inside the translation subgroup. *)
Lemma standard_C5_centralizer_trivial (u : S5)
    (hu0 : u o0 = o0)
    (hufix : forall i, u i = i -> i = o0) :
  'C_standard_C5[u] :=: 1%G.
Proof.
apply/trivgP/subsetP=> s hs.
move/setIP: hs=> [hsC /cent1P hcomm].
have hpoint := congr1 (fun p : S5 => p o0) hcomm.
have hus : u (s o0) = s o0.
  by move: hpoint; rewrite !permM hu0.
have hs0 : s o0 = o0 := hufix _ hus.
have hs1 : s = 1%g := standard_C5_fix_o0_identity hsC hs0.
by rewrite !inE hs1 eqxx.
Qed.

Lemma multiplier_two_unique_fixed i :
  multiplier_two i = i -> i = o0.
Proof. by move=> /eqP; rewrite multiplier_two_fixedP => /eqP. Qed.

Lemma multiplier_two_sq_unique_fixed i :
  (multiplier_two ^+ 2) i = i -> i = o0.
Proof. by move=> /eqP; rewrite multiplier_two_sq_fixedP => /eqP. Qed.

Lemma multiplier_two_cube_unique_fixed i :
  (multiplier_two ^+ 3) i = i -> i = o0.
Proof. by move=> /eqP; rewrite multiplier_two_cube_fixedP => /eqP. Qed.

Lemma multiplier_two_C5_centralizer_trivial :
  'C_standard_C5[multiplier_two] :=: 1%G.
Proof.
exact: standard_C5_centralizer_trivial multiplier_two_o0
  multiplier_two_unique_fixed.
Qed.

Lemma multiplier_two_sq_C5_centralizer_trivial :
  'C_standard_C5[multiplier_two ^+ 2] :=: 1%G.
Proof.
apply: standard_C5_centralizer_trivial.
- by rewrite expgS expg1 permM !multiplier_two_o0.
- exact: multiplier_two_sq_unique_fixed.
Qed.

Lemma multiplier_two_cube_C5_centralizer_trivial :
  'C_standard_C5[multiplier_two ^+ 3] :=: 1%G.
Proof.
apply: standard_C5_centralizer_trivial.
- by rewrite expgS expgS expg1 permM permM multiplier_two_o0
    multiplier_two_o0 multiplier_two_o0.
- exact: multiplier_two_cube_unique_fixed.
Qed.

Lemma five_cycle_C4_centralizer_trivial :
  'C_standard_C4[five_cycle] :=: 1%G.
Proof.
apply/trivgP/subsetP=> s hs.
move/setIP: hs=> [hsC4 /cent1P hcomm].
have hs0 := standard_C4_fix_o0 hsC4.
have hpoint0 := congr1 (fun p : S5 => p o0) hcomm.
have hs4 : s o4 = o4.
  move: hpoint0; rewrite !permM hs0 => h.
  rewrite !tpermL in h.
  exact: esym h.
have hpoint4 := congr1 (fun p : S5 => p o4) hcomm.
have hs3 : s o3 = o3.
  move: hpoint4; rewrite !permM hs4 => h.
  rewrite (tpermD (x := o0) (y := o1) (z := o4)) // in h.
  rewrite (tpermD (x := o1) (y := o2) (z := o4)) // in h.
  rewrite (tpermD (x := o2) (y := o3) (z := o4)) // tpermR in h.
  exact: esym h.
have hsF20 : s \in standard_F20 :=
  (subsetP standard_C4_sub_standard_F20) s hsC4.
have hs1 : s = 1%g := normalizer_fix34_identity hsF20 hs3 hs4.
by rewrite !inE hs1 eqxx.
Qed.

Lemma five_cycle_C4_class_sub_C5_nonidentity :
  five_cycle ^: standard_C4 \subset standard_C5 :\ 1%g.
Proof.
apply/subsetP=> z /imsetP[s hs ->].
apply/setD1P; split.
- have hc1 : five_cycle != 1%g.
    by rewrite -order_eq1 order_five_cycle.
  by rewrite conjg_eq1 hc1.
- have hsN : s \in 'N(standard_C5) :=
    (subsetP standard_C4_sub_standard_F20) s hs.
  by rewrite memJ_norm //; exact: cycle_id.
Qed.

Lemma five_cycle_C4_class_card :
  #|five_cycle ^: standard_C4| = 4%N.
Proof.
by rewrite -index_cent1 five_cycle_C4_centralizer_trivial
  indexg1 card_standard_C4.
Qed.

Lemma standard_C5_nonidentity_card :
  #|standard_C5 :\ 1%g| = 4%N.
Proof.
have h := cardsD1 1%g standard_C5.
rewrite card_standard_C5 group1 in h.
change (5 = 1 + #|standard_C5^#|)%N in h.
change (S 4 = S #|standard_C5^#|) in h.
have hp := congr1 predn h.
change (4 = #|standard_C5^#|)%N in hp.
exact: esym hp.
Qed.

Lemma five_cycle_C4_classE :
  five_cycle ^: standard_C4 = standard_C5 :\ 1%g.
Proof.
apply/eqP.
by rewrite eqEcard five_cycle_C4_class_sub_C5_nonidentity
  five_cycle_C4_class_card standard_C5_nonidentity_card leqnn.
Qed.

(** Conjugating a multiplier power by [C5] fills its entire right coset.
    The proof uses the trivial centralizer and equal cardinalities, rather
    than listing the five coset elements. *)
Lemma C5_class_eq_rcoset u
    (huC4 : u \in standard_C4)
    (hcent : 'C_standard_C5[u] :=: 1%G) :
  u ^: standard_C5 = standard_C5 :* u.
Proof.
have huN : u \in 'N(standard_C5) :=
  (subsetP standard_C4_sub_standard_F20) u huC4.
have hsub : u ^: standard_C5 \subset standard_C5 :* u.
  apply/subsetP=> z /imsetP[s hs ->].
  rewrite mem_rcoset conjgE !mulgA.
  have hsJ : s ^ u^-1 \in standard_C5.
    by rewrite memJ_norm ?groupV //.
  have heq : s^-1 * u * s * u^-1 = s^-1 * (s ^ u^-1).
    by rewrite conjgE invgK !mulgA.
  rewrite heq.
  have hsV : s^-1 \in standard_C5 by rewrite groupV.
  exact: groupM hsV hsJ.
apply/eqP.
by rewrite eqEcard hsub card_rcoset -index_cent1 hcent indexg1 leqnn.
Qed.

Lemma multiplier_two_C5_classE :
  multiplier_two ^: standard_C5 = standard_C5 :* multiplier_two.
Proof.
apply: C5_class_eq_rcoset.
- exact: cycle_id.
- exact: multiplier_two_C5_centralizer_trivial.
Qed.

Lemma multiplier_two_sq_C5_classE :
  (multiplier_two ^+ 2) ^: standard_C5 =
    standard_C5 :* (multiplier_two ^+ 2).
Proof.
apply: C5_class_eq_rcoset.
- exact: mem_cycle.
- exact: multiplier_two_sq_C5_centralizer_trivial.
Qed.

Lemma multiplier_two_cube_C5_classE :
  (multiplier_two ^+ 3) ^: standard_C5 =
    standard_C5 :* (multiplier_two ^+ 3).
Proof.
apply: C5_class_eq_rcoset.
- exact: mem_cycle.
- exact: multiplier_two_cube_C5_centralizer_trivial.
Qed.

Lemma five_cycle_class_sub_f20 :
  five_cycle ^: standard_C4 \subset
    f20_class f20_five_cycle_classb.
Proof.
apply/subsetP=> z /imsetP[s hs ->].
rewrite inE.
change (normalizes_cycleb (five_cycle ^ s) &&
  f20_five_cycle_classb (five_cycle ^ s)).
rewrite normalizes_cyclebE.
apply/andP; split.
- have hzC5 : five_cycle ^ s \in standard_C5.
    have hsN : s \in 'N(standard_C5) :=
      (subsetP standard_C4_sub_standard_F20) s hs.
    by rewrite memJ_norm //; exact: cycle_id.
  exact: (subsetP (normG standard_C5)) _ hzC5.
- by rewrite f20_five_cycle_classb_conjugate five_cycle_classb_base.
Qed.

Lemma multiplier_two_class_sub_f20 :
  multiplier_two ^: standard_C5 \subset f20_class f20_one_four_classb.
Proof.
apply/subsetP=> z /imsetP[s hs ->].
rewrite inE.
change (normalizes_cycleb (multiplier_two ^ s) &&
  f20_one_four_classb (multiplier_two ^ s)).
rewrite normalizes_cyclebE.
apply/andP; split.
- have hsF20 : s \in standard_F20 :=
    (subsetP (normG standard_C5)) _ hs.
  have huF20 : multiplier_two \in standard_F20 :=
    multiplier_two_mem_standard_F20.
  by rewrite groupJr.
- by rewrite f20_one_four_classb_conjugate multiplier_two_one_four_base.
Qed.

Lemma multiplier_two_sq_class_sub_f20 :
  (multiplier_two ^+ 2) ^: standard_C5 \subset
    f20_class f20_one_two_two_classb.
Proof.
apply/subsetP=> z /imsetP[s hs ->].
rewrite inE.
change (normalizes_cycleb ((multiplier_two ^+ 2) ^ s) &&
  f20_one_two_two_classb ((multiplier_two ^+ 2) ^ s)).
rewrite normalizes_cyclebE.
apply/andP; split.
- have hsF20 : s \in standard_F20 :=
    (subsetP (normG standard_C5)) _ hs.
  have huF20 : multiplier_two ^+ 2 \in standard_F20.
    exact: groupX multiplier_two_mem_standard_F20.
  by rewrite groupJr.
- by rewrite f20_one_two_two_classb_conjugate
    multiplier_two_sq_one_two_two_base.
Qed.

Lemma multiplier_two_cube_class_sub_f20 :
  (multiplier_two ^+ 3) ^: standard_C5 \subset
    f20_class f20_one_four_classb.
Proof.
apply/subsetP=> z /imsetP[s hs ->].
rewrite inE.
change (normalizes_cycleb ((multiplier_two ^+ 3) ^ s) &&
  f20_one_four_classb ((multiplier_two ^+ 3) ^ s)).
rewrite normalizes_cyclebE.
apply/andP; split.
- have hsF20 : s \in standard_F20 :=
    (subsetP (normG standard_C5)) _ hs.
  have huF20 : multiplier_two ^+ 3 \in standard_F20.
    exact: groupX multiplier_two_mem_standard_F20.
  by rewrite groupJr.
- by rewrite f20_one_four_classb_conjugate
    multiplier_two_cube_one_four_base.
Qed.

(** Every element of [F20] has a unique multiplier exponent modulo four.
    We only need existence here; uniqueness is used below through disjointness
    of the two order-four cosets. *)
Lemma standard_F20_structural_cases s :
  s \in standard_F20 ->
    s = 1%g \/
    s \in five_cycle ^: standard_C4 \/
    s \in multiplier_two ^: standard_C5 \/
    s \in (multiplier_two ^+ 2) ^: standard_C5 \/
    s \in (multiplier_two ^+ 3) ^: standard_C5.
Proof.
move=> hs.
have hnorm : standard_C4 \subset 'N(standard_C5).
  exact: standard_C4_sub_standard_F20.
have hjoin : (affine_F20 : {set S5}) =
    (standard_C5 * standard_C4)%g.
  exact: norm_joinEr hnorm.
have hsprod : s \in (standard_C5 * standard_C4)%g.
  by move: hs; rewrite -affine_F20E hjoin.
case/imset2P: hsprod=> x y hx hy ->.
case/cyclePmin: hy=> k hk ->.
rewrite order_multiplier_two in hk.
case: k hk=> [|[|[|[|k]]]] hk.
- rewrite expg0 mulg1.
  case hx1: (x == 1%g).
  + by left; exact/eqP.
  + right; left; rewrite five_cycle_C4_classE.
    apply/setD1P; split.
    * by rewrite hx1.
    * exact: hx.
- right; right; left.
  rewrite multiplier_two_C5_classE expg1.
  by apply/rcosetP; exists x.
- right; right; right; left.
  rewrite multiplier_two_sq_C5_classE.
  by apply/rcosetP; exists x.
- right; right; right; right.
  rewrite multiplier_two_cube_C5_classE.
  by apply/rcosetP; exists x.
- by move: hk.
Qed.

Lemma f20_fixed_count_one : f20_fixed_count (1%g : S5) = 5%N.
Proof.
rewrite /f20_fixed_count.
have hone : [pred i : 'I_5 | (1%g : S5) i == i] =1 predT.
  by move=> i; rewrite /= perm1 eqxx.
by rewrite (eq_count hone) count_predT size_enum_ord.
Qed.

(** The fixed-point count separates the translation class from the three
    multiplier classes; the square test separates exponent two from the two
    order-four classes. *)
Lemma five_cycle_C4_fixed_count z :
  z \in five_cycle ^: standard_C4 -> f20_fixed_count z = 0%N.
Proof.
by move=> /imsetP[c hc ->]; rewrite f20_fixed_count_conjugate
  f20_fixed_count_five_cycle.
Qed.

Lemma multiplier_two_C5_fixed_count z :
  z \in multiplier_two ^: standard_C5 -> f20_fixed_count z = 1%N.
Proof.
by move=> /imsetP[c hc ->]; rewrite f20_fixed_count_conjugate
  f20_fixed_count_multiplier_two.
Qed.

Lemma multiplier_two_sq_C5_fixed_count z :
  z \in (multiplier_two ^+ 2) ^: standard_C5 ->
  f20_fixed_count z = 1%N.
Proof.
by move=> /imsetP[c hc ->]; rewrite f20_fixed_count_conjugate
  f20_fixed_count_multiplier_two_sq.
Qed.

Lemma multiplier_two_cube_C5_fixed_count z :
  z \in (multiplier_two ^+ 3) ^: standard_C5 ->
  f20_fixed_count z = 1%N.
Proof.
by move=> /imsetP[c hc ->]; rewrite f20_fixed_count_conjugate
  f20_fixed_count_multiplier_two_cube.
Qed.

Lemma multiplier_two_C5_sq_neq1 z :
  z \in multiplier_two ^: standard_C5 -> z ^+ 2 != 1%g.
Proof.
by move=> /imsetP[c hc ->]; rewrite f20_power_one_conjugate
  multiplier_two_sq_neq1.
Qed.

Lemma multiplier_two_sq_C5_sq_eq1 z :
  z \in (multiplier_two ^+ 2) ^: standard_C5 -> z ^+ 2 = 1%g.
Proof.
move=> /imsetP[c hc ->].
by rewrite -conjXg -expgnA multiplier_two_expg4 conj1g.
Qed.

Lemma multiplier_two_cube_C5_sq_neq1 z :
  z \in (multiplier_two ^+ 3) ^: standard_C5 -> z ^+ 2 != 1%g.
Proof.
by move=> /imsetP[c hc ->]; rewrite f20_power_one_conjugate
  multiplier_two_cube_sq_neq1.
Qed.

Lemma f20_identity_classE :
  f20_class f20_identity_classb = [set (1%g : S5)].
Proof.
apply/setP=> s; rewrite !inE /f20_class /f20_identity_classb.
apply/idP/idP.
- by move=> /andP[_ /eqP ->]; rewrite eqxx.
- move=> /eqP ->.
  by rewrite normalizes_cyclebE group1 eqxx.
Qed.

Lemma f20_five_cycle_classE :
  f20_class f20_five_cycle_classb = five_cycle ^: standard_C4.
Proof.
apply/setP=> z; apply/idP/idP.
- rewrite inE.
  rewrite normalizes_cyclebE.
  move=> /andP[hzF20 hzP].
  move/andP: hzP=> [/eqP hzfix _].
  change (f20_fixed_count z = 0%N) in hzfix.
  case: (standard_F20_structural_cases hzF20)=>
    [hz1 | [hz5 | [hzm | [hzm2 | hzm3]]]].
  + subst z. by move: hzfix; rewrite f20_fixed_count_one.
  + exact: hz5.
  + by move: hzfix; rewrite (multiplier_two_C5_fixed_count hzm).
  + by move: hzfix; rewrite (multiplier_two_sq_C5_fixed_count hzm2).
  + by move: hzfix; rewrite (multiplier_two_cube_C5_fixed_count hzm3).
- exact: (subsetP five_cycle_class_sub_f20) z.
Qed.

Lemma f20_one_two_two_classE :
  f20_class f20_one_two_two_classb =
    (multiplier_two ^+ 2) ^: standard_C5.
Proof.
apply/setP=> z; apply/idP/idP.
- rewrite inE.
  rewrite normalizes_cyclebE.
  move=> /andP[hzF20 hzP].
  move/andP: hzP=> [/eqP hzfix /eqP hzsq].
  change (f20_fixed_count z = 1%N) in hzfix.
  case: (standard_F20_structural_cases hzF20)=>
    [hz1 | [hz5 | [hzm | [hzm2 | hzm3]]]].
  + subst z. by move: hzfix; rewrite f20_fixed_count_one.
  + by move: hzfix; rewrite (five_cycle_C4_fixed_count hz5).
  + have hzneq := multiplier_two_C5_sq_neq1 hzm.
    by move: hzneq; rewrite hzsq eqxx.
  + exact: hzm2.
  + have hzneq := multiplier_two_cube_C5_sq_neq1 hzm3.
    by move: hzneq; rewrite hzsq eqxx.
- exact: (subsetP multiplier_two_sq_class_sub_f20) z.
Qed.

Lemma f20_one_four_classE :
  f20_class f20_one_four_classb =
    (multiplier_two ^: standard_C5) :|:
      ((multiplier_two ^+ 3) ^: standard_C5).
Proof.
apply/setP=> z; apply/idP/idP.
- rewrite inE.
  rewrite normalizes_cyclebE.
  move=> /andP[hzF20 hzP].
  move/andP: hzP=> [hzP hzsq_neq].
  move/andP: hzP=> [/eqP hzfix _].
  change (f20_fixed_count z = 1%N) in hzfix.
  case: (standard_F20_structural_cases hzF20)=>
    [hz1 | [hz5 | [hzm | [hzm2 | hzm3]]]].
  + subst z. by move: hzfix; rewrite f20_fixed_count_one.
  + by move: hzfix; rewrite (five_cycle_C4_fixed_count hz5).
  + by rewrite inE hzm.
  + have hzsq := multiplier_two_sq_C5_sq_eq1 hzm2.
    by move: hzsq_neq; rewrite hzsq eqxx.
  + by rewrite inE hzm3 orbT.
- rewrite inE.
  move=> /orP[hz | hz].
  + exact: (subsetP multiplier_two_class_sub_f20) hz.
  + exact: (subsetP multiplier_two_cube_class_sub_f20) hz.
Qed.

Lemma multiplier_two_C5_class_card :
  #|multiplier_two ^: standard_C5| = 5%N.
Proof.
by rewrite multiplier_two_C5_classE card_rcoset card_standard_C5.
Qed.

Lemma multiplier_two_sq_C5_class_card :
  #|(multiplier_two ^+ 2) ^: standard_C5| = 5%N.
Proof.
by rewrite multiplier_two_sq_C5_classE card_rcoset card_standard_C5.
Qed.

Lemma multiplier_two_cube_C5_class_card :
  #|(multiplier_two ^+ 3) ^: standard_C5| = 5%N.
Proof.
by rewrite multiplier_two_cube_C5_classE card_rcoset card_standard_C5.
Qed.

Lemma multiplier_two_sq_notin_standard_C5 :
  multiplier_two ^+ 2 \notin standard_C5.
Proof.
have hti : standard_C5 :&: standard_C4 = 1%G.
  apply: coprime_TIg.
  by rewrite card_standard_C5 card_standard_C4.
apply/negP=> hmC5.
have hmC4 : multiplier_two ^+ 2 \in standard_C4.
  exact: mem_cycle.
have hmI : multiplier_two ^+ 2 \in standard_C5 :&: standard_C4.
  by rewrite inE hmC5 hmC4.
move: hmI; rewrite hti !inE => /eqP hm1.
by move: multiplier_two_sq_neq1; rewrite hm1 eqxx.
Qed.

Lemma multiplier_two_classes_disjoint :
  [disjoint multiplier_two ^: standard_C5 &
    (multiplier_two ^+ 3) ^: standard_C5].
Proof.
rewrite multiplier_two_C5_classE multiplier_two_cube_C5_classE.
rewrite disjoint_subset.
apply/subsetP=> z hzm.
rewrite inE.
apply/negP=> hzm3.
have /rcoset_eqP hcosm := hzm.
have /rcoset_eqP hcosm3 := hzm3.
have hcos : standard_C5 :* multiplier_two =
    standard_C5 :* (multiplier_two ^+ 3) :=
  eq_trans (esym hcosm) hcosm3.
have hm : multiplier_two \in standard_C5 :* (multiplier_two ^+ 3).
  apply/rcoset_eqP.
  exact: hcos.
have hm3inv : (multiplier_two ^+ 3)^-1 = multiplier_two.
  apply: (mulIg (multiplier_two ^+ 3)).
  by rewrite mulVg -expgS multiplier_two_expg4.
have hmm : multiplier_two * multiplier_two = multiplier_two ^+ 2.
  by rewrite expgS expg1.
move: hm; rewrite mem_rcoset hm3inv hmm => hmC5.
by move: multiplier_two_sq_notin_standard_C5; rewrite hmC5.
Qed.

Lemma card_f20_identity_class :
  #|f20_class f20_identity_classb| = 1%N.
Proof. by rewrite f20_identity_classE cards1. Qed.

Lemma card_f20_five_cycle_class :
  #|f20_class f20_five_cycle_classb| = 4%N.
Proof. by rewrite f20_five_cycle_classE five_cycle_C4_class_card. Qed.

Lemma card_f20_one_two_two_class :
  #|f20_class f20_one_two_two_classb| = 5%N.
Proof. by rewrite f20_one_two_two_classE multiplier_two_sq_C5_class_card. Qed.

Lemma card_f20_one_four_class :
  #|f20_class f20_one_four_classb| = 10%N.
Proof.
rewrite f20_one_four_classE cardsU
  (disjoint_setI0 multiplier_two_classes_disjoint) cards0
  multiplier_two_C5_class_card multiplier_two_cube_C5_class_card.
by [].
Qed.

(** The four predicates cover every member of the standard [F20]. *)
Lemma f20_cycle_classes_exhaustb :
  [forall s : S5,
    normalizes_cycleb s ==>
      (f20_identity_classb s || f20_five_cycle_classb s ||
       f20_one_two_two_classb s || f20_one_four_classb s)].
Proof.
apply/forallP=> s.
apply/implyP=> hs.
rewrite normalizes_cyclebE in hs.
case: (standard_F20_structural_cases hs)=>
  [-> | [hs5 | [hsm | [hsm2 | hsm3]]]].
- by rewrite /f20_identity_classb eqxx.
- have hsP := (subsetP five_cycle_class_sub_f20) s hs5.
  rewrite inE in hsP.
  move/andP: hsP=> [_ hsP].
  by rewrite hsP !orbT.
- have hsP := (subsetP multiplier_two_class_sub_f20) s hsm.
  rewrite inE in hsP.
  move/andP: hsP=> [_ hsP].
  by rewrite hsP !orbT.
- have hsP := (subsetP multiplier_two_sq_class_sub_f20) s hsm2.
  rewrite inE in hsP.
  move/andP: hsP=> [_ hsP].
  by rewrite hsP !orbT.
- have hsP := (subsetP multiplier_two_cube_class_sub_f20) s hsm3.
  rewrite inE in hsP.
  move/andP: hsP=> [_ hsP].
  by rewrite hsP !orbT.
Qed.

Theorem f20_cycle_class_counts :
  #|f20_class f20_identity_classb| = 1%N /\
  #|f20_class f20_five_cycle_classb| = 4%N /\
  #|f20_class f20_one_two_two_classb| = 5%N /\
  #|f20_class f20_one_four_classb| = 10%N.
Proof.
repeat split.
- exact: card_f20_identity_class.
- exact: card_f20_five_cycle_class.
- exact: card_f20_one_two_two_class.
- exact: card_f20_one_four_class.
Qed.

(** * The exact algebraic class-sum identity *)

Section MolienAlgebra.

Local Close Scope group_scope.
Local Open Scope ring_scope.

Variable F : fieldType.

Definition f20_molien_identity_denominator (t : F) : F :=
  (1 - t) ^+ 5.

Definition f20_molien_five_denominator (t : F) : F :=
  1 - t ^+ 5.

Definition f20_molien_one_two_two_denominator (t : F) : F :=
  (1 - t) * (1 - t ^+ 2) ^+ 2.

Definition f20_molien_one_four_denominator (t : F) : F :=
  (1 - t) * (1 - t ^+ 4).

Definition f20_molien_numerator (t : F) : F :=
  1 + t ^+ 4 + t ^+ 5 + t ^+ 6 + t ^+ 7 + t ^+ 8.

Definition f20_symmetric_denominator (t : F) : F :=
  (1 - t) * (1 - t ^+ 2) * (1 - t ^+ 3) *
    (1 - t ^+ 4) * (1 - t ^+ 5).

Definition f20_molien_class_sum (t : F) : F :=
  (1 / 20%:R) *
    (1 / f20_molien_identity_denominator t +
     4%:R / f20_molien_five_denominator t +
     5%:R / f20_molien_one_two_two_denominator t +
     10%:R / f20_molien_one_four_denominator t).

(** Product of the four class denominators. *)
Definition f20_molien_common_denominator (t : F) : F :=
  f20_molien_identity_denominator t *
  f20_molien_five_denominator t *
  f20_molien_one_two_two_denominator t *
  f20_molien_one_four_denominator t.

(** The numerator of the four-term class sum after using the common
    denominator, before dividing by the group order 20. *)
Definition f20_molien_weighted_complement (t : F) : F :=
  f20_molien_five_denominator t *
      f20_molien_one_two_two_denominator t *
      f20_molien_one_four_denominator t +
  4%:R * (f20_molien_identity_denominator t *
      f20_molien_one_two_two_denominator t *
      f20_molien_one_four_denominator t) +
  5%:R * (f20_molien_identity_denominator t *
      f20_molien_five_denominator t *
      f20_molien_one_four_denominator t) +
  10%:R * (f20_molien_identity_denominator t *
      f20_molien_five_denominator t *
      f20_molien_one_two_two_denominator t).

(** Local bridge from MathComp's packed field operations to the standard
    [ring] and [field] tactics. *)
Let molien_carrier : Type := F.
Local Definition molien_zero : molien_carrier := @GRing.zero F.
Local Definition molien_one : molien_carrier := @GRing.one F.
Local Definition molien_add : molien_carrier -> molien_carrier -> molien_carrier :=
  @GRing.add F.
Local Definition molien_mul : molien_carrier -> molien_carrier -> molien_carrier :=
  @GRing.mul F.
Local Definition molien_sub : molien_carrier -> molien_carrier -> molien_carrier :=
  fun x y => x - y.
Local Definition molien_opp : molien_carrier -> molien_carrier := @GRing.opp F.
Local Definition molien_div : molien_carrier -> molien_carrier -> molien_carrier :=
  fun x y => (x / y)%R.
Local Definition molien_inv : molien_carrier -> molien_carrier := @GRing.inv F.
Local Definition molien_eq : molien_carrier -> molien_carrier -> Prop :=
  @eq molien_carrier.

Lemma molien_addE (x y : F) : (x + y)%R = molien_add x y.
Proof. reflexivity. Qed.
Lemma molien_mulE (x y : F) : (x * y)%R = molien_mul x y.
Proof. reflexivity. Qed.
Lemma molien_subE (x y : F) : (x - y)%R = molien_sub x y.
Proof. reflexivity. Qed.
Lemma molien_oppE (x : F) : (- x)%R = molien_opp x.
Proof. reflexivity. Qed.
Lemma molien_divE (x y : F) : (x / y)%R = molien_div x y.
Proof. reflexivity. Qed.
Lemma molien_invE (x : F) : (x^-1)%R = molien_inv x.
Proof. reflexivity. Qed.
Lemma molien_zeroE : (0 : F)%R = molien_zero.
Proof. reflexivity. Qed.
Lemma molien_oneE : (1 : F)%R = molien_one.
Proof. reflexivity. Qed.

Lemma f20_molien_ring_theory :
  @ring_theory molien_carrier molien_zero molien_one molien_add molien_mul
    molien_sub molien_opp molien_eq.
Proof.
constructor; unfold molien_zero, molien_one, molien_add, molien_mul,
  molien_sub, molien_opp, molien_eq; intros.
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

Lemma f20_molien_field_theory :
  @field_theory molien_carrier molien_zero molien_one molien_add molien_mul
    molien_sub molien_opp molien_div molien_inv molien_eq.
Proof.
constructor.
- exact: f20_molien_ring_theory.
- unfold molien_one, molien_zero, molien_eq.
  move=> h10.
  have h := (@oner_neq0 F).
  by move: h; rewrite h10 eqxx.
- by unfold molien_div, molien_mul, molien_inv, molien_eq.
- move=> x hx.
  unfold molien_inv, molien_mul, molien_one, molien_zero, molien_eq in *.
  apply: mulVr.
  rewrite unitfE.
  apply/negP=> /eqP hx0.
  exact: hx hx0.
Qed.

Add Ring lazard_f20_molien_ring : f20_molien_ring_theory.
Add Field lazard_f20_molien_field : f20_molien_field_theory.
Opaque molien_zero molien_one molien_add molien_mul molien_sub molien_opp
  molien_div molien_inv.

Lemma f20_molien_two_natrE : (2%:R : F) = 1 + 1.
Proof. exact: (@natrD F 1 1). Qed.

Lemma f20_molien_three_natrE : (3%:R : F) = 1 + 1 + 1.
Proof.
rewrite -f20_molien_two_natrE.
exact: (@natrD F 2 1).
Qed.

Lemma f20_molien_four_natrE : (4%:R : F) = 1 + 1 + 1 + 1.
Proof.
rewrite -f20_molien_three_natrE.
exact: (@natrD F 3 1).
Qed.

Lemma f20_molien_five_natrE : (5%:R : F) = 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -f20_molien_four_natrE.
exact: (@natrD F 4 1).
Qed.

Lemma f20_molien_ten_natrE : (10%:R : F) = 5%:R + 5%:R.
Proof. exact: (@natrD F 5 5). Qed.

Lemma f20_molien_twenty_natrE : (20%:R : F) = 10%:R + 10%:R.
Proof. exact: (@natrD F 10 10). Qed.

Ltac finish_f20_molien_ring :=
  repeat first
    [ rewrite molien_addE | rewrite molien_mulE | rewrite molien_subE
    | rewrite molien_oppE | rewrite molien_zeroE | rewrite molien_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (molien_eq lhs rhs)
  end;
  ring.

Ltac finish_f20_molien_field :=
  repeat first
    [ rewrite molien_addE | rewrite molien_mulE | rewrite molien_subE
    | rewrite molien_oppE | rewrite molien_divE | rewrite molien_invE
    | rewrite molien_zeroE | rewrite molien_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (molien_eq lhs rhs)
  end;
  field.

(** Unconditional cleared-denominator form.  This is a polynomial identity
    over every field, including at the poles of the displayed fractions. *)
Theorem f20_molien_cleared_identity (t : F) :
  f20_symmetric_denominator t * f20_molien_weighted_complement t =
  20%:R * f20_molien_numerator t *
    f20_molien_common_denominator t.
Proof.
rewrite /f20_symmetric_denominator /f20_molien_weighted_complement
  /f20_molien_numerator /f20_molien_common_denominator
  /f20_molien_identity_denominator /f20_molien_five_denominator
  /f20_molien_one_two_two_denominator
  /f20_molien_one_four_denominator.
rewrite !exprS expr0 !mulr1.
rewrite f20_molien_twenty_natrE !f20_molien_ten_natrE
  !f20_molien_five_natrE !f20_molien_four_natrE.
finish_f20_molien_ring.
Qed.

(** The pole-aware class-sum equality.  Instantiating [F] with the fraction
    field of [rat['X]] and [t] with the embedded indeterminate yields the
    formal rational-function identity. *)
Theorem f20_molien_class_sum_identity (t : F)
    (h1 : 1 - t != 0)
    (h2 : 1 - t ^+ 2 != 0)
    (h3 : 1 - t ^+ 3 != 0)
    (h4 : 1 - t ^+ 4 != 0)
    (h5 : 1 - t ^+ 5 != 0)
    (h20 : (20%:R : F) != 0) :
  f20_molien_class_sum t =
    f20_molien_numerator t / f20_symmetric_denominator t.
Proof.
have hid : f20_molien_identity_denominator t != 0.
  by rewrite /f20_molien_identity_denominator; exact: expf_neq0 5 h1.
have hfive : f20_molien_five_denominator t != 0.
  by rewrite /f20_molien_five_denominator.
have htwo : f20_molien_one_two_two_denominator t != 0.
  rewrite /f20_molien_one_two_two_denominator.
  exact: mulf_neq0 h1 (expf_neq0 2 h2).
have hfour : f20_molien_one_four_denominator t != 0.
  by rewrite /f20_molien_one_four_denominator; exact: mulf_neq0 h1 h4.
have hcommon : f20_molien_common_denominator t != 0.
  rewrite /f20_molien_common_denominator.
  exact: mulf_neq0 (mulf_neq0 (mulf_neq0 hid hfive) htwo) hfour.
have hsymmetric : f20_symmetric_denominator t != 0.
  rewrite /f20_symmetric_denominator.
  exact: mulf_neq0
    (mulf_neq0 (mulf_neq0 (mulf_neq0 h1 h2) h3) h4) h5.
have h20common :
    (20%:R : F) * f20_molien_common_denominator t != 0 :=
  mulf_neq0 h20 hcommon.
have hclass :
    f20_molien_class_sum t =
      f20_molien_weighted_complement t /
        ((20%:R : F) * f20_molien_common_denominator t).
  rewrite /f20_molien_class_sum.
  rewrite (addf_div _ _ hid hfive).
  rewrite (addf_div _ _ (mulf_neq0 hid hfive) htwo).
  rewrite (addf_div _ _
    (mulf_neq0 (mulf_neq0 hid hfive) htwo) hfour).
  rewrite mulf_div mul1r /f20_molien_weighted_complement
    /f20_molien_common_denominator.
  apply/eqP.
  rewrite (eqr_div _ _ h20common h20common).
  apply/eqP.
  rewrite f20_molien_twenty_natrE !f20_molien_ten_natrE
    !f20_molien_five_natrE !f20_molien_four_natrE.
  finish_f20_molien_ring.
rewrite hclass.
apply/eqP.
rewrite (eqr_div _ _ h20common hsymmetric).
apply/eqP.
rewrite [f20_molien_weighted_complement t *
    f20_symmetric_denominator t]mulrC.
rewrite mulrA [f20_molien_numerator t * (20%:R : F)]mulrC.
exact: f20_molien_cleared_identity.
Qed.

End MolienAlgebra.

End PolynomialFormulasLazardQuinticF20Molien.
