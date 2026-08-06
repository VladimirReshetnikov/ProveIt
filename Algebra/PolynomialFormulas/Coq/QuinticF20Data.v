From mathcomp Require Import all_ssreflect all_fingroup all_solvable.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Concrete finite data for the Frobenius subgroup used by the recursive
    quintic criterion.  The structural facts are proved symbolically, so this
    file does not rely on evaluation of MathComp's finite-group records. *)
Module PolynomialFormulasQuinticF20Data.

Local Open Scope group_scope.

Definition S5 := {perm 'I_5}.

Definition o0 : 'I_5 := @Ordinal 5 0 isT.
Definition o1 : 'I_5 := @Ordinal 5 1 isT.
Definition o2 : 'I_5 := @Ordinal 5 2 isT.
Definition o3 : 'I_5 := @Ordinal 5 3 isT.
Definition o4 : 'I_5 := @Ordinal 5 4 isT.

(** The cycle [(0 1 2 3 4)] in MathComp's multiplication convention. *)
Definition five_cycle : S5 :=
  (tperm o0 o1 * tperm o1 o2 * tperm o2 o3 * tperm o3 o4)%g.

Definition standard_C5 : {group S5} := <[five_cycle]>.
Definition standard_F20 : {group S5} := 'N(standard_C5).

Lemma five_cycle_o0 : five_cycle o0 = o4.
Proof. by rewrite /five_cycle !permM tpermL !tpermL. Qed.

Lemma five_cycle_o1 : five_cycle o1 = o0.
Proof. rewrite /five_cycle !permM tpermR. by rewrite !tpermD. Qed.

Lemma five_cycle_o2 : five_cycle o2 = o1.
Proof.
rewrite /five_cycle !permM
  (tpermD (x := o0) (y := o1) (z := o2)) // tpermR.
by rewrite (tpermD (x := o2) (y := o3) (z := o1)) //
  (tpermD (x := o3) (y := o4) (z := o1)).
Qed.

Lemma five_cycle_o3 : five_cycle o3 = o2.
Proof.
rewrite /five_cycle !permM
  (tpermD (x := o0) (y := o1) (z := o3)) //.
rewrite (tpermD (x := o1) (y := o2) (z := o3)) // tpermR.
by rewrite (tpermD (x := o3) (y := o4) (z := o2)).
Qed.

Lemma five_cycle_o4 : five_cycle o4 = o3.
Proof.
rewrite /five_cycle !permM
  (tpermD (x := o0) (y := o1) (z := o4)) //.
rewrite (tpermD (x := o1) (y := o2) (z := o4)) //.
by rewrite (tpermD (x := o2) (y := o3) (z := o4)) // tpermR.
Qed.

Lemma perm_expg5E (s : S5) i :
  (s ^+ 5) i = s (s (s (s (s i)))).
Proof. by rewrite !expgS expg0 !permM perm1. Qed.

Lemma order_five_cycle : #[five_cycle] = 5%N.
Proof.
apply: nt_prime_order; first by [].
- apply/permP=> i; rewrite perm1 perm_expg5E.
  case: i=> [[|[|[|[|[|i]]]]] hi].
  + have -> : @Ordinal 5 0 hi = o0 by apply/val_inj.
    by rewrite five_cycle_o0 five_cycle_o4 five_cycle_o3
      five_cycle_o2 five_cycle_o1.
  + have -> : @Ordinal 5 1 hi = o1 by apply/val_inj.
    by rewrite five_cycle_o1 five_cycle_o0 five_cycle_o4
      five_cycle_o3 five_cycle_o2.
  + have -> : @Ordinal 5 2 hi = o2 by apply/val_inj.
    by rewrite five_cycle_o2 five_cycle_o1 five_cycle_o0
      five_cycle_o4 five_cycle_o3.
  + have -> : @Ordinal 5 3 hi = o3 by apply/val_inj.
    by rewrite five_cycle_o3 five_cycle_o2 five_cycle_o1
      five_cycle_o0 five_cycle_o4.
  + have -> : @Ordinal 5 4 hi = o4 by apply/val_inj.
    by rewrite five_cycle_o4 five_cycle_o3 five_cycle_o2
      five_cycle_o1 five_cycle_o0.
  + by move: hi.
- have hc0 : five_cycle o0 != o0.
    by rewrite five_cycle_o0.
  case hcycle: (five_cycle == 1%g).
  + move/eqP: hcycle=> hcycle.
    by move: hc0; rewrite hcycle perm1 eqxx.
  + by [].
Qed.

Lemma card_standard_C5 : #|standard_C5| = 5%N.
Proof. exact: order_five_cycle. Qed.

Lemma standard_C5_sylow :
  5.-Sylow([set: S5]) standard_C5.
Proof.
rewrite pHallE subsetT card_standard_C5 cardsT /S5 card_Sn.
rewrite andTb p_part (logn_fact 5) //.
do 5! rewrite big_nat_recr //=.
rewrite big_geq //=.
Qed.

Lemma sylow5_count_arithmetic n :
    n <= 24 -> n %| 120 -> n %% 5 = 1%N -> n != 1%N -> n = 6%N.
Proof.
move=> hn hd hm hn1.
have hq0 : n %/ 5 <= 24 %/ 5 := leq_div2r 5 hn.
have hq : n %/ 5 <= 4 by exact hq0.
have hdecomp := divn_eq n 5.
rewrite hm in hdecomp.
move: hq hdecomp.
case hqv: (n %/ 5) => [|[|[|[|[|q]]]]] //= _ hdecomp.
- by move: hn1; rewrite hdecomp eqxx.
- by move: hd; rewrite hdecomp.
- by move: hd; rewrite hdecomp.
- by move: hd; rewrite hdecomp.
Qed.

Lemma conjg_permE (f s : S5) i :
  (f ^ s) i = s (f (s^-1 i)).
Proof. by rewrite conjgE !permM. Qed.

Lemma five_cycle_power_o4_unique k :
  k < 5 -> (five_cycle ^+ k) o4 = o3 -> k = 1%N.
Proof.
case: k=> [|[|[|[|[|k]]]]] //= _ hpoint.
- by rewrite expg0 perm1 in hpoint.
- by move: hpoint; rewrite expgS permM expg1 five_cycle_o4 five_cycle_o3.
- by move: hpoint; rewrite expgS permM expgS permM expg1 five_cycle_o4
    five_cycle_o3 five_cycle_o2.
- by move: hpoint; rewrite expgS permM expgS permM expgS permM expg1
    five_cycle_o4 five_cycle_o3 five_cycle_o2 five_cycle_o1.
Qed.

Definition swap01 : S5 := tperm o0 o1.
Definition conjugated_five_cycle : S5 := (five_cycle ^ swap01)%g.

Lemma conjugated_five_cycle_o0 :
  conjugated_five_cycle o0 = o1.
Proof.
by rewrite /conjugated_five_cycle conjg_permE /swap01
  tpermV tpermL five_cycle_o1 tpermL.
Qed.

Lemma conjugated_five_cycle_o4 :
  conjugated_five_cycle o4 = o3.
Proof.
rewrite /conjugated_five_cycle conjg_permE /swap01 tpermV
  (tpermD (x := o0) (y := o1) (z := o4)) // five_cycle_o4.
by rewrite (tpermD (x := o0) (y := o1) (z := o3)).
Qed.

Lemma five_cycle_conjugate_not_commute :
  ~ commute five_cycle conjugated_five_cycle.
Proof.
move=> hcomm.
have hpoint := congr1 (fun s : S5 => s o0) hcomm.
move: hpoint.
rewrite (permM five_cycle conjugated_five_cycle o0)
  (permM conjugated_five_cycle five_cycle o0)
  five_cycle_o0 conjugated_five_cycle_o4
  conjugated_five_cycle_o0 five_cycle_o1.
by [].
Qed.

Lemma conjugated_five_cycle_notin :
  conjugated_five_cycle \notin standard_C5.
Proof.
apply/negP=> hcg.
have /centsP hc := cycle_abelian five_cycle.
have hcomm : commute five_cycle conjugated_five_cycle :=
  hc five_cycle (cycle_id five_cycle) conjugated_five_cycle hcg.
exact: five_cycle_conjugate_not_commute hcomm.
Qed.

Lemma swap01_not_normalizer :
  swap01 \notin standard_F20.
Proof.
apply/negP=> hsw.
move/normP: hsw=> hnorm.
have hfcJ : five_cycle ^ swap01 \in standard_C5.
  rewrite -hnorm -/standard_C5 -cycleJ.
  exact: cycle_id (five_cycle ^ swap01).
move: conjugated_five_cycle_notin.
by rewrite /conjugated_five_cycle hfcJ.
Qed.

Lemma standard_C5_not_normal :
  ~~ (standard_C5 <| [set : S5]).
Proof.
apply/negP=> hn.
have hsub : [set : S5] \subset standard_F20.
  exact: normal_norm hn.
have hswap : swap01 \in standard_F20.
  apply: (subsetP hsub).
  by rewrite inE.
move: swap01_not_normalizer.
by rewrite hswap.
Qed.

Lemma card_sylow5_neq1 :
  #|'Syl_5([set : S5])| != 1%N.
Proof.
apply/eqP=> hcard.
have hcardb : #|'Syl_5([set : S5])| == 1%N by exact/eqP.
have [P sylP nP] :=
  elimT (@normal_sylowP S5 5 [set : S5]) hcardb.
have [x _ hPx] := Sylow_trans standard_C5_sylow sylP.
have nC5 : standard_C5 <| [set : S5].
  rewrite -(normalJ standard_C5 [set : S5] x) conjTg -hPx.
  exact: nP.
move: standard_C5_not_normal.
by rewrite nC5.
Qed.

Lemma card_sylow5 : #|'Syl_5([set : S5])| = 6%N.
Proof.
apply: sylow5_count_arithmetic.
- have hindexC5 : #|[set : S5] : standard_C5| = 24%N.
    have hlag := Lagrange (subsetT standard_C5).
    rewrite card_standard_C5 cardsT /S5 card_Sn in hlag.
    have h' : (5 * #|[set : S5] : standard_C5|)%N = (5 * 24)%N
      by exact hlag.
    move/eqP: h'.
    rewrite eqn_mul2l.
    move/orP=> [/eqP h50 | /eqP hidx]; last exact hidx.
    by [].
  have hdivindex :
      #|[set : S5] : standard_F20| %|
        #|[set : S5] : standard_C5| :=
    @indexgS S5 [set : S5] standard_C5 standard_F20
      (normG standard_C5).
  have hleindex :
      #|[set : S5] : standard_F20| <=
        #|[set : S5] : standard_C5| :=
    dvdn_leq (indexg_gt0 [set : S5] standard_C5) hdivindex.
  rewrite hindexC5 in hleindex.
  rewrite (card_Syl standard_C5_sylow) setTI.
  exact: hleindex.
- have hdvd : #|'Syl_5([set : S5])| %| #|[set : S5]| :=
    @card_Syl_dvd 5 S5 [set : S5].
  move: hdvd.
  by rewrite cardsT /S5 card_Sn.
- exact: (@card_Syl_mod 5 S5 [set : S5]) isT.
- exact: card_sylow5_neq1.
Qed.

Lemma card_standard_F20 : #|standard_F20| = 20%N.
Proof.
have hindex : #|[set : S5] : standard_F20| = 6%N.
  have hcard := card_Syl standard_C5_sylow.
  rewrite setTI in hcard.
  rewrite -hcard.
  exact: card_sylow5.
have hlag := Lagrange (subsetT standard_F20).
rewrite hindex cardsT /S5 card_Sn in hlag.
have h' : (#|standard_F20| * 6)%N = (20 * 6)%N by exact hlag.
move/eqP: h'.
rewrite eqn_mul2r.
move/orP=> [/eqP h60 | /eqP hcard]; last exact hcard.
by [].
Qed.

Lemma index_standard_F20 :
  #|[set : S5] : standard_F20| = 6%N.
Proof.
have hcard := card_Syl standard_C5_sylow.
rewrite setTI in hcard.
rewrite -hcard.
exact: card_sylow5.
Qed.

Lemma standard_F20_solvable : solvable standard_F20.
Proof.
rewrite (series_sol (normalG standard_C5)).
apply/andP; split.
- exact: abelian_sol (cycle_abelian five_cycle).
- apply: (@pgroup_sol _ 2).
  rewrite /pgroup card_quotient ?normG // -divgS.
  2: exact: normG standard_C5.
  rewrite card_standard_F20 card_standard_C5.
  by [].
Qed.

(** Membership in the cyclic subgroup and its normalizer can be tested by
    inspecting only the five powers of the distinguished generator.  These
    small tests keep the concrete certificates below independent of the
    implementation of finite-group enumeration. *)
Definition cycle_memberb (x : S5) : bool :=
  [exists k : 'I_5, x == five_cycle ^+ k].

Lemma cycle_memberbE x : cycle_memberb x = (x \in standard_C5).
Proof.
apply/idP/idP.
- move/existsP=> [k /eqP ->].
  exact: mem_cycle.
- move/cyclePmin=> [k hk ->].
  rewrite order_five_cycle in hk.
  apply/existsP; exists (Ordinal hk).
  by rewrite eqxx.
Qed.

Definition normalizes_cycleb (s : S5) : bool :=
  cycle_memberb (five_cycle ^ s).

Lemma normalizes_cyclebE s :
  normalizes_cycleb s = (s \in standard_F20).
Proof.
rewrite /normalizes_cycleb cycle_memberbE /standard_F20 /standard_C5.
symmetry.
by rewrite -cycle_subG norms_cycle.
Qed.

Lemma normalizer_fix34_identity (s : S5) :
  s \in standard_F20 -> s o3 = o3 -> s o4 = o4 -> s = 1%g.
Proof.
move=> hsN hs3 hs4.
have hs4V : s^-1 o4 = o4.
  have hs4eq := congr1 s^-1 hs4.
  by move: hs4eq; rewrite permK.
have hcJ : five_cycle ^ s \in standard_C5.
  move: hsN.
  rewrite -normalizes_cyclebE /normalizes_cycleb cycle_memberbE.
  by [].
have [k hk hcJk] := cyclePmin hcJ.
rewrite order_five_cycle in hk.
have hpoint := congr1 (fun p : S5 => p o4) hcJk.
rewrite conjg_permE hs4V five_cycle_o4 hs3 in hpoint.
have hk1 : k = 1%N := five_cycle_power_o4_unique hk (esym hpoint).
have hcJs : five_cycle ^ s = five_cycle by rewrite hcJk hk1 expg1.
have hcomm : commute five_cycle s.
  apply/commgP/conjg_fixP.
  exact: hcJs.
have hs2 : s o2 = o2.
  have hs2eq := congr1 (fun p : S5 => p o3) hcomm.
  by move: hs2eq; rewrite permM permM five_cycle_o3 hs3 five_cycle_o3.
have hs1 : s o1 = o1.
  have hs1eq := congr1 (fun p : S5 => p o2) hcomm.
  by move: hs1eq; rewrite permM permM five_cycle_o2 hs2 five_cycle_o2.
have hs0 : s o0 = o0.
  have hs0eq := congr1 (fun p : S5 => p o1) hcomm.
  by move: hs0eq; rewrite permM permM five_cycle_o1 hs1 five_cycle_o1.
apply/permP=> i; rewrite perm1.
case: i=> [[|[|[|[|[|i]]]]] hi].
- have -> : @Ordinal 5 0 hi = o0 by apply/val_inj.
  exact: hs0.
- have -> : @Ordinal 5 1 hi = o1 by apply/val_inj.
  exact: hs1.
- have -> : @Ordinal 5 2 hi = o2 by apply/val_inj.
  exact: hs2.
- have -> : @Ordinal 5 3 hi = o3 by apply/val_inj.
  exact: hs3.
- have -> : @Ordinal 5 4 hi = o4 by apply/val_inj.
  exact: hs4.
- by move: hi.
Qed.

(** The six representatives
    [1, (0 1 2), (0 2 1), (0 1), (1 2), (0 2)]. *)
Definition three_cycle : S5 := (tperm o0 o1 * tperm o1 o2)%g.

Definition representative_table : 6.-tuple S5 :=
  [tuple 1%g; three_cycle; three_cycle^-1;
    tperm o0 o1; tperm o1 o2; tperm o0 o2].

Definition representative (i : 'I_6) : S5 :=
  tnth representative_table i.

Lemma representative_o3 i : representative i o3 = o3.
Proof.
case: i=> [[|[|[|[|[|[|i]]]]]]] hi; last by move: hi.
all: rewrite /representative /representative_table /= ?perm1 /three_cycle
  ?invgM ?tpermV ?permM.
all: by rewrite ?tpermD.
Qed.

Lemma representative_o4 i : representative i o4 = o4.
Proof.
case: i=> [[|[|[|[|[|[|i]]]]]]] hi; last by move: hi.
all: rewrite /representative /representative_table /= ?perm1 /three_cycle
  ?invgM ?tpermV ?permM.
all: by rewrite ?tpermD.
Qed.

Definition representative_o0_table : 6.-tuple 'I_5 :=
  [tuple o0; o2; o1; o1; o0; o2].

Definition representative_o1_table : 6.-tuple 'I_5 :=
  [tuple o1; o0; o2; o0; o2; o1].

Definition representative_o2_table : 6.-tuple 'I_5 :=
  [tuple o2; o1; o0; o2; o1; o0].

Lemma representative_o0E i :
  representative i o0 = tnth representative_o0_table i.
Proof.
case: i=> [[|[|[|[|[|[|i]]]]]]] hi; last by move: hi.
- by rewrite /representative /representative_table
    /representative_o0_table /= perm1.
- by rewrite /representative /representative_table
    /representative_o0_table /= /three_cycle permM !tpermL.
- rewrite /representative /representative_table
    /representative_o0_table /= /three_cycle invgM !tpermV permM.
  by rewrite (tpermD (x := o1) (y := o2) (z := o0)) // tpermL.
- by rewrite /representative /representative_table
    /representative_o0_table /= tpermL.
- rewrite /representative /representative_table
    /representative_o0_table /=.
  by rewrite (tpermD (x := o1) (y := o2) (z := o0)).
- by rewrite /representative /representative_table
    /representative_o0_table /= tpermL.
Qed.

Lemma representative_o1E i :
  representative i o1 = tnth representative_o1_table i.
Proof.
case: i=> [[|[|[|[|[|[|i]]]]]]] hi; last by move: hi.
- by rewrite /representative /representative_table
    /representative_o1_table /= perm1.
- rewrite /representative /representative_table
    /representative_o1_table /= /three_cycle permM tpermR.
  by rewrite (tpermD (x := o1) (y := o2) (z := o0)).
- rewrite /representative /representative_table
    /representative_o1_table /= /three_cycle invgM !tpermV permM tpermL.
  by rewrite (tpermD (x := o0) (y := o1) (z := o2)).
- by rewrite /representative /representative_table
    /representative_o1_table /= tpermR.
- by rewrite /representative /representative_table
    /representative_o1_table /= tpermL.
- rewrite /representative /representative_table
    /representative_o1_table /=.
  by rewrite (tpermD (x := o0) (y := o2) (z := o1)).
Qed.

Lemma representative_o2E i :
  representative i o2 = tnth representative_o2_table i.
Proof.
case: i=> [[|[|[|[|[|[|i]]]]]]] hi; last by move: hi.
- by rewrite /representative /representative_table
    /representative_o2_table /= perm1.
- rewrite /representative /representative_table
    /representative_o2_table /= /three_cycle permM.
  by rewrite (tpermD (x := o0) (y := o1) (z := o2)) // tpermR.
- by rewrite /representative /representative_table
    /representative_o2_table /= /three_cycle invgM !tpermV permM !tpermR.
- by rewrite /representative /representative_table
    /representative_o2_table /= tpermD.
- by rewrite /representative /representative_table
    /representative_o2_table /= tpermR.
- by rewrite /representative /representative_table
    /representative_o2_table /= tpermR.
Qed.

Lemma inverse_imageE (s : S5) x y : s x = y -> s^-1 y = x.
Proof. by move=> <-; rewrite permK. Qed.

Definition representative_inv_o0_table : 6.-tuple 'I_5 :=
  [tuple o0; o1; o2; o1; o0; o2].

Definition representative_inv_o1_table : 6.-tuple 'I_5 :=
  [tuple o1; o2; o0; o0; o2; o1].

Definition representative_inv_o2_table : 6.-tuple 'I_5 :=
  [tuple o2; o0; o1; o2; o1; o0].

Lemma representative_inv_o0E i :
  (representative i)^-1 o0 = tnth representative_inv_o0_table i.
Proof.
case: i=> [[|[|[|[|[|[|i]]]]]]] hi; last by move: hi.
all: rewrite /representative_inv_o0_table /=.
- apply: inverse_imageE; exact: representative_o0E.
- apply: inverse_imageE; exact: representative_o1E.
- apply: inverse_imageE; exact: representative_o2E.
- apply: inverse_imageE; exact: representative_o1E.
- apply: inverse_imageE; exact: representative_o0E.
- apply: inverse_imageE; exact: representative_o2E.
Qed.

Lemma representative_inv_o1E i :
  (representative i)^-1 o1 = tnth representative_inv_o1_table i.
Proof.
case: i=> [[|[|[|[|[|[|i]]]]]]] hi; last by move: hi.
all: rewrite /representative_inv_o1_table /=.
- apply: inverse_imageE; exact: representative_o1E.
- apply: inverse_imageE; exact: representative_o2E.
- apply: inverse_imageE; exact: representative_o0E.
- apply: inverse_imageE; exact: representative_o0E.
- apply: inverse_imageE; exact: representative_o2E.
- apply: inverse_imageE; exact: representative_o1E.
Qed.

Lemma representative_inv_o2E i :
  (representative i)^-1 o2 = tnth representative_inv_o2_table i.
Proof.
case: i=> [[|[|[|[|[|[|i]]]]]]] hi; last by move: hi.
all: rewrite /representative_inv_o2_table /=.
- apply: inverse_imageE; exact: representative_o2E.
- apply: inverse_imageE; exact: representative_o0E.
- apply: inverse_imageE; exact: representative_o1E.
- apply: inverse_imageE; exact: representative_o2E.
- apply: inverse_imageE; exact: representative_o1E.
- apply: inverse_imageE; exact: representative_o0E.
Qed.

Lemma representative_inv_o3 i : (representative i)^-1 o3 = o3.
Proof. apply: inverse_imageE; exact: representative_o3. Qed.

Lemma representative_inv_o4 i : (representative i)^-1 o4 = o4.
Proof. apply: inverse_imageE; exact: representative_o4. Qed.

Lemma representative_injective : injective representative.
Proof.
move=> i j hij; apply/val_inj.
case: i hij=> [[|[|[|[|[|[|i]]]]]]] hi hij.
all: try (exfalso; have h66 : 6 < 6 := leq_ltn_trans (leq_addr 6 i) hi;
  move: h66; by rewrite ltnn).
all: case: j hij=> [[|[|[|[|[|[|j]]]]]]] hj hij.
all: try (exfalso; have h66 : 6 < 6 :=
  leq_ltn_trans (leq_addr 6 j) hj; move: h66; by rewrite ltnn).
all: try reflexivity.
all: exfalso.
all: have h0 := congr1 (fun p : S5 => p o0) hij.
all: have h1 := congr1 (fun p : S5 => p o1) hij.
all: move: h0 h1.
all: rewrite !representative_o0E !representative_o1E
  /representative_o0_table /representative_o1_table /=.
all: discriminate.
Qed.

(** Equality of the left cosets represented by [g] and [h]. *)
Definition same_left_cosetb (g h : S5) : bool :=
  g^-1 * h \in standard_F20.

Lemma same_left_coset_refl g : same_left_cosetb g g.
Proof. by rewrite /same_left_cosetb mulVg group1. Qed.

Lemma same_left_cosetbE g h :
  same_left_cosetb g h = normalizes_cycleb (g^-1 * h).
Proof. by rewrite /same_left_cosetb normalizes_cyclebE. Qed.

Lemma representative_cosets_distinct :
  [forall i : 'I_6, [forall j : 'I_6,
    same_left_cosetb (representative i) (representative j) ==
      (i == j)]].
Proof.
apply/forallP=> i; apply/forallP=> j.
apply/eqP.
case eij: (i == j).
- move/eqP: eij=> ->.
  by rewrite /same_left_cosetb mulVg group1.
- case hsame: (same_left_cosetb (representative i) (representative j));
    last reflexivity.
  exfalso.
  have hcoset : same_left_cosetb (representative i) (representative j).
    by rewrite hsame.
  have hi3V : (representative i)^-1 o3 = o3.
    have hi3eq := congr1 (representative i)^-1 (representative_o3 i).
    by move: hi3eq; rewrite permK.
  have hi4V : (representative i)^-1 o4 = o4.
    have hi4eq := congr1 (representative i)^-1 (representative_o4 i).
    by move: hi4eq; rewrite permK.
  have hq3 : ((representative i)^-1 * representative j) o3 = o3.
    by rewrite permM hi3V representative_o3.
  have hq4 : ((representative i)^-1 * representative j) o4 = o4.
    by rewrite permM hi4V representative_o4.
  have hq1 : (representative i)^-1 * representative j = 1%g :=
    normalizer_fix34_identity hcoset hq3 hq4.
  have hrep : representative i = representative j.
    have hmul := congr1 (fun q : S5 => representative i * q) hq1.
    by move: hmul; rewrite mulgA mulgV mul1g mulg1.
  have hij := representative_injective hrep.
  by move: eij; rewrite hij eqxx.
Qed.

Definition F20_left_coset :=
  {C : {set S5} | C \in lcosets standard_F20 [set : S5]}.

Lemma representative_left_coset_mem i :
  representative i *: standard_F20 \in
    lcosets standard_F20 [set : S5].
Proof.
rewrite mem_lcosets.
apply/mulsgP.
exists (representative i) 1%g.
- by rewrite inE.
- exact: group1.
- by rewrite mulg1.
Qed.

Definition representative_left_coset (i : 'I_6) : F20_left_coset :=
  Sub (representative i *: standard_F20) (representative_left_coset_mem i).

Lemma representative_left_coset_injective :
  injective representative_left_coset.
Proof.
move=> i j hij.
have hcosets : representative i *: standard_F20 =
    representative j *: standard_F20 := congr1 val hij.
have hmem : representative j \in representative i *: standard_F20.
  apply/lcoset_eqP.
  exact: esym hcosets.
have hsame : same_left_cosetb (representative i) (representative j).
  by rewrite /same_left_cosetb -mem_lcoset.
have hdist := forallP (forallP representative_cosets_distinct i) j.
rewrite hsame /= in hdist.
exact/eqP.
Qed.

Lemma card_F20_left_coset : #|{: F20_left_coset}| = 6%N.
Proof.
rewrite /F20_left_coset card_sub card_lcosets.
exact: index_standard_F20.
Qed.

Lemma representative_left_coset_onto (C : F20_left_coset) :
  exists i, representative_left_coset i = C.
Proof.
have hcard : #|{: 'I_6}| >= #|{: F20_left_coset}|.
  by rewrite card_ord card_F20_left_coset.
have [inv _ honto] :=
  inj_card_bij representative_left_coset_injective hcard.
by exists (inv C); apply: honto.
Qed.

Lemma representative_cosets_exhaustive :
  [forall g : S5,
    has (same_left_cosetb g) representative_table].
Proof.
apply/forallP=> g.
have hgmem : g *: standard_F20 \in
    lcosets standard_F20 [set : S5].
  rewrite mem_lcosets.
  apply/mulsgP.
  exists g 1%g.
  - by rewrite inE.
  - exact: group1.
  - by rewrite mulg1.
have [i hi] := representative_left_coset_onto
  (Sub (g *: standard_F20) hgmem : F20_left_coset).
have hcosets : representative i *: standard_F20 =
    g *: standard_F20 := congr1 val hi.
apply/hasP; exists (representative i).
- by rewrite /representative; exact: mem_tnth.
- rewrite /same_left_cosetb -mem_lcoset.
  apply/lcoset_eqP.
  exact: hcosets.
Qed.

(** Exponent vectors of the ten monomials [x_i^2 x_j x_k] in Dummit's
    quartic invariant. *)
Definition quintic_exponent := 5.-tuple nat.

Definition theta_exponent_table : 10.-tuple quintic_exponent :=
  [tuple
    [tuple 2; 1; 0; 0; 1];
    [tuple 2; 0; 1; 1; 0];
    [tuple 1; 2; 1; 0; 0];
    [tuple 0; 2; 0; 1; 1];
    [tuple 1; 0; 2; 0; 1];
    [tuple 0; 1; 2; 1; 0];
    [tuple 1; 1; 0; 2; 0];
    [tuple 0; 0; 1; 2; 1];
    [tuple 1; 0; 0; 1; 2];
    [tuple 0; 1; 1; 0; 2]]%N.

Lemma theta_exponent_table_uniq : uniq theta_exponent_table.
Proof. by rewrite /theta_exponent_table /=. Qed.

Definition act_exponent (s : S5) (d : quintic_exponent) :
    quintic_exponent :=
  [tuple tnth d (s^-1 i) | i < 5].

Lemma act_exponent_one d : act_exponent 1 d = d.
Proof.
apply: eq_from_tnth=> i.
by rewrite /act_exponent tnth_mktuple invg1 perm1.
Qed.

Lemma act_exponent_mul s t d :
  act_exponent (s * t) d = act_exponent t (act_exponent s d).
Proof.
apply: eq_from_tnth=> i.
rewrite /act_exponent !tnth_mktuple invMg permM.
by [].
Qed.

Definition representative_exponent (i : 'I_6) (d : quintic_exponent) :
    quintic_exponent :=
  [tuple
    tnth d (tnth representative_inv_o0_table i);
    tnth d (tnth representative_inv_o1_table i);
    tnth d (tnth representative_inv_o2_table i);
    tnth d o3;
    tnth d o4].

Lemma act_exponent_representativeE i d :
  act_exponent (representative i) d = representative_exponent i d.
Proof.
apply: eq_from_tnth=> j.
case: j=> [[|[|[|[|[|j]]]]] hj].
- have -> : @Ordinal 5 0 hj = o0 by apply/val_inj.
  by rewrite /act_exponent /representative_exponent !tnth_mktuple
    representative_inv_o0E.
- have -> : @Ordinal 5 1 hj = o1 by apply/val_inj.
  by rewrite /act_exponent /representative_exponent !tnth_mktuple
    representative_inv_o1E.
- have -> : @Ordinal 5 2 hj = o2 by apply/val_inj.
  by rewrite /act_exponent /representative_exponent !tnth_mktuple
    representative_inv_o2E.
- have -> : @Ordinal 5 3 hj = o3 by apply/val_inj.
  by rewrite /act_exponent /representative_exponent !tnth_mktuple
    representative_inv_o3.
- have -> : @Ordinal 5 4 hj = o4 by apply/val_inj.
  by rewrite /act_exponent /representative_exponent !tnth_mktuple
    representative_inv_o4.
- by move: hj.
Qed.

Lemma five_cycle_inv_o0 : five_cycle^-1 o0 = o1.
Proof.
have h := congr1 five_cycle^-1 five_cycle_o1.
by move: h; rewrite permK.
Qed.

Lemma five_cycle_inv_o1 : five_cycle^-1 o1 = o2.
Proof.
have h := congr1 five_cycle^-1 five_cycle_o2.
by move: h; rewrite permK.
Qed.

Lemma five_cycle_inv_o2 : five_cycle^-1 o2 = o3.
Proof.
have h := congr1 five_cycle^-1 five_cycle_o3.
by move: h; rewrite permK.
Qed.

Lemma five_cycle_inv_o3 : five_cycle^-1 o3 = o4.
Proof.
have h := congr1 five_cycle^-1 five_cycle_o4.
by move: h; rewrite permK.
Qed.

Lemma five_cycle_inv_o4 : five_cycle^-1 o4 = o0.
Proof.
have h := congr1 five_cycle^-1 five_cycle_o0.
by move: h; rewrite permK.
Qed.

Definition rotate_exponent (d : quintic_exponent) : quintic_exponent :=
  [tuple tnth d o1; tnth d o2; tnth d o3; tnth d o4; tnth d o0].

Lemma act_exponent_five_cycleE d :
  act_exponent five_cycle d = rotate_exponent d.
Proof.
apply: eq_from_tnth=> i.
case: i=> [[|[|[|[|[|i]]]]] hi].
- have -> : @Ordinal 5 0 hi = o0 by apply/val_inj.
  by rewrite /act_exponent /rotate_exponent tnth_mktuple
    five_cycle_inv_o0.
- have -> : @Ordinal 5 1 hi = o1 by apply/val_inj.
  by rewrite /act_exponent /rotate_exponent tnth_mktuple
    five_cycle_inv_o1.
- have -> : @Ordinal 5 2 hi = o2 by apply/val_inj.
  by rewrite /act_exponent /rotate_exponent tnth_mktuple
    five_cycle_inv_o2.
- have -> : @Ordinal 5 3 hi = o3 by apply/val_inj.
  by rewrite /act_exponent /rotate_exponent tnth_mktuple
    five_cycle_inv_o3.
- have -> : @Ordinal 5 4 hi = o4 by apply/val_inj.
  by rewrite /act_exponent /rotate_exponent tnth_mktuple
    five_cycle_inv_o4.
- by move: hi.
Qed.

Definition theta_supportb (d : quintic_exponent) : bool :=
  d \in theta_exponent_table.

Definition theta_stabilizesb (s : S5) : bool :=
  all (fun d => theta_supportb (act_exponent s d)) theta_exponent_table.

Definition multiplier_two : S5 :=
  (tperm o4 o3 * tperm o2 o4 * tperm o1 o2)%g.

Lemma multiplier_two_o0 : multiplier_two o0 = o0.
Proof.
rewrite /multiplier_two !permM
  (tpermD (x := o4) (y := o3) (z := o0)) //
  (tpermD (x := o2) (y := o4) (z := o0)) //.
by rewrite (tpermD (x := o1) (y := o2) (z := o0)).
Qed.

Lemma multiplier_two_o1 : multiplier_two o1 = o2.
Proof.
rewrite /multiplier_two !permM
  (tpermD (x := o4) (y := o3) (z := o1)) //
  (tpermD (x := o2) (y := o4) (z := o1)) //.
by rewrite tpermL.
Qed.

Lemma multiplier_two_o2 : multiplier_two o2 = o4.
Proof.
rewrite /multiplier_two !permM
  (tpermD (x := o4) (y := o3) (z := o2)) // tpermL.
by rewrite (tpermD (x := o1) (y := o2) (z := o4)).
Qed.

Lemma multiplier_two_o3 : multiplier_two o3 = o1.
Proof. by rewrite /multiplier_two !permM !tpermR. Qed.

Lemma multiplier_two_o4 : multiplier_two o4 = o3.
Proof.
rewrite /multiplier_two !permM tpermL
  (tpermD (x := o2) (y := o4) (z := o3)) //.
by rewrite (tpermD (x := o1) (y := o2) (z := o3)).
Qed.

Lemma multiplier_two_inv_o0 : multiplier_two^-1 o0 = o0.
Proof.
have h := congr1 multiplier_two^-1 multiplier_two_o0.
by move: h; rewrite permK.
Qed.

Lemma multiplier_two_inv_o1 : multiplier_two^-1 o1 = o3.
Proof.
have h := congr1 multiplier_two^-1 multiplier_two_o3.
by move: h; rewrite permK.
Qed.

Lemma multiplier_two_inv_o2 : multiplier_two^-1 o2 = o1.
Proof.
have h := congr1 multiplier_two^-1 multiplier_two_o1.
by move: h; rewrite permK.
Qed.

Lemma multiplier_two_inv_o3 : multiplier_two^-1 o3 = o4.
Proof.
have h := congr1 multiplier_two^-1 multiplier_two_o4.
by move: h; rewrite permK.
Qed.

Lemma multiplier_two_inv_o4 : multiplier_two^-1 o4 = o2.
Proof.
have h := congr1 multiplier_two^-1 multiplier_two_o2.
by move: h; rewrite permK.
Qed.

Lemma multiplier_two_conj_five_cycle :
  five_cycle ^ multiplier_two = five_cycle ^+ 2.
Proof.
apply/permP=> i.
rewrite conjg_permE expgS expg1.
case: i=> [[|[|[|[|[|i]]]]] hi].
- have -> : @Ordinal 5 0 hi = o0 by apply/val_inj.
  rewrite multiplier_two_inv_o0; fold multiplier_two.
  by rewrite five_cycle_o0 multiplier_two_o4 permM
    five_cycle_o0 five_cycle_o4.
- have -> : @Ordinal 5 1 hi = o1 by apply/val_inj.
  rewrite multiplier_two_inv_o1; fold multiplier_two.
  by rewrite five_cycle_o3 multiplier_two_o2 permM
    five_cycle_o1 five_cycle_o0.
- have -> : @Ordinal 5 2 hi = o2 by apply/val_inj.
  rewrite multiplier_two_inv_o2; fold multiplier_two.
  by rewrite five_cycle_o1 multiplier_two_o0 permM
    five_cycle_o2 five_cycle_o1.
- have -> : @Ordinal 5 3 hi = o3 by apply/val_inj.
  rewrite multiplier_two_inv_o3; fold multiplier_two.
  by rewrite five_cycle_o4 multiplier_two_o3 permM
    five_cycle_o3 five_cycle_o2.
- have -> : @Ordinal 5 4 hi = o4 by apply/val_inj.
  rewrite multiplier_two_inv_o4; fold multiplier_two.
  by rewrite five_cycle_o2 multiplier_two_o1 permM
    five_cycle_o4 five_cycle_o3.
- by move: hi.
Qed.

Lemma multiplier_two_mem_standard_F20 : multiplier_two \in standard_F20.
Proof.
rewrite -normalizes_cyclebE /normalizes_cycleb cycle_memberbE
  multiplier_two_conj_five_cycle.
exact: mem_cycle.
Qed.

Lemma perm_expg4E (s : S5) i :
  (s ^+ 4) i = s (s (s (s i))).
Proof. by rewrite !expgS expg0 !permM perm1. Qed.

Lemma multiplier_two_expg4 : multiplier_two ^+ 4 = 1%g.
Proof.
apply/permP=> i; rewrite perm1 perm_expg4E.
case: i=> [[|[|[|[|[|i]]]]] hi].
- have -> : @Ordinal 5 0 hi = o0 by apply/val_inj.
  by rewrite !multiplier_two_o0.
- have -> : @Ordinal 5 1 hi = o1 by apply/val_inj.
  by rewrite multiplier_two_o1 multiplier_two_o2 multiplier_two_o4
    multiplier_two_o3.
- have -> : @Ordinal 5 2 hi = o2 by apply/val_inj.
  by rewrite multiplier_two_o2 multiplier_two_o4 multiplier_two_o3
    multiplier_two_o1.
- have -> : @Ordinal 5 3 hi = o3 by apply/val_inj.
  by rewrite multiplier_two_o3 multiplier_two_o1 multiplier_two_o2
    multiplier_two_o4.
- have -> : @Ordinal 5 4 hi = o4 by apply/val_inj.
  by rewrite multiplier_two_o4 multiplier_two_o3 multiplier_two_o1
    multiplier_two_o2.
- by move: hi.
Qed.

Lemma order_multiplier_two : #[multiplier_two] = 4%N.
Proof.
have hd : #[multiplier_two] %| 4%N.
  by rewrite order_dvdn multiplier_two_expg4 eqxx.
have hle : #[multiplier_two] <= 4 :=
  dvdn_leq (ltn0Sn 3) hd.
have hne1 : #[multiplier_two] != 1%N.
  rewrite order_eq1.
  apply/eqP=> hm1.
  have hpoint := congr1 (fun p : S5 => p o1) hm1.
  by move: hpoint; rewrite multiplier_two_o1 perm1.
have hne2 : #[multiplier_two] != 2%N.
  apply/eqP=> hm2.
  have hm2one := expg_order multiplier_two.
  rewrite hm2 in hm2one.
  have hpoint := congr1 (fun p : S5 => p o1) hm2one.
  move: hpoint.
  by rewrite expgS expg1 permM multiplier_two_o1 multiplier_two_o2 perm1.
move: hle hd hne1 hne2.
case ho: #[multiplier_two]=> [|[|[|[|[|n]]]]] //= hle hd hne1 hne2.
Qed.

Definition standard_C4 : {group S5} := <[multiplier_two]>.

Lemma card_standard_C4 : #|standard_C4| = 4%N.
Proof. exact: order_multiplier_two. Qed.

(** The two displayed affine generators already generate the whole normalizer.
    Keeping this as a separate certificate lets the theta-invariance proof use
    only closure under subgroup generation. *)
Definition affine_F20 : {group S5} := standard_C5 <*> standard_C4.

Lemma five_cycle_mem_standard_F20 : five_cycle \in standard_F20.
Proof.
apply: (subsetP (normG standard_C5)).
exact: cycle_id.
Qed.

Lemma standard_C4_sub_standard_F20 :
  standard_C4 \subset standard_F20.
Proof. by rewrite /standard_C4 cycle_subG; exact: multiplier_two_mem_standard_F20. Qed.

Lemma affine_F20_sub_standard_F20 : affine_F20 \subset standard_F20.
Proof.
rewrite /affine_F20 join_subG.
apply/andP; split.
- exact: normG standard_C5.
- exact: standard_C4_sub_standard_F20.
Qed.

Lemma card_affine_F20 : #|affine_F20| = 20%N.
Proof.
have hnorm : standard_C4 \subset 'N(standard_C5).
  exact: standard_C4_sub_standard_F20.
have hti : standard_C5 :&: standard_C4 = 1%G.
  apply: coprime_TIg.
  by rewrite card_standard_C5 card_standard_C4.
have hjoin : (affine_F20 : {set S5}) =
    (standard_C5 * standard_C4)%g.
  exact: norm_joinEr hnorm.
rewrite hjoin (TI_cardMg hti).
by rewrite card_standard_C5 card_standard_C4.
Qed.

Lemma affine_F20E : affine_F20 = standard_F20.
Proof.
apply: val_inj.
apply/eqP.
rewrite eqEcard affine_F20_sub_standard_F20
  card_affine_F20 card_standard_F20.
exact: leqnn 20.
Qed.

Definition multiplier_exponent (d : quintic_exponent) : quintic_exponent :=
  [tuple tnth d o0; tnth d o3; tnth d o1; tnth d o4; tnth d o2].

Lemma act_exponent_multiplier_twoE d :
  act_exponent multiplier_two d = multiplier_exponent d.
Proof.
apply: eq_from_tnth=> i.
case: i=> [[|[|[|[|[|i]]]]] hi].
- have -> : @Ordinal 5 0 hi = o0 by apply/val_inj.
  by rewrite /act_exponent /multiplier_exponent tnth_mktuple
    multiplier_two_inv_o0.
- have -> : @Ordinal 5 1 hi = o1 by apply/val_inj.
  by rewrite /act_exponent /multiplier_exponent tnth_mktuple
    multiplier_two_inv_o1.
- have -> : @Ordinal 5 2 hi = o2 by apply/val_inj.
  by rewrite /act_exponent /multiplier_exponent tnth_mktuple
    multiplier_two_inv_o2.
- have -> : @Ordinal 5 3 hi = o3 by apply/val_inj.
  by rewrite /act_exponent /multiplier_exponent tnth_mktuple
    multiplier_two_inv_o3.
- have -> : @Ordinal 5 4 hi = o4 by apply/val_inj.
  by rewrite /act_exponent /multiplier_exponent tnth_mktuple
    multiplier_two_inv_o4.
- by move: hi.
Qed.

Lemma five_cycle_stabilizes_theta : theta_stabilizesb five_cycle.
Proof.
apply/allP=> d hd.
move/tnthP: hd=> [i ->].
case: i=> [[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]] hi;
  last by move: hi.
all: by rewrite /theta_supportb act_exponent_five_cycleE
  /rotate_exponent /theta_exponent_table /=.
Qed.

Lemma multiplier_two_stabilizes_theta : theta_stabilizesb multiplier_two.
Proof.
apply/allP=> d hd.
move/tnthP: hd=> [i ->].
case: i=> [[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]] hi;
  last by move: hi.
all: by rewrite /theta_supportb act_exponent_multiplier_twoE
  /multiplier_exponent /theta_exponent_table /=.
Qed.

(** Stabilizing the ten displayed monomials means permuting their exponent
    table.  The injectivity lemma packages the only finite-cardinality step
    needed to pass from pointwise containment to equality of supports. *)
Definition theta_table_image (s : S5) : seq quintic_exponent :=
  [seq act_exponent s d | d <- theta_exponent_table].

Lemma theta_table_image_one :
  theta_table_image 1 = theta_exponent_table.
Proof.
rewrite /theta_table_image.
apply: map_id_in=> d hd.
by rewrite act_exponent_one.
Qed.

Lemma theta_table_image_mul s t :
  theta_table_image (s * t) =
    map (act_exponent t) (theta_table_image s).
Proof.
rewrite /theta_table_image -map_comp.
apply: eq_map=> d.
exact: act_exponent_mul.
Qed.

Lemma act_exponent_injective s : injective (act_exponent s).
Proof.
move=> d e hde.
have h := congr1 (act_exponent s^-1) hde.
move: h.
rewrite -(act_exponent_mul s s^-1 d)
  -(act_exponent_mul s s^-1 e) mulgV !act_exponent_one.
by [].
Qed.

Lemma theta_stabilizesb_perm s :
  theta_stabilizesb s ->
  perm_eq (theta_table_image s) theta_exponent_table.
Proof.
move=> hs.
have himage_uniq : uniq (theta_table_image s).
  rewrite /theta_table_image map_inj_uniq //.
  exact: act_exponent_injective.
have hsub : {subset theta_table_image s <= theta_exponent_table}.
  move=> x /mapP[d hd ->].
  move/allP: hs=> /(_ d hd).
  by rewrite /theta_supportb.
have hsize : size theta_exponent_table <= size (theta_table_image s).
  by rewrite /theta_table_image size_map.
have [_ hmem] := uniq_min_size himage_uniq hsub hsize.
exact: uniq_perm himage_uniq theta_exponent_table_uniq hmem.
Qed.

Lemma theta_perm_stabilizesb s :
  perm_eq (theta_table_image s) theta_exponent_table ->
  theta_stabilizesb s.
Proof.
move=> hp; apply/allP=> d hd.
rewrite /theta_supportb -(perm_mem hp).
apply/mapP; exists d=> //.
Qed.

Lemma theta_stabilizesbE s :
  theta_stabilizesb s =
  perm_eq (theta_table_image s) theta_exponent_table.
Proof.
apply/idP/idP.
- exact: theta_stabilizesb_perm.
- exact: theta_perm_stabilizesb.
Qed.

Definition theta_stabilizer_set : {set S5} :=
  [set s | perm_eq (theta_table_image s) theta_exponent_table].

Lemma theta_stabilizer_set1 : 1 \in theta_stabilizer_set.
Proof. by rewrite inE theta_table_image_one perm_refl. Qed.

Lemma theta_stabilizer_setM s t :
  s \in theta_stabilizer_set ->
  t \in theta_stabilizer_set ->
  s * t \in theta_stabilizer_set.
Proof.
rewrite !inE theta_table_image_mul=> hs ht.
exact: perm_trans (perm_map (act_exponent t) hs) ht.
Qed.

Lemma theta_stabilizer_setV s :
  s \in theta_stabilizer_set -> s^-1 \in theta_stabilizer_set.
Proof.
rewrite !inE=> hs.
have hmap := perm_map (act_exponent s^-1) hs.
fold (theta_table_image s^-1) in hmap.
rewrite -theta_table_image_mul mulgV theta_table_image_one in hmap.
by rewrite perm_sym in hmap.
Qed.

Lemma theta_stabilizer_group_set : group_set theta_stabilizer_set.
Proof.
apply/group_setP; split.
- exact: theta_stabilizer_set1.
- exact: theta_stabilizer_setM.
Qed.

Definition theta_stabilizer : {group S5} :=
  group theta_stabilizer_group_set.

Lemma mem_theta_stabilizer s :
  (s \in theta_stabilizer) = theta_stabilizesb s.
Proof.
rewrite /theta_stabilizer /theta_stabilizer_set inE.
by rewrite theta_stabilizesbE.
Qed.

Lemma standard_C5_sub_theta_stabilizer :
  standard_C5 \subset theta_stabilizer.
Proof.
rewrite /standard_C5 cycle_subG mem_theta_stabilizer.
exact: five_cycle_stabilizes_theta.
Qed.

Lemma standard_C4_sub_theta_stabilizer :
  standard_C4 \subset theta_stabilizer.
Proof.
rewrite /standard_C4 cycle_subG mem_theta_stabilizer.
exact: multiplier_two_stabilizes_theta.
Qed.

Lemma standard_F20_sub_theta_stabilizer :
  standard_F20 \subset theta_stabilizer.
Proof.
rewrite -affine_F20E /affine_F20 join_subG.
by rewrite standard_C5_sub_theta_stabilizer
  standard_C4_sub_theta_stabilizer.
Qed.

(** Of the six left-coset representatives, precisely the identity permutes
    the theta exponent table.  The five negative cases reduce to explicit
    counterexample rows after the point-action table is unfolded. *)
Lemma representative_theta_stabilizer_certificate :
  [forall i : 'I_6,
    theta_stabilizesb (representative i) == (i == ord0)].
Proof.
apply/forallP=> i; apply/eqP.
case: i=> [[|[|[|[|[|[|i]]]]]]] hi; last by move: hi.
all: rewrite -val_eqE.
- change (theta_stabilizesb (representative (@Ordinal 6 0 hi)) = true).
  apply/eqP.
  rewrite /representative /representative_table /=.
  rewrite -(mem_theta_stabilizer 1).
  by rewrite group1.
- change (theta_stabilizesb (representative (@Ordinal 6 1 hi)) = false).
  apply/negbTE/negP=> /allP hs.
  have hd : [tuple 1; 2; 1; 0; 0]%N \in theta_exponent_table.
    by rewrite /theta_exponent_table /=.
  have hbad := hs _ hd.
  move: hbad.
  by rewrite /theta_supportb act_exponent_representativeE
    /representative_exponent /representative_inv_o0_table
    /representative_inv_o1_table /representative_inv_o2_table
    /theta_exponent_table /=.
- change (theta_stabilizesb (representative (@Ordinal 6 2 hi)) = false).
  apply/negbTE/negP=> /allP hs.
  have hd : [tuple 2; 1; 0; 0; 1]%N \in theta_exponent_table.
    by rewrite /theta_exponent_table /=.
  have hbad := hs _ hd.
  move: hbad.
  by rewrite /theta_supportb act_exponent_representativeE
    /representative_exponent /representative_inv_o0_table
    /representative_inv_o1_table /representative_inv_o2_table
    /theta_exponent_table /=.
- change (theta_stabilizesb (representative (@Ordinal 6 3 hi)) = false).
  apply/negbTE/negP=> /allP hs.
  have hd : [tuple 2; 1; 0; 0; 1]%N \in theta_exponent_table.
    by rewrite /theta_exponent_table /=.
  have hbad := hs _ hd.
  move: hbad.
  by rewrite /theta_supportb act_exponent_representativeE
    /representative_exponent /representative_inv_o0_table
    /representative_inv_o1_table /representative_inv_o2_table
    /theta_exponent_table /=.
- change (theta_stabilizesb (representative (@Ordinal 6 4 hi)) = false).
  apply/negbTE/negP=> /allP hs.
  have hd : [tuple 2; 1; 0; 0; 1]%N \in theta_exponent_table.
    by rewrite /theta_exponent_table /=.
  have hbad := hs _ hd.
  move: hbad.
  by rewrite /theta_supportb act_exponent_representativeE
    /representative_exponent /representative_inv_o0_table
    /representative_inv_o1_table /representative_inv_o2_table
    /theta_exponent_table /=.
- change (theta_stabilizesb (representative (@Ordinal 6 5 hi)) = false).
  apply/negbTE/negP=> /allP hs.
  have hd : [tuple 2; 1; 0; 0; 1]%N \in theta_exponent_table.
    by rewrite /theta_exponent_table /=.
  have hbad := hs _ hd.
  move: hbad.
  by rewrite /theta_supportb act_exponent_representativeE
    /representative_exponent /representative_inv_o0_table
    /representative_inv_o1_table /representative_inv_o2_table
    /theta_exponent_table /=.
Qed.

(** A transparent choice of the displayed representative of an arbitrary
    left coset.  Exhaustiveness above guarantees that the [pick] succeeds. *)
Definition representative_index (g : S5) : 'I_6 :=
  odflt ord0 [pick i : 'I_6 |
    same_left_cosetb g (representative i)].

Lemma representative_indexP g :
  same_left_cosetb g (representative (representative_index g)).
Proof.
have hex : exists i : 'I_6, same_left_cosetb g (representative i).
  have hhas := forallP representative_cosets_exhaustive g.
  move/hasP: hhas=> [x hx hgx].
  move/tnthP: hx=> [i hi].
  exists i.
  by rewrite /representative -hi.
rewrite /representative_index.
case: pickP=> [i hi | hnone]; first exact: hi.
have [i hi] := hex.
by move: (hnone i); rewrite hi.
Qed.

(** Left multiplication by the standard five-cycle on the six cosets. *)
Definition five_cycle_coset_index (i : 'I_6) : 'I_6 :=
  representative_index (five_cycle * representative i).

Lemma five_cycle_representative_table :
  [forall i : 'I_6,
    same_left_cosetb (five_cycle * representative i)
      (representative (five_cycle_coset_index i))].
Proof.
apply/forallP=> i.
exact: representative_indexP.
Qed.

(** Exhaustiveness of the six cosets and the representative certificate give
    the reverse containment without enumerating the 120 permutations. *)
Lemma theta_stabilizer_sub_standard_F20 :
  theta_stabilizer \subset standard_F20.
Proof.
apply/subsetP=> s hs.
pose i := representative_index s.
have hkF : s^-1 * representative i \in standard_F20.
  move: (representative_indexP s).
  by rewrite /same_left_cosetb.
have hkT : s^-1 * representative i \in theta_stabilizer :=
  subsetP standard_F20_sub_theta_stabilizer _ hkF.
have hrepT : representative i \in theta_stabilizer.
  have hprod := groupM hs hkT.
  by move: hprod; rewrite mulVKg.
have hstab : theta_stabilizesb (representative i).
  by move: hrepT; rewrite mem_theta_stabilizer.
have hcert := forallP representative_theta_stabilizer_certificate i.
have hi0 : i == ord0.
  by move: hcert; rewrite hstab.
move/eqP: hi0=> hi0.
move: hkF.
by rewrite hi0 /representative /representative_table /= mulg1 groupV.
Qed.

Lemma theta_stabilizerE : theta_stabilizer = standard_F20.
Proof.
apply: val_inj.
apply/eqP.
by rewrite eqEsubset theta_stabilizer_sub_standard_F20
  standard_F20_sub_theta_stabilizer.
Qed.

(** Subgroup-level bridge used by the Dummit criterion: a subgroup lies in
    the standard Frobenius group exactly when all of its elements preserve
    the ten theta monomials. *)
Lemma subgroup_standard_F20_iff_theta (G : {group S5}) :
  (G \subset standard_F20) =
  [forall s in G, theta_stabilizesb s].
Proof.
rewrite -theta_stabilizerE.
apply/idP/idP.
- move=> hsub; apply/forall_inP=> s hs.
  have := subsetP hsub s hs.
  by rewrite mem_theta_stabilizer.
- move/forall_inP=> hall; apply/subsetP=> s hs.
  move: (hall s hs).
  by rewrite mem_theta_stabilizer.
Qed.

End PolynomialFormulasQuinticF20Data.
