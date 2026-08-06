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

(** The six representatives
    [1, (0 1 2), (0 2 1), (0 1), (1 2), (0 2)]. *)
Definition three_cycle : S5 := (tperm o0 o1 * tperm o1 o2)%g.

Definition representative_table : 6.-tuple S5 :=
  [tuple 1%g; three_cycle; three_cycle^-1;
    tperm o0 o1; tperm o1 o2; tperm o0 o2].

Definition representative (i : 'I_6) : S5 :=
  tnth representative_table i.

(** Equality of the left cosets represented by [g] and [h]. *)
Definition same_left_cosetb (g h : S5) : bool :=
  g^-1 * h \in standard_F20.

Lemma same_left_coset_refl g : same_left_cosetb g g.
Proof. by rewrite /same_left_cosetb mulVg group1. Qed.

Lemma same_left_cosetbE g h :
  same_left_cosetb g h = normalizes_cycleb (g^-1 * h).
Proof. by rewrite /same_left_cosetb normalizes_cyclebE. Qed.

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

Definition theta_supportb (d : quintic_exponent) : bool :=
  d \in theta_exponent_table.

Definition theta_stabilizesb (s : S5) : bool :=
  all (fun d => theta_supportb (act_exponent s d)) theta_exponent_table.

(** Left multiplication by the standard five-cycle on the six cosets. *)
Definition five_cycle_coset_index (i : 'I_6) : 'I_6 :=
  inord (nth 0 [:: 0; 5; 3; 4; 1; 2]%N i).

End PolynomialFormulasQuinticF20Data.
