From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import SexticRecursiveCore
  SexticComputedResolvents.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

(** A transparent finite rational-root search for ascending integer
    coefficient lists.  The search uses the rectangle supplied by the
    rational-root theorem: the numerator is bounded by the constant
    coefficient and the positive denominator by the leading coefficient. *)
Module PolynomialFormulasSexticRationalRootSearch.

Import PolynomialFormulasSexticComputedResolvents.
Import PolynomialFormulasSexticRecursiveCore.

Fixpoint coefficient_list_eval_int (cs : seq int) (z : int) : int :=
  if cs is a :: cs' then a + z * coefficient_list_eval_int cs' z else 0.

Fixpoint coefficient_list_eval_rat (cs : seq int) (q : rat) : rat :=
  if cs is a :: cs' then
    a%:~R + q * coefficient_list_eval_rat cs' q
  else 0.

Fixpoint coefficient_list_poly_int (cs : seq int) : {poly int} :=
  if cs is a :: cs' then a%:P + 'X * coefficient_list_poly_int cs' else 0.

Fixpoint homogeneous_eval (cs : seq int) (u v : int) : int :=
  if cs is a :: cs' then
    a * v ^+ (size cs') + u * homogeneous_eval cs' u v
  else 0.

Definition constant_coefficient (cs : seq int) : int := nth 0 cs 0.

Definition leading_coefficient (cs : seq int) : int :=
  lead_coef (coefficient_list_poly_int cs).

Definition positive_interval (R : nat) : seq int :=
  [seq n%:Z | n <- iota 1 R].

Definition numerator_candidates (cs : seq int) : seq int :=
  symmetric_interval (absz (constant_coefficient cs)).

Definition denominator_candidates (cs : seq int) : seq int :=
  positive_interval (absz (leading_coefficient cs)).

Definition bounded_rational_rootb (cs : seq int) : bool :=
  if constant_coefficient cs == 0 then true else
  has (fun u => has (fun v =>
      coefficient_list_eval_rat cs (u%:~R / v%:~R) == 0)
    (denominator_candidates cs)) (numerator_candidates cs).

Definition has_bounded_rational_root (cs : seq int) : Prop :=
  constant_coefficient cs = 0 \/
  exists u, u \in numerator_candidates cs /\
  exists v, v \in denominator_candidates cs /\
    coefficient_list_eval_rat cs (u%:~R / v%:~R) = 0.

Definition has_rational_root (cs : seq int) : Prop :=
  exists q : rat,
    (map_poly (intr : int -> rat) (coefficient_list_poly_int cs)).[q] = 0.

Lemma coefficient_list_eval_intE cs z :
  (coefficient_list_poly_int cs).[z] = coefficient_list_eval_int cs z.
Proof.
elim: cs=> [|a cs ih] /=.
- by rewrite horner0.
- by rewrite hornerD hornerC hornerM hornerX ih.
Qed.

Lemma coefficient_list_eval_ratE cs q :
  (map_poly (intr : int -> rat) (coefficient_list_poly_int cs)).[q] =
    coefficient_list_eval_rat cs q.
Proof.
elim: cs=> [|a cs ih] /=.
- by rewrite map_poly0 horner0.
- by rewrite !rmorphD !rmorphM /= !map_polyC !map_polyX
    hornerD hornerC hornerM hornerX ih.
Qed.

Lemma coefficient_list_poly_int_coef0 cs :
  (coefficient_list_poly_int cs)`_0 = constant_coefficient cs.
Proof.
rewrite -horner_coef0 coefficient_list_eval_intE.
by case: cs=> [|a cs] /=; rewrite ?mul0r ?addr0.
Qed.

Lemma coefficient_list_poly_int_coef cs i :
  (coefficient_list_poly_int cs)`_i = nth 0 cs i.
Proof.
elim: cs i=> [|a cs ih] [|i] /=.
- by rewrite coef0.
- by rewrite coef0.
- by rewrite coefD coefC coefXM eqxx addr0.
- by rewrite coefD coefC coefXM /= add0r ih.
Qed.

Lemma size_lead_cancel (p : {poly int}) :
  p != 0 ->
  (size ((lead_coef p *: ('X ^ ((size p).-1)) - p)%R) <=
    (size p).-1)%N.
Proof.
move=> hp; set d := (size p).-1.
apply/leq_sizeP=> i hdi.
rewrite coefB coefZ coefXn.
case hid: (i == d).
- move/eqP: hid=> ->.
  by rewrite /d -lead_coefE /= mulr1 subrr.
- rewrite /= mulr0.
  have hdlt : (d < i)%N by rewrite ltn_neqAle eq_sym hid hdi.
  have hsize : (size p <= i)%N.
    rewrite (polySpred hp).
    exact: hdlt.
  by rewrite nth_default // sub0r oppr0.
Qed.

(** Denominator half of the rational-root theorem, specialized to the
    canonical reduced numerator and positive denominator of MathComp's
    rationals. *)
Lemma denq_dvd_leading_coefficient (p : {poly int}) (q : rat) :
  p != 0 ->
  (map_poly (intr : int -> rat) p).[q] = 0 ->
  (denq q %| lead_coef p)%Z.
Proof.
move=> hp hq.
pose d := (size p).-1.
pose a := lead_coef p.
pose p1 : {poly int} := a *: ('X ^ d) - p.
have Dp1 : map_poly (intr : int -> rat) p1 =
    a%:~R *: ('X ^ d) - map_poly (intr : int -> rat) p.
  apply/polyP=> i.
  rewrite /p1 coef_map !coefB !coefZ !coefXn coef_map.
  change (((a * ((i == d)%:R : int) - p`_i)%:~R : rat) =
    a%:~R * ((i == d)%:R : rat) - (p`_i)%:~R).
  rewrite intrB intrM.
  by case: (i == d); rewrite /= ?mulr0 ?mulr1.
have sz_p1 :
    (size (map_poly (intr : int -> rat) p1) <= d)%N.
  rewrite (size_map_inj_poly (@intr_inj rat)
    (rmorph0 (intr : int -> rat))).
  exact: size_lead_cancel hp.
have hcop : coprimez (denq q) (numq q ^+ d).
  by rewrite coprimez_sym coprimezXl //; apply: coprime_num_den.
have /Gauss_dvdzl <- : coprimez (denq q) (numq q ^+ d) := hcop.
apply/dvdzP.
exists (\sum_(i < d)
  p1`_i * numq q ^+ i * denq q ^+ (d - i.+1)).
apply: (@intr_inj rat).
rewrite rmorphM mulr_suml rmorph_sum /=.
transitivity
  ((map_poly (intr : int -> rat) p1).[q] *
    (denq q ^+ d)%:~R).
- rewrite Dp1 !hornerE hq subr0.
  by rewrite !rmorphXn /= numqE exprMn mulrA.
- rewrite (horner_coef_wide _ sz_p1) mulr_suml.
  apply: eq_bigr=> i _.
  rewrite -!mulrA -exprSr coef_map !rmorphM !rmorphXn /=
    numqE exprMn -mulrA.
  by rewrite -exprD -addSnnS subnKC.
Qed.

(** Clearing the canonical denominator in one nonconstant monomial. *)
Lemma num_den_power_clear (q : rat) (d i : nat) :
  (i < d)%N ->
  (numq q)%:~R * ((numq q)%:~R ^+ i *
      (denq q)%:~R ^+ (d - i.+1)) =
    q ^+ i.+1 * (denq q)%:~R ^+ d.
Proof.
move=> hi.
rewrite !numqE !exprMn.
rewrite [q ^+ i.+1]exprSr.
rewrite -[d in RHS](subnKC hi) exprD exprSr.
rewrite !mulrA.
rewrite [q * (denq q)%:~R * q ^+ i]mulrAC.
rewrite [q * q ^+ i]mulrC.
rewrite [q ^+ i * q * (denq q)%:~R * (denq q)%:~R ^+ i]mulrAC.
reflexivity.
Qed.

(** Numerator half of the rational-root theorem. *)
Lemma numq_dvd_constant_coefficient (p : {poly int}) (q : rat) :
  (map_poly (intr : int -> rat) p).[q] = 0 ->
  (numq q %| p`_0)%Z.
Proof.
move=> hq.
case hp: (p == 0).
- move/eqP: hp=> ->; by rewrite coef0 dvdz0.
- pose d := (size p).-1.
  have hp0 : p != 0 by rewrite hp.
  pose S := \sum_(i < d)
    p`_i.+1 * numq q ^+ i * denq q ^+ (d - i.+1).
  have szp :
      (size (map_poly (intr : int -> rat) p) <= d.+1)%N.
    rewrite (size_map_inj_poly (@intr_inj rat)
      (rmorph0 (intr : int -> rat))) /d.
    by rewrite -{1}(polySpred hp0).
  have hcop : coprimez (numq q) (denq q ^+ d).
    rewrite coprimezXr //.
    exact: coprime_num_den.
  have /Gauss_dvdzr <- : coprimez (numq q) (denq q ^+ d) := hcop.
  apply/dvdzP; exists (- S).
  apply: (@intr_inj rat).
  have hclear :
      ((p`_0 * denq q ^+ d)%:~R : rat) +
        (numq q * S)%:~R = 0.
    transitivity
      ((map_poly (intr : int -> rat) p).[q] *
        (denq q ^+ d)%:~R).
    - rewrite (horner_coef_wide _ szp) big_ord_recl /=
        mulrDl !intrM.
      congr (_ + _).
      + by rewrite coef_map expr0 mulr1.
      have Smorph : (S%:~R : rat) =
          \sum_(i < d)
            (p`_i.+1 * numq q ^+ i *
              denq q ^+ (d - i.+1))%:~R.
        change ((intr : int -> rat) S =
          \sum_(i < d) (intr : int -> rat)
            (p`_i.+1 * numq q ^+ i *
              denq q ^+ (d - i.+1))).
        by rewrite /S rmorph_sum.
      rewrite Smorph mulr_sumr mulr_suml.
      apply: eq_bigr=> [[i hi]] _ /=.
      rewrite /bump /= coef_map !rmorphM !rmorphXn /=.
      rewrite -!mulrA.
      rewrite mulrCA add1n (num_den_power_clear q hi).
      reflexivity.
    - by rewrite hq mul0r.
  rewrite [denq q ^+ d * p`_0]mulrC [(- S) * numq q]mulrC.
  apply: (addrI ((numq q * S)%:~R : rat)).
  rewrite [((numq q * S)%:~R : rat) + _]addrC hclear.
  by rewrite mulrN intrN addrN.
Qed.

Lemma absz_le_of_dvdz (a b : int) :
  b != 0 -> (a %| b)%Z -> (absz a <= absz b)%N.
Proof.
move=> hb; rewrite dvdzE=> hab.
apply: dvdn_leq hab.
by rewrite absz_gt0.
Qed.

Lemma mem_symmetric_interval_absz (R : nat) (z : int) :
  (absz z <= R)%N -> z \in symmetric_interval R.
Proof.
move=> hz; apply/mem_symmetric_interval.
case: z hz=> n hz /=.
- rewrite absz_nat in hz.
  exists (R + n)%N; split; first by
    rewrite addn1 ltnS mulSn mul1n leq_add2l.
  by rewrite PoszD addrAC subrr add0r.
- rewrite NegzE abszN absz_nat in hz.
  have hnR : (n.+1 <= R)%N := hz.
  exists (R - n.+1)%N; split; first by
    rewrite addn1 ltnS mulSn mul1n;
    exact: leq_trans (leq_subr n.+1 R) (leq_addr R R).
  by rewrite NegzE -(subzn (m := R) (n := n.+1) hnR)
    addrAC subrr add0r.
Qed.

Lemma denq_mem_positive_interval (q : rat) (R : nat) :
  (absz (denq q) <= R)%N -> denq q \in positive_interval R.
Proof.
have [n hden] := denqP q.
rewrite hden absz_nat=> hnR.
apply/mapP; exists n.+1; last reflexivity.
rewrite mem_iota.
apply/andP; split.
- by rewrite ltnS.
- by rewrite ltnS.
Qed.

Theorem has_bounded_rational_root_of_rational cs :
  has_rational_root cs -> has_bounded_rational_root cs.
Proof.
move=> [q hq].
case h0: (constant_coefficient cs == 0).
- left; exact/eqP.
- right.
  pose p := coefficient_list_poly_int cs.
  have hp0 : p != 0.
    apply/eqP=> hp.
    have hc0 : constant_coefficient cs = 0.
      rewrite -coefficient_list_poly_int_coef0.
      change (p`_0 = 0).
      by rewrite hp coef0.
    by move: h0; rewrite hc0 eqxx.
  have hnum_dvd : (numq q %| constant_coefficient cs)%Z.
    rewrite -coefficient_list_poly_int_coef0.
    exact: numq_dvd_constant_coefficient hq.
  have hden_dvd : (denq q %| leading_coefficient cs)%Z.
    exact: denq_dvd_leading_coefficient hp0 hq.
  have hnum_bound :
      (absz (numq q) <= absz (constant_coefficient cs))%N.
    apply: absz_le_of_dvdz hnum_dvd.
    by rewrite h0.
  have hden_bound :
      (absz (denq q) <= absz (leading_coefficient cs))%N.
    apply: absz_le_of_dvdz hden_dvd.
    rewrite /leading_coefficient /p lead_coef_eq0.
    exact: hp0.
  exists (numq q); split.
  + exact: mem_symmetric_interval_absz hnum_bound.
  exists (denq q); split.
  + exact: denq_mem_positive_interval hden_bound.
  rewrite -coefficient_list_eval_ratE divq_num_den.
  exact: hq.
Qed.

Lemma bounded_rational_rootP cs :
  reflect (has_bounded_rational_root cs) (bounded_rational_rootb cs).
Proof.
rewrite /bounded_rational_rootb /has_bounded_rational_root.
case h0: (constant_coefficient cs == 0).
- constructor; left; exact/eqP.
- apply: (iffP hasP).
  + move=> [u hu /hasP[v hv /eqP huv]].
    right; exists u; split=> //.
    exists v; by split.
  + move=> [hz|[u [hu [v [hv huv]]]]].
    * by move: h0; rewrite hz eqxx.
    * exists u=> //; apply/hasP; exists v=> //; exact/eqP.
Qed.

Lemma zero_is_rational_root cs :
  constant_coefficient cs = 0 -> has_rational_root cs.
Proof.
move=> h0; exists 0.
rewrite -[0 : rat](rmorph0 (intr : int -> rat))
  horner_map coefficient_list_eval_intE.
case: cs h0=> [|a cs] /=.
- by rewrite rmorph0.
- move=> h; rewrite /constant_coefficient /= in h.
  by rewrite mul0r addr0 h rmorph0.
Qed.

Theorem has_rational_root_of_bounded cs :
  has_bounded_rational_root cs -> has_rational_root cs.
Proof.
move=> [h0|[u [hu [v [hv huv]]]]].
- exact: zero_is_rational_root h0.
- exists (u%:~R / v%:~R).
  by rewrite coefficient_list_eval_ratE huv.
Qed.

Theorem rational_rootP cs :
  reflect (has_rational_root cs) (bounded_rational_rootb cs).
Proof.
apply: (iffP (bounded_rational_rootP cs)).
- exact: has_rational_root_of_bounded.
- exact: has_bounded_rational_root_of_rational.
Qed.

Definition pair_scaled_rational_rootb f x : bool :=
  bounded_rational_rootb (pair_scaled_resolvent f x).

Definition triple_scaled_rational_rootb f x : bool :=
  bounded_rational_rootb (triple_scaled_resolvent f x).

Lemma pair_scaled_rational_rootP f x :
  reflect (has_rational_root (pair_scaled_resolvent f x))
    (pair_scaled_rational_rootb f x).
Proof. exact: rational_rootP. Qed.

Lemma triple_scaled_rational_rootP f x :
  reflect (has_rational_root (triple_scaled_resolvent f x))
    (triple_scaled_rational_rootb f x).
Proof. exact: rational_rootP. Qed.

End PolynomialFormulasSexticRationalRootSearch.
