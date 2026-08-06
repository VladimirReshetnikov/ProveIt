From mathcomp Require Import
  all_ssreflect all_algebra all_field.
From Stdlib Require Import Lia Classical_Prop.
From PolynomialFormulas Require Import SexticRecursiveCore.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory Order.POrderTheory.
Local Open Scope ring_scope.

(** Mathematical completeness of the transparent bounded factor search. *)
Module PolynomialFormulasSexticFactorCompleteness.

Import PolynomialFormulasSexticRecursiveCore.

Lemma coef_monic_polynomial_ord (f : monic_sextic) (i : 'I_6) :
  (monic_polynomial f)`_i = tnth f i.
Proof.
case: i => [[|[|[|[|[|[|i]]]]]] hi] /=.
all: rewrite /monic_polynomial.
all: repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
all: simpl.
all: repeat (first
  [ rewrite mulr0 | rewrite mulr1 | rewrite addr0 | rewrite add0r ]).
all: rewrite (tnth_nth 0).
all: try reflexivity.
by move: hi.
Qed.

Definition algC_polynomial (f : monic_sextic) : {poly algC} :=
  map_poly (intr : int -> algC) (monic_polynomial f).

Lemma size_algC_polynomial f : size (algC_polynomial f) = 7%N.
Proof.
rewrite /algC_polynomial
  (size_map_inj_poly (@intr_inj algC) (rmorph0 (intr : int -> algC))).
exact: size_monic_polynomial.
Qed.

Lemma coef_algC_polynomial_ord (f : monic_sextic) (i : 'I_6) :
  (algC_polynomial f)`_i = (tnth f i)%:~R.
Proof. by rewrite /algC_polynomial coef_map coef_monic_polynomial_ord. Qed.

Lemma lower_coefficient_norm_sum (f : monic_sextic) :
  \sum_(i < 6) `|(algC_polynomial f)`_i| = (height f)%:R :> algC.
Proof.
under eq_bigr => i _ do rewrite coef_algC_polynomial_ord -intr_norm.
rewrite !big_ord_recl big_ord0 /= /height !natrD.
rewrite !(tnth_nth 0) addr0.
by [] .
Qed.

Lemma coef_algC_polynomial_six (f : monic_sextic) :
  (algC_polynomial f)`_6 = 1.
Proof.
rewrite /algC_polynomial coef_map /monic_polynomial.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
simpl.
by rewrite !mulr0 !addr0 rmorph1.
Qed.

(** Explicit Cauchy bound used by the finite searches.  The bound is the
    transparent integer [height] plus one; no existential bound is selected. *)
Lemma algC_root_norm_le_height_succ (f : monic_sextic) (x : algC) :
  root (algC_polynomial f) x ->
  `|x| <= (height f + 1)%:R.
Proof.
move=> hx.
pose H : algC := (height f)%:R.
rewrite natrD -/H.
rewrite real_leNgt ?normr_real ?rpredD ?rpred1 ?rpred_nat //.
apply/negP=> hlarge.
have hH0 : 0 <= H by rewrite /H ler0n.
have h11 : (1 : algC) <= 1 by
  rewrite real_leNgt ?rpred1 // ltxx.
have hOne : 1 <= H + 1 := ler_wpDl hH0 h11.
have hx_ge1 : 1 <= `|x| := le_trans hOne (ltW hlarge).
pose s := \sum_(i < 6) (algC_polynomial f)`_i * x ^+ i.
have hroot : (algC_polynomial f).[x] = 0 := elimT rootP hx.
have hsum0 : s + x ^+ 6 = 0.
  move: hroot.
  rewrite horner_coef size_algC_polynomial big_ord_recr /=
    coef_algC_polynomial_six mul1r -/s.
  by [] .
have hx6 : x ^+ 6 = - s.
  have h := congr1 (fun z : algC => z - s) hsum0.
  move: h.
  by rewrite [s + x ^+ 6]addrC addrK sub0r.
have hnorm :
    `|x| ^+ 6 <=
      \sum_(i < 6) `|(algC_polynomial f)`_i| * `|x| ^+ i.
  rewrite -normrX hx6 normrN /s.
  rewrite (le_trans (ler_norm_sum _ _ _)) //.
  apply: ler_sum => i _.
  by rewrite normrM normrX.
have hterms :
    \sum_(i < 6) `|(algC_polynomial f)`_i| * `|x| ^+ i <=
      \sum_(i < 6) `|(algC_polynomial f)`_i| * `|x| ^+ 5.
  apply: ler_sum => i _.
  apply: ler_wpM2l; first exact: normr_ge0.
  have hi5 : (i <= 5)%N by rewrite -ltnS; exact: ltn_ord i.
  by rewrite ler_weXn2l.
have hpow := le_trans hnorm hterms.
rewrite -big_distrl lower_coefficient_norm_sum -/H in hpow.
have hx0 : 0 < `|x| := lt_le_trans ltr01 hx_ge1.
have hx5 : 0 < `|x| ^+ 5 := exprn_gt0 5 hx0.
have hcancel : `|x| <= H.
  move: hpow.
  rewrite exprS.
  by rewrite (ler_pM2r hx5).
have hHlt : H < H + 1 by rewrite ltrDl ltr01.
move: (lt_trans hHlt (lt_le_trans hlarge hcancel)).
by rewrite ltxx.
Qed.

(** Pseudo-divisibility over [int] still transfers roots after mapping to the
    field [algC]: the nonzero pseudo-division scalar can be cancelled. *)
Lemma root_algC_polynomial_of_dvdp (f : monic_sextic) (q : {poly int})
    (z : algC) :
  q %| monic_polynomial f ->
  root (map_poly (intr : int -> algC) q) z ->
  root (algC_polynomial f) z.
Proof.
move/Pdiv.Idomain.dvdpP=> [[a r] ha hfactor] hqz.
have hmap := congr1 (map_poly (intr : int -> algC)) hfactor.
rewrite map_polyZ rmorphM /= in hmap.
change (a%:~R *: algC_polynomial f =
  map_poly (intr : int -> algC) r * map_poly (intr : int -> algC) q) in hmap.
have hqz0 : (map_poly (intr : int -> algC) q).[z] = 0 :=
  elimT rootP hqz.
have heval := congr1 (fun u : {poly algC} => u.[z]) hmap.
rewrite hornerZ hornerM hqz0 mulr0 in heval.
have haC : (a%:~R : algC) != 0 by rewrite intr_eq0.
apply/rootP.
apply: (mulfI haC).
by rewrite mulr0 heval.
Qed.

Lemma mapped_linear_factor_root (c : int) :
  root (map_poly (intr : int -> algC) (linear_factor c)) (- c)%:~R.
Proof.
apply/rootP.
rewrite horner_map /linear_factor hornerD hornerX hornerC.
by rewrite addNr rmorph0.
Qed.

Lemma mem_symmetric_interval_absz (R : nat) (z : int) :
  (absz z <= R)%N -> z \in symmetric_interval R.
Proof.
move=> hz; apply/mem_symmetric_interval.
case: z hz => n hz /=.
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

Lemma linear_factor_mem_symmetric_interval_of_dvdp
    (f : monic_sextic) (c : int) :
  linear_factor c %| monic_polynomial f ->
  c \in symmetric_interval (root_bound f).
Proof.
move=> hdiv.
have hroot : root (algC_polynomial f) (- c)%:~R :=
  root_algC_polynomial_of_dvdp hdiv (mapped_linear_factor_root c).
have hnorm := algC_root_norm_le_height_succ hroot.
have habs_neg : (absz (- c) <= height f + 1)%N.
  move: hnorm.
  by rewrite -intr_norm ler_nat.
have habs : (absz c <= height f + 1)%N.
  by move: habs_neg; rewrite abszN.
apply: mem_symmetric_interval_absz.
apply: leq_trans habs _.
rewrite /root_bound leq_add2l.
by [] .
Qed.

Lemma quadratic_factor_monic (b c : int) :
  quadratic_factor b c \is monic.
Proof.
apply/monicP.
rewrite lead_coefE size_quadratic_factor /quadratic_factor.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
simpl.
by rewrite !mulr0 !addr0.
Qed.

Lemma cubic_factor_monic (b c d : int) :
  cubic_factor b c d \is monic.
Proof.
apply/monicP.
rewrite lead_coefE size_cubic_factor /cubic_factor.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
simpl.
by rewrite !mulr0 !addr0.
Qed.

(** A monic integer factor splits in [algC] into exactly its degree-many
    roots, and pseudo-divisibility makes every one of those a root of the
    original sextic. *)
Lemma bounded_roots_of_monic_factor (f : monic_sextic)
    (q : {poly int}) (n : nat) :
  q \is monic -> size q = n.+1 -> q %| monic_polynomial f ->
  exists rs : seq algC,
    size rs = n /\
    map_poly (intr : int -> algC) q =
      \prod_(z <- rs) ('X - z%:P) /\
    all (fun z => `|z| <= (height f + 1)%:R) rs.
Proof.
move=> hqmonic hqsize hdiv.
pose qC := map_poly (intr : int -> algC) q.
have hqCmonic : qC \is monic := monic_map (intr : int -> algC) hqmonic.
have [rs hrs] := closed_field_poly_normal qC.
have hlead : lead_coef qC = 1 := elimT monicP hqCmonic.
rewrite hlead scale1r in hrs.
exists rs; split.
- apply: succn_inj.
  rewrite -hqsize
    -(size_map_inj_poly (@intr_inj algC) (rmorph0 (intr : int -> algC))).
  change ((size rs).+1 = size qC).
  by rewrite hrs size_prod_XsubC.
- split; first exact: hrs.
  apply/allP=> z hz.
  have hzq : root qC z by rewrite hrs root_prod_XsubC hz.
  have hzp : root (algC_polynomial f) z.
    exact: root_algC_polynomial_of_dvdp hdiv hzq.
  exact: algC_root_norm_le_height_succ hzp.
Qed.

Lemma map_quadratic_factor (b c : int) :
  map_poly (intr : int -> algC) (quadratic_factor b c) =
    'X^2 + (b%:~R)%:P * 'X + (c%:~R)%:P.
Proof.
by rewrite /quadratic_factor !rmorphD !rmorphM /= !map_polyX !map_polyC.
Qed.

Lemma map_cubic_factor (b c d : int) :
  map_poly (intr : int -> algC) (cubic_factor b c d) =
    'X^3 + (b%:~R)%:P * 'X^2 + (c%:~R)%:P * 'X + (d%:~R)%:P.
Proof.
by rewrite /cubic_factor !rmorphD !rmorphM /= !map_polyX !map_polyC.
Qed.

Lemma coef1_map_quadratic_factor (b c : int) :
  (map_poly (intr : int -> algC) (quadratic_factor b c))`_1 = b%:~R.
Proof.
by rewrite map_quadratic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
  ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
Qed.

Lemma coef0_map_quadratic_factor (b c : int) :
  (map_poly (intr : int -> algC) (quadratic_factor b c))`_0 = c%:~R.
Proof.
by rewrite map_quadratic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
  ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
Qed.

Lemma coef2_map_cubic_factor (b c d : int) :
  (map_poly (intr : int -> algC) (cubic_factor b c d))`_2 = b%:~R.
Proof.
rewrite map_cubic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
  ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
by rewrite coefXn /= mulr1.
Qed.

Lemma coef1_map_cubic_factor (b c d : int) :
  (map_poly (intr : int -> algC) (cubic_factor b c d))`_1 = c%:~R.
Proof.
rewrite map_cubic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
  ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
by rewrite ?coefXn ?coefX ?coefC /=
  ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
Qed.

Lemma coef0_map_cubic_factor (b c d : int) :
  (map_poly (intr : int -> algC) (cubic_factor b c d))`_0 = d%:~R.
Proof.
rewrite map_cubic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
  ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
by rewrite ?coefXn ?coefX ?coefC /=
  ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
Qed.

Lemma two_root_coef1 (x y : algC) :
  (\prod_(z <- [:: x; y]) ('X - z%:P))`_1 = -(x + y).
Proof.
rewrite !big_cons big_nil mulr1 coefM.
rewrite !big_ord_recl big_ord0 /=.
rewrite !coefB !coefX !coefC /=.
rewrite sub0r subr0 mulr1 mul1r addr0 opprD.
by rewrite sub0r.
Qed.

Lemma two_root_coef0 (x y : algC) :
  (\prod_(z <- [:: x; y]) ('X - z%:P))`_0 = x * y.
Proof.
rewrite !big_cons big_nil mulr1 coefM.
rewrite !big_ord_recl big_ord0 /=.
rewrite !coefB !coefX !coefC /=.
by rewrite !sub0r mulrNN addr0.
Qed.

Lemma three_root_coef2 (x y z : algC) :
  (\prod_(w <- [:: x; y; z]) ('X - w%:P))`_2 = -(x + y + z).
Proof.
rewrite !big_cons big_nil mulr1 coefM.
rewrite !big_ord_recl big_ord0 /=.
rewrite !coefM !big_ord_recl big_ord0 /=.
rewrite !coefB !coefX !coefC /=.
rewrite !big_ord0 /=.
rewrite ?subr0 ?sub0r ?subrr ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
rewrite !opprD.
by rewrite mulr1 addrA.
Qed.

Lemma three_root_coef1 (x y z : algC) :
  (\prod_(w <- [:: x; y; z]) ('X - w%:P))`_1 =
    x * y + x * z + y * z.
Proof.
rewrite !big_cons big_nil mulr1 coefM.
rewrite !big_ord_recl big_ord0 /=.
rewrite !coefM !big_ord_recl big_ord0 /=.
rewrite !coefB !coefX !coefC /=.
rewrite !big_ord0 /=.
rewrite ?subr0 ?sub0r ?subrr ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
by rewrite mulrDr !mulrNN.
Qed.

Lemma three_root_coef0 (x y z : algC) :
  (\prod_(w <- [:: x; y; z]) ('X - w%:P))`_0 = -(x * y * z).
Proof.
rewrite !big_cons big_nil mulr1 coefM.
rewrite !big_ord_recl big_ord0 /=.
rewrite !coefM !big_ord_recl big_ord0 /=.
rewrite !coefB !coefX !coefC /=.
rewrite !sub0r !addr0 mulrNN mulNr.
by rewrite mulrA.
Qed.

Lemma quadratic_factor_coefficients_bounded_of_dvdp
    (f : monic_sextic) (b c : int) :
  quadratic_factor b c %| monic_polynomial f ->
  b \in symmetric_interval (2 * root_bound f) /\
  c \in symmetric_interval (root_bound f ^ 2).
Proof.
move=> hdiv.
have [rs [hrs [hpoly hall]]] :=
  bounded_roots_of_monic_factor
    (quadratic_factor_monic b c) (size_quadratic_factor b c) hdiv.
case: rs hrs hpoly hall => [|x [|y [|z rs]]] //= _ hpoly.
move/andP=> [hx /andP [hy _]].
have hb_eq : (b%:~R : algC) = -(x + y).
  have h := congr1 (fun p : {poly algC} => p`_1) hpoly.
  by rewrite coef1_map_quadratic_factor two_root_coef1 in h.
have hc_eq : (c%:~R : algC) = x * y.
  have h := congr1 (fun p : {poly algC} => p`_0) hpoly.
  by rewrite coef0_map_quadratic_factor two_root_coef0 in h.
have hb_norm :
    `|(b%:~R : algC)| <= (2 * (height f + 1))%:R.
  rewrite hb_eq normrN natrM mulrC mulr_natr mulr2n.
  exact: le_trans (ler_normD x y) (lerD hx hy).
have hc_norm :
    `|(c%:~R : algC)| <= ((height f + 1) ^ 2)%:R.
  rewrite hc_eq normrM natrX expr2.
  exact: ler_pM (normr_ge0 x) (normr_ge0 y) hx hy.
have hb_nat : (absz b <= 2 * (height f + 1))%N.
  by move: hb_norm; rewrite -intr_norm ler_nat.
have hc_nat : (absz c <= (height f + 1) ^ 2)%N.
  by move: hc_norm; rewrite -intr_norm ler_nat.
split; apply: mem_symmetric_interval_absz.
- apply: leq_trans hb_nat _.
  by rewrite /root_bound leq_mul2l /= leq_add2l.
- apply: leq_trans hc_nat _.
  by rewrite /root_bound leq_exp2r // leq_add2l.
Qed.

Lemma cubic_factor_coefficients_bounded_of_dvdp
    (f : monic_sextic) (b c d : int) :
  cubic_factor b c d %| monic_polynomial f ->
  b \in symmetric_interval (3 * root_bound f) /\
  c \in symmetric_interval (3 * root_bound f ^ 2) /\
  d \in symmetric_interval (root_bound f ^ 3).
Proof.
move=> hdiv.
have [rs [hrs [hpoly hall]]] :=
  bounded_roots_of_monic_factor
    (cubic_factor_monic b c d) (size_cubic_factor b c d) hdiv.
case: rs hrs hpoly hall => [|x [|y [|z [|w rs]]]] //= _ hpoly.
move/andP=> [hx /andP [hy /andP [hz _]]].
have hb_eq : (b%:~R : algC) = -(x + y + z).
  have h := congr1 (fun p : {poly algC} => p`_2) hpoly.
  by rewrite coef2_map_cubic_factor three_root_coef2 in h.
have hc_eq : (c%:~R : algC) = x * y + x * z + y * z.
  have h := congr1 (fun p : {poly algC} => p`_1) hpoly.
  by rewrite coef1_map_cubic_factor three_root_coef1 in h.
have hd_eq : (d%:~R : algC) = -(x * y * z).
  have h := congr1 (fun p : {poly algC} => p`_0) hpoly.
  by rewrite coef0_map_cubic_factor three_root_coef0 in h.
pose R : algC := (height f + 1)%:R.
have hR0 : 0 <= R by rewrite /R ler0n.
have hxy : `|x * y| <= R ^+ 2.
  rewrite normrM expr2.
  exact: ler_pM (normr_ge0 x) (normr_ge0 y) hx hy.
have hxz : `|x * z| <= R ^+ 2.
  rewrite normrM expr2.
  exact: ler_pM (normr_ge0 x) (normr_ge0 z) hx hz.
have hyz : `|y * z| <= R ^+ 2.
  rewrite normrM expr2.
  exact: ler_pM (normr_ge0 y) (normr_ge0 z) hy hz.
have hxyz : `|x * y * z| <= R ^+ 3.
  rewrite normrM exprSr.
  apply: ler_pM; first exact: normr_ge0.
  - exact: normr_ge0.
  - exact: hxy.
  - exact: hz.
have hb_norm : `|(b%:~R : algC)| <= 3%:R * R.
  rewrite hb_eq normrN mulrC mulr_natr mulrS mulr2n.
  rewrite addrA.
  apply: le_trans (ler_normD (x + y) z) _.
  apply: lerD; last exact: hz.
  exact: le_trans (ler_normD x y) (lerD hx hy).
have hc_norm : `|(c%:~R : algC)| <= 3%:R * R ^+ 2.
  rewrite hc_eq [3%:R * R ^+ 2]mulrC mulr_natr mulrS mulr2n.
  rewrite addrA.
  apply: le_trans (ler_normD (x * y + x * z) (y * z)) _.
  apply: lerD; last exact: hyz.
  exact: le_trans (ler_normD (x * y) (x * z)) (lerD hxy hxz).
have hd_norm : `|(d%:~R : algC)| <= R ^+ 3.
  by rewrite hd_eq normrN.
have hb_nat : (absz b <= 3 * (height f + 1))%N.
  move: hb_norm.
  by rewrite /R -intr_norm -natrM ler_nat.
have hc_nat : (absz c <= 3 * (height f + 1) ^ 2)%N.
  move: hc_norm.
  by rewrite /R -intr_norm -natrX -natrM ler_nat.
have hd_nat : (absz d <= (height f + 1) ^ 3)%N.
  move: hd_norm.
  by rewrite /R -intr_norm -natrX ler_nat.
split; first apply: mem_symmetric_interval_absz.
- apply: leq_trans hb_nat _.
  by rewrite /root_bound leq_mul2l /= leq_add2l.
- split; apply: mem_symmetric_interval_absz.
  + apply: leq_trans hc_nat _.
    rewrite leq_mul2l /=.
    by rewrite /root_bound leq_exp2r // leq_add2l.
  + apply: leq_trans hd_nat _.
    by rewrite /root_bound leq_exp2r // leq_add2l.
Qed.

Lemma monic_polynomial_monic (f : monic_sextic) :
  monic_polynomial f \is monic.
Proof.
apply/monicP.
rewrite lead_coefE size_monic_polynomial /monic_polynomial.
repeat (first
  [ rewrite coefD | rewrite coefXn | rewrite coefCM
  | rewrite coefX | rewrite coefC ]).
simpl.
by rewrite ?mulr0 ?addr0.
Qed.

Lemma monic_size2_linear_factor (q : {poly int}) :
  q \is monic -> size q = 2%N -> q = linear_factor q`_0.
Proof.
move=> hmonic hsize; apply/polyP=> i.
case: i => [|[|i]].
- by rewrite /linear_factor coefD coefX coefC /= add0r.
- have hlead := elimT monicP hmonic.
  rewrite /linear_factor coefD coefX coefC /= addr0.
  by move: hlead; rewrite lead_coefE hsize.
- rewrite nth_default; last by rewrite hsize.
  by rewrite /linear_factor coefD coefX coefC /=.
Qed.

Lemma monic_size3_quadratic_factor (q : {poly int}) :
  q \is monic -> size q = 3%N ->
  q = quadratic_factor q`_1 q`_0.
Proof.
move=> hmonic hsize; apply/polyP=> i.
case: i => [|[|[|i]]].
- by rewrite /quadratic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
- by rewrite /quadratic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
- have hlead := elimT monicP hmonic.
  rewrite /quadratic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
  by move: hlead; rewrite lead_coefE hsize.
- rewrite nth_default; last by rewrite hsize.
  by rewrite /quadratic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
Qed.

Lemma monic_size4_cubic_factor (q : {poly int}) :
  q \is monic -> size q = 4%N ->
  q = cubic_factor q`_2 q`_1 q`_0.
Proof.
move=> hmonic hsize; apply/polyP=> i.
case: i => [|[|[|[|i]]]].
- by rewrite /cubic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r
    ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
- by rewrite /cubic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r
    ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
- by rewrite /cubic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r
    ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
- have hlead := elimT monicP hmonic.
  rewrite /cubic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r
    ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
  by move: hlead; rewrite lead_coefE hsize.
- rewrite nth_default; last by rewrite hsize.
  by rewrite /cubic_factor !coefD ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r
    ?coefXn ?coefCM ?coefX ?coefC /=
    ?mulr0 ?mul0r ?mulr1 ?mul1r ?addr0 ?add0r.
Qed.

(** Gauss's lemma, specialized to a monic target: a nonconstant rational
    divisor can be cleared of denominators and normalized by a sign to a
    monic integer divisor of the same size. *)
Lemma lift_monic_rational_factor (f : monic_sextic) (q : {poly rat}) :
  (1 < size q)%N ->
  q %| map_poly (intr : int -> rat) (monic_polynomial f) ->
  exists qz : {poly int},
    qz \is monic /\ size qz = size q /\ qz %| monic_polynomial f.
Proof.
move=> hqgt1.
case/dvdpP_rat_int=> qz [a ha hscale] [r hproduct].
have hsize : size qz = size q.
  have h := congr1 (fun u : {poly rat} => size u) hscale.
  rewrite size_scale // size_rat_int_poly in h.
  exact: esym h.
have hqzdiv : qz %| monic_polynomial f.
  by rewrite hproduct; exact: dvdp_mulIl.
have hleadprod : lead_coef qz * lead_coef r = 1.
  rewrite -lead_coefM -hproduct.
  exact: elimT monicP (monic_polynomial_monic f).
have hunit : lead_coef qz \is a intUnitRing.unitz.
  apply: (intUnitRing.unitzPl (n := lead_coef r)).
  by rewrite mulrC hleadprod.
move: hunit; rewrite qualifE => /orP [/eqP hlead | /eqP hlead].
- exists qz; split; first exact/monicP.
  by split.
- exists (- qz); split.
  + apply/monicP.
    by rewrite lead_coefN hlead opprK.
  + rewrite size_polyN hsize; split=> //.
    by rewrite dvdpNl.
Qed.

Lemma small_monic_factor_found (f : monic_sextic) (q : {poly int}) :
  q \is monic -> (1 < size q <= 4)%N ->
  q %| monic_polynomial f -> has_bounded_proper_factor f.
Proof.
move=> hmonic /andP [hgt hle] hdiv.
have /or3P [/eqP hs2 | /eqP hs3 | /eqP hs4] :
    [|| size q == 2%N, size q == 3%N | size q == 4%N].
  move: hgt hle.
  by case: (size q) => [|[|[|[|[|n]]]]] //.
- have hform := monic_size2_linear_factor hmonic hs2.
  rewrite hform in hdiv.
  have hc := linear_factor_mem_symmetric_interval_of_dvdp hdiv.
  rewrite /has_bounded_proper_factor.
  apply/orP; left; apply/has_bounded_linear_factorP.
  by exists q`_0.
- have hform := monic_size3_quadratic_factor hmonic hs3.
  rewrite hform in hdiv.
  have [hb hc] := quadratic_factor_coefficients_bounded_of_dvdp hdiv.
  rewrite /has_bounded_proper_factor /has_bounded_nonlinear_factor.
  apply/orP; right; apply/orP; left; apply/has_bounded_quadratic_factorP.
  by exists q`_1; split=> //; exists q`_0.
- have hform := monic_size4_cubic_factor hmonic hs4.
  rewrite hform in hdiv.
  have [hb [hc hd]] := cubic_factor_coefficients_bounded_of_dvdp hdiv.
  rewrite /has_bounded_proper_factor /has_bounded_nonlinear_factor.
  apply/orP; right; apply/orP; right; apply/has_bounded_cubic_factorP.
  by exists q`_2; split=> //; exists q`_1; split=> //; exists q`_0.
Qed.

(** The only classical step in factor-search completeness is extracting a
    proper divisor from the negation of MathComp's propositional definition of
    irreducibility.  Everything after this witness extraction is explicit. *)
Lemma reducible_sextic_has_small_rational_factor (p : {poly rat}) :
  size p = 7%N -> ~ irreducible_poly p ->
  exists q : {poly rat}, (1 < size q <= 4)%N /\ q %| p.
Proof.
move=> hp7 hnot.
have hex : exists q : {poly rat},
    size q != 1%N /\ q %| p /\ ~ q %= p.
  apply: NNPP=> hnex.
  apply: hnot; split; first by rewrite hp7.
  move=> q hq1 hdiv.
  case heq: (q %= p); first by [] .
  exfalso; apply: hnex; exists q; split=> //; split=> //.
  by rewrite heq.
have [q [hq1 [hqdiv hqneqp]]] := hex.
have hp0 : p != 0 by rewrite -size_poly_gt0 hp7.
have hq0 : q != 0.
  apply: contraTneq hqdiv=> ->.
  by rewrite dvd0p (negPf hp0).
have hqgt1 : (1 < size q)%N.
  by rewrite ltn_neqAle eq_sym hq1 size_poly_gt0 hq0.
have hqsize_ne : size q != size p.
  apply/eqP=> hsize.
  apply: hqneqp.
  move: (dvdp_size_eqp hqdiv).
  by rewrite hsize eqxx => <-.
have hqlt : (size q < size p)%N.
  rewrite ltn_neqAle hqsize_ne.
  exact: dvdp_leq hp0 hqdiv.
case/dvdpP/sig_eqW: hqdiv => r hproduct.
have hr0 : r != 0.
  apply/negP=> /eqP hrzero.
  by move: hp0; rewrite hproduct hrzero mul0r eqxx.
have hrdiv : r %| p.
  by rewrite hproduct; exact: dvdp_mulIl.
have hqdiv' : q %| p.
  by rewrite hproduct; exact: dvdp_mulIr.
have hsize_product : size p = (size r + size q).-1.
  by rewrite hproduct size_mul.
case hqle4: (size q <= 4)%N.
- have hqle4P : (size q <= 4)%N by rewrite hqle4.
  exists q; split; last exact: hqdiv'.
  by apply/andP; split.
- have hqgt4 : (4 < size q)%N.
    by rewrite ltnNge hqle4.
  have hrpos : (0 < size r)%N by rewrite size_poly_gt0 hr0.
  have hsumpos : (0 < size r + size q)%N :=
    leq_trans hrpos (leq_addr (size q) (size r)).
  have hsum_eq : (size p).+1 = size r + size q.
    rewrite hsize_product.
    exact: prednK hsumpos.
  have /orP [/eqP hq5 | /eqP hq6] :
      (size q == 5%N) || (size q == 6%N).
    move: hqgt4 hqlt; rewrite hp7.
    by case: (size q) => [|[|[|[|[|[|[|n]]]]]]] //.
  + have hr3 : size r = 3%N.
      move: hsum_eq; rewrite hp7 hq5 /=.
      move=> heq.
      apply/eqP; rewrite -(eqn_add2r 5%N); apply/eqP.
      exact: esym heq.
    exists r; split; last exact: hrdiv.
    by rewrite hr3.
  + have hr2 : size r = 2%N.
      move: hsum_eq; rewrite hp7 hq6 /=.
      move=> heq.
      apply/eqP; rewrite -(eqn_add2r 6%N); apply/eqP.
      exact: esym heq.
    exists r; split; last exact: hrdiv.
    by rewrite hr2.
Qed.

Lemma not_irreducible_bounded_proper_factor (f : monic_sextic) :
  ~ irreducible_poly (monic_polynomial f) ->
  has_bounded_proper_factor f.
Proof.
move=> hnot.
pose pQ := map_poly (intr : int -> rat) (monic_polynomial f).
have hpQsize : size pQ = 7%N.
  by rewrite /pQ size_rat_int_poly size_monic_polynomial.
have hnotQ : ~ irreducible_poly pQ.
  move=> hirrQ; apply: hnot.
  exact: (proj1 (irreducible_rat_int (monic_polynomial f))) hirrQ.
have [q [hqsmall hqdiv]] :=
  reducible_sextic_has_small_rational_factor hpQsize hnotQ.
have hqgt1 : (1 < size q)%N := (andP hqsmall).1.
have [qz [hqzmonic [hqzsize hqzdiv]]] :=
  lift_monic_rational_factor hqgt1 hqdiv.
apply: small_monic_factor_found hqzmonic _ hqzdiv.
by rewrite hqzsize.
Qed.

Lemma has_bounded_proper_factor_iff_not_irreducible (f : monic_sextic) :
  has_bounded_proper_factor f <->
  ~ irreducible_poly (monic_polynomial f).
Proof.
split.
- exact: bounded_proper_factor_not_irreducible.
- exact: not_irreducible_bounded_proper_factor.
Qed.

Lemma has_bounded_proper_factorP (f : monic_sextic) :
  reflect (~ irreducible_poly (monic_polynomial f))
    (has_bounded_proper_factor f).
Proof.
apply: (iffP idP).
- exact: bounded_proper_factor_not_irreducible.
- exact: not_irreducible_bounded_proper_factor.
Qed.

End PolynomialFormulasSexticFactorCompleteness.
