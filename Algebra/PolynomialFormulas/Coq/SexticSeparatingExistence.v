From mathcomp Require Import all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From PolynomialFormulas Require Import SexticSparseResolvents
  SexticNewtonPowerSums SexticResolventSymmetry SexticComputedResolvents
  SexticSeparatingSearch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

(** Algebraic termination proof for the executable separating search.  The
    descriptor is viewed as a polynomial in the two natural parameters: an
    outer polynomial whose coefficients are polynomials in the inner
    parameter. *)
Module PolynomialFormulasSexticSeparatingExistence.

Import PolynomialFormulasSexticSparseResolvents.
Import PolynomialFormulasSexticNewtonPowerSums.
Import PolynomialFormulasSexticResolventSymmetry.
Import PolynomialFormulasSexticSeparatingSearch.
Import PolynomialFormulasSexticComputedResolvents.

Definition code_wfb (c : seq nat) : bool :=
  [&& sorted leq c, uniq c & all (fun n => n < 6)%N c].

Lemma pair_codes_wfb p : all code_wfb (pair_member_blocks p).
Proof.
rewrite pair_member_blocks_correct.
case: p=> [[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]]]]]]] hp] //;
vm_compute.
Qed.

Lemma triple_codes_wfb p : all code_wfb (triple_member_blocks p).
Proof.
rewrite triple_member_blocks_correct.
case: p=> [[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]] hp] //;
vm_compute.
Qed.

Lemma pair_codes_uniq p : uniq (pair_member_blocks p).
Proof.
rewrite pair_member_blocks_correct.
case: p=> [[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]]]]]]] hp] //;
vm_compute.
Qed.

Lemma triple_codes_uniq p : uniq (triple_member_blocks p).
Proof.
rewrite triple_member_blocks_correct.
case: p=> [[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]] hp] //;
vm_compute.
Qed.

Lemma pair_codes_perm_injective p q :
  perm_eq (pair_member_blocks p) (pair_member_blocks q) -> p = q.
Proof.
rewrite !pair_member_blocks_correct.
case: p=> [[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]]]]]]] hp] //;
case: q=> [[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|q]]]]]]]]]]]]]]] hq] //;
vm_compute.
all: by move=> _; apply: val_inj.
Qed.

Lemma triple_codes_perm_injective p q :
  perm_eq (triple_member_blocks p) (triple_member_blocks q) -> p = q.
Proof.
rewrite !triple_member_blocks_correct.
case: p=> [[|[|[|[|[|[|[|[|[|[|p]]]]]]]]]] hp] //;
case: q=> [[|[|[|[|[|[|[|[|[|[|q]]]]]]]]]] hq] //;
vm_compute.
all: by move=> _; apply: val_inj.
Qed.

Section DescriptorPolynomials.

Variable R : idomainType.

Definition code_roots (roots : 6.-tuple R) (c : seq nat) : seq R :=
  [seq root_at_nat roots n | n <- c].

Definition block_polynomial (roots : 6.-tuple R) (c : seq nat) : {poly R} :=
  \prod_(z <- code_roots roots c) ('X - z%:P).

Definition descriptor_bipolynomial
    (roots : 6.-tuple R) (codes : seq (seq nat)) : {poly {poly R}} :=
  \prod_(z <- [seq block_polynomial roots c | c <- codes]) ('X - z%:P).

Definition tuple_injective (roots : 6.-tuple R) : Prop :=
  injective (tnth roots).

Lemma root_at_nat_injective_bounded roots
    (hroots : tuple_injective roots) n m :
  (n < 6)%N -> (m < 6)%N ->
  root_at_nat roots n = root_at_nat roots m -> n = m.
Proof.
move=> hn hm hnm.
pose ni : 'I_6 := Ordinal hn.
pose mi : 'I_6 := Ordinal hm.
have hni : tnth roots ni = root_at_nat roots n.
  by rewrite /root_at_nat -(@tnth_nth 6 R 0 roots ni).
have hmi : tnth roots mi = root_at_nat roots m.
  by rewrite /root_at_nat -(@tnth_nth 6 R 0 roots mi).
have him : ni = mi by apply: hroots; rewrite hni hmi.
have hval : nat_of_ord ni = nat_of_ord mi :=
  congr1 (@nat_of_ord 6) him.
exact hval.
Qed.

Lemma block_polynomial_perm roots c d
    (hroots : tuple_injective roots)
    (hc : code_wfb c) (hd : code_wfb d) :
  block_polynomial roots c = block_polynomial roots d -> perm_eq c d.
Proof.
move/and3P: hc=> [hcs hcu hcb].
move/and3P: hd=> [hds hdu hdb] hpoly.
apply: (uniq_perm hcu hdu)=> n; apply/idP/idP=> hn.
- have hroot : root (block_polynomial roots c) (root_at_nat roots n).
    rewrite /block_polynomial root_prod_XsubC /code_roots.
    apply/mapP; by exists n.
  rewrite hpoly /block_polynomial root_prod_XsubC /code_roots in hroot.
  move/mapP: hroot=> [m hm hmn].
  have hn6 : (n < 6)%N := (allP hcb n hn).
  have hm6 : (m < 6)%N := (allP hdb m hm).
  have hnm : n = m := root_at_nat_injective_bounded hroots hn6 hm6 hmn.
  by rewrite hnm.
- have hroot : root (block_polynomial roots d) (root_at_nat roots n).
    rewrite /block_polynomial root_prod_XsubC /code_roots.
    apply/mapP; by exists n.
  rewrite -hpoly /block_polynomial root_prod_XsubC /code_roots in hroot.
  move/mapP: hroot=> [m hm hmn].
  have hn6 : (n < 6)%N := (allP hdb n hn).
  have hm6 : (m < 6)%N := (allP hcb m hm).
  have hnm : n = m := root_at_nat_injective_bounded hroots hn6 hm6 hmn.
  by rewrite hnm.
Qed.

Lemma block_polynomial_eq roots c d
    (hroots : tuple_injective roots)
    (hc : code_wfb c) (hd : code_wfb d) :
  block_polynomial roots c = block_polynomial roots d -> c = d.
Proof.
move=> hpoly.
have hperm : perm_eq c d := block_polynomial_perm hroots hc hd hpoly.
move/and3P: hc=> [hcs _ _].
move/and3P: hd=> [hds _ _].
exact: (@sorted_eq _ leq leq_trans anti_leq c d hcs hds hperm).
Qed.

Lemma descriptor_bipolynomial_perm roots codes1 codes2
    (hroots : tuple_injective roots)
    (hwf1 : all code_wfb codes1) (hwf2 : all code_wfb codes2)
    (hu1 : uniq codes1) (hu2 : uniq codes2) :
  descriptor_bipolynomial roots codes1 =
    descriptor_bipolynomial roots codes2 ->
  perm_eq codes1 codes2.
Proof.
move=> hpoly.
apply: (uniq_perm hu1 hu2)=> c; apply/idP/idP=> hc.
- have hroot :
      root (descriptor_bipolynomial roots codes1)
        (block_polynomial roots c).
    rewrite /descriptor_bipolynomial root_prod_XsubC.
    apply/mapP; by exists c.
  rewrite hpoly /descriptor_bipolynomial root_prod_XsubC in hroot.
  move/mapP: hroot=> [d hd hdc].
  have hcwf := allP hwf1 c hc.
  have hdwf := allP hwf2 d hd.
  have hcd : c = d.
    have hpoly_cd : block_polynomial roots c = block_polynomial roots d.
      exact: hdc.
    exact: (block_polynomial_eq hroots hcwf hdwf hpoly_cd).
  by rewrite hcd.
- have hroot :
      root (descriptor_bipolynomial roots codes2)
        (block_polynomial roots c).
    rewrite /descriptor_bipolynomial root_prod_XsubC.
    apply/mapP; by exists c.
  rewrite -hpoly /descriptor_bipolynomial root_prod_XsubC in hroot.
  move/mapP: hroot=> [d hd hdc].
  have hcwf := allP hwf2 c hc.
  have hdwf := allP hwf1 d hd.
  have hcd : c = d.
    have hpoly_cd : block_polynomial roots c = block_polynomial roots d.
      exact: hdc.
    exact: (block_polynomial_eq hroots hcwf hdwf hpoly_cd).
  by rewrite hcd.
Qed.

Lemma pair_descriptor_bipolynomial_injective roots
    (hroots : tuple_injective roots) :
  injective (fun p : pair_partition =>
    descriptor_bipolynomial roots (pair_member_blocks p)).
Proof.
move=> p q hpq; apply: pair_codes_perm_injective.
apply: descriptor_bipolynomial_perm hpq.
- exact: hroots.
- exact: pair_codes_wfb.
- exact: pair_codes_wfb.
- exact: pair_codes_uniq.
- exact: pair_codes_uniq.
Qed.

Lemma triple_descriptor_bipolynomial_injective roots
    (hroots : tuple_injective roots) :
  injective (fun p : triple_partition =>
    descriptor_bipolynomial roots (triple_member_blocks p)).
Proof.
move=> p q hpq; apply: triple_codes_perm_injective.
apply: descriptor_bipolynomial_perm hpq.
- exact: hroots.
- exact: triple_codes_wfb.
- exact: triple_codes_wfb.
- exact: triple_codes_uniq.
- exact: triple_codes_uniq.
Qed.

End DescriptorPolynomials.

Section NaturalGrid.

Lemma nat_cast_inj_algC : injective (fun n : nat => (n%:R : algC)).
Proof.
move=> m n hmn.
have hmnz : (m%:Z : int) = n%:Z.
  apply: (@intr_inj algC).
  exact: hmn.
by case: hmnz.
Qed.

Lemma exists_nat_horner_ne_zero (p : {poly algC}) :
  p != 0 -> exists n : nat, p.[n%:R] != 0.
Proof.
move=> hp.
pose rs := [seq (n%:R : algC) | n <- iota 0 (size p)].
have hrs_size : size rs = size p by rewrite /rs size_map size_iota.
have hrs_uniq : uniq rs.
  rewrite /rs map_inj_uniq ?iota_uniq //.
  exact: nat_cast_inj_algC.
have [hall|hall] := boolP (all (root p) rs).
- have hsmall := max_poly_roots hp hall hrs_uniq.
  by rewrite hrs_size ltnn in hsmall.
- move/allPn: hall=> [z hz hzroot].
  move/mapP: hz=> [n hn hnz].
  exists n.
  rewrite -hnz.
  by rewrite /root in hzroot.
Qed.

Definition bipoly_eval (a b : algC) (P : {poly {poly algC}}) : algC :=
  (map_poly (horner_eval b) P).[a].

Lemma exists_nat_bipoly_eval_ne_zero (P : {poly {poly algC}}) :
  P != 0 ->
  exists a b : nat, bipoly_eval a%:R b%:R P != 0.
Proof.
move=> hP.
have hlead : lead_coef P != 0 by move: hP; rewrite lead_coef_eq0.
have [b hb] := exists_nat_horner_ne_zero hlead.
pose Q : {poly algC} := map_poly (horner_eval b%:R) P.
have hcoef : Q`_(size P).-1 != 0.
  by rewrite /Q coef_map -lead_coefE.
have hQ : Q != 0.
  apply: contraNneq hcoef=> hQ0.
  by rewrite hQ0 coef0 eqxx.
have [a ha] := exists_nat_horner_ne_zero hQ.
exists a, b.
exact: ha.
Qed.

End NaturalGrid.

Section EvaluationBridge.

Variable R : idomainType.

Lemma block_polynomial_horner (roots : 6.-tuple R) code b :
  (block_polynomial roots code).[b] =
    block_code_value roots b code.
Proof.
rewrite /block_polynomial /block_code_value /code_roots
  horner_prod big_map.
apply: eq_bigr=> n _.
by rewrite hornerXsubC.
Qed.

End EvaluationBridge.

Definition natural_parameter (a b : nat) : parameter := [tuple a; b].

Lemma descriptor_bipolynomial_nat_eval roots codes a b :
  bipoly_eval a%:R b%:R (descriptor_bipolynomial roots codes) =
    descriptor_codes_value roots (natural_parameter a b) codes.
Proof.
rewrite /bipoly_eval /descriptor_bipolynomial /descriptor_codes_value
  rmorph_prod horner_prod big_map.
apply: eq_bigr=> code _.
rewrite rmorphB.
rewrite /= map_polyX map_polyC hornerXsubC.
change (a%:R - (block_polynomial roots code).[b%:R] =
  (tnth (natural_parameter a b) ord0)%:R -
    block_code_value roots
      (tnth (natural_parameter a b) ord_max)%:R code).
rewrite block_polynomial_horner.
by rewrite /natural_parameter /=.
Qed.

Section CollisionGrid.

Variable I : finType.

Lemma bipoly_eval_collision_product
    (v : I -> {poly {poly algC}}) a b :
  bipoly_eval a b (collision_product v) =
    collision_product (fun i => bipoly_eval a b (v i)).
Proof.
rewrite /bipoly_eval /collision_product rmorph_prod horner_prod.
apply: eq_bigr=> p _.
rewrite rmorph_prod horner_prod.
apply: eq_bigr=> q _.
case hpq: (p == q).
- by rewrite /= rmorph1 hornerC.
- by rewrite /= rmorphB hornerD hornerN.
Qed.

Lemma exists_nat_eval_injective (v : I -> {poly {poly algC}}) :
  injective v ->
  exists a b : nat,
    injective (fun i => bipoly_eval a%:R b%:R (v i)).
Proof.
move=> hv.
have hcollision : collision_product v != 0 :=
  (proj2 (collision_product_neq0_iff v)) hv.
have [a [b hab]] := exists_nat_bipoly_eval_ne_zero hcollision.
exists a, b.
apply: (proj1 (collision_product_neq0_iff _)).
rewrite -bipoly_eval_collision_product.
exact: hab.
Qed.

End CollisionGrid.

Lemma pair_descriptor_bipolynomial_nat_eval roots a b p :
  bipoly_eval a%:R b%:R
      (descriptor_bipolynomial roots (pair_member_blocks p)) =
    sparse_eval_ring roots
      (pair_sparse_descriptor_value (natural_parameter a b) p).
Proof.
rewrite descriptor_bipolynomial_nat_eval.
exact: esym (pair_descriptor_member_codes roots (natural_parameter a b) p).
Qed.

Lemma triple_descriptor_bipolynomial_nat_eval roots a b p :
  bipoly_eval a%:R b%:R
      (descriptor_bipolynomial roots (triple_member_blocks p)) =
    sparse_eval_ring roots
      (triple_sparse_descriptor_value (natural_parameter a b) p).
Proof.
rewrite descriptor_bipolynomial_nat_eval.
exact: esym (triple_descriptor_member_codes roots (natural_parameter a b) p).
Qed.

Theorem exists_pair_descriptor_injective (roots : 6.-tuple algC) :
  tuple_injective roots ->
  exists x : parameter, pair_descriptor_injective roots x.
Proof.
move=> hroots.
have hpoly := pair_descriptor_bipolynomial_injective hroots.
have [a [b hab]] := exists_nat_eval_injective hpoly.
exists (natural_parameter a b).
move=> p q hpq; apply: hab.
by rewrite !pair_descriptor_bipolynomial_nat_eval hpq.
Qed.

Theorem exists_triple_descriptor_injective (roots : 6.-tuple algC) :
  tuple_injective roots ->
  exists x : parameter, triple_descriptor_injective roots x.
Proof.
move=> hroots.
have hpoly := triple_descriptor_bipolynomial_injective hroots.
have [a [b hab]] := exists_nat_eval_injective hpoly.
exists (natural_parameter a b).
move=> p q hpq; apply: hab.
by rewrite !triple_descriptor_bipolynomial_nat_eval hpq.
Qed.

Theorem pair_separating_search_terminates roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots) :
  tuple_injective roots ->
  exists fuel, pair_separating_up_to f fuel.
Proof.
move=> hroots.
exact: (pair_separating_search_eventually hvieta
  (exists_pair_descriptor_injective hroots)).
Qed.

Theorem triple_separating_search_terminates roots f
    (hvieta : @cast_int_values algC (monic_elementary_values f) =
      elementary_values roots) :
  tuple_injective roots ->
  exists fuel, triple_separating_up_to f fuel.
Proof.
move=> hroots.
exact: (triple_separating_search_eventually hvieta
  (exists_triple_descriptor_injective hroots)).
Qed.

End PolynomialFormulasSexticSeparatingExistence.
