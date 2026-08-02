From mathcomp Require Import all_ssreflect all_algebra all_field.
From Abel Require Import abel.
From PolynomialFormulas Require Import AbelRuffini QuinticRadicalDecidability.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Notation ratrC := (@ratr algC).

(** Rootwise semantic lemmas used by the reducible branches of the sextic
    decision.  The generic statements keep the elementary root-set argument
    separate from the particular MathComp-Abel radical predicate. *)
Module PolynomialFormulasSexticReducibleSemantics.

Import LeanProofs.PolynomialFormulasAbelRuffini.
Import PolynomialFormulasQuinticRadicalDecidability.

Definition all_roots_satisfy
    (Q : algC -> Prop) (p : {poly rat}) : Prop :=
  {in root (map_poly ratrC p), forall x, Q x}.

Lemma all_roots_satisfy_mul (Q : algC -> Prop) (p q : {poly rat}) :
  all_roots_satisfy Q (p * q) <->
    all_roots_satisfy Q p /\ all_roots_satisfy Q q.
Proof.
rewrite /all_roots_satisfy.
split.
- move=> hpq; split=> x hx; apply: hpq.
  + apply/rootP; move/rootP: hx=> hx.
    by rewrite rmorphM hornerM hx mul0r.
  + apply/rootP; move/rootP: hx=> hx.
    by rewrite rmorphM hornerM hx mulr0.
- move=> [hp hq] x hx.
  move/rootP: hx=> hx.
  have /orP[hpx|hqx] :
      ((map_poly ratrC p).[x] == 0) ||
      ((map_poly ratrC q).[x] == 0).
    rewrite -mulf_eq0; apply/eqP.
    by move: hx; rewrite rmorphM hornerM.
  + apply: hp; exact/rootP/eqP.
  + apply: hq; exact/rootP/eqP.
Qed.

Lemma all_roots_satisfy_scale
    (Q : algC -> Prop) (c : rat) (p : {poly rat}) (hc : c != 0) :
  all_roots_satisfy Q (c *: p) <-> all_roots_satisfy Q p.
Proof.
have hcC : ratrC c != 0 by rewrite fmorph_eq0.
rewrite /all_roots_satisfy.
split.
- move=> h x hx; apply: h; apply/rootP; move/rootP: hx=> hx.
  by rewrite map_polyZ hornerZ hx mulr0.
- move=> h x hx; apply: h; apply/rootP.
  move/rootP: hx=> hx.
  move: hx; rewrite map_polyZ hornerZ=> hx.
  have heq : ratrC c * (map_poly ratrC p).[x] == 0 by exact/eqP.
  move: heq; rewrite mulf_eq0 (negPf hcC) orFb=> /eqP.
  exact.
Qed.

(** The exact rootwise radical predicate is an instance of the generic
    closure lemmas above.  No nonzeroness hypotheses are needed here. *)
Lemma radical_formula_solves_mul (p q : {poly rat}) :
  radical_formula_solves (p * q) <->
    radical_formula_solves p /\ radical_formula_solves q.
Proof. exact: all_roots_satisfy_mul. Qed.

Lemma radical_formula_solves_scale (c : rat) (p : {poly rat}) :
  c != 0 ->
  radical_formula_solves (c *: p) <-> radical_formula_solves p.
Proof. exact: all_roots_satisfy_scale. Qed.

Lemma radical_formula_solves_mul_iff_left (p q : {poly rat}) :
  radical_formula_solves q ->
  (radical_formula_solves (p * q) <-> radical_formula_solves p).
Proof.
move=> hq; rewrite radical_formula_solves_mul.
split; first by move=> [hp _].
by move=> hp; split.
Qed.

Lemma radical_formula_solves_mul_iff_right (p q : {poly rat}) :
  radical_formula_solves p ->
  (radical_formula_solves (p * q) <-> radical_formula_solves q).
Proof.
move=> hp; rewrite radical_formula_solves_mul.
split; first by move=> [_ hq].
by move=> hq; split.
Qed.

Lemma radical_formula_solves_factorization
    (p a b : {poly rat}) :
  p = a * b ->
  (radical_formula_solves p <->
    radical_formula_solves a /\ radical_formula_solves b).
Proof. by move=> ->; exact: radical_formula_solves_mul. Qed.

(** MathComp-Abel's field-theoretic predicate agrees with the rootwise one
    for nonzero polynomials, so it inherits the same factorization laws. *)
Lemma solvable_by_radical_poly_mul
    (p q : {poly rat}) (hp : p != 0) (hq : q != 0) :
  solvable_by_radical_poly (p * q) <->
    solvable_by_radical_poly p /\ solvable_by_radical_poly q.
Proof.
have hpq : p * q != 0 := mulf_neq0 hp hq.
rewrite (radical_formula_solvesP hpq)
  (radical_formula_solvesP hp) (radical_formula_solvesP hq).
exact: radical_formula_solves_mul.
Qed.

Lemma solvable_by_radical_poly_scale
    (c : rat) (p : {poly rat}) (hc : c != 0) (hp : p != 0) :
  solvable_by_radical_poly (c *: p) <-> solvable_by_radical_poly p.
Proof.
have hcp : c *: p != 0 by rewrite scaler_eq0 negb_or hc hp.
rewrite (radical_formula_solvesP hcp) (radical_formula_solvesP hp).
exact: radical_formula_solves_scale.
Qed.

Lemma solvable_by_radical_poly_factorization
    (p a b : {poly rat}) (ha : a != 0) (hb : b != 0) :
  p = a * b ->
  (solvable_by_radical_poly p <->
    solvable_by_radical_poly a /\ solvable_by_radical_poly b).
Proof. by move=> ->; exact: solvable_by_radical_poly_mul. Qed.

(** The integer-coefficient predicate used by the quintic and sextic
    endpoints is definitionally the same rootwise predicate after mapping
    coefficients to the rationals. *)
Lemma all_roots_radical_intE (p : {poly int}) :
  all_roots_radical_int p <->
    radical_formula_solves (int_to_rat_poly p).
Proof. by []. Qed.

Lemma all_roots_radical_int_mul (p q : {poly int}) :
  all_roots_radical_int (p * q) <->
    all_roots_radical_int p /\ all_roots_radical_int q.
Proof.
rewrite !all_roots_radical_intE /int_to_rat_poly rmorphM.
exact: radical_formula_solves_mul.
Qed.

Lemma all_roots_radical_int_scale (c : int) (p : {poly int}) :
  c != 0 ->
  all_roots_radical_int (c *: p) <-> all_roots_radical_int p.
Proof.
move=> hc.
rewrite !all_roots_radical_intE /int_to_rat_poly map_polyZ.
apply: radical_formula_solves_scale.
by rewrite intr_eq0.
Qed.

Lemma all_roots_radical_int_mul_iff_left (p q : {poly int}) :
  all_roots_radical_int q ->
  (all_roots_radical_int (p * q) <-> all_roots_radical_int p).
Proof.
move=> hq; rewrite all_roots_radical_int_mul.
split; first by move=> [hp _].
by move=> hp; split.
Qed.

Lemma all_roots_radical_int_mul_iff_right (p q : {poly int}) :
  all_roots_radical_int p ->
  (all_roots_radical_int (p * q) <-> all_roots_radical_int q).
Proof.
move=> hp; rewrite all_roots_radical_int_mul.
split; first by move=> [_ hq].
by move=> hq; split.
Qed.

Lemma all_roots_radical_int_factorization
    (p a b : {poly int}) :
  p = a * b ->
  (all_roots_radical_int p <->
    all_roots_radical_int a /\ all_roots_radical_int b).
Proof. by move=> ->; exact: all_roots_radical_int_mul. Qed.

End PolynomialFormulasSexticReducibleSemantics.
