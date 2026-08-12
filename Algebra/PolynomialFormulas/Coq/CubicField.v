From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Cardano's formula over an arbitrary MathComp field.

    The corrected scope explicitly excludes characteristics two and three.
    The square and cube radicals are supplied together with their defining
    equations, and the two cube roots carry Cardano's compatibility equation.
    Under those hypotheses the three displayed values give an exact linear
    factorization and exhaust all roots.

    The final section isolates the branch that is only described informally
    in Lazard's paper.  If the depressed cubic [X^3 + p X + q] is irreducible
    and [p = 0], then [q != 0].  Of the supplied square roots [s] and [-s],
    one is selected so that the first cubic radicand is nonzero.  The other
    radicand is then zero.  A supplied cube root [s1] of the first radicand is
    nonzero, hence the printed denominator [3 s1] is nonzero, and the derived
    second radical [-p / (3 s1)] is zero and compatible. *)
Module PolynomialFormulasCubicField.

Import GRing.Theory.
Local Open Scope ring_scope.

Section CubicField.

Variable F : fieldType.

Definition depressed_cubic_value (p q y : F) : F :=
  y ^+ 3 + p * y + q.

Definition depressed_cubic_polynomial (p q : F) : {poly F} :=
  'X^3 + p *: 'X + q%:P.

Definition cardano_delta (p q : F) : F :=
  (q / 2%:R) ^+ 2 + (p / 3%:R) ^+ 3.

Definition cardano_first_radicand (q s : F) : F :=
  - q / 2%:R + s.

Definition cardano_second_radicand (q s : F) : F :=
  - q / 2%:R - s.

Definition cardano_root0 (u v : F) : F := u + v.

Definition cardano_root1 (u v omega : F) : F :=
  omega * u + omega ^+ 2 * v.

Definition cardano_root2 (u v omega : F) : F :=
  omega ^+ 2 * u + omega * v.

(** Local bridge from MathComp's packed operations to Stdlib [ring]. *)
Let ring_carrier : Type := F.
Local Definition ring_zero : ring_carrier := @GRing.zero F.
Local Definition ring_one : ring_carrier := @GRing.one F.
Local Definition ring_add : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.add F.
Local Definition ring_mul : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.mul F.
Local Definition ring_sub : ring_carrier -> ring_carrier -> ring_carrier :=
  fun x y => x - y.
Local Definition ring_opp : ring_carrier -> ring_carrier := @GRing.opp F.
Local Definition ring_eq : ring_carrier -> ring_carrier -> Prop :=
  @eq ring_carrier.

Lemma cubic_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma cubic_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma cubic_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma cubic_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma cubic_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma cubic_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma cubic_ring_theory :
  @ring_theory ring_carrier ring_zero ring_one ring_add ring_mul
    ring_sub ring_opp ring_eq.
Proof.
constructor; unfold ring_zero, ring_one, ring_add, ring_mul, ring_sub,
  ring_opp, ring_eq; intros.
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

Add Ring cubic_field_ring : cubic_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Lemma cubic_two_natrE : (2%:R : F) = 1 + 1.
Proof. exact: (@natrD F 1 1). Qed.

Lemma cubic_three_natrE : (3%:R : F) = 1 + 1 + 1.
Proof.
rewrite -cubic_two_natrE.
exact: (@natrD F 2 1).
Qed.

Lemma cubic_expr2 (x : F) : x ^+ 2 = x * x.
Proof. by rewrite expr2. Qed.

Lemma cubic_expr3 (x : F) : x ^+ 3 = x * x * x.
Proof. by rewrite exprSr expr2. Qed.

Ltac finish_cubic_field_ring :=
  repeat first
    [ rewrite cubic_two_natrE
    | rewrite cubic_three_natrE
    | rewrite cubic_expr2
    | rewrite cubic_expr3
    | rewrite cubic_ring_addE
    | rewrite cubic_ring_mulE
    | rewrite cubic_ring_subE
    | rewrite cubic_ring_oppE
    | rewrite cubic_ring_zeroE
    | rewrite cubic_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

Lemma cubic_two_mul_div (x : F) (two_neq0 : (2%:R : F) != 0) :
  2%:R * (x / 2%:R) = x.
Proof. by rewrite [2%:R * _]mulrC (divfK two_neq0 x). Qed.

Lemma cubic_three_mul_div (x : F) (three_neq0 : (3%:R : F) != 0) :
  3%:R * (x / 3%:R) = x.
Proof. by rewrite [3%:R * _]mulrC (divfK three_neq0 x). Qed.

(** The quadratic equation is the algebraic primitive-cube-root equation
    used in the three Cardano branches. *)
Lemma primitive_cube_root_cubed (omega : F)
    (homega : omega ^+ 2 + omega + 1 = 0) :
  omega ^+ 3 = 1.
Proof.
transitivity
  (1 + (omega - 1) * (omega ^+ 2 + omega + 1)).
- finish_cubic_field_ring.
- by rewrite homega mulr0 addr0.
Qed.

(** A genuine primitive third root satisfies the quadratic equation used by
    the three Cardano branches. *)
Lemma primitive_cube_root_quadratic (omega : F)
    (omega_primitive : 3.-primitive_root omega) :
  omega ^+ 2 + omega + 1 = 0.
Proof.
have homega3 : omega ^+ 3 = 1 := prim_expr_order omega_primitive.
have homega1 : omega != 1.
  apply/negP=> /eqP homega_one.
  have hbad : (3 %| 1)%N.
    by rewrite (prim_order_dvd omega_primitive) homega_one expr1.
  by move: hbad.
have hleft : omega - 1 != 0 by rewrite subr_eq0.
have hproduct :
    (omega - 1) * (omega ^+ 2 + omega + 1) = 0.
  transitivity (omega ^+ 3 - 1).
  - finish_cubic_field_ring.
  - by rewrite homega3 subrr.
have hproductb :
    (omega - 1) * (omega ^+ 2 + omega + 1) == 0.
  apply/eqP.
  exact: hproduct.
move: hproductb.
rewrite mulf_eq0 (negPf hleft) /=.
by move/eqP.
Qed.

(** Conversely, when three is nonzero, the quadratic equation describes an
    actual primitive (not merely arbitrary) third root of unity. *)
Lemma primitive_cube_root_of_quadratic (omega : F)
    (three_neq0 : (3%:R : F) != 0)
    (homega : omega ^+ 2 + omega + 1 = 0) :
  3.-primitive_root omega.
Proof.
have homega3 : omega ^+ 3 = 1 := primitive_cube_root_cubed homega.
have homega1 : omega != 1.
  apply/negP=> /eqP homega_one.
  have hthree0 : (3%:R : F) = 0.
    move: homega.
    by rewrite homega_one expr1n -cubic_three_natrE.
  by move: three_neq0; rewrite hthree0 eqxx.
have [m hm hdiv] :=
  prim_order_exists (n := 3) (z := omega)
    (isT : 0 < 3)%N homega3.
have hm_ne1 : m != 1%N.
  apply/negP=> /eqP hm1.
  have horder := prim_expr_order hm.
  rewrite hm1 expr1 in horder.
  by move: homega1; rewrite horder eqxx.
have hm3 : m = 3%N :=
  elimT (prime_nt_dvdP (isT : prime 3) hm_ne1) hdiv.
by move: hm; rewrite hm3.
Qed.

(** The sum and product of Cardano's two raw radicands. *)
Lemma cardano_radicands_sum q s
    (two_neq0 : (2%:R : F) != 0) :
  cardano_first_radicand q s + cardano_second_radicand q s = - q.
Proof.
rewrite /cardano_first_radicand /cardano_second_radicand.
transitivity (2%:R * (- q / 2%:R)).
- finish_cubic_field_ring.
- exact: cubic_two_mul_div (- q) two_neq0.
Qed.

Lemma cardano_radicands_product p q s
    (hs : s ^+ 2 = cardano_delta p q) :
  cardano_first_radicand q s * cardano_second_radicand q s =
    - (p / 3%:R) ^+ 3.
Proof.
rewrite /cardano_first_radicand /cardano_second_radicand.
transitivity ((q / 2%:R) ^+ 2 - s ^+ 2).
- finish_cubic_field_ring.
- rewrite hs /cardano_delta.
  finish_cubic_field_ring.
Qed.

Lemma cardano_cube_sum q s u v
    (two_neq0 : (2%:R : F) != 0)
    (hu : u ^+ 3 = cardano_first_radicand q s)
    (hv : v ^+ 3 = cardano_second_radicand q s) :
  u ^+ 3 + v ^+ 3 = - q.
Proof.
rewrite hu hv.
exact: cardano_radicands_sum q s two_neq0.
Qed.

Lemma cardano_compatibility_scaled (p u v : F)
    (three_neq0 : (3%:R : F) != 0)
    (huv : u * v = - p / 3%:R) :
  3%:R * u * v = - p.
Proof.
rewrite -mulrA huv.
exact: cubic_three_mul_div (- p) three_neq0.
Qed.

(** Any three values with the expected elementary symmetric functions give
    the exact depressed-cubic factorization. *)
Lemma depressed_cubic_factorization_of_vieta p q r0 r1 r2 y
    (hsum : r0 + r1 + r2 = 0)
    (hpairs : r0 * r1 + r0 * r2 + r1 * r2 = p)
    (hproduct : r0 * r1 * r2 = - q) :
  depressed_cubic_value p q y =
    (y - r0) * (y - r1) * (y - r2).
Proof.
transitivity
  (y ^+ 3 - (r0 + r1 + r2) * y ^+ 2 +
    (r0 * r1 + r0 * r2 + r1 * r2) * y - r0 * r1 * r2).
- rewrite /depressed_cubic_value hsum hpairs hproduct.
  finish_cubic_field_ring.
- finish_cubic_field_ring.
Qed.

(** Cardano's three compatible values have the required symmetric sums. *)
Lemma cardano_root_sum u v omega
    (homega : omega ^+ 2 + omega + 1 = 0) :
  cardano_root0 u v + cardano_root1 u v omega +
    cardano_root2 u v omega = 0.
Proof.
rewrite /cardano_root0 /cardano_root1 /cardano_root2.
transitivity ((u + v) * (omega ^+ 2 + omega + 1)).
- finish_cubic_field_ring.
- by rewrite homega mulr0.
Qed.

Lemma cardano_root_pair_sum p u v omega
    (three_neq0 : (3%:R : F) != 0)
    (homega : omega ^+ 2 + omega + 1 = 0)
    (huv : u * v = - p / 3%:R) :
  cardano_root0 u v * cardano_root1 u v omega +
    cardano_root0 u v * cardano_root2 u v omega +
    cardano_root1 u v omega * cardano_root2 u v omega = p.
Proof.
have hcompat := cardano_compatibility_scaled three_neq0 huv.
rewrite /cardano_root0 /cardano_root1 /cardano_root2.
transitivity
  (- (3%:R * u * v) +
    (u * v * omega ^+ 2 +
      (u ^+ 2 - u * v + v ^+ 2) * omega + 3%:R * u * v) *
      (omega ^+ 2 + omega + 1)).
- finish_cubic_field_ring.
- rewrite homega mulr0 addr0 hcompat.
  finish_cubic_field_ring.
Qed.

Lemma cardano_root_product q u v omega
    (homega : omega ^+ 2 + omega + 1 = 0)
    (hcubes : u ^+ 3 + v ^+ 3 = - q) :
  cardano_root0 u v * cardano_root1 u v omega *
    cardano_root2 u v omega = - q.
Proof.
rewrite /cardano_root0 /cardano_root1 /cardano_root2.
transitivity
  (u ^+ 3 + v ^+ 3 +
    ((v * u ^+ 2 + v ^+ 2 * u) * omega ^+ 2 +
      (u ^+ 3 + v ^+ 3) * omega - (u ^+ 3 + v ^+ 3)) *
      (omega ^+ 2 + omega + 1)).
- finish_cubic_field_ring.
- by rewrite homega mulr0 addr0 hcubes.
Qed.

(** Complete depressed-cubic Cardano factorization from explicitly supplied
    compatible radicals.  The square equation is retained in the interface
    because it certifies the printed radical construction; the factorization
    itself uses the two cube equations and their branch compatibility. *)
Theorem cardano_depressed_factorization p q s u v omega y
    (two_neq0 : (2%:R : F) != 0)
    (three_neq0 : (3%:R : F) != 0)
    (homega : omega ^+ 2 + omega + 1 = 0)
    (_hs : s ^+ 2 = cardano_delta p q)
    (hu : u ^+ 3 = cardano_first_radicand q s)
    (hv : v ^+ 3 = cardano_second_radicand q s)
    (huv : u * v = - p / 3%:R) :
  depressed_cubic_value p q y =
    (y - cardano_root0 u v) *
      (y - cardano_root1 u v omega) *
      (y - cardano_root2 u v omega).
Proof.
have hcubes := cardano_cube_sum two_neq0 hu hv.
apply: depressed_cubic_factorization_of_vieta.
- exact: cardano_root_sum homega.
- exact: cardano_root_pair_sum three_neq0 homega huv.
- exact: cardano_root_product homega hcubes.
Qed.

Theorem cardano_depressed_roots p q s u v omega
    (two_neq0 : (2%:R : F) != 0)
    (three_neq0 : (3%:R : F) != 0)
    (homega : omega ^+ 2 + omega + 1 = 0)
    (hs : s ^+ 2 = cardano_delta p q)
    (hu : u ^+ 3 = cardano_first_radicand q s)
    (hv : v ^+ 3 = cardano_second_radicand q s)
    (huv : u * v = - p / 3%:R) :
  depressed_cubic_value p q (cardano_root0 u v) = 0 /\
  depressed_cubic_value p q (cardano_root1 u v omega) = 0 /\
  depressed_cubic_value p q (cardano_root2 u v omega) = 0.
Proof.
repeat split;
  rewrite (cardano_depressed_factorization
    (p := p) (q := q) (s := s) (u := u) (v := v) (omega := omega)
    _
    two_neq0 three_neq0 homega hs hu hv huv);
  finish_cubic_field_ring.
Qed.

(** Every field-valued root occurs among the three Cardano values. *)
Theorem cardano_depressed_exhaustive p q s u v omega x
    (two_neq0 : (2%:R : F) != 0)
    (three_neq0 : (3%:R : F) != 0)
    (homega : omega ^+ 2 + omega + 1 = 0)
    (hs : s ^+ 2 = cardano_delta p q)
    (hu : u ^+ 3 = cardano_first_radicand q s)
    (hv : v ^+ 3 = cardano_second_radicand q s)
    (huv : u * v = - p / 3%:R)
    (hx : depressed_cubic_value p q x = 0) :
  x = cardano_root0 u v \/
  x = cardano_root1 u v omega \/
  x = cardano_root2 u v omega.
Proof.
rewrite (cardano_depressed_factorization
  (p := p) (q := q) (s := s) (u := u) (v := v) (omega := omega)
  x
  two_neq0 three_neq0 homega hs hu hv huv) in hx.
have hproductb :
    (x - cardano_root0 u v) *
      (x - cardano_root1 u v omega) *
      (x - cardano_root2 u v omega) == 0.
  apply/eqP.
  exact: hx.
move: hproductb.
rewrite !mulf_eq0 !subr_eq0.
move/orP=> [/orP [/eqP h0 | /eqP h1] | /eqP h2].
- by left.
- by right; left.
- by right; right.
Qed.

Theorem cardano_depressed_eq_zero_iff p q s u v omega x
    (two_neq0 : (2%:R : F) != 0)
    (three_neq0 : (3%:R : F) != 0)
    (homega : omega ^+ 2 + omega + 1 = 0)
    (hs : s ^+ 2 = cardano_delta p q)
    (hu : u ^+ 3 = cardano_first_radicand q s)
    (hv : v ^+ 3 = cardano_second_radicand q s)
    (huv : u * v = - p / 3%:R) :
  depressed_cubic_value p q x = 0 <->
    x = cardano_root0 u v \/
    x = cardano_root1 u v omega \/
    x = cardano_root2 u v omega.
Proof.
split.
- exact: cardano_depressed_exhaustive
    two_neq0 three_neq0 homega hs hu hv huv.
- move=> [-> | [-> | ->]].
  + exact: (cardano_depressed_roots
      two_neq0 three_neq0 homega hs hu hv huv).1.
  + exact: (cardano_depressed_roots
      two_neq0 three_neq0 homega hs hu hv huv).2.1.
  + exact: (cardano_depressed_roots
      two_neq0 three_neq0 homega hs hu hv huv).2.2.
Qed.

Lemma depressed_cubic_polynomial_horner p q x :
  (depressed_cubic_polynomial p q).[x] = depressed_cubic_value p q x.
Proof.
by rewrite /depressed_cubic_polynomial /depressed_cubic_value
  !hornerD !hornerZ !hornerXn !hornerX !hornerC.
Qed.

Theorem cardano_depressed_polynomial_root_iff p q s u v omega x
    (two_neq0 : (2%:R : F) != 0)
    (three_neq0 : (3%:R : F) != 0)
    (homega : omega ^+ 2 + omega + 1 = 0)
    (hs : s ^+ 2 = cardano_delta p q)
    (hu : u ^+ 3 = cardano_first_radicand q s)
    (hv : v ^+ 3 = cardano_second_radicand q s)
    (huv : u * v = - p / 3%:R) :
  root (depressed_cubic_polynomial p q) x <->
    x = cardano_root0 u v \/
    x = cardano_root1 u v omega \/
    x = cardano_root2 u v omega.
Proof.
rewrite rootE depressed_cubic_polynomial_horner.
split.
- move/eqP=> hzero.
  exact: cardano_depressed_exhaustive
    two_neq0 three_neq0 homega hs hu hv huv hzero.
- move=> hroot; apply/eqP.
  exact: (proj2 (cardano_depressed_eq_zero_iff
    (p := p) (q := q) (s := s) (u := u) (v := v) (omega := omega)
    x two_neq0 three_neq0 homega hs hu hv huv) hroot).
Qed.

(**************************************************************************)
(** The exact printed [p = 0] sign branch. *)

Definition cardano_selected_sqrt (q s : F) : F :=
  if cardano_first_radicand q s == 0 then - s else s.

Definition cardano_derived_second (p s1 : F) : F :=
  - p / (3%:R * s1).

Lemma cardano_first_radicand_neg q s :
  cardano_first_radicand q (- s) = cardano_second_radicand q s.
Proof.
rewrite /cardano_first_radicand /cardano_second_radicand.
finish_cubic_field_ring.
Qed.

Lemma cardano_second_radicand_neg q s :
  cardano_second_radicand q (- s) = cardano_first_radicand q s.
Proof.
rewrite /cardano_first_radicand /cardano_second_radicand.
finish_cubic_field_ring.
Qed.

Lemma cardano_selected_sqrt_is_sign q s :
  cardano_selected_sqrt q s = s \/ cardano_selected_sqrt q s = - s.
Proof.
rewrite /cardano_selected_sqrt.
case: (cardano_first_radicand q s == 0).
- by right.
- by left.
Qed.

Lemma cardano_selected_sqrt_square q s :
  cardano_selected_sqrt q s ^+ 2 = s ^+ 2.
Proof.
rewrite /cardano_selected_sqrt.
case: (cardano_first_radicand q s == 0)=> //.
by rewrite sqrrN.
Qed.

Lemma cardano_selected_first_radicand_neq0 q s
    (two_neq0 : (2%:R : F) != 0) (q_neq0 : q != 0) :
  cardano_first_radicand q (cardano_selected_sqrt q s) != 0.
Proof.
rewrite /cardano_selected_sqrt.
case hfirst : (cardano_first_radicand q s == 0).
- rewrite cardano_first_radicand_neg.
  apply/negP=> hsecondb.
  have hfirstb : cardano_first_radicand q s == 0 by rewrite hfirst.
  have hfirst0 : cardano_first_radicand q s = 0 := eqP hfirstb.
  have hsecond0 : cardano_second_radicand q s = 0 := eqP hsecondb.
  have hsum := cardano_radicands_sum q s two_neq0.
  rewrite hfirst0 hsecond0 add0r in hsum.
  have hqneg : - q = 0 := esym hsum.
  have hq0 : q = 0.
    apply: oppr_inj.
    by rewrite oppr0 hqneg.
  move: q_neq0.
  by rewrite hq0 eqxx.
- by rewrite hfirst.
Qed.

(** Irreducibility rules out [q = 0], since with [p = 0] the polynomial is
    [X^3] and has the proper divisor [X]. *)
Lemma irreducible_depressed_p_zero_q_neq0 p q
    (hirr : irreducible_poly (depressed_cubic_polynomial p q))
    (hp : p = 0) :
  q != 0.
Proof.
apply/negP=> /eqP hq.
have hirrX3 : irreducible_poly ('X^3 : {poly F}).
  move: hirr.
  by rewrite /depressed_cubic_polynomial hp hq scale0r rmorph0 !addr0.
have hXsize : size ('X : {poly F}) != 1%N.
  by rewrite size_polyX.
have hXdiv : ('X : {poly F}) %| 'X^3.
  apply: dvdp_exp; first by [].
  exact: dvdpp.
have hXeqp : ('X : {poly F}) %= 'X^3 :=
  hirrX3.2 'X hXsize hXdiv.
have hsize := eqp_size hXeqp.
move: hsize.
by rewrite size_polyX size_polyXn.
Qed.

Lemma cardano_selected_second_radicand_zero p q s
    (two_neq0 : (2%:R : F) != 0)
    (q_neq0 : q != 0) (hp : p = 0)
    (hs : s ^+ 2 = cardano_delta p q) :
  cardano_second_radicand q (cardano_selected_sqrt q s) = 0.
Proof.
have hs_selected :
    cardano_selected_sqrt q s ^+ 2 = cardano_delta p q.
  rewrite cardano_selected_sqrt_square.
  exact: hs.
have hproduct := cardano_radicands_product
  (p := p) (q := q) (s := cardano_selected_sqrt q s) hs_selected.
have hproduct0 :
    cardano_first_radicand q (cardano_selected_sqrt q s) *
      cardano_second_radicand q (cardano_selected_sqrt q s) = 0.
  move: hproduct.
  by rewrite hp mul0r cubic_expr3 !mul0r oppr0.
have hfirst := cardano_selected_first_radicand_neq0
  (q := q) s two_neq0 q_neq0.
have hproductb :
    cardano_first_radicand q (cardano_selected_sqrt q s) *
      cardano_second_radicand q (cardano_selected_sqrt q s) == 0.
  apply/eqP.
  exact: hproduct0.
move: hproductb.
rewrite mulf_eq0 (negPf hfirst) /=.
by move/eqP.
Qed.

Lemma cardano_selected_first_cube_root_neq0 q s s1
    (two_neq0 : (2%:R : F) != 0) (q_neq0 : q != 0)
    (hs1 : s1 ^+ 3 =
      cardano_first_radicand q (cardano_selected_sqrt q s)) :
  s1 != 0.
Proof.
have hfirst := cardano_selected_first_radicand_neq0
  (q := q) s two_neq0 q_neq0.
apply/negP=> /eqP hs10.
have hrad0 :
    cardano_first_radicand q (cardano_selected_sqrt q s) = 0.
  rewrite -hs1 hs10.
  by rewrite cubic_expr3 !mul0r.
move: hfirst.
by rewrite hrad0 eqxx.
Qed.

Lemma cardano_p_zero_denominator_neq0 q s s1
    (two_neq0 : (2%:R : F) != 0)
    (three_neq0 : (3%:R : F) != 0) (q_neq0 : q != 0)
    (hs1 : s1 ^+ 3 =
      cardano_first_radicand q (cardano_selected_sqrt q s)) :
  3%:R * s1 != 0.
Proof.
exact: mulf_neq0 three_neq0
  (cardano_selected_first_cube_root_neq0 two_neq0 q_neq0 hs1).
Qed.

Lemma cardano_derived_second_p_zero p s1 (hp : p = 0) :
  cardano_derived_second p s1 = 0.
Proof. by rewrite /cardano_derived_second hp oppr0 mul0r. Qed.

Record CardanoPZeroBranchCertificate
    (p q s s1 : F) : Prop := {
  pzero_selected_is_sign :
    cardano_selected_sqrt q s = s \/ cardano_selected_sqrt q s = - s;
  pzero_selected_square :
    cardano_selected_sqrt q s ^+ 2 = cardano_delta p q;
  pzero_q_neq0 : q != 0;
  pzero_first_radicand_neq0 :
    cardano_first_radicand q (cardano_selected_sqrt q s) != 0;
  pzero_second_radicand_zero :
    cardano_second_radicand q (cardano_selected_sqrt q s) = 0;
  pzero_s1_cube :
    s1 ^+ 3 = cardano_first_radicand q (cardano_selected_sqrt q s);
  pzero_s1_neq0 : s1 != 0;
  pzero_s1_denominator_neq0 : 3%:R * s1 != 0;
  pzero_derived_second_zero : cardano_derived_second p s1 = 0;
  pzero_derived_second_cube :
    cardano_derived_second p s1 ^+ 3 =
      cardano_second_radicand q (cardano_selected_sqrt q s);
  pzero_derived_pair_compatible :
    s1 * cardano_derived_second p s1 = - p / 3%:R
}.

(** Complete formal version of the paper's [p = 0] sign choice. *)
Theorem cardano_irreducible_p_zero_branch p q s s1
    (two_neq0 : (2%:R : F) != 0)
    (three_neq0 : (3%:R : F) != 0)
    (hirr : irreducible_poly (depressed_cubic_polynomial p q))
    (hp : p = 0)
    (hs : s ^+ 2 = cardano_delta p q)
    (hs1 : s1 ^+ 3 =
      cardano_first_radicand q (cardano_selected_sqrt q s)) :
  CardanoPZeroBranchCertificate p q s s1.
Proof.
have hq := irreducible_depressed_p_zero_q_neq0 hirr hp.
have hfirst := cardano_selected_first_radicand_neq0
  (q := q) s two_neq0 hq.
have hsecond := cardano_selected_second_radicand_zero
  (p := p) (q := q) (s := s) two_neq0 hq hp hs.
have hs1_neq0 := cardano_selected_first_cube_root_neq0
  (q := q) (s := s) (s1 := s1) two_neq0 hq hs1.
have hdenom := cardano_p_zero_denominator_neq0
  (q := q) (s := s) (s1 := s1)
  two_neq0 three_neq0 hq hs1.
have hs2zero := cardano_derived_second_p_zero
  (p := p) s1 hp.
constructor.
- exact: cardano_selected_sqrt_is_sign.
- rewrite cardano_selected_sqrt_square.
  exact: hs.
- exact: hq.
- exact: hfirst.
- exact: hsecond.
- exact: hs1.
- exact: hs1_neq0.
- exact: hdenom.
- exact: hs2zero.
- rewrite hs2zero hsecond.
  by rewrite cubic_expr3 !mul0r.
- rewrite hs2zero hp.
  by rewrite mulr0 oppr0 mul0r.
Qed.

Print Assumptions cardano_depressed_factorization.
Print Assumptions cardano_depressed_roots.
Print Assumptions cardano_depressed_eq_zero_iff.
Print Assumptions cardano_depressed_polynomial_root_iff.
Print Assumptions primitive_cube_root_quadratic.
Print Assumptions primitive_cube_root_of_quadratic.
Print Assumptions irreducible_depressed_p_zero_q_neq0.
Print Assumptions cardano_irreducible_p_zero_branch.

End CubicField.

End PolynomialFormulasCubicField.
