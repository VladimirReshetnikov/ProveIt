From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import char0 cyclotomic_ext abel.
From PolynomialFormulas Require Import
  QuinticChapman LazardOptimality.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A concrete counterexample to Lazard's Theorem 4 as it is literally
    stated in the paper.

    Let [z] be a primitive eleventh root of unity and put [x = z + z^-1].
    The irreducible polynomial

      [X^5 + X^4 - 4 X^3 - 3 X^2 + 3 X + 1]

    has all its roots in the eleventh cyclotomic field.  In a common
    fifty-fifth cyclotomic ambient field that subfield is a one-step radical
    extension in the sense of Lazard's Definition 1, but it does not contain
    the displayed primitive fifth root.  Hence no field which contains that
    fifth root can be least among the radical extensions containing all roots.

    Everything in this file is constructed from MathComp--Abel's concrete
    [numfield], [C_prim_root_exists], and cyclotomic automorphism APIs.  In
    particular, no root, splitting, Vieta, degree, or automorphism certificate
    is taken as a hypothesis. *)
Module PolynomialFormulasLazardOptimalityCyclicQuinticCounterexample.

Import GRing.Theory.
Import PolynomialFormulasLazardOptimality.
Module QC := PolynomialFormulasQuinticChapman.

Local Open Scope group_scope.
Local Open Scope ring_scope.

(* -------------------------------------------------------------------- *)
(** * A reusable Laurent certificate *)

Section LaurentCertificate.

Variable F : fieldType.

Add Ring lazard_cyclic_counterexample_ring : (@QC.mathcomp_ring_theory F).
Opaque QC.ring_zero QC.ring_one QC.ring_add QC.ring_mul QC.ring_sub
  QC.ring_opp QC.ring_eq.

Lemma counterexample_two_natrE : (2%:R : F) = 1 + 1.
Proof. exact: (@natrD F 1 1). Qed.

Lemma counterexample_three_natrE : (3%:R : F) = 1 + 1 + 1.
Proof.
rewrite -counterexample_two_natrE.
exact: (@natrD F 2 1).
Qed.

Lemma counterexample_four_natrE : (4%:R : F) = 1 + 1 + 1 + 1.
Proof.
rewrite -counterexample_three_natrE.
exact: (@natrD F 3 1).
Qed.

Lemma counterexample_five_natrE : (5%:R : F) = 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -counterexample_four_natrE.
exact: (@natrD F 4 1).
Qed.

Lemma counterexample_six_natrE : (6%:R : F) = 1 + 1 + 1 + 1 + 1 + 1.
Proof.
rewrite -counterexample_five_natrE.
exact: (@natrD F 5 1).
Qed.

Lemma counterexample_ten_natrE :
    (10%:R : F) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1.
Proof.
have h7 : (7%:R : F) = 1 + 1 + 1 + 1 + 1 + 1 + 1.
  rewrite -counterexample_six_natrE.
  exact: (@natrD F 6 1).
have h8 : (8%:R : F) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1.
  rewrite -h7.
  exact: (@natrD F 7 1).
have h9 : (9%:R : F) = 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1 + 1.
  rewrite -h8.
  exact: (@natrD F 8 1).
rewrite -h9.
exact: (@natrD F 9 1).
Qed.

Ltac finish_cyclic_counterexample_ring :=
  repeat first
    [ rewrite counterexample_two_natrE
    | rewrite counterexample_three_natrE
    | rewrite counterexample_four_natrE
    | rewrite counterexample_five_natrE
    | rewrite counterexample_six_natrE
    | rewrite counterexample_ten_natrE
    | rewrite exprSr | rewrite expr0
    | rewrite QC.ring_addE | rewrite QC.ring_mulE
    | rewrite QC.ring_subE | rewrite QC.ring_oppE
    | rewrite QC.ring_zeroE | rewrite QC.ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (QC.ring_eq lhs rhs)
  end;
  ring.

(** Evaluation form of the cyclic quintic. *)
Definition cyclic_quintic_value (x : F) : F :=
  x ^+ 5 + x ^+ 4 - 4%:R * x ^+ 3 - 3%:R * x ^+ 2 +
    3%:R * x + 1.

(** Nested form produced by coefficientwise polynomial evaluation. *)
Lemma cyclic_quintic_value_nested (x : F) :
  x ^+ 5 + (x ^+ 4 +
    ((intr : int -> F) (-4 : int) * x ^+ 3 +
      ((intr : int -> F) (-3 : int) * x ^+ 2 +
        ((intr : int -> F) (3 : int) * x +
          (intr : int -> F) (1 : int))))) =
    cyclic_quintic_value x.
Proof.
rewrite /cyclic_quintic_value.
have intr_neg_four :
    (intr : int -> F) (-4 : int) = - (4%:R : F) by reflexivity.
have intr_neg_three :
    (intr : int -> F) (-3 : int) = - (3%:R : F) by reflexivity.
have intr_three :
    (intr : int -> F) (3 : int) = (3%:R : F) by reflexivity.
have intr_one :
    (intr : int -> F) (1 : int) = (1 : F) by reflexivity.
rewrite intr_neg_four intr_neg_three intr_three intr_one.
finish_cyclic_counterexample_ring.
Qed.

(** Quotient for the two-variable polynomial identity below.  It was chosen
    so that substitution [y = z^-1] kills the right hand side by [z*y=1]. *)
Definition cyclic_laurent_quotient (z y : F) : F :=
  (1 + z + z ^+ 2 + z ^+ 3 + z ^+ 4 -
      2%:R * z ^+ 6 + 4%:R * z ^+ 7 + 5%:R * z ^+ 8) +
  (z + z ^+ 2 + z ^+ 3 + z ^+ 4 - 2%:R * z ^+ 5 +
      6%:R * z ^+ 6 + 10%:R * z ^+ 7) * y +
  (z ^+ 2 + z ^+ 3 + z ^+ 4 + 4%:R * z ^+ 5 +
      10%:R * z ^+ 6) * y ^+ 2 +
  (z ^+ 3 + z ^+ 4 + 5%:R * z ^+ 5) * y ^+ 3 +
  z ^+ 4 * y ^+ 4.

(** Closed Laurent certificate.  This is an ordinary polynomial identity in
    the two independent variables [z] and [y]. *)
Lemma cyclic_laurent_certificate (z y : F) :
  z ^+ 5 * cyclic_quintic_value (z + y) -
      \sum_(i < 11) z ^+ i =
    ((z * y - 1) * cyclic_laurent_quotient z y)%R.
Proof.
rewrite /cyclic_quintic_value /cyclic_laurent_quotient.
rewrite !big_ord_recr big_ord0 /=.
finish_cyclic_counterexample_ring.
Qed.

(** The familiar Laurent identity follows without any root-of-unity
    assumption: nonzeroness is exactly what permits [y = z^-1]. *)
Lemma scaled_cyclic_quintic_identity (z : F) :
  z != 0 ->
  z ^+ 5 * cyclic_quintic_value (z + z^-1) =
    \sum_(i < 11) z ^+ i.
Proof.
move=> z_neq0; apply/eqP; rewrite -subr_eq0; apply/eqP.
have h := cyclic_laurent_certificate z z^-1.
by move: h; rewrite mulfV // subrr mul0r.
Qed.

(** A primitive eleventh root has zero geometric sum. *)
Lemma primitive_eleven_geometric_sum_zero (z : F) :
  11.-primitive_root z -> \sum_(i < 11) z ^+ i = 0.
Proof.
move=> z_primitive.
have z_neq1 : z != 1.
  apply/negP=> /eqP z_eq1.
  have h := prim_order_dvd z_primitive 1.
  by move: h; rewrite z_eq1 expr1 eqxx.
have zB1_neq0 : z - 1 != 0.
  apply/negP=> /eqP zB1_eq0.
  have z_eq1_from_sub : z = 1 := subr0_eq zB1_eq0.
  by move: z_neq1; rewrite z_eq1_from_sub eqxx.
have hgeom :
    (z - 1) * \sum_(i < 11) z ^+ i = z ^+ 11 - 1.
  rewrite !big_ord_recr big_ord0 /=.
  finish_cyclic_counterexample_ring.
apply: (mulfI zB1_neq0).
by rewrite mulr0 hgeom (prim_expr_order z_primitive) subrr.
Qed.

(** The real-cyclotomic generator is a root of the explicit cyclic quintic. *)
Lemma primitive_eleven_cyclic_quintic_root (z : F) :
  11.-primitive_root z -> cyclic_quintic_value (z + z^-1) = 0.
Proof.
move=> z_primitive.
have z_neq0 : z != 0.
  by rewrite (prim_root_eq0 z_primitive).
have hscaled := scaled_cyclic_quintic_identity z_neq0.
rewrite (primitive_eleven_geometric_sum_zero z_primitive) in hscaled.
have hscaledb :
    z ^+ 5 * cyclic_quintic_value (z + z^-1) == 0 by exact/eqP.
move: hscaledb.
by rewrite mulf_eq0 (negPf (expf_neq0 5 z_neq0)) orFb=> /eqP.
Qed.

End LaurentCertificate.

(* -------------------------------------------------------------------- *)
(** * The explicit irreducible polynomial *)

Section DegreeFivePolynomialShape.

Variable R : comNzRingType.

(** Small structural size lemmas keep the explicit degree-five
    certificates independent of reduction through the polynomial
    implementation. *)
Lemma size_polyD_lt_six (p q : {poly R}) :
  (size p < 6)%N -> (size q < 6)%N -> (size (p + q)%R < 6)%N.
Proof.
move=> hp hq.
have hle :
    (size (p + q)%R <= maxn (size p) (size q))%N := size_polyD p q.
have hmax : (maxn (size p) (size q) < 6)%N.
  by rewrite gtn_max hp hq.
exact: leq_ltn_trans hle hmax.
Qed.

Lemma size_Xn_lt_six (n : nat) :
  (n < 5)%N -> (size ('X^n : {poly R}) < 6)%N.
Proof. by move=> hn; rewrite size_polyXn. Qed.

Lemma size_scale_Xn_lt_six (c : R) (n : nat) :
  (n < 5)%N -> (size (c *: ('X^n : {poly R})) < 6)%N.
Proof.
move=> hn.
have hle :
    (size (c *: ('X^n : {poly R})) <= size ('X^n : {poly R}))%N :=
  size_scale_leq c 'X^n.
exact: leq_ltn_trans hle (size_Xn_lt_six hn).
Qed.

Lemma size_scale_X_lt_six (c : R) :
  (size (c *: ('X : {poly R})) < 6)%N.
Proof.
have h := size_scale_Xn_lt_six c (isT : (1 < 5)%N).
by rewrite expr1 in h.
Qed.

Lemma size_polyC_lt_six (c : R) : (size c%:P < 6)%N.
Proof.
exact: leq_ltn_trans (size_polyC_leq1 c) (isT : (1 < 6)%N).
Qed.

Lemma size_X5_add_lower (p : {poly R}) :
  (size p < 6)%N -> size ('X^5 + p) = 6%N.
Proof. by move=> hp; rewrite size_polyDl ?size_polyXn. Qed.

Lemma monic_X5_add_lower (p : {poly R}) :
  (size p < 6)%N -> 'X^5 + p \is monic.
Proof.
move=> hp; apply/eqP.
by rewrite lead_coefDl ?size_polyXn ?lead_coefXn.
Qed.

End DegreeFivePolynomialShape.

Definition cyclic_quintic_lower_Z : {poly int} :=
  'X^4 + ((-4 : int) *: 'X^3 +
    ((-3 : int) *: 'X^2 + ((3 : int) *: 'X + 1%:P))).

Definition cyclic_quintic_Z : {poly int} :=
  'X^5 + cyclic_quintic_lower_Z.

Definition shifted_cyclic_quintic_lower_Z : {poly int} :=
  (11 : int) *: 'X^4 + ((44 : int) *: 'X^3 +
    ((77 : int) *: 'X^2 + ((55 : int) *: 'X + 11%:P))).

Definition shifted_cyclic_quintic_Z : {poly int} :=
  'X^5 + shifted_cyclic_quintic_lower_Z.

Definition cyclic_quintic_Q : {poly rat} :=
  map_poly (intr : int -> rat) cyclic_quintic_Z.

Definition shifted_cyclic_quintic_Q : {poly rat} :=
  map_poly (intr : int -> rat) shifted_cyclic_quintic_Z.

Lemma cyclic_quintic_lower_Z_size_lt :
  (size cyclic_quintic_lower_Z < 6)%N.
Proof.
rewrite /cyclic_quintic_lower_Z.
apply: size_polyD_lt_six; first by apply: size_Xn_lt_six.
apply: size_polyD_lt_six; first by apply: size_scale_Xn_lt_six.
apply: size_polyD_lt_six; first by apply: size_scale_Xn_lt_six.
apply: size_polyD_lt_six; first exact: size_scale_X_lt_six.
exact: size_polyC_lt_six.
Qed.

Lemma shifted_cyclic_quintic_lower_Z_size_lt :
  (size shifted_cyclic_quintic_lower_Z < 6)%N.
Proof.
rewrite /shifted_cyclic_quintic_lower_Z.
apply: size_polyD_lt_six; first by apply: size_scale_Xn_lt_six.
apply: size_polyD_lt_six; first by apply: size_scale_Xn_lt_six.
apply: size_polyD_lt_six; first by apply: size_scale_Xn_lt_six.
apply: size_polyD_lt_six; first exact: size_scale_X_lt_six.
exact: size_polyC_lt_six.
Qed.

Lemma cyclic_quintic_Z_size : size cyclic_quintic_Z = 6%N.
Proof.
rewrite /cyclic_quintic_Z.
exact: size_X5_add_lower cyclic_quintic_lower_Z_size_lt.
Qed.

Lemma cyclic_quintic_Z_monic : cyclic_quintic_Z \is monic.
Proof.
rewrite /cyclic_quintic_Z.
exact: monic_X5_add_lower cyclic_quintic_lower_Z_size_lt.
Qed.

Lemma cyclic_quintic_Q_size : size cyclic_quintic_Q = 6%N.
Proof.
rewrite /cyclic_quintic_Q size_rat_int_poly.
exact: cyclic_quintic_Z_size.
Qed.

Lemma cyclic_quintic_Q_monic : cyclic_quintic_Q \is monic.
Proof.
apply: monic_map.
exact: cyclic_quintic_Z_monic.
Qed.

Lemma shifted_cyclic_quintic_Z_size :
  size shifted_cyclic_quintic_Z = 6%N.
Proof.
rewrite /shifted_cyclic_quintic_Z.
exact: size_X5_add_lower shifted_cyclic_quintic_lower_Z_size_lt.
Qed.

Lemma shifted_cyclic_quintic_Z_monic :
  shifted_cyclic_quintic_Z \is monic.
Proof.
rewrite /shifted_cyclic_quintic_Z.
exact: monic_X5_add_lower shifted_cyclic_quintic_lower_Z_size_lt.
Qed.

Lemma shifted_cyclic_quintic_Z_coef0 :
  shifted_cyclic_quintic_Z`_0 = 11.
Proof.
rewrite /shifted_cyclic_quintic_Z /shifted_cyclic_quintic_lower_Z
  !coefD !coefZ !coefXn !coefC.
by rewrite coefX /= !mulr0 !add0r.
Qed.

(** The translate by [X |-> X+2] is Eisenstein at 11. *)
Lemma shifted_cyclic_quintic_Z_irreducible :
  irreducible_poly shifted_cyclic_quintic_Z.
Proof.
apply: (eisenstein_crit (p := 11)).
- by vm_compute.
- by rewrite shifted_cyclic_quintic_Z_size.
- rewrite (eqP shifted_cyclic_quintic_Z_monic).
  by vm_compute.
- rewrite shifted_cyclic_quintic_Z_coef0.
  by vm_compute.
- move=> i hi.
  rewrite /shifted_cyclic_quintic_Z /shifted_cyclic_quintic_lower_Z
    !coefD !coefZ !coefXn !coefX !coefC.
  have hi5 : (i < 5)%N.
    by move: hi; rewrite shifted_cyclic_quintic_Z_size.
  clear hi.
  move: i hi5 => [|[|[|[|[|i]]]]] hi5.
  - by vm_compute.
  - by vm_compute.
  - by vm_compute.
  - by vm_compute.
  - by vm_compute.
  - by move: hi5; rewrite !ltnS.
Qed.

Lemma shifted_cyclic_quintic_Q_irreducible :
  irreducible_poly shifted_cyclic_quintic_Q.
Proof.
rewrite /shifted_cyclic_quintic_Q irreducible_rat_int.
exact: shifted_cyclic_quintic_Z_irreducible.
Qed.

(** Compute the translation over the integers, before embedding coefficients
    into the rationals.  This avoids normalizing the implementation of
    rational arithmetic inside an entire mapped polynomial. *)
Local Definition cyclic_o0 : 'I_6 := Ordinal (isT : (0 < 6)%N).
Local Definition cyclic_o1 : 'I_6 := Ordinal (isT : (1 < 6)%N).
Local Definition cyclic_o2 : 'I_6 := Ordinal (isT : (2 < 6)%N).
Local Definition cyclic_o3 : 'I_6 := Ordinal (isT : (3 < 6)%N).
Local Definition cyclic_o4 : 'I_6 := Ordinal (isT : (4 < 6)%N).
Local Definition cyclic_o5 : 'I_6 := Ordinal (isT : (5 < 6)%N).

Lemma cyclic_sum_ord6 (R : comNzRingType) (f : 'I_6 -> R) :
  \sum_(i : 'I_6) f i =
    f cyclic_o0 + (f cyclic_o1 + (f cyclic_o2 +
      (f cyclic_o3 + (f cyclic_o4 + f cyclic_o5)))).
Proof.
rewrite !big_ord_recl !big_ord0.
have h0 : (@ord0 5) = cyclic_o0 by apply: val_inj.
have h1 : lift (@ord0 5) (@ord0 4) = cyclic_o1 by apply: val_inj.
have h2 : lift (@ord0 5) (lift (@ord0 4) (@ord0 3)) = cyclic_o2
  by apply: val_inj.
have h3 : lift (@ord0 5)
    (lift (@ord0 4) (lift (@ord0 3) (@ord0 2))) = cyclic_o3
  by apply: val_inj.
have h4 : lift (@ord0 5)
    (lift (@ord0 4) (lift (@ord0 3)
      (lift (@ord0 2) (@ord0 1)))) = cyclic_o4 by apply: val_inj.
have h5 : lift (@ord0 5)
    (lift (@ord0 4) (lift (@ord0 3)
      (lift (@ord0 2) (lift (@ord0 1) (@ord0 0))))) = cyclic_o5
  by apply: val_inj.
by rewrite h5 h4 h3 h2 h1 h0 addr0.
Qed.

Lemma cyclic_coef_XaddC_exp (c : int) n i :
  (('X + c%:P) ^+ n)`_i = (c ^+ (n - i)) *+ 'C(n, i).
Proof.
rewrite addrC exprDn coef_sum.
under eq_bigr do rewrite coefMn -polyC_exp coefCM coefXn.
have [hi | hi] := ltnP i n.+1.
- pose ii : 'I_n.+1 := Ordinal hi.
  rewrite (bigD1 ii) //=.
  rewrite /ii /= eqxx mulr1.
  rewrite big1 ?addr0 // => j hj.
  have hij : i != nat_of_ord j.
    apply/negP=> /eqP hij.
    have hjeq : j = ii.
      apply: val_inj.
      by rewrite /ii /= -hij.
    by move: hj; rewrite hjeq eqxx.
  by rewrite (negPf hij) mulr0 mul0rn.
- rewrite big1.
  - by rewrite bin_small ?mulr0n.
  - move=> j _.
    have hjle : (nat_of_ord j <= n)%N.
      by move: (valP j); rewrite ltnS.
    have hji : (nat_of_ord j < i)%N := leq_ltn_trans hjle hi.
    have hij : i != nat_of_ord j.
      apply/negP=> /eqP hij.
      by move: hji; rewrite -hij ltnn.
    by rewrite (negPf hij) mulr0 mul0rn.
Qed.

Ltac finish_cyclic_translate_coefficient :=
  rewrite coef_comp_poly cyclic_quintic_Z_size;
  under eq_bigr do rewrite cyclic_coef_XaddC_exp;
  rewrite cyclic_sum_ord6;
  rewrite /cyclic_quintic_Z /cyclic_quintic_lower_Z
    /shifted_cyclic_quintic_Z /shifted_cyclic_quintic_lower_Z
    /cyclic_o0 /cyclic_o1 /cyclic_o2 /cyclic_o3 /cyclic_o4 /cyclic_o5
    !coefD !coefZ !coefXn !coefX !coefC /=;
  try rewrite !mulr0;
  try rewrite !mul0r;
  try rewrite !mulr1;
  try rewrite !mul1r;
  try rewrite !addr0;
  try rewrite !add0r;
  try rewrite !mulr0n;
  try rewrite !mul0rn;
  try rewrite !expr0;
  try rewrite !expr1;
  reflexivity.

Lemma cyclic_quintic_Z_translate_low_coefficient (i : 'I_6) :
  (cyclic_quintic_Z \Po ('X + (2 : int)%:P))`_i =
    shifted_cyclic_quintic_Z`_i.
Proof.
case: i => [[|[|[|[|[|[|i]]]]]] hi]; last by move: hi.
all: finish_cyclic_translate_coefficient.
Qed.

Lemma cyclic_quintic_Z_translate :
  cyclic_quintic_Z \Po ('X + (2 : int)%:P) = shifted_cyclic_quintic_Z.
Proof.
have hcomp_size :
    size (cyclic_quintic_Z \Po ('X + (2 : int)%:P)) = 6%N.
  have hsame_size :
      size (cyclic_quintic_Z \Po ('X + (2 : int)%:P)) =
        size cyclic_quintic_Z.
    apply: size_comp_poly2.
    exact: size_XaddC.
  exact: eq_trans hsame_size cyclic_quintic_Z_size.
apply/polyP=> i.
have [hi | hi] := ltnP i 6%N.
- exact: (cyclic_quintic_Z_translate_low_coefficient (Ordinal hi)).
- have hleft :
      (cyclic_quintic_Z \Po ('X + (2 : int)%:P))`_i = 0.
    apply: nth_default.
    by rewrite hcomp_size.
  have hright : shifted_cyclic_quintic_Z`_i = 0.
    apply: nth_default.
    by rewrite shifted_cyclic_quintic_Z_size.
  by rewrite hleft hright.
Qed.

Lemma cyclic_quintic_Q_translate :
  cyclic_quintic_Q \Po ('X + (2 : rat)%:P) = shifted_cyclic_quintic_Q.
Proof.
rewrite /cyclic_quintic_Q /shifted_cyclic_quintic_Q.
  have hinner :
    map_poly (intr : int -> rat) ('X + (2 : int)%:P) =
      'X + (2 : rat)%:P.
  have h2 : (intr : int -> rat) (2 : int) = (2 : rat) by vm_compute.
  rewrite rmorphD.
  change (map_poly (intr : int -> rat) 'X +
    map_poly (intr : int -> rat) (2 : int)%:P =
      'X + (2 : rat)%:P).
  rewrite map_polyX map_polyC.
  exact (congr1 (fun x : rat => 'X + x%:P) h2).
rewrite -hinner -map_comp_poly cyclic_quintic_Z_translate.
reflexivity.
Qed.

(** Translation by a constant preserves irreducibility in the direction
    needed here.  This small lemma is independent of the explicit quintic. *)
Lemma irreducible_of_comp_XaddC
    (K : fieldType) (p : {poly K}) (c : K) :
  irreducible_poly (p \Po ('X + c%:P)) -> irreducible_poly p.
Proof.
move=> [pcomp_gt1 pcomp_irred]; split.
- move: pcomp_gt1.
  by rewrite (size_comp_poly2 p) ?size_XaddC.
- move=> q q_size1 q_dvd_p.
  have qcomp_size1 : size (q \Po ('X + c%:P)) != 1%N.
    by rewrite (size_comp_poly2 q) ?size_XaddC.
  have qcomp_dvd :
      q \Po ('X + c%:P) %| p \Po ('X + c%:P) :=
    dvdp_comp_poly _ q_dvd_p.
  have qcomp_eq := pcomp_irred _ qcomp_size1 qcomp_dvd.
  apply/andP; case/andP: qcomp_eq=> qcp pcq; split.
  + move/(dvdp_comp_poly ('X - c%:P)): qcp.
    by rewrite !comp_polyXaddC_K.
  + move/(dvdp_comp_poly ('X - c%:P)): pcq.
    by rewrite !comp_polyXaddC_K.
Qed.

Lemma cyclic_quintic_Q_irreducible : irreducible_poly cyclic_quintic_Q.
Proof.
apply: (irreducible_of_comp_XaddC (c := (2 : rat))).
rewrite cyclic_quintic_Q_translate.
exact: shifted_cyclic_quintic_Q_irreducible.
Qed.

(* -------------------------------------------------------------------- *)
(** * A concrete common fifty-fifth cyclotomic ambient field *)

Definition cyclotomic_rat (n : nat) : {poly rat} :=
  map_poly (intr : int -> rat) 'Phi_n.

Definition cyclotomic55_Q : {poly rat} := cyclotomic_rat 55.

Lemma cyclotomic55_Q_monic : cyclotomic55_Q \is monic.
Proof.
rewrite /cyclotomic55_Q /cyclotomic_rat.
apply: monic_map.
exact: Cyclotomic_monic.
Qed.

Lemma cyclotomic55_Q_neq0 : cyclotomic55_Q != 0.
Proof. exact: monic_neq0 cyclotomic55_Q_monic. Qed.

Definition Ambient : splittingFieldType rat := numfield cyclotomic55_Q.

Definition ambient_inC : {rmorphism Ambient -> algC} :=
  numfield_inC cyclotomic55_Q.

Definition zeta55C : algC :=
  projT1 (C_prim_root_exists (n := 55) isT).

Lemma zeta55C_primitive : 55.-primitive_root zeta55C.
Proof.
rewrite /zeta55C; case: C_prim_root_exists=> z /= z_primitive.
exact: z_primitive.
Qed.

Lemma zeta55C_root_cyclotomic55 :
  root (map_poly (@ratr algC) cyclotomic55_Q) zeta55C.
Proof.
rewrite /cyclotomic55_Q /cyclotomic_rat -map_poly_comp.
have hmap :
    (@ratr algC) \o (intr : int -> rat) =1 (intr : int -> algC).
  by move=> a /=; rewrite rmorph_int.
rewrite (eq_map_poly hmap) (Phi_cyclotomic zeta55C_primitive).
rewrite root_cyclotomic.
- exact: zeta55C_primitive.
- exact: zeta55C_primitive.
Qed.

(** The chosen complex primitive root has an internal preimage in the
    concrete MathComp--Abel splitting field. *)
Lemma zeta55_in_ambient :
  {z : Ambient | ambient_inC z = zeta55C}.
Proof.
have hfactor :
    map_poly (@ratr algC) cyclotomic55_Q %=
      \prod_(z <- numfield_roots cyclotomic55_Q)
        ('X - (ambient_inC z)%:P).
  move: (poly_numfield_eqp cyclotomic55_Q_neq0).
  rewrite -(eqp_map ambient_inC) map_prod_XsubC -map_poly_comp.
  by rewrite (eq_map_poly
    (fmorph_eq_rat (ambient_inC \o in_alg Ambient))).
have hzprod :
    root (\prod_(z <- numfield_roots cyclotomic55_Q)
      ('X - (ambient_inC z)%:P)) zeta55C.
  by rewrite -(eqp_root hfactor) zeta55C_root_cyclotomic55.
have hprod :
    (\prod_(z <- numfield_roots cyclotomic55_Q)
      ('X - (ambient_inC z)%:P)) =
    (\prod_(a <- map ambient_inC (numfield_roots cyclotomic55_Q))
      ('X - a%:P)).
  by rewrite big_map.
have hzmem :
    zeta55C \in map ambient_inC (numfield_roots cyclotomic55_Q).
  move: hzprod.
  by rewrite hprod root_prod_XsubC.
have hhas :
    has (fun z : Ambient => ambient_inC z == zeta55C)
      (numfield_roots cyclotomic55_Q).
  move: hzmem.
  by rewrite -has_pred1 has_map.
pose z := nth 0 (numfield_roots cyclotomic55_Q)
  (find (fun z : Ambient => ambient_inC z == zeta55C)
    (numfield_roots cyclotomic55_Q)).
exists z.
apply/eqP.
rewrite /z.
exact: nth_find hhas.
Qed.

Definition zeta55 : Ambient := sval zeta55_in_ambient.

Lemma ambient_inC_zeta55 : ambient_inC zeta55 = zeta55C.
Proof.
rewrite /zeta55; case: zeta55_in_ambient=> z /=.
exact.
Qed.

Lemma zeta55_primitive : 55.-primitive_root zeta55.
Proof.
move: zeta55C_primitive.
by rewrite -ambient_inC_zeta55 fmorph_primitive_root.
Qed.

Definition zeta11 : Ambient := zeta55 ^+ 5.
Definition zeta5 : Ambient := zeta55 ^+ 11.

Lemma zeta11_primitive : 11.-primitive_root zeta11.
Proof.
rewrite /zeta11.
apply: (dvdn_prim_root zeta55_primitive).
by vm_compute.
Qed.

Lemma zeta5_primitive : 5.-primitive_root zeta5.
Proof.
rewrite /zeta5.
apply: (dvdn_prim_root zeta55_primitive).
by vm_compute.
Qed.

Definition ElevenField : {subfield Ambient} := <<1; zeta11>>%AS.

(** An automorphism of the 55th cyclotomic field with exponent 12 fixes the
    eleventh root and moves the fifth root.  The construction starts in
    [algC] and is restricted honestly to the normal [numfield]. *)
Lemma exists_endomorphism_fixing_zeta11_moving_zeta5 :
  {u : {lrmorphism Ambient -> Ambient} |
    u zeta11 = zeta11 /\ u zeta5 != zeta5}.
Proof.
have co12_55 : coprime 12 55 by vm_compute.
have [nu nuE] := Qn_aut_exists co12_55.
have [u uE] := restrict_aut_to_normal_num_field ambient_inC nu.
exists u; split.
- apply: (fmorph_inj ambient_inC).
  rewrite uE /zeta11 !rmorphXn /= ambient_inC_zeta55.
  rewrite (nuE zeta55C (prim_expr_order zeta55C_primitive)).
  rewrite -exprM.
  have h60 : (12 * 5)%N = (55 + 5)%N by vm_compute.
  by rewrite h60 exprD (prim_expr_order zeta55C_primitive) mul1r.
- apply/negP=> /eqP u_zeta5.
  have h := congr1 ambient_inC u_zeta5.
  move: h.
  rewrite uE /zeta5 !rmorphXn /= ambient_inC_zeta55.
  rewrite (nuE zeta55C (prim_expr_order zeta55C_primitive)) -exprM.
  move=> hpow.
  have hpowb : zeta55C ^+ (12 * 11) == zeta55C ^+ 11
    by exact/eqP/hpow.
  move: hpowb.
  rewrite (eq_prim_root_expr zeta55C_primitive).
  vm_compute.
discriminate.
Qed.

(** Every element generated by the base field and [zeta11] is fixed by any
    base-linear field endomorphism which fixes [zeta11]. *)
Lemma endomorphism_fixed_on_ElevenField
    (u : {lrmorphism Ambient -> Ambient}) :
  u zeta11 = zeta11 -> {in ElevenField, u =1 id}.
Proof.
move=> u_zeta11 x /Fadjoin_polyP[p p_over ->].
have up : map_poly u p = p.
  have /polyOver1P[q ->] := p_over.
  rewrite -map_poly_comp.
  apply: eq_map_poly=> a.
  by rewrite !fmorph_eq_rat.
rewrite -horner_map.
rewrite up.
exact (congr1 (fun y : Ambient => p.[y]) u_zeta11).
Qed.

Lemma zeta5_notin_ElevenField : zeta5 \notin ElevenField.
Proof.
apply/negP=> zeta5_in.
have [u [u_zeta11 /negP u_zeta5]] :=
  exists_endomorphism_fixing_zeta11_moving_zeta5.
apply: u_zeta5; apply/eqP.
exact (endomorphism_fixed_on_ElevenField u_zeta11 zeta5_in).
Qed.

(* -------------------------------------------------------------------- *)
(** * Root, splitting, and radical-extension package *)

Definition cyclic_quintic_root : Ambient := zeta11 + zeta11^-1.

Lemma ambient_cyclic_quintic_horner (x : Ambient) :
  (map_poly (in_alg Ambient) cyclic_quintic_Q).[x] =
    cyclic_quintic_value x.
Proof.
rewrite /cyclic_quintic_Q /cyclic_quintic_Z /cyclic_quintic_value.
rewrite -map_poly_comp.
have hmap :
    (in_alg Ambient) \o (intr : int -> rat) =1 (intr : int -> Ambient).
  by move=> a /=; rewrite alg_num_field ratr_int.
rewrite (eq_map_poly hmap).
rewrite ?rmorphD ?rmorphB ?linearD ?linearB ?linearZ /=.
rewrite ?map_polyX ?map_polyC ?map_polyXn.
rewrite !hornerD ?hornerN ?hornerZ !hornerXn ?hornerX !hornerC.
rewrite !map_polyZ ?map_polyXn ?map_polyX.
rewrite ?hornerZ ?hornerXn ?hornerX.
exact: cyclic_quintic_value_nested x.
Qed.

Lemma cyclic_quintic_root_is_root :
  root (map_poly (in_alg Ambient) cyclic_quintic_Q)
    cyclic_quintic_root.
Proof.
rewrite rootE ambient_cyclic_quintic_horner.
apply/eqP.
exact: (primitive_eleven_cyclic_quintic_root zeta11_primitive).
Qed.

(** An irreducible monic rational polynomial which has [x] as a root is the
    minimal polynomial of [x] over the prime rational subfield. *)
Lemma irreducible_monic_root_eq_minPoly
    (p : {poly rat}) (x : Ambient) :
  irreducible_poly p -> p \is monic ->
  root (map_poly (in_alg Ambient) p) x ->
  map_poly (in_alg Ambient) p = minPoly 1 x.
Proof.
move=> p_irred p_monic px0.
have p_over : map_poly (in_alg Ambient) p \is a polyOver 1%AS.
  by apply/polyOver1P; exists p.
have min_dvd : minPoly 1 x %| map_poly (in_alg Ambient) p.
  exact: minPoly_dvdp p_over px0.
have min_size1 : size (minPoly 1 x) != 1%N by rewrite size_minPoly.
have /polyOver1P[q hq] := minPolyOver 1 x.
have q_size1 : size q != 1%N.
  move: min_size1.
  by rewrite hq size_map_poly.
have q_dvd_p : q %| p.
  move: min_dvd.
  by rewrite hq dvdp_map.
have min_eqp : minPoly 1 x %= map_poly (in_alg Ambient) p.
  rewrite hq eqp_map.
  exact: p_irred q q_size1 q_dvd_p.
have mapped_monic : map_poly (in_alg Ambient) p \is monic.
  by rewrite map_monic.
apply/eqP.
rewrite -eqp_monic ?monic_minPoly //.
by move: min_eqp; rewrite eqp_sym.
Qed.

Lemma cyclic_quintic_eq_minPoly :
  map_poly (in_alg Ambient) cyclic_quintic_Q =
    minPoly 1 cyclic_quintic_root.
Proof.
exact: irreducible_monic_root_eq_minPoly
  cyclic_quintic_Q_irreducible cyclic_quintic_Q_monic
  cyclic_quintic_root_is_root.
Qed.

Lemma ElevenField_galois : galois 1 ElevenField.
Proof.
exact (galois_Fadjoin_cyclotomic 1%AS zeta11_primitive).
Qed.

Lemma ElevenField_normal : normalField 1 ElevenField.
Proof.
move/and3P: ElevenField_galois=> [_ _ hnormal].
exact: hnormal.
Qed.

Lemma cyclic_quintic_splits_in_ElevenField :
  {rs : seq Ambient |
    all [in ElevenField] rs /\
    map_poly (in_alg Ambient) cyclic_quintic_Q =
      \prod_(x <- rs) ('X - x%:P)}.
Proof.
have root_in : cyclic_quintic_root \in ElevenField.
  rewrite /cyclic_quintic_root /ElevenField.
  apply: rpredD; first exact: memv_adjoin.
  rewrite rpredV.
  exact: memv_adjoin.
(** [normalFieldP] exposes its factor list propositionally; [sig2_eqW]
    selects that finite list in [Type] for this computational witness. *)
have /sig2_eqW[rs rs_in min_factor] :=
  normalFieldP ElevenField_normal cyclic_quintic_root root_in.
exists rs; split=> //.
by rewrite cyclic_quintic_eq_minPoly min_factor.
Qed.

(** Propositional splitting witness used by the public counterexample
    endpoint.  Recording the factorization rules out reading the later
    root-containment statement merely as a statement about whichever roots
    happen to exist in the chosen ambient field. *)
Lemma cyclic_quintic_splits_in_ElevenFieldP :
  exists rs : seq Ambient,
    all [in ElevenField] rs /\
    map_poly (in_alg Ambient) cyclic_quintic_Q =
      \prod_(x <- rs) ('X - x%:P).
Proof.
have [rs hrs] := cyclic_quintic_splits_in_ElevenField.
by exists rs; exact: hrs.
Qed.

(** A fixed factor list extracted from the proved splitting witness. *)
Definition cyclic_quintic_factor_roots : seq Ambient :=
  sval cyclic_quintic_splits_in_ElevenField.

Lemma cyclic_quintic_factor_roots_spec :
  all [in ElevenField] cyclic_quintic_factor_roots /\
  map_poly (in_alg Ambient) cyclic_quintic_Q =
    \prod_(x <- cyclic_quintic_factor_roots) ('X - x%:P).
Proof.
rewrite /cyclic_quintic_factor_roots.
by case: cyclic_quintic_splits_in_ElevenField.
Qed.

(** The concrete field generated by the full proved factor list. *)
Definition CyclicQuinticSplittingField : {subfield Ambient} :=
  <<1 & cyclic_quintic_factor_roots>>%AS.

Definition is_cyclic_quintic_root (x : Ambient) : Prop :=
  root (map_poly (in_alg Ambient) cyclic_quintic_Q) x.

Lemma every_cyclic_quintic_root_in_ElevenField :
  forall x, is_cyclic_quintic_root x -> x \in ElevenField.
Proof.
have [rs [rs_in factor]] := cyclic_quintic_splits_in_ElevenField.
move=> x; rewrite /is_cyclic_quintic_root factor root_prod_XsubC=> x_in.
exact: (allP rs_in x x_in).
Qed.

Lemma cyclic_quintic_root_mem_splittingField x :
  is_cyclic_quintic_root x -> x \in CyclicQuinticSplittingField.
Proof.
have [_ factor] := cyclic_quintic_factor_roots_spec.
move=> hx.
have hx_in : x \in cyclic_quintic_factor_roots.
  by move: hx; rewrite /is_cyclic_quintic_root factor root_prod_XsubC.
by rewrite /CyclicQuinticSplittingField seqv_sub_adjoin.
Qed.

(** Conversely, the extracted factor field is contained in every field
    containing all roots.  Together with the preceding lemma this records
    that it is the field generated by all roots, not merely some splitting
    overfield. *)
Lemma cyclic_quintic_splittingField_le
    (E : {subfield Ambient}) :
  (forall x, is_cyclic_quintic_root x -> x \in E) ->
  (CyclicQuinticSplittingField <= E)%VS.
Proof.
move=> hall.
apply/Fadjoin_seqP; split; first exact: sub1v.
move=> x hx.
apply: hall.
have [_ factor] := cyclic_quintic_factor_roots_spec.
by rewrite /is_cyclic_quintic_root factor root_prod_XsubC.
Qed.

(** The precise field named in Theorem 4: the field generated by all roots
    and the displayed primitive fifth root. *)
Definition ClaimedAllRootsWithZeta5Field : {subfield Ambient} :=
  <<CyclicQuinticSplittingField; zeta5>>%AS.

Lemma claimedAllRootsWithZeta5_contains_roots x :
  is_cyclic_quintic_root x -> x \in ClaimedAllRootsWithZeta5Field.
Proof.
move=> hx.
apply: (subvP (subv_adjoin CyclicQuinticSplittingField zeta5)).
exact: cyclic_quintic_root_mem_splittingField hx.
Qed.

Lemma zeta5_mem_claimedAllRootsWithZeta5 :
  zeta5 \in ClaimedAllRootsWithZeta5Field.
Proof. exact: memv_adjoin CyclicQuinticSplittingField zeta5. Qed.

(** Its universal property makes the phrase "generated by all roots and
    zeta5" formal rather than documentary. *)
Lemma claimedAllRootsWithZeta5_le
    (E : {subfield Ambient}) :
  (forall x, is_cyclic_quintic_root x -> x \in E) ->
  zeta5 \in E ->
  (ClaimedAllRootsWithZeta5Field <= E)%VS.
Proof.
move=> hroots hzeta.
apply/FadjoinP; split.
- exact: cyclic_quintic_splittingField_le hroots.
- exact: hzeta.
Qed.

Lemma ElevenField_simple_radical_step :
  simple_radical_step (L := Ambient) 1 ElevenField.
Proof.
exists zeta11, 11%N; split; first by vm_compute.
split.
- rewrite (prim_expr_order zeta11_primitive).
  exact: mem1v.
- reflexivity.
Qed.

Lemma ElevenField_radical_extension :
  radical_extension (L := Ambient) 1 ElevenField.
Proof.
have h0 : @radical_extension rat Ambient 1 1 :=
  @RadicalExtensionRefl rat Ambient 1.
exact: (@RadicalExtensionStep rat Ambient 1 1 ElevenField h0
  ElevenField_simple_radical_step).
Qed.

(** The fifth root is not forced by radicality, even for the actual
    irreducible cyclic quintic and even when the competing radical extension
    contains every root. *)
Lemma primitive_fifth_root_not_forced_by_radicality :
  ~ (forall M : {subfield Ambient},
      radical_extension (L := Ambient) 1 M ->
      (forall x, is_cyclic_quintic_root x -> x \in M) ->
      zeta5 \in M).
Proof.
exact: (radicality_does_not_force_missing_element
  ElevenField_radical_extension every_cyclic_quintic_root_in_ElevenField
  zeta5_notin_ElevenField).
Qed.

(** Strong form of the literal Theorem 4 contradiction: *any* proposed least
    radical field containing all roots is impossible as soon as it also
    contains the displayed primitive fifth root. *)
Lemma no_least_radical_root_field_containing_zeta5
    (E : {subfield Ambient}) :
  zeta5 \in E ->
  ~ least_radical_extension_containing
      (L := Ambient) 1 E is_cyclic_quintic_root.
Proof.
move=> zeta5_in_E.
exact: (not_least_radical_extension_of_missing_element
  ElevenField_radical_extension every_cyclic_quintic_root_in_ElevenField
  zeta5_in_E zeta5_notin_ElevenField).
Qed.

(** The exact leastness conclusion of the printed Theorem 4, stated with
    both advertised containment properties of its candidate field.  The
    first premise is intentionally unused: the explicit competing radical
    field already shows that the presence of [zeta5] alone contradicts
    literal leastness among radical all-root fields. *)
Theorem lazard_theorem4_literal_leastness_conclusion_fails
    (E : {subfield Ambient}) :
  (forall x, is_cyclic_quintic_root x -> x \in E) ->
  zeta5 \in E ->
  ~ least_radical_extension_containing
      (L := Ambient) 1 E is_cyclic_quintic_root.
Proof.
move=> _.
exact: no_least_radical_root_field_containing_zeta5.
Qed.

(** Direct refutation for the exact generated field appearing in the
    printed statement. *)
Theorem claimedAllRootsWithZeta5_is_not_least_radical :
  ~ least_radical_extension_containing
      (L := Ambient) 1 ClaimedAllRootsWithZeta5Field
      is_cyclic_quintic_root.
Proof.
exact: (no_least_radical_root_field_containing_zeta5
  zeta5_mem_claimedAllRootsWithZeta5).
Qed.

(** Complete concrete counterexample package. *)
Theorem lazard_theorem4_counterexample :
  [/\
    size cyclic_quintic_Q = 6%N,
    cyclic_quintic_Q \is monic,
    irreducible_poly cyclic_quintic_Q
  & [/\
      root (map_poly (in_alg Ambient) cyclic_quintic_Q)
        cyclic_quintic_root,
      (exists rs : seq Ambient,
        all [in ElevenField] rs /\
        map_poly (in_alg Ambient) cyclic_quintic_Q =
          \prod_(x <- rs) ('X - x%:P)),
      (forall x, is_cyclic_quintic_root x -> x \in ElevenField)
    & [/\
        radical_extension (L := Ambient) 1 ElevenField,
        5.-primitive_root zeta5,
        zeta5 \notin ElevenField
      & [/\
          ~ (forall M : {subfield Ambient},
              radical_extension (L := Ambient) 1 M ->
              (forall x, is_cyclic_quintic_root x -> x \in M) ->
              zeta5 \in M),
          ~ least_radical_extension_containing
              (L := Ambient) 1 ClaimedAllRootsWithZeta5Field
              is_cyclic_quintic_root
        & forall E : {subfield Ambient}, zeta5 \in E ->
            ~ least_radical_extension_containing
                (L := Ambient) 1 E is_cyclic_quintic_root]]]].
Proof.
split.
- exact: cyclic_quintic_Q_size.
- exact: cyclic_quintic_Q_monic.
- exact: cyclic_quintic_Q_irreducible.
- split.
  + exact: cyclic_quintic_root_is_root.
  + exact: cyclic_quintic_splits_in_ElevenFieldP.
  + exact: every_cyclic_quintic_root_in_ElevenField.
  + split.
    * exact: ElevenField_radical_extension.
    * exact: zeta5_primitive.
    * exact: zeta5_notin_ElevenField.
    * split.
      -- exact: primitive_fifth_root_not_forced_by_radicality.
      -- exact: claimedAllRootsWithZeta5_is_not_least_radical.
      -- exact: no_least_radical_root_field_containing_zeta5.
Qed.

End PolynomialFormulasLazardOptimalityCyclicQuinticCounterexample.
