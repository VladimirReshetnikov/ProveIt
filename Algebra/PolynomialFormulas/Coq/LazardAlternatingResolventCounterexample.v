From mathcomp Require Import
  all_ssreflect all_algebra all_field.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * The obstruction in Lazard's alternating-resolvent example

    Section 3 of Lazard's paper says that the Vandermonde resolvent is
    always separable because an irreducible polynomial cannot have zero
    discriminant.  Over an imperfect positive-characteristic field,
    irreducibility does not imply separability.

    The first theorem below isolates the exact MathComp obstruction: any
    positive-degree polynomial with zero derivative is nonseparable, even if
    it is irreducible.  The second section constructs the standard concrete
    example [X^3-t] over [F_3(t)] using MathComp's generic fraction field.
    If a cube [p^3/q^3] were equal to [t], cross multiplication would give
    [p^3 = t q^3].  Polynomial degree modulo three makes this impossible.
    The generic cubic criterion then proves irreducibility, while direct
    derivative and resultant computations prove inseparability and zero
    discriminant.  The associated alternating resolvent is [X^2], hence is
    nonseparable.

    This file is wired into the public build and assumption-audit graph, but
    remains source-only until that graph receives a focused kernel check. *)
Module PolynomialFormulasLazardAlternatingResolventCounterexample.

Import GRing.Theory.

Section AbstractObstruction.

Variable F : fieldType.

(** The quadratic shape used by the alternating/Vandermonde resolvent. *)
Definition vandermonde_quadratic_resolvent (delta : F) : {poly F} :=
  'X ^+ 2 - delta%:P.

Lemma vandermonde_quadratic_resolvent_size delta :
  size (vandermonde_quadratic_resolvent delta) = 3.
Proof. by rewrite /vandermonde_quadratic_resolvent size_XnsubC. Qed.

Lemma vandermonde_quadratic_resolvent_derivative delta :
  (vandermonde_quadratic_resolvent delta)^`() =
    (2%:R : F) *: 'X.
Proof.
by rewrite /vandermonde_quadratic_resolvent
  derivB derivXn derivC subr0 -scaler_nat expr1.
Qed.

(** The sufficient half of the corrected statement: nonzero [2] and
    nonzero discriminant parameter make [X^2-Delta] separable. *)
Lemma vandermonde_quadratic_resolvent_separable delta :
  (2%:R : F) != 0 ->
  delta != 0 ->
  separable_poly (vandermonde_quadratic_resolvent delta).
Proof.
move=> two_neq0 delta_neq0.
rewrite unlock vandermonde_quadratic_resolvent_derivative.
rewrite (coprimepZr _ _ two_neq0) coprimepX rootE.
by rewrite /vandermonde_quadratic_resolvent
  hornerB hornerXn hornerC expr0 // sub0r oppr_eq0 delta_neq0.
Qed.

(** Characteristic different from two is necessary as well. *)
Lemma vandermonde_quadratic_resolvent_separable_only_if_two_ne_zero delta :
  separable_poly (vandermonde_quadratic_resolvent delta) ->
  (2%:R : F) != 0.
Proof.
move=> resolvent_separable.
apply/negP=> /eqP two_eq0.
have derivative_zero :
    (vandermonde_quadratic_resolvent delta)^`() = 0.
  by rewrite vandermonde_quadratic_resolvent_derivative
    two_eq0 scale0r.
have derivative_nonzero :=
  separable_deriv_eq0 resolvent_separable
    (dvdpp (vandermonde_quadratic_resolvent delta))
    (by rewrite vandermonde_quadratic_resolvent_size).
by rewrite derivative_zero eqxx in derivative_nonzero.
Qed.

(** A nonzero discriminant parameter is also necessary: at [Delta=0] the
    resolvent is the non-squarefree polynomial [X^2]. *)
Lemma vandermonde_quadratic_resolvent_separable_only_if_delta_ne_zero delta :
  separable_poly (vandermonde_quadratic_resolvent delta) ->
  delta != 0.
Proof.
move=> resolvent_separable.
apply/negP=> /eqP delta_eq0.
rewrite delta_eq0 /vandermonde_quadratic_resolvent
  polyC0 subr0 in resolvent_separable.
have no_square := separable_nosquare resolvent_separable
  (isT : 1 < 2) (by rewrite size_polyX).
by rewrite dvdpp in no_square.
Qed.

(** Exact corrected criterion: [X^2-Delta] is separable if and only if
    both [2] and [Delta] are nonzero. *)
Theorem vandermonde_quadratic_resolvent_separable_iff delta :
  separable_poly (vandermonde_quadratic_resolvent delta) <->
  ((2%:R : F) != 0) /\ (delta != 0).
Proof.
split.
- move=> resolvent_separable; split.
  + exact: vandermonde_quadratic_resolvent_separable_only_if_two_ne_zero
      resolvent_separable.
  + exact: vandermonde_quadratic_resolvent_separable_only_if_delta_ne_zero
      resolvent_separable.
- by move=> [two_neq0 delta_neq0];
    exact: vandermonde_quadratic_resolvent_separable.
Qed.

(** Separability of the source polynomial gives the nonzero raw
    discriminant/resultant that irreducibility alone does not supply. *)
Lemma separable_resultant_derivative_nonzero (f : {poly F}) :
  separable_poly f -> resultant f f^`() != 0.
Proof.
move=> f_separable.
rewrite resultant_eq0.
move: f_separable; rewrite unlock coprimep_def=> /eqP gcd_size_one.
by rewrite gcd_size_one.
Qed.

(** A source-polynomial separability hypothesis plus [2 != 0] therefore
    yields a separable quadratic resolvent for the raw discriminant. *)
Theorem corrected_vandermonde_resolvent_separable
    (f : {poly F}) :
  separable_poly f ->
  (2%:R : F) != 0 ->
  separable_poly
    (vandermonde_quadratic_resolvent (resultant f f^`())).
Proof.
move=> f_separable two_neq0.
exact: vandermonde_quadratic_resolvent_separable two_neq0
  (separable_resultant_derivative_nonzero f_separable).
Qed.

(** Irreducibility by itself supplies no contradiction to zero derivative.
    The conclusion follows from separability's derivative criterion; the
    irreducibility premise is retained to match precisely the paper's claimed
    implication. *)
Lemma irreducible_zero_derivative_not_separable (f : {poly F}) :
  irreducible_poly f ->
  1 < size f ->
  f^`() = 0 ->
  ~~ separable_poly f.
Proof.
move=> _ f_positive_degree f_derivative_zero.
apply/negP=> f_separable.
have derivative_nonzero :=
  separable_deriv_eq0 f_separable (dvdpp f) f_positive_degree.
by rewrite f_derivative_zero eqxx in derivative_nonzero.
Qed.

(** Corrected local form of the step used in the paper: separability, not
    irreducibility alone, rules out a zero derivative in positive degree. *)
Lemma separable_positive_degree_derivative_nonzero (f : {poly F}) :
  separable_poly f ->
  1 < size f ->
  f^`() != 0.
Proof.
move=> f_separable f_positive_degree.
apply/negP=> /eqP f_derivative_zero.
have derivative_nonzero :=
  separable_deriv_eq0 f_separable (dvdpp f) f_positive_degree.
by rewrite f_derivative_zero eqxx in derivative_nonzero.
Qed.

End AbstractObstruction.

(**************************************************************************)
(** * The concrete counterexample [X^3-t] over [F_3(t)] *)

Section ConcreteF3t.

Local Notation F3 := 'F_3.
Local Notation F3t := {fraction {poly F3}}.
Local Notation "p %:F3t" :=
  (@FracField.tofrac {poly F3} p)
  (at level 2, format "p %:F3t").

(** The transcendental rational-function variable. *)
Definition f3t_variable : F3t := ('X : {poly F3})%:F3t.

Lemma f3t_variable_neq0 : f3t_variable != 0.
Proof. by rewrite /f3t_variable tofrac_eq0 polyX_eq0. Qed.

(** The coefficient field really has characteristic three. *)
Lemma F3t_pchar_three : 3 \in [pchar F3t].
Proof.
exact: (rmorph_pchar (@FracField.tofrac {poly F3}) pchar_Fp).
Qed.

(** Expose a nonzero numerator/denominator for every quotient element. *)
Lemma f3t_fraction_presentation (x : F3t) :
  exists p q : {poly F3}, q != 0 /\ x = p%:F3t / q%:F3t.
Proof.
elim/quotW: x=> r.
exists \n_r, \d_r; split; first exact: denom_ratioP.
symmetry.
unlock FracField.tofrac.
rewrite !piE /FracField.invf /FracField.mulf
  !numden_Ratio ?(oner_neq0, mulf_neq0, denom_ratioP) //.
by rewrite !mulr1 !mul1r Ratio_numden.
Qed.

(** Cross multiplication for a hypothetical cube root of [t]. *)
Lemma f3t_cube_cross_multiply p q (q0 : q != 0) :
  (p%:F3t / q%:F3t) ^+ 3 = f3t_variable ->
  p ^+ 3 = 'X * q ^+ 3.
Proof.
move=> cube_eq.
rewrite expr_div_n in cube_eq.
have q3F0 : (q%:F3t ^+ 3) != 0.
  exact: expf_neq0 (by rewrite tofrac_eq0).
have cube_eqb :
    p%:F3t ^+ 3 / q%:F3t ^+ 3 == f3t_variable / 1.
  by rewrite divr1; exact/eqP: cube_eq.
move: cube_eqb.
rewrite (eqr_div q3F0 oner_neq0) mulr1 /f3t_variable.
rewrite -!rmorphXn -rmorphM tofrac_eq.
by move/eqP.
Qed.

(** Degree at infinity: [t] cannot be a cube in [F_3(t)]. *)
Lemma f3t_variable_not_cube (b : F3t) :
  b ^+ 3 != f3t_variable.
Proof.
apply/negP=> /eqP cube_eq.
have [p [q [q0 bE]]] := f3t_fraction_presentation b.
rewrite bE in cube_eq.
have cross := f3t_cube_cross_multiply q0 cube_eq.
have size_cross := congr1 size cross.
rewrite -commr_polyX size_mulX ?expf_neq0 // in size_cross.
have size_cross_pred := congr1 predn size_cross.
rewrite /= size_exp in size_cross_pred.
rewrite [size (q ^+ 3)]polySpred ?expf_neq0 // size_exp
  in size_cross_pred.
have size_cross_mod :=
  congr1 (fun m : nat => m %% 3) size_cross_pred.
move: size_cross_mod.
by rewrite modnMl -addn1 modnMDl modn_small.
Qed.

(** The irreducible inseparable cubic. *)
Definition f3t_inseparable_cubic : {poly F3t} :=
  'X ^+ 3 - (f3t_variable)%:P.

Lemma f3t_inseparable_cubic_size :
  size f3t_inseparable_cubic = 4.
Proof. by rewrite /f3t_inseparable_cubic size_XnsubC. Qed.

Lemma f3t_inseparable_cubic_has_no_root x :
  ~~ root f3t_inseparable_cubic x.
Proof.
apply/negP=> root_x.
move: root_x.
rewrite /f3t_inseparable_cubic rootE hornerB hornerXn hornerC
  subr_eq0.
exact: f3t_variable_not_cube x.
Qed.

Theorem f3t_inseparable_cubic_irreducible :
  irreducible_poly f3t_inseparable_cubic.
Proof.
apply: cubic_irreducible.
- by rewrite f3t_inseparable_cubic_size.
- exact: f3t_inseparable_cubic_has_no_root.
Qed.

Lemma f3t_inseparable_cubic_derivative :
  f3t_inseparable_cubic^`() = 0.
Proof.
rewrite /f3t_inseparable_cubic derivB derivXn derivC subr0.
exact: mulrn_pchar F3t_pchar_three.
Qed.

Theorem f3t_inseparable_cubic_not_separable :
  ~~ separable_poly f3t_inseparable_cubic.
Proof.
exact: irreducible_zero_derivative_not_separable
  f3t_inseparable_cubic_irreducible
  (by rewrite f3t_inseparable_cubic_size)
  f3t_inseparable_cubic_derivative.
Qed.

(** For a monic polynomial the resultant with its derivative differs from
    the usual discriminant only by the standard degree-dependent sign.  Its
    vanishing is therefore the exact discriminant obstruction used here. *)
Definition f3t_inseparable_cubic_discriminant : F3t :=
  resultant f3t_inseparable_cubic f3t_inseparable_cubic^`().

Lemma f3t_inseparable_cubic_discriminant_zero :
  f3t_inseparable_cubic_discriminant = 0.
Proof.
apply/eqP.
rewrite /f3t_inseparable_cubic_discriminant
  f3t_inseparable_cubic_derivative resultant_eq0 gcdp0
  f3t_inseparable_cubic_size.
by [].
Qed.

(** Lazard's alternating resolvent specialized to this discriminant. *)
Definition f3t_alternating_resolvent : {poly F3t} :=
  'X ^+ 2 - (f3t_inseparable_cubic_discriminant)%:P.

Lemma f3t_alternating_resolventE :
  f3t_alternating_resolvent = 'X ^+ 2.
Proof.
by rewrite /f3t_alternating_resolvent
  f3t_inseparable_cubic_discriminant_zero polyC0 subr0.
Qed.

Theorem f3t_alternating_resolvent_not_separable :
  ~~ separable_poly f3t_alternating_resolvent.
Proof.
rewrite f3t_alternating_resolventE.
apply/negP=> X2_separable.
have no_square := separable_nosquare X2_separable
  (isT : 1 < 2) (by rewrite size_polyX).
by rewrite dvdpp in no_square.
Qed.

(** Characteristic three is allowed by the paper's printed global
    exclusions [char != 2,5]. *)
Lemma F3t_pchar_not_two : 2 \notin [pchar F3t].
Proof. by rewrite (GRing.pcharf_eq F3t_pchar_three). Qed.

Lemma F3t_pchar_not_five : 5 \notin [pchar F3t].
Proof. by rewrite (GRing.pcharf_eq F3t_pchar_three). Qed.

Theorem F3t_satisfies_lazard_printed_characteristic_exclusions :
  (2 \notin [pchar F3t]) /\ (5 \notin [pchar F3t]).
Proof. exact: conj F3t_pchar_not_two F3t_pchar_not_five. Qed.

(** A single closed semantic package for the whole obstruction: no
    irreducibility, characteristic, discriminant, or separability fact is
    supplied by the caller. *)
Theorem f3t_closed_alternating_resolvent_counterexample :
  3 \in [pchar F3t] /\
  2 \notin [pchar F3t] /\
  5 \notin [pchar F3t] /\
  irreducible_poly f3t_inseparable_cubic /\
  ~~ separable_poly f3t_inseparable_cubic /\
  f3t_inseparable_cubic_discriminant = 0 /\
  ~~ separable_poly f3t_alternating_resolvent.
Proof.
repeat split.
- exact: F3t_pchar_three.
- exact: F3t_pchar_not_two.
- exact: F3t_pchar_not_five.
- exact: f3t_inseparable_cubic_irreducible.
- exact: f3t_inseparable_cubic_not_separable.
- exact: f3t_inseparable_cubic_discriminant_zero.
- exact: f3t_alternating_resolvent_not_separable.
Qed.

End ConcreteF3t.

Print Assumptions vandermonde_quadratic_resolvent_separable_iff.
Print Assumptions corrected_vandermonde_resolvent_separable.
Print Assumptions f3t_inseparable_cubic_irreducible.
Print Assumptions f3t_inseparable_cubic_not_separable.
Print Assumptions f3t_inseparable_cubic_discriminant_zero.
Print Assumptions f3t_alternating_resolvent_not_separable.
Print Assumptions F3t_satisfies_lazard_printed_characteristic_exclusions.
Print Assumptions f3t_closed_alternating_resolvent_counterexample.

End PolynomialFormulasLazardAlternatingResolventCounterexample.
