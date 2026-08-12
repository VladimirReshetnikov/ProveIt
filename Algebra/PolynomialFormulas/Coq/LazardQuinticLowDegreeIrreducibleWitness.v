From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardQuinticLowDegreeSpecialization.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * An irreducible binomial witness for the degree-five bound

    Lazard's definition of an always-separable resolvent quantifies over
    irreducible input polynomials.  The generic cyclic-tuple collision does
    not alone discharge that quantifier.  Here we instantiate it with the
    rational Eisenstein quintic [X^5 - 2], choose an actual fifth root in
    [algC], and prove that its five primitive-root translates are distinct
    roots.  The literal [S5/C5] and [S5/D5] orbit products are then both
    nonseparable for every rational invariant of degree below five.

    This source mirrors
    [LazardQuinticLowDegreeIrreducibleWitness.lean]. *)
Module PolynomialFormulasLazardQuinticLowDegreeIrreducibleWitness.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module Low := PolynomialFormulasLazardQuinticLowDegreeSpecialization.
Module GE := PolynomialFormulasLazardGeneralResolventExplicit.
Module GC := PolynomialFormulasLazardGeneralResolventCriterion.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module QF := PolynomialFormulasQuinticF20Data.
Module Class := PolynomialFormulasFin5TransitiveClassification.

Local Notation ratrC := (@ratr algC).
Local Notation MPR := {mpoly rat[5]}.
Local Notation MPC := {mpoly algC[5]}.

(** ** The irreducible rational quintic [X^5 - 2] *)

Definition x5_sub_two_Z : {poly int} := 'X^5 - (2 : int)%:P.

Definition x5_sub_two_Q : {poly rat} :=
  map_poly (intr : int -> rat) x5_sub_two_Z.

Lemma x5_sub_two_Z_size : size x5_sub_two_Z = 6%N.
Proof. vm_compute; reflexivity. Qed.

Lemma x5_sub_two_Z_irreducible : irreducible_poly x5_sub_two_Z.
Proof.
apply: (eisenstein_crit (p := 2)).
- by vm_compute.
- by rewrite x5_sub_two_Z_size.
- by vm_compute.
- by vm_compute.
- move=> [|[|[|[|[|i]]]]] //= _; vm_compute.
Qed.

Lemma x5_sub_two_Q_size : size x5_sub_two_Q = 6%N.
Proof. by rewrite /x5_sub_two_Q size_map_poly x5_sub_two_Z_size. Qed.

Lemma x5_sub_two_Q_irreducible : irreducible_poly x5_sub_two_Q.
Proof.
rewrite /x5_sub_two_Q irreducible_rat_int.
exact: x5_sub_two_Z_irreducible.
Qed.

Definition x5_sub_two_C : {poly algC} :=
  map_poly ratrC x5_sub_two_Q.

Lemma x5_sub_two_C_size : size x5_sub_two_C = 6%N.
Proof. by rewrite /x5_sub_two_C size_map_poly x5_sub_two_Q_size. Qed.

Lemma x5_sub_two_CE :
  x5_sub_two_C = 'X^5 - (2 : algC)%:P.
Proof.
by rewrite /x5_sub_two_C /x5_sub_two_Q /x5_sub_two_Z
  !map_polyB !map_polyXn !map_polyC !rmorph_nat.
Qed.

(** ** Five distinct roots in [algC] *)

Definition alpha_witness : {z : algC | root x5_sub_two_C z}.
Proof.
apply: sigW.
apply/closed_rootP.
by rewrite x5_sub_two_C_size.
Defined.

Definition alpha : algC := sval alpha_witness.

Lemma alpha_root : root x5_sub_two_C alpha.
Proof. exact: svalP alpha_witness. Qed.

Lemma alpha_pow_five : alpha ^+ 5 = (2 : algC).
Proof.
move: alpha_root.
by rewrite x5_sub_two_CE rootE hornerB hornerXn hornerC subr_eq0.
Qed.

Lemma alpha_neq0 : alpha != 0.
Proof.
apply/eqP=> alpha0.
have two_neq0 : (2 : algC) != 0 by rewrite pnatr_eq0.
move: two_neq0.
by rewrite -alpha_pow_five alpha0 expr0n // eqxx.
Qed.

Definition omega : algC := projT1 (C_prim_root_exists (n := 5) isT).

Lemma omega_primitive : 5.-primitive_root omega.
Proof.
rewrite /omega; case: C_prim_root_exists=> z /= hz.
exact: hz.
Qed.

Definition roots : 5.-tuple algC :=
  @Low.lazard_quintic_cyclic_root_tuple algC alpha omega.

Lemma roots_are_roots i : root x5_sub_two_C (tnth roots i).
Proof.
rewrite x5_sub_two_CE -alpha_pow_five.
exact: (@Low.lazard_quintic_cyclic_root_is_root
  algC alpha omega omega_primitive i).
Qed.

Lemma roots_injective : injective (tnth roots).
Proof.
move=> i j hij.
have powers_eq : omega ^+ (i : nat) = omega ^+ (j : nat).
  apply: (mulfI alpha_neq0).
  move: hij.
  by rewrite /roots /Low.lazard_quintic_cyclic_root_tuple !tnth_mktuple.
apply/val_inj.
have powers_eqb : omega ^+ (i : nat) == omega ^+ (j : nat).
  exact/eqP.
move: powers_eqb.
rewrite (eq_prim_root_expr omega_primitive)
  !modn_small ?ltn_ord.
by move/eqP.
Qed.

(** The five displayed roots exhaust the degree-five polynomial, rather
    than merely furnishing five pointwise root proofs. *)
Lemma x5_sub_two_C_monic : x5_sub_two_C \is monic.
Proof.
rewrite x5_sub_two_CE.
exact: monicXnsubC (by []).
Qed.

Lemma all_roots_x5_sub_two_C : all (root x5_sub_two_C) roots.
Proof.
rewrite -forallb_tnth.
apply/forallP=> i.
exact: roots_are_roots i.
Qed.

Lemma uniq_roots_x5_sub_two_C : uniq_roots roots.
Proof.
rewrite uniq_rootsE.
exact/tuple_uniqP: roots_injective.
Qed.

Theorem x5_sub_two_C_factorization :
  x5_sub_two_C = \prod_(z <- roots) ('X - z%:P).
Proof.
have hfactor := all_roots_prod_XsubC
  (p := x5_sub_two_C) (rs := roots)
  (by rewrite x5_sub_two_C_size size_tuple)
  all_roots_x5_sub_two_C uniq_roots_x5_sub_two_C.
move: hfactor.
by rewrite (monicP x5_sub_two_C_monic) scale1r.
Qed.

Theorem x5_sub_two_C_root_iff z :
  root x5_sub_two_C z = (z \in roots).
Proof. by rewrite x5_sub_two_C_factorization root_prod_XsubC. Qed.

(** ** Scalar extension of rational invariants *)

Definition lift_invariant (p : MPR) : MPC := map_mpoly ratrC p.

Lemma lift_invariant_under (G : {group QF.S5}) p :
  @GE.lazard_invariant_under rat 5 G p ->
  @GE.lazard_invariant_under algC 5 G (lift_invariant p).
Proof.
move=> invariant s sG.
rewrite /lift_invariant
  -(@GE.map_mpoly_left_action rat algC 5 ratrC s p).
by rewrite (invariant s sG).
Qed.

Lemma msize_lift_invariant p :
  msize (lift_invariant p) = msize p.
Proof.
have ratrC_inj : injective ratrC := fmorph_inj ratrC.
rewrite /lift_invariant !msizeE.
exact: (perm_big _ (msupp_map_mpoly p ratrC_inj)).
Qed.

(** ** Irreducible witnesses for the two literal relative resolvents *)

Theorem irreducible_x5_sub_two_C5_relative_resolvent_not_separable p :
  @Low.lazard_C5_invariant rat p ->
  msize p <= 5 ->
  irreducible_poly x5_sub_two_Q /\
  injective (tnth roots) /\
  (forall i : 'I_5, root x5_sub_two_C (tnth roots i)) /\
  x5_sub_two_C = \prod_(z <- roots) ('X - z%:P) /\
  (forall z : algC, root x5_sub_two_C z = (z \in roots)) /\
  ~~ separable_poly
    (GC.lazard_orbit_resolvent QF.standard_C5
      (@Low.lazard_C5_specialized_orbit_value
        algC alpha omega (lift_invariant p))).
Proof.
move=> invariant size_p; split.
- exact: x5_sub_two_Q_irreducible.
- split; first exact: roots_injective.
  split; first exact: roots_are_roots.
  split; first exact: x5_sub_two_C_factorization.
  split; first exact: x5_sub_two_C_root_iff.
  apply: (@Low.lazard_C5_low_degree_relative_resolvent_not_separable
    algC alpha omega omega_primitive (lift_invariant p)).
  + exact: lift_invariant_under invariant.
  + by rewrite msize_lift_invariant.
Qed.

Theorem irreducible_x5_sub_two_D5_relative_resolvent_not_separable p :
  @Low.lazard_D5_invariant rat p ->
  msize p <= 5 ->
  irreducible_poly x5_sub_two_Q /\
  injective (tnth roots) /\
  (forall i : 'I_5, root x5_sub_two_C (tnth roots i)) /\
  x5_sub_two_C = \prod_(z <- roots) ('X - z%:P) /\
  (forall z : algC, root x5_sub_two_C z = (z \in roots)) /\
  ~~ separable_poly
    (GC.lazard_orbit_resolvent Class.standard_D5
      (@Low.lazard_D5_specialized_orbit_value
        algC alpha omega (lift_invariant p))).
Proof.
move=> invariant size_p; split.
- exact: x5_sub_two_Q_irreducible.
- split; first exact: roots_injective.
  split; first exact: roots_are_roots.
  split; first exact: x5_sub_two_C_factorization.
  split; first exact: x5_sub_two_C_root_iff.
  apply: (@Low.lazard_D5_low_degree_relative_resolvent_not_separable
    algC alpha omega omega_primitive (lift_invariant p)).
  + exact: lift_invariant_under invariant.
  + by rewrite msize_lift_invariant.
Qed.

End PolynomialFormulasLazardQuinticLowDegreeIrreducibleWitness.
