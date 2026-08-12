From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  Fin5TransitiveClassification LazardGeneralResolventExplicit
  LazardInvariantMultinomials QuinticF20Data.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corrected form of Lazard's low-degree specialization argument.

    Put the roots of [X^5-alpha^5] in the order

      [r_i = alpha * omega^i]

    for a primitive fifth root [omega].  The distinguished five-cycle shifts
    this tuple to [omega * r].  Hence a homogeneous [C5]-invariant of degree
    [d] has value [v = omega^d v].  If [0 < d < 5], primitivity forces
    [v = 0].

    The word "homogeneous" (or, equivalently, removal of the constant
    component) is essential.  An arbitrary invariant of total degree below
    five specializes to its degree-zero component, not necessarily to zero;
    the constant polynomial [1] is the literal counterexample.  Since [C5]
    is normal in its normalizer [F20], every [F20]-conjugate satisfies the
    same corrected statement. *)
Module PolynomialFormulasLazardQuinticLowDegreeSpecialization.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module QF := PolynomialFormulasQuinticF20Data.
Module GC := PolynomialFormulasLazardGeneralResolventCriterion.
Module GE := PolynomialFormulasLazardGeneralResolventExplicit.
Module Class := PolynomialFormulasFin5TransitiveClassification.

Section LowDegreeSpecialization.

Variable F : fieldType.
Variables (alpha omega : F).
Hypothesis omega_primitive : 5.-primitive_root omega.

Local Notation MP := {mpoly F[5]}.

Definition lazard_quintic_cyclic_root_tuple : 5.-tuple F :=
  [tuple alpha * omega ^+ (i : nat) | i < 5].

Definition lazard_quintic_cyclic_root (i : 'I_5) : F :=
  tnth lazard_quintic_cyclic_root_tuple i.

Definition lazard_X5_sub_alpha5 : {poly F} :=
  'X ^+ 5 - (alpha ^+ 5)%:P.

Lemma lazard_quintic_cyclic_root_pow_five i :
  lazard_quintic_cyclic_root i ^+ 5 = alpha ^+ 5.
Proof.
rewrite /lazard_quintic_cyclic_root
  /lazard_quintic_cyclic_root_tuple tnth_mktuple exprMn.
rewrite -exprM mulnC exprM (prim_expr_order omega_primitive).
by rewrite expr1n mulr1.
Qed.

Lemma lazard_quintic_cyclic_root_is_root i :
  root lazard_X5_sub_alpha5 (lazard_quintic_cyclic_root i).
Proof.
by rewrite /lazard_X5_sub_alpha5 rootE hornerB hornerXn hornerC
  subr_eq0 lazard_quintic_cyclic_root_pow_five eqxx.
Qed.

(** The inverse of the chosen five-cycle advances the exponent, including
    the wraparound [omega^5 = 1]. *)
Lemma lazard_quintic_cyclic_root_shift i :
  lazard_quintic_cyclic_root (QF.five_cycle^-1 i) =
    omega * lazard_quintic_cyclic_root i.
Proof.
case: i=> [[|[|[|[|[|i]]]]] hi].
- have -> : @Ordinal 5 0 hi = QF.o0 by apply/val_inj.
  rewrite QF.five_cycle_inv_o0 /lazard_quintic_cyclic_root
    /lazard_quintic_cyclic_root_tuple !tnth_mktuple /=.
  by rewrite [omega ^+ 1]exprS mulrCA.
- have -> : @Ordinal 5 1 hi = QF.o1 by apply/val_inj.
  rewrite QF.five_cycle_inv_o1 /lazard_quintic_cyclic_root
    /lazard_quintic_cyclic_root_tuple !tnth_mktuple /=.
  by rewrite [omega ^+ 2]exprS mulrCA.
- have -> : @Ordinal 5 2 hi = QF.o2 by apply/val_inj.
  rewrite QF.five_cycle_inv_o2 /lazard_quintic_cyclic_root
    /lazard_quintic_cyclic_root_tuple !tnth_mktuple /=.
  by rewrite [omega ^+ 3]exprS mulrCA.
- have -> : @Ordinal 5 3 hi = QF.o3 by apply/val_inj.
  rewrite QF.five_cycle_inv_o3 /lazard_quintic_cyclic_root
    /lazard_quintic_cyclic_root_tuple !tnth_mktuple /=.
  by rewrite [omega ^+ 4]exprS mulrCA.
- have -> : @Ordinal 5 4 hi = QF.o4 by apply/val_inj.
  rewrite QF.five_cycle_inv_o4 /lazard_quintic_cyclic_root
    /lazard_quintic_cyclic_root_tuple !tnth_mktuple /=.
  rewrite expr0 mulr1 [omega * (alpha * omega ^+ 4)]mulrCA -exprS.
  by rewrite (prim_expr_order omega_primitive) mulr1.
- by move: hi.
Qed.

Definition lazard_quintic_permutation
    (s : QF.S5) (p : MP) : MP :=
  IM.mpoly_left_action s p.

Lemma lazard_quintic_permutation1 p :
  lazard_quintic_permutation 1 p = p.
Proof. exact: IM.mpoly_left_action1. Qed.

Lemma lazard_quintic_permutationM s t p :
  lazard_quintic_permutation (s * t) p =
    lazard_quintic_permutation s (lazard_quintic_permutation t p).
Proof. exact: IM.mpoly_left_actionM. Qed.

Lemma lazard_quintic_permutationD s :
  {morph lazard_quintic_permutation s : x y / x + y}.
Proof. exact: IM.mpoly_left_actionD. Qed.

Lemma lazard_quintic_permutation_sum s
    (I : finType) (P : pred I) (f : I -> MP) :
  lazard_quintic_permutation s (\sum_(i | P i) f i) =
    \sum_(i | P i) lazard_quintic_permutation s (f i).
Proof.
rewrite /lazard_quintic_permutation /IM.mpoly_left_action.
exact: raddf_sum.
Qed.

(** Evaluation after the honest left variable action. *)
Lemma lazard_meval_quintic_permutation
    (s : QF.S5) (p : MP) (v : 5.-tuple F) :
  (lazard_quintic_permutation s p).@[tnth v] =
    p.@[fun i => tnth v (s^-1 i)].
Proof.
rewrite /lazard_quintic_permutation /IM.mpoly_left_action.
rewrite -{1}(comp_mpoly_id (msym s^-1 p)).
rewrite msym_mPo comp_mpoly_meval.
apply: meval_eq=> i.
by rewrite !tnth_mktuple mevalXU.
Qed.

(** Scalar substitution in a homogeneous multivariate polynomial. *)
Lemma lazard_meval_scale_homogeneous
    (c : F) (v : 'I_5 -> F) (p : MP) d :
  p \is d.-homog ->
  p.@[fun i => c * v i] = c ^+ d * p.@[v].
Proof.
move/dhomogP=> hp.
rewrite !mevalE big_distrr.
apply: eq_bigr=> m mm.
rewrite (eq_bigr (fun i : 'I_5 =>
    c ^+ m i * v i ^+ m i)); last first.
  by move=> i _; rewrite exprMn.
rewrite big_split /= -expr_sum -mdegE (hp m mm).
by rewrite !mulrA [p@_m * c ^+ d]mulrC.
Qed.

Lemma lazard_meval_degree_zero_eq
    (p : MP) (v w : 'I_5 -> F) :
  p \is 0.-homog -> p.@[v] = p.@[w].
Proof.
move/dhomogP=> hp.
rewrite !mevalE.
apply: eq_bigr=> m mm.
have m0 : m = 0%MM.
  apply/eqP.
  by rewrite -mdeg_eq0 (hp m mm).
rewrite m0.
by rewrite !big1 // => i; rewrite mnm0E expr0.
Qed.

Lemma lazard_primitive_fifth_power_neq_one d :
  0 < d -> d < 5 -> omega ^+ d != 1.
Proof.
move=> d0 d5.
apply/negP=> /eqP hd.
have hd_eq : omega ^+ d == omega ^+ 0 by rewrite expr0 hd.
move: hd_eq.
rewrite (eq_prim_root_expr omega_primitive) !modn_small //.
by rewrite eqn0Ngt d0.
Qed.

Definition lazard_C5_invariant (p : MP) : Prop :=
  forall s : QF.S5, s \in QF.standard_C5 ->
    lazard_quintic_permutation s p = p.

Lemma lazard_C5_invariant_five_cycle p :
  lazard_C5_invariant p ->
  lazard_quintic_permutation QF.five_cycle p = p.
Proof.
move=> invariant.
exact: invariant QF.five_cycle (cycle_id QF.five_cycle).
Qed.

Lemma lazard_C5_invariant_pihomog p d :
  lazard_C5_invariant p ->
  lazard_C5_invariant (pihomog mdeg d p).
Proof.
move=> invariant s sC.
rewrite /lazard_quintic_permutation /IM.mpoly_left_action
  msym_pihomog.
by rewrite (invariant s sC).
Qed.

(** Corrected homogeneous vanishing theorem. *)
Theorem lazard_C5_homogeneous_low_degree_vanish p d :
  lazard_C5_invariant p ->
  p \is d.-homog ->
  0 < d -> d < 5 ->
  p.@[tnth lazard_quintic_cyclic_root_tuple] = 0.
Proof.
move=> invariant homogeneous d0 d5.
have fixed_cycle := lazard_C5_invariant_five_cycle invariant.
have action_eval := lazard_meval_quintic_permutation
  QF.five_cycle p lazard_quintic_cyclic_root_tuple.
rewrite fixed_cycle in action_eval.
have shift_eval :
    p.@[fun i => lazard_quintic_cyclic_root
        (QF.five_cycle^-1 i)] =
      p.@[fun i => omega * lazard_quintic_cyclic_root i].
  apply: meval_eq=> i.
  exact: lazard_quintic_cyclic_root_shift.
have scale_eval := lazard_meval_scale_homogeneous
  omega (fun i => lazard_quintic_cyclic_root i) homogeneous.
have value_scale :
    p.@[tnth lazard_quintic_cyclic_root_tuple] =
      omega ^+ d * p.@[tnth lazard_quintic_cyclic_root_tuple].
  exact: etrans action_eval (etrans shift_eval scale_eval).
apply/eqP; apply/negP=> value0.
have omega_d_one : omega ^+ d = 1.
  apply: (mulfI value0).
  by rewrite mulr1 mulrC -value_scale.
have omega_d_ne_one := lazard_primitive_fifth_power_neq_one d0 d5.
by move: omega_d_ne_one; rewrite omega_d_one eqxx.
Qed.

(** Every polynomial of total degree below five specializes to its constant
    homogeneous component.  Here [msize p <= 5] is precisely the support
    bound [mdeg m < 5]. *)
Theorem lazard_C5_low_degree_specializes_to_constant_component p :
  lazard_C5_invariant p ->
  msize p <= 5 ->
  p.@[tnth lazard_quintic_cyclic_root_tuple] =
    (pihomog mdeg 0 p).@[tnth lazard_quintic_cyclic_root_tuple].
Proof.
move=> invariant size_p.
have pE := pihomog_partitionE
  (mf := mdeg) (k := 5) (p := p) size_p.
rewrite {1}pE raddf_sum /= big_ord_recl /=.
rewrite big1 ?addr0 // => i _.
apply: lazard_C5_homogeneous_low_degree_vanish.
- exact: lazard_C5_invariant_pihomog invariant.
- exact: pihomogP.
- by [].
- by rewrite ltnS; exact: ltn_ord i.
Qed.

(** Normality bridge: [F20] is defined as the normalizer of [C5], so an
    [F20]-conjugate of a [C5]-invariant is again [C5]-invariant. *)
Lemma lazard_C5_invariant_F20_conjugate p g :
  g \in QF.standard_F20 ->
  lazard_C5_invariant p ->
  lazard_C5_invariant (lazard_quintic_permutation g p).
Proof.
move=> gF invariant s sC.
have sgC : s ^ g \in QF.standard_C5.
  by rewrite memJ_norm //.
have hsg : s * g = g * (s ^ g).
  by rewrite conjgE mulgA mulgV mul1g.
rewrite -lazard_quintic_permutationM hsg
  lazard_quintic_permutationM (invariant (s ^ g) sgC).
Qed.

Lemma lazard_degree_zero_conjugate_value p g :
  p \is 0.-homog ->
  (lazard_quintic_permutation g p).@[
      tnth lazard_quintic_cyclic_root_tuple] =
    p.@[tnth lazard_quintic_cyclic_root_tuple].
Proof.
move=> homogeneous.
rewrite lazard_meval_quintic_permutation.
exact: lazard_meval_degree_zero_eq homogeneous.
Qed.

(** The same corrected constant-component statement for every conjugate by
    the metacyclic normalizer. *)
Theorem lazard_F20_conjugate_low_degree_specializes_to_constant p g :
  lazard_C5_invariant p ->
  msize p <= 5 ->
  g \in QF.standard_F20 ->
  (lazard_quintic_permutation g p).@[
      tnth lazard_quintic_cyclic_root_tuple] =
    (pihomog mdeg 0 p).@[tnth lazard_quintic_cyclic_root_tuple].
Proof.
move=> invariant size_p gF.
have pE := pihomog_partitionE
  (mf := mdeg) (k := 5) (p := p) size_p.
rewrite [p in lazard_quintic_permutation g p]pE
  lazard_quintic_permutation_sum raddf_sum /= big_ord_recl /=.
rewrite lazard_degree_zero_conjugate_value ?pihomogP //.
rewrite big1 ?addr0 // => i _.
apply: lazard_C5_homogeneous_low_degree_vanish.
- apply: lazard_C5_invariant_F20_conjugate gF.
  exact: lazard_C5_invariant_pihomog invariant.
- exact: IM.mpoly_left_action_homogeneous pihomogP.
- by [].
- by rewrite ltnS; exact: ltn_ord i.
Qed.

Theorem lazard_F20_conjugate_value_collision p g h :
  lazard_C5_invariant p ->
  msize p <= 5 ->
  g \in QF.standard_F20 -> h \in QF.standard_F20 ->
  (lazard_quintic_permutation g p).@[
      tnth lazard_quintic_cyclic_root_tuple] =
    (lazard_quintic_permutation h p).@[
      tnth lazard_quintic_cyclic_root_tuple].
Proof.
move=> invariant size_p gF hF.
rewrite (lazard_F20_conjugate_low_degree_specializes_to_constant
  invariant size_p gF).
exact: esym (lazard_F20_conjugate_low_degree_specializes_to_constant
  invariant size_p hF).
Qed.

(** A preliminary repeated-value witness for the raw [F20]-indexed family:
    the identity and the nonidentity five-cycle are distinct group elements
    with the same specialized value.  They lie in the same [C5] coset, so
    this lemma alone does *not* establish nonseparability of the relative
    coset resolvent; the multiplier-by-two construction below does. *)
Theorem lazard_raw_F20_repeated_value_witness p :
  lazard_C5_invariant p ->
  msize p <= 5 ->
  exists g h : QF.S5,
    g \in QF.standard_F20 /\
    h \in QF.standard_F20 /\
    g != h /\
    (lazard_quintic_permutation g p).@[
        tnth lazard_quintic_cyclic_root_tuple] =
      (lazard_quintic_permutation h p).@[
        tnth lazard_quintic_cyclic_root_tuple].
Proof.
move=> invariant size_p.
have cycle_ne_one : QF.five_cycle != 1%g.
  apply/eqP=> cycle_one.
  have horder := QF.order_five_cycle.
  by rewrite cycle_one order1 in horder.
exists 1%g, QF.five_cycle; split.
- exact: group1.
- split.
  + exact: QF.five_cycle_mem_standard_F20.
  + split.
    * by rewrite eq_sym.
    * exact: lazard_F20_conjugate_value_collision
        invariant size_p group1 QF.five_cycle_mem_standard_F20.
Qed.

(** The multiplier-by-two element normalizes [C5] but does not belong to
    [C5].  Unlike the five-cycle used in the raw group-indexed witness above,
    it therefore represents a genuinely different coset. *)
Lemma lazard_multiplier_two_not_mem_standard_C5 :
  QF.multiplier_two \notin QF.standard_C5.
Proof.
rewrite -QF.cycle_memberbE /QF.cycle_memberb.
vm_compute.
Qed.

(** The actual right-coset value used by the general resolvent adapter. *)
Definition lazard_C5_specialized_orbit_value
    (p : MP) (C : {set QF.S5}) : F :=
  (@GE.lazard_formal_orbit_value
      F 5 QF.standard_C5 p C).@[
        tnth lazard_quintic_cyclic_root_tuple].

Lemma lazard_C5_specialized_orbit_value_rcoset p
    (invariant : lazard_C5_invariant p) g :
  lazard_C5_specialized_orbit_value p (QF.standard_C5 :* g) =
    (lazard_quintic_permutation g^-1 p).@[
      tnth lazard_quintic_cyclic_root_tuple].
Proof.
have invariant' :
    @GE.lazard_invariant_under F 5 QF.standard_C5 p := invariant.
rewrite /lazard_C5_specialized_orbit_value
  (@GE.lazard_formal_orbit_value_rcoset
    F 5 QF.standard_C5 p invariant' g).
by [].
Qed.

(** The identity coset and the multiplier-by-two coset are distinct members
    of [S5/C5], but every degree-below-five cyclic invariant takes the same
    specialized value on them. *)
Theorem lazard_C5_distinct_coset_value_collision p :
  lazard_C5_invariant p ->
  msize p <= 5 ->
  exists C D : {set QF.S5},
    C \in GC.lazard_right_coset_orbit QF.standard_C5 /\
    D \in GC.lazard_right_coset_orbit QF.standard_C5 /\
    C != D /\
    lazard_C5_specialized_orbit_value p C =
      lazard_C5_specialized_orbit_value p D.
Proof.
move=> invariant size_p.
exists (QF.standard_C5 :* 1%g),
  (QF.standard_C5 :* QF.multiplier_two); split.
- exact: GC.lazard_right_coset_mem.
- split.
  + exact: GC.lazard_right_coset_mem.
  + split.
    * apply/eqP=> cosets_eq.
      have one_mem :
          1%g \in QF.standard_C5 :* QF.multiplier_two :=
        (elimT rcoset_eqP cosets_eq).
      have multiplier_mem : QF.multiplier_two \in QF.standard_C5.
        by move: one_mem; rewrite mem_rcoset mul1g groupV.
      exact: lazard_multiplier_two_not_mem_standard_C5 multiplier_mem.
    * rewrite !lazard_C5_specialized_orbit_value_rcoset // invg1.
      apply: lazard_F20_conjugate_value_collision invariant size_p.
      -- exact: group1.
      -- by rewrite groupV QF.multiplier_two_mem_standard_F20.
Qed.

(** Paper-level conclusion: the literal coset-product relative resolvent is
    nonseparable on the roots of [X^5-alpha^5]. *)
Theorem lazard_C5_low_degree_relative_resolvent_not_separable p :
  lazard_C5_invariant p ->
  msize p <= 5 ->
  ~~ separable_poly
    (GC.lazard_orbit_resolvent QF.standard_C5
      (lazard_C5_specialized_orbit_value p)).
Proof.
move=> invariant size_p.
apply/negP=> separable_resolvent.
have values_injective :
    {in GC.lazard_right_coset_orbit QF.standard_C5 &,
      injective (lazard_C5_specialized_orbit_value p)}.
  apply/dinjectiveP.
  rewrite /dinjectiveb.
  move: separable_resolvent.
  by rewrite /GC.lazard_orbit_resolvent
    /GC.lazard_orbit_value_sequence separable_prod_XsubC.
have [C [D [Cmem [Dmem [Cne values_eq]]]]] :=
  lazard_C5_distinct_coset_value_collision invariant size_p.
apply: Cne.
exact: values_injective Cmem Dmem values_eq.
Qed.

(** ** The literal [S5/D5] relative resolvent *)

(** The paper asserts the degree-five lower bound for invariants of [D5]
    as well as [C5].  Distinct [C5] cosets need not remain distinct modulo
    [D5], so this conclusion needs its own coset calculation. *)
Definition lazard_D5_invariant (p : MP) : Prop :=
  forall s : QF.S5, s \in Class.standard_D5 ->
    lazard_quintic_permutation s p = p.

Lemma lazard_C5_invariant_of_D5_invariant p :
  lazard_D5_invariant p -> lazard_C5_invariant p.
Proof.
move=> invariant s sC.
exact: invariant s (subsetP Class.standard_C5_sub_standard_D5 s sC).
Qed.

Lemma lazard_multiplier_two_not_mem_standard_D5 :
  QF.multiplier_two \notin Class.standard_D5.
Proof. vm_compute. Qed.

Definition lazard_D5_specialized_orbit_value
    (p : MP) (D : {set QF.S5}) : F :=
  (@GE.lazard_formal_orbit_value
      F 5 Class.standard_D5 p D).@[
        tnth lazard_quintic_cyclic_root_tuple].

Lemma lazard_D5_specialized_orbit_value_rcoset p
    (invariant : lazard_D5_invariant p) g :
  lazard_D5_specialized_orbit_value p (Class.standard_D5 :* g) =
    (lazard_quintic_permutation g^-1 p).@[
      tnth lazard_quintic_cyclic_root_tuple].
Proof.
have invariant' :
    @GE.lazard_invariant_under F 5 Class.standard_D5 p := invariant.
rewrite /lazard_D5_specialized_orbit_value
  (@GE.lazard_formal_orbit_value_rcoset
    F 5 Class.standard_D5 p invariant' g).
by [].
Qed.

Lemma lazard_D5_specialized_orbit_value_constant p
    (invariant : lazard_D5_invariant p) g :
  msize p <= 5 ->
  g \in QF.standard_F20 ->
  lazard_D5_specialized_orbit_value p (Class.standard_D5 :* g) =
    (pihomog mdeg 0 p).@[tnth lazard_quintic_cyclic_root_tuple].
Proof.
move=> size_p gF.
rewrite lazard_D5_specialized_orbit_value_rcoset //.
apply: lazard_F20_conjugate_low_degree_specializes_to_constant.
- exact: lazard_C5_invariant_of_D5_invariant invariant.
- exact: size_p.
- by rewrite groupV gF.
Qed.

Theorem lazard_D5_distinct_coset_value_collision p :
  lazard_D5_invariant p ->
  msize p <= 5 ->
  exists C D : {set QF.S5},
    C \in GC.lazard_right_coset_orbit Class.standard_D5 /\
    D \in GC.lazard_right_coset_orbit Class.standard_D5 /\
    C != D /\
    lazard_D5_specialized_orbit_value p C =
      lazard_D5_specialized_orbit_value p D.
Proof.
move=> invariant size_p.
exists (Class.standard_D5 :* 1%g),
  (Class.standard_D5 :* QF.multiplier_two); split.
- exact: GC.lazard_right_coset_mem.
- split.
  + exact: GC.lazard_right_coset_mem.
  + split.
    * apply/eqP=> cosets_eq.
      have one_mem :
          1%g \in Class.standard_D5 :* QF.multiplier_two :=
        (elimT rcoset_eqP cosets_eq).
      have multiplier_mem : QF.multiplier_two \in Class.standard_D5.
        by move: one_mem; rewrite mem_rcoset mul1g groupV.
      exact: lazard_multiplier_two_not_mem_standard_D5 multiplier_mem.
    * rewrite !lazard_D5_specialized_orbit_value_constant //.
      -- exact: group1.
      -- exact: QF.multiplier_two_mem_standard_F20.
Qed.

(** The actual [S5/D5] orbit-product resolvent has a repeated factor on
    every degree-below-five [D5]-invariant at the cyclic binomial tuple. *)
Theorem lazard_D5_low_degree_relative_resolvent_not_separable p :
  lazard_D5_invariant p ->
  msize p <= 5 ->
  ~~ separable_poly
    (GC.lazard_orbit_resolvent Class.standard_D5
      (lazard_D5_specialized_orbit_value p)).
Proof.
move=> invariant size_p.
apply/negP=> separable_resolvent.
have values_injective :
    {in GC.lazard_right_coset_orbit Class.standard_D5 &,
      injective (lazard_D5_specialized_orbit_value p)}.
  apply/dinjectiveP.
  rewrite /dinjectiveb.
  move: separable_resolvent.
  by rewrite /GC.lazard_orbit_resolvent
    /GC.lazard_orbit_value_sequence separable_prod_XsubC.
have [C [D [Cmem [Dmem [Cne values_eq]]]]] :=
  lazard_D5_distinct_coset_value_collision invariant size_p.
apply: Cne.
exact: values_injective Cmem Dmem values_eq.
Qed.

(** Literal counterexample to the paper's unqualified phrase "any invariant
    of degree below five is zero". *)
Theorem lazard_literal_any_low_degree_invariant_zero_counterexample :
  exists p : MP,
    lazard_C5_invariant p /\
    msize p <= 5 /\
    p.@[tnth lazard_quintic_cyclic_root_tuple] != 0.
Proof.
exists 1; split.
- move=> s _.
  by rewrite /lazard_quintic_permutation /IM.mpoly_left_action msym1.
- split.
  + by rewrite msize1.
  + by rewrite meval1 oner_neq0.
Qed.

End LowDegreeSpecialization.

End PolynomialFormulasLazardQuinticLowDegreeSpecialization.
