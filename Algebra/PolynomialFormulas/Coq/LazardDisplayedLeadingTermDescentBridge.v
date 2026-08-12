From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantSymmetricModule LazardInvariantLeadingTermDescent
  LazardDisplayedGroebnerGeneralOrderInterface
  LazardDisplayedGroebnerGeneralOrderPort
  LazardDisplayedGroebnerQuintic.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The literal displayed-quintic form of Lazard's leading-term descent.

    [LazardInvariantLeadingTermDescent] proves Lemma 2 in the reverse Artin
    basis used by the homogeneous Reynolds construction.  The displayed
    quintic file uses the same basis after reversing the five root variables
    so that its exponent staircase has the orientation printed in Lazard's
    paper.  This file proves that the two coordinate functions agree under
    that reversal and transports all three leading-row clauses to the actual
    formal [formal_artin_remainder].

    Consequently the top nonzero coefficient of the unique paper-standard
    displayed-[J] representative is literally [r%:MP]: it contains no formal
    [e] variables.  No normal-form or leading-coefficient certificate is
    accepted from a caller. *)
Module PolynomialFormulasLazardDisplayedLeadingTermDescentBridge.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module SM := PolynomialFormulasLazardInvariantSymmetricModule.
Module AS := PolynomialFormulasLazardInvariantArtinSuccessor.
Module SIM := PolynomialFormulasLazardInvariantSubgroupModule.
Module SR := PolynomialFormulasLazardInvariantSubgroupReynolds.
Module T2 := PolynomialFormulasLazardInvariantSubgroupTheoremTwo.
Module LT := PolynomialFormulasLazardInvariantLeadingTermDescent.
Module OI := PolynomialFormulasLazardDisplayedGroebnerGeneralOrderInterface.
Module OP := PolynomialFormulasLazardDisplayedGroebnerGeneralOrderPort.
Module D := PolynomialFormulasLazardDisplayedGroebnerQuintic.

Local Notation Coeff := {mpoly rat[5]}.
Local Notation Ambient := {mpoly Coeff[5]}.
Local Notation RootRing := {mpoly rat[5]}.
Local Notation ReverseArtin :=
  (FF.ffd_index
    (@AS.lazard_reverse_artin_finite_free_decomposition rat 5)).

(** Reversing the root variables preserves total root degree.  Since this is
    the fixed family of 120 quintic Artin indices, the equality is checked by
    proof-producing finite computation, just like the staircase and
    injectivity checks in the displayed-basis file. *)
Definition paper_artin_degree_check : bool :=
  [forall a : ReverseArtin,
    mdeg (D.paper_artin_exponent a) ==
      @AS.lazard_reverse_artin_degree rat 5 a].

Lemma paper_artin_degree_checkP : paper_artin_degree_check.
Proof. vm_compute. Qed.

Lemma paper_artin_root_degreeE (a : ReverseArtin) :
  mdeg (D.paper_artin_exponent a) =
    @AS.lazard_reverse_artin_degree rat 5 a.
Proof.
have /forallP h := paper_artin_degree_checkP.
exact/eqP: h a.
Qed.

(** The coefficient of a staircase monomial in the literal formal Artin
    remainder is its canonical paper Artin coordinate. *)
Lemma formal_artin_remainder_coefficient
    (q : RootRing) (a : ReverseArtin) :
  D.formal_artin_remainder q @_ D.paper_artin_exponent a =
    D.paper_artin_coordinate q a.
Proof.
rewrite /D.formal_artin_remainder raddf_sum (bigD1 a) //=.
rewrite mcoeffZ mcoeffX eqxx mulr1.
rewrite big1 ?addr0 // => b hba.
rewrite mcoeffZ mcoeffX.
have hne : D.paper_artin_exponent b != D.paper_artin_exponent a.
  apply/negP=> /eqP heq.
  have hba' : b = a := D.paper_artin_exponent_injective heq.
  by move: hba; rewrite hba' eqxx.
by rewrite (negbTE hne) mulr0.
Qed.

(** Every outer/root support exponent of the canonical formal remainder is
    one of the paper-oriented Artin staircase exponents. *)
Lemma formal_artin_remainder_outer_support_index
    (q : RootRing) (u : 'X_{1..5}) :
  u \in msupp (D.formal_artin_remainder q) ->
  exists a : ReverseArtin, D.paper_artin_exponent a = u.
Proof.
move=> hu.
have hstandard := D.formal_artin_remainder_standard q.
move/D.paper_standardP: hstandard=> hstandard.
pose a := D.artin_index_of_standard u (hstandard u hu).
exists (D.reverse_index_of_artin a).
rewrite D.reverse_index_of_artinE /a.
exact: D.artin_exponent_of_standardE.
Qed.

Section QuinticSubgroup.

Variable (H : {group 'S_5}).
Hypothesis cardH_neq0 : (#|[subg H]|%:R : rat) != 0.

Local Notation S := {mpoly rat[5]}.
Local Notation Inv := (SIM.lazard_subgroup_invariant_module rat H).
Local Notation Artin :=
  (SIM.lazard_ambient_artin_homogeneous_decomposition rat 5).
Local Notation B := (FF.hffd_free Artin).
Local Notation degree := (FF.hffd_degree Artin).
Local Notation bound :=
  (PolynomialFormulasLazardInvariantMultinomials.lazard_degree_bound 5).
Local Notation Index :=
  (T2.lazard_theorem_two_index
    (F := rat) (H := H) (cardH_neq0 := cardH_neq0)).
Local Notation generator :=
  (T2.lazard_theorem_two_generator
    (F := rat) (H := H) (cardH_neq0 := cardH_neq0)).
Local Notation generator_degree :=
  (T2.lazard_theorem_two_degree
    (F := rat) (H := H) (cardH_neq0 := cardH_neq0)).
Local Notation artin_coeff :=
  (T2.lazard_invariant_artin_coeff
    (F := rat) (H := H) (cardH_neq0 := cardH_neq0)).

(** Put the reverse Artin basis into the paper's displayed root-variable
    orientation. *)
Definition paper_oriented_root_polynomial (p : Inv) : RootRing :=
  msym D.paper_reverse_perm (SIM.lazard_subgroup_invariant_val p).

(** The paper Artin coordinate of the oriented polynomial is definitionally
    the intrinsic Artin coefficient used by Lemma 2, after cancelling the
    two inverse root permutations. *)
Lemma paper_artin_coordinate_oriented (p : Inv) (a : ReverseArtin) :
  D.paper_artin_coordinate (paper_oriented_root_polynomial p) a =
    artin_coeff p a.
Proof.
rewrite /D.paper_artin_coordinate /paper_oriented_root_polynomial
  /T2.lazard_invariant_artin_coeff.
by rewrite -msymMm mulgV msym1m.
Qed.

Lemma paper_artin_root_degree_artinE (a : ReverseArtin) :
  mdeg (D.paper_artin_exponent a) = degree a.
Proof.
rewrite paper_artin_root_degreeE.
exact: erefl.
Qed.

(** The exact formal displayed-ring conclusion corresponding to Lazard's
    [lazard_paper_leading_normal_form].  The coefficient assertions refer to
    the actual outer monomial coefficients of [formal_artin_remainder], not
    merely to an abstract coordinate family. *)
Record quintic_displayed_leading_normal_form (p : Inv) (d : nat) : Prop := {
  quintic_displayed_remainder_standard :
    D.paper_standard
      (D.formal_artin_remainder (paper_oriented_root_polynomial p));
  quintic_displayed_remainder_specializes :
    D.formal_specialization
      (D.formal_artin_remainder (paper_oriented_root_polynomial p)) =
      paper_oriented_root_polynomial p;
  quintic_displayed_remainder_unique : forall s : Ambient,
    D.paper_standard s ->
    D.generated_by D.displayed_J
      (D.formal_artin_remainder (paper_oriented_root_polynomial p) - s) ->
    s = D.formal_artin_remainder (paper_oriented_root_polynomial p);
  quintic_displayed_rows_above_zero : forall a : ReverseArtin,
    d < mdeg (D.paper_artin_exponent a) ->
    D.formal_artin_remainder (paper_oriented_root_polynomial p)
        @_ D.paper_artin_exponent a = 0;
  quintic_displayed_top_row_constant : forall j : 'I_(#|ReverseArtin|),
    mdeg (D.paper_artin_exponent (enum_val j)) = d ->
    exists r : rat,
      D.formal_artin_remainder (paper_oriented_root_polynomial p)
          @_ D.paper_artin_exponent (enum_val j) = r%:MP;
  quintic_displayed_top_row_nonzero :
    exists (j : 'I_(#|ReverseArtin|)) (r : rat),
      mdeg (D.paper_artin_exponent (enum_val j)) = d /\
      r != 0 /\
      D.formal_artin_remainder (paper_oriented_root_polynomial p)
          @_ D.paper_artin_exponent (enum_val j) = r%:MP
}.

(** The fixed-orientation version of the same displayed certificate.  Its
    subject is an ordinary root polynomial [q], with no hidden permutation
    in any field.  This is the record needed for the literal fixed-subgroup
    statement of Lemma 2. *)
Record quintic_fixed_orientation_leading_normal_form
    (q : RootRing) (d : nat) : Prop := {
  quintic_fixed_orientation_remainder_standard :
    D.paper_standard (D.formal_artin_remainder q);
  quintic_fixed_orientation_remainder_specializes :
    D.formal_specialization (D.formal_artin_remainder q) = q;
  quintic_fixed_orientation_remainder_unique : forall s : Ambient,
    D.paper_standard s ->
    D.generated_by D.displayed_J (D.formal_artin_remainder q - s) ->
    s = D.formal_artin_remainder q;
  quintic_fixed_orientation_rows_above_zero : forall a : ReverseArtin,
    d < mdeg (D.paper_artin_exponent a) ->
    D.formal_artin_remainder q @_ D.paper_artin_exponent a = 0;
  quintic_fixed_orientation_top_row_constant :
    forall j : 'I_(#|ReverseArtin|),
      mdeg (D.paper_artin_exponent (enum_val j)) = d ->
      exists r : rat,
        D.formal_artin_remainder q
          @_ D.paper_artin_exponent (enum_val j) = r%:MP;
  quintic_fixed_orientation_top_row_nonzero :
    exists (j : 'I_(#|ReverseArtin|)) (r : rat),
      mdeg (D.paper_artin_exponent (enum_val j)) = d /\
      r != 0 /\
      D.formal_artin_remainder q
        @_ D.paper_artin_exponent (enum_val j) = r%:MP
}.

(** Intrinsic Lemma-2 leading descent transports to the literal unique
    displayed-[J] normal representative. *)
Theorem lazard_paper_leading_normal_form_displayed (p : Inv) d :
  LT.lazard_paper_leading_normal_form
      (F := rat) (H := H) cardH_neq0 p d ->
  quintic_displayed_leading_normal_form p d.
Proof.
move=> hp.
constructor.
- exact: D.formal_artin_remainder_standard.
- exact: D.formal_specialization_formal_artin_remainder.
- move=> s hs hclass.
  apply: (D.paper_standard_remainders_unique
    (p := D.formal_artin_remainder (paper_oriented_root_polynomial p))
    (r := s)
    (s := D.formal_artin_remainder (paper_oriented_root_polynomial p))).
  + exact: hs.
  + exact: D.formal_artin_remainder_standard.
  + exact: hclass.
  + rewrite subrr.
    exact: D.generated_by0.
- move=> a hdegree.
  rewrite formal_artin_remainder_coefficient
    paper_artin_coordinate_oriented.
  apply: (LT.lazard_leading_rows_above_zero hp).
  by rewrite -paper_artin_root_degree_artinE.
- move=> j hdegree.
  have hdegree' : degree (enum_val j) = d.
    by rewrite -paper_artin_root_degree_artinE.
  have [r hr] := LT.lazard_leading_top_row_constant hp hdegree'.
  exists r.
  by rewrite formal_artin_remainder_coefficient
    paper_artin_coordinate_oriented.
- have [j [r [hdegree [hr0 hr]]]] :=
    LT.lazard_leading_top_row_nonzero hp.
  exists j, r.
  split.
  + by rewrite paper_artin_root_degree_artinE.
  + split; first exact: hr0.
    by rewrite formal_artin_remainder_coefficient
      paper_artin_coordinate_oriented.
Qed.

(** Forgetting the historical presentation of the record exposes that its
    actual subject is the relabelled root polynomial. *)
Lemma quintic_displayed_leading_normal_form_fixed_orientation
    (p : Inv) d :
  quintic_displayed_leading_normal_form p d ->
  quintic_fixed_orientation_leading_normal_form
    (paper_oriented_root_polynomial p) d.
Proof.
move=> [hstandard hspecializes hunique habove hconstant hnonzero].
constructor.
- exact: hstandard.
- exact: hspecializes.
- exact: hunique.
- exact: habove.
- exact: hconstant.
- exact: hnonzero.
Qed.

(** Fixed-degree displayed package for the canonical quintic invariant basis:
    every generator has the unique standard formal representative above, and
    the same family spans all invariants over the symmetric coefficient ring. *)
Definition quintic_displayed_paper_lemma_two : Prop :=
  (forall g : Index,
    quintic_displayed_leading_normal_form
      (generator g) (generator_degree g)) /\
  (forall p : Inv, exists c : Index -> S,
    p = \sum_g c g *: generator g).

Theorem quintic_displayed_paper_lemma_two_proved :
  quintic_displayed_paper_lemma_two.
Proof.
split.
- move=> g.
  apply: lazard_paper_leading_normal_form_displayed.
  exact: LT.lazard_theorem_two_generator_leading_normal_form.
- move=> p.
  have [_ hspan] := LT.lazard_paper_lemma_two_proved
    (F := rat) (H := H) cardH_neq0.
  exact: hspan p.
Qed.

End QuinticSubgroup.

(** The displayed three-row certificate implies the order-free literal
    combined-support certificate used by the arbitrary-order interface. *)
Theorem quintic_fixed_orientation_literal_top_row_constant
    (q : RootRing) (d : nat) :
  quintic_fixed_orientation_leading_normal_form q d ->
  @OI.literal_top_row_constant rat 5
    (D.formal_artin_remainder q) d.
Proof.
move=> hnormal.
constructor.
- move=> [u v] huv.
  have hu : u \in msupp (D.formal_artin_remainder q) :=
    OP.combined_support_outer_support huv.
  have [a ha] := formal_artin_remainder_outer_support_index hu.
  rewrite /OI.combined_root_degree /=.
  rewrite leqNgt; apply/negP=> hdu.
  have hzero :=
    quintic_fixed_orientation_rows_above_zero hnormal a (by
      move: hdu; by rewrite ha).
  apply: huv.
  by rewrite /OI.combined_coefficient /= -ha hzero mcoeff0.
- have [j [r [hdegree [hr0 hr]]]] :=
    quintic_fixed_orientation_top_row_nonzero hnormal.
  exists (D.paper_artin_exponent (enum_val j), 0%MM).
  split.
  + rewrite /OI.combined_support /OI.combined_coefficient /= hr
      mcoeffC eqxx mulr1.
    move=> hrzero.
    move: hr0.
    by rewrite hrzero eqxx.
  + split.
    * exact: hdegree.
    * exact: erefl.
- move=> [u v] huv hdegree.
  have hdegreeu : mdeg u = d.
    move: hdegree.
    by rewrite /OI.combined_root_degree /=.
  have hu : u \in msupp (D.formal_artin_remainder q) :=
    OP.combined_support_outer_support huv.
  have [a ha] := formal_artin_remainder_outer_support_index hu.
  pose j := enum_rank a.
  have hj : enum_val j = a := enum_rankK a.
  have hdegree' :
      mdeg (D.paper_artin_exponent (enum_val j)) = d.
    by rewrite hj ha; exact: hdegreeu.
  have [r hr] :=
    quintic_fixed_orientation_top_row_constant hnormal j hdegree'.
  have huv' : (r%:MP : Coeff) @_ v <> 0.
    move: huv.
    by rewrite /OI.combined_support /OI.combined_coefficient /= -ha -hj hr.
  apply: (OP.base_mpolyC_support_zero (F := rat) (n := 5)).
  rewrite mcoeff_msupp.
  apply/negP=> /eqP hv0.
  exact: huv' hv0.
Qed.

(** The selected monomial is the actual maximum of the finite combined
    support.  It has root degree [d] and no formal-[e] component for every
    decidable admissible paper order.  No equal-degree tie-break hypothesis
    is needed because the whole top row is already constant. *)
Theorem quintic_fixed_orientation_actual_combined_leading
    (O : OI.admissible_monomial_order 5)
    (HO : OI.paper_order_hypotheses O)
    (C : OP.decidable_admissible_order O)
    (q : RootRing) (d : nat)
    (N : quintic_fixed_orientation_leading_normal_form q d) :
  OI.is_leading_monomial O (D.formal_artin_remainder q)
      (OP.combined_leading_monomial C (D.formal_artin_remainder q)) /\
  OI.combined_root_degree
      (OP.combined_leading_monomial C (D.formal_artin_remainder q)) = d /\
  (OP.combined_leading_monomial C
      (D.formal_artin_remainder q)).2 = 0%MM.
Proof.
have htop := quintic_fixed_orientation_literal_top_row_constant N.
have hp0 : D.formal_artin_remainder q <> 0.
  move=> hpzero.
  have [a [ha _]] := OI.ltr_top_exists htop.
  rewrite hpzero in ha.
  exact: (OI.combined_zero_not_support a) ha.
have hlead := OP.combined_leading_monomialP C hp0.
have hshape :=
  OI.leading_monomial_root_degree_and_coefficient_part_zero
    HO htop hlead.
exact: conj hlead hshape.
Qed.

(** * Removal of the reversal from the fixed-subgroup conclusion

    Put [t = paper_reverse_perm^-1].  The displayed polynomial attached to
    a source generator is

      [msym paper_reverse_perm p = t . p]

    for the honest left action.  Therefore one must construct the source
    generators for [H :^ t], not for [H].  Acting by [t] then transports
    them into the literal [H]-fixed module.  Conversely, acting by [t^-1]
    transports every [H]-invariant into the source module.  The two maps
    are inverse and linear over the symmetric coefficient ring, so both the
    displayed normal-form property and the spanning equation transport.

    No hypothesis that [H] is normalized by the reversal is used. *)
Section FixedOrientationQuinticSubgroup.

Variable (H : {group 'S_5}).

(** The group element whose honest left action is the [msym] reversal used
    by the displayed Artin basis. *)
Definition paper_reorientation : 'S_5 :=
  (D.paper_reverse_perm^-1)%g.

(** Reynolds generators are first constructed for this conjugate. *)
Definition paper_source_subgroup : {group 'S_5} :=
  H :^ paper_reorientation.

(** Over [rat], the Reynolds denominator for the conjugate subgroup is
    automatically nonzero.  In particular this does not require a
    reversal-normality hypothesis on [H]. *)
Definition paper_source_card_neq0 :
    (#|[subg paper_source_subgroup]|%:R : rat) != 0 :=
  SR.lazard_subgroup_card_neq0_of_pchar0
    paper_source_subgroup (pchar_num rat).

Local Notation SourceH := paper_source_subgroup.
Local Notation SourceInv :=
  (SIM.lazard_subgroup_invariant_module rat SourceH).
Local Notation TargetInv :=
  (SIM.lazard_subgroup_invariant_module rat H).
Local Notation SourceIndex :=
  (T2.lazard_theorem_two_index
    (F := rat) (H := SourceH)
    (cardH_neq0 := paper_source_card_neq0)).
Local Notation source_generator :=
  (T2.lazard_theorem_two_generator
    (F := rat) (H := SourceH)
    (cardH_neq0 := paper_source_card_neq0)).
Local Notation source_degree :=
  (T2.lazard_theorem_two_degree
    (F := rat) (H := SourceH)
    (cardH_neq0 := paper_source_card_neq0)).

(** Relabel a source invariant into the original variable orientation. *)
Definition paper_reoriented_value (p : SourceInv) :
    SM.symmetric_polynomial_module rat 5 :=
  SM.symmetric_mpoly_left_action paper_reorientation
    (SIM.lazard_subgroup_invariant_val p).

(** Explicit action orientation: an element [g] of [H] becomes [g^t] in
    [H :^ t], and [g*t = t*(g^t)]. *)
Lemma paper_reoriented_value_invariant (p : SourceInv) :
  paper_reoriented_value p
    \in SIM.lazard_subgroup_invariant_pred (F := rat) H.
Proof.
apply/SIM.lazard_subgroup_invariantP=> g.
pose hval := (sgval g) ^ paper_reorientation.
have hh : hval \in SourceH.
  rewrite /SourceH /paper_source_subgroup /hval memJ_conjg.
  exact: subgP g.
pose h : [subg SourceH] := subg hval.
have hE : sgval h = hval := subgK hh.
have hp := SIM.lazard_subgroup_invariant_val_fixed p h.
rewrite /paper_reoriented_value -SM.symmetric_mpoly_left_actionM.
have hgt : sgval g * paper_reorientation =
    paper_reorientation * sgval h.
  by rewrite hE /hval conjgE mulgA mulgV mul1g.
rewrite hgt SM.symmetric_mpoly_left_actionM hp.
Qed.

(** The relabelled polynomial, bundled in the literal [H]-fixed module. *)
Definition paper_reoriented_invariant (p : SourceInv) : TargetInv :=
  @SIM.LazardSubgroupInvariant rat 5 H
    (paper_reoriented_value p) (paper_reoriented_value_invariant p).

Lemma paper_reoriented_invariant_val (p : SourceInv) :
  SIM.lazard_subgroup_invariant_val (paper_reoriented_invariant p) =
    paper_reoriented_value p.
Proof. reflexivity. Qed.

(** Conversely, undo the relabelling on an [H]-invariant. *)
Definition paper_unoriented_value (p : TargetInv) :
    SM.symmetric_polynomial_module rat 5 :=
  SM.symmetric_mpoly_left_action (paper_reorientation^-1)%g
    (SIM.lazard_subgroup_invariant_val p).

(** Explicit reverse orientation: membership in [H :^ t] is equivalent to
    membership of [h^(t^-1)] in [H], and
    [h*t^-1 = t^-1*(h^(t^-1))]. *)
Lemma paper_unoriented_value_invariant (p : TargetInv) :
  paper_unoriented_value p
    \in SIM.lazard_subgroup_invariant_pred (F := rat) SourceH.
Proof.
apply/SIM.lazard_subgroup_invariantP=> h.
pose gval := (sgval h) ^ (paper_reorientation^-1)%g.
have hg : gval \in H.
  move: (subgP h).
  by rewrite /SourceH /paper_source_subgroup mem_conjg /gval.
pose g : [subg H] := subg gval.
have gE : sgval g = gval := subgK hg.
have hp := SIM.lazard_subgroup_invariant_val_fixed p g.
rewrite /paper_unoriented_value -SM.symmetric_mpoly_left_actionM.
have hgt : sgval h * (paper_reorientation^-1)%g =
    (paper_reorientation^-1)%g * sgval g.
  by rewrite gE /gval conjgE mulgA mulgV mul1g.
rewrite hgt SM.symmetric_mpoly_left_actionM hp.
Qed.

Definition paper_unoriented_invariant (p : TargetInv) : SourceInv :=
  @SIM.LazardSubgroupInvariant rat 5 SourceH
    (paper_unoriented_value p) (paper_unoriented_value_invariant p).

Lemma paper_unoriented_invariant_val (p : TargetInv) :
  SIM.lazard_subgroup_invariant_val (paper_unoriented_invariant p) =
    paper_unoriented_value p.
Proof. reflexivity. Qed.

(** Reorientation followed by unorientation is the identity on the
    originally labelled invariant module. *)
Lemma paper_reoriented_unorientedK (p : TargetInv) :
  paper_reoriented_invariant (paper_unoriented_invariant p) = p.
Proof.
apply: SIM.lazard_subgroup_invariant_val_injective.
rewrite paper_reoriented_invariant_val paper_unoriented_invariant_val
  /paper_reoriented_value /paper_unoriented_value
  -SM.symmetric_mpoly_left_actionM mulgV
  SM.symmetric_mpoly_left_action1.
Qed.

(** The transport is linear over the full symmetric-polynomial coefficient
    ring. *)
Fact paper_reoriented_invariant_is_linear :
  linear paper_reoriented_invariant.
Proof.
move=> a p q.
apply: SIM.lazard_subgroup_invariant_val_injective.
rewrite !paper_reoriented_invariant_val /paper_reoriented_value /=.
by rewrite SM.symmetric_mpoly_left_actionD
  SM.symmetric_mpoly_left_actionZ.
Qed.

Definition paper_reoriented_invariant_linear :
    {linear SourceInv -> TargetInv} :=
  HB.pack paper_reoriented_invariant
    (GRing.isLinear.Build Coeff SourceInv TargetInv *:%R
      paper_reoriented_invariant paper_reoriented_invariant_is_linear).

Lemma paper_reoriented_invariant_linearE p :
  paper_reoriented_invariant_linear p = paper_reoriented_invariant p.
Proof. reflexivity. Qed.

(** The transported finite generator family in the original subgroup and
    original root-variable orientation. *)
Definition quintic_fixed_orientation_index : finType := SourceIndex.

Definition quintic_fixed_orientation_degree
    (g : quintic_fixed_orientation_index) : nat := source_degree g.

Definition quintic_fixed_orientation_generator
    (g : quintic_fixed_orientation_index) : TargetInv :=
  paper_reoriented_invariant (source_generator g).

(** Its underlying root polynomial is exactly the polynomial appearing in
    the displayed normal-form certificate, not merely an equal polynomial
    for a differently named action. *)
Lemma quintic_fixed_orientation_generator_valE
    (g : quintic_fixed_orientation_index) :
  SIM.lazard_subgroup_invariant_val
      (quintic_fixed_orientation_generator g) =
    @paper_oriented_root_polynomial SourceH (source_generator g).
Proof.
rewrite /quintic_fixed_orientation_generator
  paper_reoriented_invariant_val /paper_reoriented_value
  /paper_oriented_root_polynomial /paper_reorientation
  /SM.symmetric_mpoly_left_action /IM.mpoly_left_action invgK.
Qed.

(** Each transported generator has the displayed Lemma-2 certificate in
    the literal fixed orientation. *)
Theorem quintic_fixed_orientation_generator_leading_normal_form
    (g : quintic_fixed_orientation_index) :
  quintic_fixed_orientation_leading_normal_form
    (SIM.lazard_subgroup_invariant_val
      (quintic_fixed_orientation_generator g))
    (quintic_fixed_orientation_degree g).
Proof.
rewrite quintic_fixed_orientation_generator_valE.
apply: quintic_displayed_leading_normal_form_fixed_orientation.
apply: lazard_paper_leading_normal_form_displayed.
exact: LT.lazard_theorem_two_generator_leading_normal_form.
Qed.

(** Actual-leading-monomial corollary for the transported generator.  The
    conjugate-subgroup construction above has already put the polynomial in
    the literal [H]-fixed orientation, so this theorem performs no second
    reversal and no second [msym] action. *)
Theorem quintic_fixed_orientation_generator_actual_combined_leading
    (O : OI.admissible_monomial_order 5)
    (HO : OI.paper_order_hypotheses O)
    (C : OP.decidable_admissible_order O)
    (g : quintic_fixed_orientation_index) :
  let q := SIM.lazard_subgroup_invariant_val
      (quintic_fixed_orientation_generator g) in
  OI.is_leading_monomial O (D.formal_artin_remainder q)
      (OP.combined_leading_monomial C (D.formal_artin_remainder q)) /\
  OI.combined_root_degree
      (OP.combined_leading_monomial C (D.formal_artin_remainder q)) =
        quintic_fixed_orientation_degree g /\
  (OP.combined_leading_monomial C
      (D.formal_artin_remainder q)).2 = 0%MM.
Proof.
simpl.
apply: quintic_fixed_orientation_actual_combined_leading.
exact: quintic_fixed_orientation_generator_leading_normal_form.
Qed.

(** Every invariant for the originally named subgroup is spanned by the
    transported generators, over the same symmetric coefficient ring. *)
Theorem quintic_fixed_orientation_generators_span (p : TargetInv) :
  exists c : quintic_fixed_orientation_index -> Coeff,
    p = \sum_g c g *: quintic_fixed_orientation_generator g.
Proof.
have [_ hspan] := LT.lazard_paper_lemma_two_proved
  (F := rat) (H := SourceH) paper_source_card_neq0.
have [c hc] := hspan (paper_unoriented_invariant p).
exists c.
have hmapped := congr1 paper_reoriented_invariant_linear hc.
rewrite linear_sum in hmapped.
under [RHS] eq_bigr => g _ do
  rewrite linearZ !paper_reoriented_invariant_linearE.
rewrite !paper_reoriented_invariant_linearE
  paper_reoriented_unorientedK in hmapped.
exact: hmapped.
Qed.

(** Correct fixed-subgroup, fixed-variable-orientation quintic specialization
    of Lazard's Lemma 2 over the rationals. *)
Definition quintic_fixed_orientation_paper_lemma_two : Prop :=
  (forall g : quintic_fixed_orientation_index,
    quintic_fixed_orientation_leading_normal_form
      (SIM.lazard_subgroup_invariant_val
        (quintic_fixed_orientation_generator g))
      (quintic_fixed_orientation_degree g)) /\
  (forall p : TargetInv, exists c : quintic_fixed_orientation_index -> Coeff,
    p = \sum_g c g *: quintic_fixed_orientation_generator g).

Theorem quintic_fixed_orientation_paper_lemma_two_proved :
  quintic_fixed_orientation_paper_lemma_two.
Proof.
split.
- exact: quintic_fixed_orientation_generator_leading_normal_form.
- exact: quintic_fixed_orientation_generators_span.
Qed.

End FixedOrientationQuinticSubgroup.

End PolynomialFormulasLazardDisplayedLeadingTermDescentBridge.
