From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantFiniteFree LazardInvariantMultinomials
  LazardInvariantSymmetricModule LazardInvariantArtinSuccessor
  LazardInvariantSubgroupModule LazardInvariantSubgroupReynolds
  LazardInvariantSubgroupTheoremTwo LazardInvariantLeadingTermDescent
  LazardDisplayedGroebnerGeneralOrderInterface
  LazardDisplayedGroebnerGeneralOrderPort.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Arbitrary-degree, arbitrary-field literal form of Lazard's Lemma 2.

    The intrinsic Reynolds theorem uses the recursively constructed reverse
    Artin basis.  The printed displayed family uses the opposite staircase
    orientation.  We conjugate the subgroup by the reversal, construct the
    Reynolds generators there, and transport them back by the honest left
    permutation action.  Thus the final generators belong to the originally
    named subgroup; no reversal-normality premise is used.

    For every transported generator this file constructs, rather than asks
    for, its unique literal standard [J]-remainder, its whole-top-row
    constant certificate, and its actual combined leading monomial.  The
    only algebraic hypothesis is the one genuinely used by Reynolds
    averaging: the image of the subgroup order in the field is nonzero. *)
Module PolynomialFormulasLazardDisplayedLeadingTermDescentGeneralBridge.

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

(** Keep the field and arity visible at every boundary in this bridge.  The
    port itself declares them implicit, but this file simultaneously uses
    several polynomial rings whose coefficient types are themselves
    polynomial rings, so spelling the parameters out avoids ambiguous
    inference. *)
Arguments OP.paper_artin_exponent F n a : clear implicits.
Arguments OP.paper_artin_coordinate F n q a : clear implicits.
Arguments OP.formal_artin_remainder F n q : clear implicits.
Arguments OP.formal_specialization F n p : clear implicits.

Section LiteralCoordinates.

Variables (F : fieldType) (n : nat).

Local Notation Coeff := {mpoly F[n]}.
Local Notation Ambient := {mpoly Coeff[n]}.
Local Notation RootRing := {mpoly F[n]}.
Local Notation ReverseArtin :=
  (FF.ffd_index
    (@AS.lazard_reverse_artin_finite_free_decomposition F n)).

(** Reversal only permutes coordinates and therefore preserves total root
    degree.  This replaces the old fixed-quintic finite computation. *)
Lemma paper_artin_root_degreeE (a : ReverseArtin) :
  mdeg (OP.paper_artin_exponent F n a) =
    @AS.lazard_reverse_artin_degree F n a.
Proof.
rewrite /AS.lazard_reverse_artin_degree !mdegE
  /OP.paper_artin_exponent.
under [LHS] eq_bigr=> i _ do rewrite mnmE.
under [LHS] eq_bigr=> i _ do
  rewrite -(@OP.paper_reverse_perm_invE n i).
by rewrite [RHS](reindex_perm (OP.paper_reverse_perm n)^-1).
Qed.

(** Coefficient extraction at a staircase monomial returns exactly the
    canonical paper Artin coordinate. *)
Lemma formal_artin_remainder_coefficient
    (q : RootRing) (a : ReverseArtin) :
  (OP.formal_artin_remainder F n q) @_
      (OP.paper_artin_exponent F n a) =
    OP.paper_artin_coordinate F n q a.
Proof.
rewrite /OP.formal_artin_remainder raddf_sum (bigD1 a) //=.
rewrite mcoeffZ mcoeffX eqxx mulr1.
rewrite big1 ?addr0 // => b hba.
rewrite mcoeffZ mcoeffX.
have hne : OP.paper_artin_exponent F n b !=
    OP.paper_artin_exponent F n a.
  apply/negP=> /eqP heq.
  have hba' : b = a := @OP.paper_artin_exponent_injective F n b a heq.
  by move: hba; rewrite hba' eqxx.
by rewrite (negbTE hne) mulr0.
Qed.

(** Every outer support exponent of the formal Artin remainder is one of
    the printed staircase exponents. *)
Lemma formal_artin_remainder_outer_support_index
    (q : RootRing) (u : 'X_{1..n}) :
  u \in msupp (OP.formal_artin_remainder F n q) ->
  exists a : ReverseArtin, OP.paper_artin_exponent F n a = u.
Proof.
move=> hu.
have hstandard := @OP.formal_artin_remainder_paper_standard F n q.
exact: @OP.paper_artin_exponent_complete F n u (hstandard u hu).
Qed.

(** A complete literal normal-form package in the fixed root orientation. *)
Record fixed_orientation_leading_normal_form
    (q : RootRing) (d : nat) : Prop := {
  folnf_standard :
    OI.literal_standard F n (OP.formal_artin_remainder F n q);
  folnf_specializes :
    OP.formal_specialization F n (OP.formal_artin_remainder F n q) = q;
  folnf_unique : forall s : Ambient,
    OI.literal_standard F n s ->
    OI.literal_displayed_ideal F n
      (OP.formal_artin_remainder F n q - s) ->
    s = OP.formal_artin_remainder F n q;
  folnf_rows_above_zero : forall a : ReverseArtin,
    (d < mdeg (OP.paper_artin_exponent F n a))%N ->
    (OP.formal_artin_remainder F n q) @_
      (OP.paper_artin_exponent F n a) = 0;
  folnf_top_row_constant : forall j : 'I_(#|ReverseArtin|),
    mdeg (OP.paper_artin_exponent F n (enum_val j)) = d ->
    exists r : F,
      (OP.formal_artin_remainder F n q)
        @_ (OP.paper_artin_exponent F n (enum_val j)) = r%:MP;
  folnf_top_row_nonzero :
    exists (j : 'I_(#|ReverseArtin|)) (r : F),
      mdeg (OP.paper_artin_exponent F n (enum_val j)) = d /\
      r != 0 /\
      (OP.formal_artin_remainder F n q)
        @_ (OP.paper_artin_exponent F n (enum_val j)) = r%:MP
}.

(** The displayed three-row record implies the literal whole-top-row
    combined-support certificate used by the arbitrary-order interface. *)
Theorem fixed_orientation_literal_top_row_constant
    (q : RootRing) (d : nat) :
  fixed_orientation_leading_normal_form q d ->
  @OI.literal_top_row_constant F n (OP.formal_artin_remainder F n q) d.
Proof.
move=> hnormal; constructor.
- move=> [u v] huv.
  have hu : u \in msupp (OP.formal_artin_remainder F n q) :=
    OP.combined_support_outer_support huv.
  have [a ha] := formal_artin_remainder_outer_support_index hu.
  rewrite /OI.combined_root_degree /= leqNgt; apply/negP=> hdu.
  have hdu' : (d < mdeg (OP.paper_artin_exponent F n a))%N.
    move: hdu; by rewrite ha.
  have hzero := folnf_rows_above_zero hnormal (a := a) hdu'.
  apply: huv.
  by rewrite /OI.combined_coefficient /= -ha hzero mcoeff0.
- have [j [r [hdegree [hr0 hr]]]] := folnf_top_row_nonzero hnormal.
  exists (OP.paper_artin_exponent F n (enum_val j), 0%MM); split.
  + rewrite /OI.combined_support /OI.combined_coefficient /= hr
      mcoeffC eqxx mulr1.
    move=> hrzero; move: hr0.
    by rewrite hrzero eqxx.
  + by split.
- move=> [u v] huv hdegree.
  have hdegreeu : mdeg u = d.
    move: hdegree; by rewrite /OI.combined_root_degree /=.
  have hu : u \in msupp (OP.formal_artin_remainder F n q) :=
    OP.combined_support_outer_support huv.
  have [a ha] := formal_artin_remainder_outer_support_index hu.
  pose j := enum_rank a.
  have hj : enum_val j = a := enum_rankK a.
  have hdegree' :
      mdeg (OP.paper_artin_exponent F n (enum_val j)) = d.
    by rewrite hj ha; exact: hdegreeu.
  have [r hr] := folnf_top_row_constant hnormal (j := j) hdegree'.
  have huv' : (r%:MP : Coeff) @_ v <> 0.
    move: huv.
    by rewrite /OI.combined_support /OI.combined_coefficient /= -ha -hj hr.
  apply: (OP.base_mpolyC_support_zero
    (F := F) (n := n) (c := r) (u := v)).
  rewrite mcoeff_msupp; apply/negP=> /eqP hv0.
  exact: huv' hv0.
Qed.

(** Actual finite-support maximum for every constructive paper order. *)
Theorem fixed_orientation_actual_combined_leading
    (O : OI.admissible_monomial_order n)
    (HO : OI.paper_order_hypotheses O)
    (C : OP.decidable_admissible_order O)
    (q : RootRing) (d : nat)
    (N : fixed_orientation_leading_normal_form q d) :
  OI.is_leading_monomial O (OP.formal_artin_remainder F n q)
      (OP.combined_leading_monomial C (OP.formal_artin_remainder F n q)) /\
  OI.combined_root_degree
      (OP.combined_leading_monomial C
        (OP.formal_artin_remainder F n q)) = d /\
  (OP.combined_leading_monomial C
      (OP.formal_artin_remainder F n q)).2 = 0%MM.
Proof.
have htop := fixed_orientation_literal_top_row_constant N.
have hp0 : OP.formal_artin_remainder F n q <> 0.
  move=> hpzero.
  have [a [ha _]] := OI.ltr_top_exists htop.
  rewrite hpzero in ha.
  exact: OI.combined_zero_not_support ha.
have hlead := OP.combined_leading_monomialP C hp0.
have hshape :=
  OI.leading_monomial_root_degree_and_coefficient_part_zero
    HO htop hlead.
exact: conj hlead hshape.
Qed.

(** Exact full Lemma-2 block-order version. *)
Theorem fixed_orientation_actual_combined_leading_paper_order
    (O : OI.admissible_monomial_order n)
    (HO : OI.paper_lemma_two_order_hypotheses O)
    (C : OP.decidable_admissible_order O)
    (q : RootRing) (d : nat)
    (N : fixed_orientation_leading_normal_form q d) :
  OI.is_leading_monomial O (OP.formal_artin_remainder F n q)
      (OP.combined_leading_monomial C (OP.formal_artin_remainder F n q)) /\
  OI.combined_root_degree
      (OP.combined_leading_monomial C
        (OP.formal_artin_remainder F n q)) = d /\
  (OP.combined_leading_monomial C
      (OP.formal_artin_remainder F n q)).2 = 0%MM.
Proof.
refine (@fixed_orientation_actual_combined_leading
  O _ C q d N).
exact: OI.plto_lemma_one_order HO.
Qed.

End LiteralCoordinates.

Section IntrinsicToDisplayed.

Variables (F : fieldType) (n : nat) (H : {group 'S_n}).
Hypothesis cardH_neq0 : (#|[subg H]|%:R : F) != 0.

Local Notation Coeff := {mpoly F[n]}.
Local Notation RootRing := {mpoly F[n]}.
Local Notation Inv := (SIM.lazard_subgroup_invariant_module F H).
Local Notation Artin :=
  (SIM.lazard_ambient_artin_homogeneous_decomposition F n).
Local Notation B := (FF.hffd_free Artin).
Local Notation degree := (FF.hffd_degree Artin).
Local Notation ReverseArtin :=
  (FF.ffd_index
    (@AS.lazard_reverse_artin_finite_free_decomposition F n)).
Local Notation artin_coeff :=
  (T2.lazard_invariant_artin_coeff
    (F := F) (H := H)).

Definition paper_oriented_root_polynomial (p : Inv) : RootRing :=
  msym (OP.paper_reverse_perm n) (SIM.lazard_subgroup_invariant_val p).

Lemma paper_artin_coordinate_oriented (p : Inv) (a : ReverseArtin) :
  OP.paper_artin_coordinate F n (paper_oriented_root_polynomial p) a =
    artin_coeff p a.
Proof.
rewrite /OP.paper_artin_coordinate /paper_oriented_root_polynomial
  /T2.lazard_invariant_artin_coeff.
by rewrite -msymMm mulgV msym1m.
Qed.

Lemma paper_artin_root_degree_artinE (a : ReverseArtin) :
  mdeg (OP.paper_artin_exponent F n a) = degree a.
Proof.
exact: (@paper_artin_root_degreeE F n a).
Qed.

(** Intrinsic Reynolds leading descent transports to the literal unique
    displayed remainder of the paper-oriented polynomial. *)
Theorem intrinsic_leading_normal_form_displayed (p : Inv) d :
  LT.lazard_paper_leading_normal_form
      (F := F) (H := H) p d ->
  fixed_orientation_leading_normal_form
    (paper_oriented_root_polynomial p) d.
Proof.
move=> hp; constructor.
- exact: OP.formal_artin_remainder_literal_standard.
- exact: OP.formal_specialization_formal_artin_remainder.
- move=> s hs hclass.
  have hzero := OP.literal_standard_displayed_ideal_zero
    (OP.literal_standardB
      (OP.formal_artin_remainder_literal_standard
        (q := paper_oriented_root_polynomial p)) hs) hclass.
  have heq : OP.formal_artin_remainder F n
      (paper_oriented_root_polynomial p) = s.
    have hadd := congr1 (fun z => z + s) hzero.
    by move: hadd; rewrite subrK add0r.
  by rewrite heq.
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
  exists j, r; split.
  + by rewrite paper_artin_root_degree_artinE.
  + split; first exact: hr0.
    by rewrite formal_artin_remainder_coefficient
      paper_artin_coordinate_oriented.
Qed.

End IntrinsicToDisplayed.

(** * Removal of reversal for arbitrary degree and field *)
Section FixedOrientationSubgroup.

Variables (F : fieldType) (n : nat) (H : {group 'S_n}).
Hypothesis cardH_neq0 : (#|[subg H]|%:R : F) != 0.

Local Notation Coeff := {mpoly F[n]}.
Local Notation TargetInv :=
  (SIM.lazard_subgroup_invariant_module F H).

Definition paper_reorientation : 'S_n :=
  ((OP.paper_reverse_perm n)^-1)%g.

Definition paper_source_subgroup : {group 'S_n} :=
  H :^ paper_reorientation.

Definition paper_source_card_neq0 :
    (#|[subg paper_source_subgroup]|%:R : F) != 0.
Proof.
move: cardH_neq0.
by rewrite /paper_source_subgroup !cardsT !card_sub cardJg.
Defined.

Local Notation SourceH := paper_source_subgroup.
Local Notation SourceInv :=
  (SIM.lazard_subgroup_invariant_module F SourceH).
Local Notation SourceModule :=
  (SIM.PolynomialFormulasLazardInvariantSubgroupModule_lazard_subgroup_invariant_module__canonical__GRing_Lmodule
    F SourceH).
Local Notation TargetModule :=
  (SIM.PolynomialFormulasLazardInvariantSubgroupModule_lazard_subgroup_invariant_module__canonical__GRing_Lmodule
    F H).
Local Notation SourceIndex :=
  (T2.lazard_theorem_two_index F SourceH).
Local Notation source_generator :=
  (T2.lazard_theorem_two_generator
    (F := F) (H := SourceH)).
Local Notation source_degree :=
  (T2.lazard_theorem_two_degree
    (F := F) (H := SourceH)).

Definition paper_reoriented_value (p : SourceInv) :
    SM.symmetric_polynomial_module F n :=
  SM.symmetric_mpoly_left_action paper_reorientation
    (SIM.lazard_subgroup_invariant_val p).

Lemma paper_reoriented_value_invariant (p : SourceInv) :
  paper_reoriented_value p
    \in SIM.lazard_subgroup_invariant_pred (F := F) H.
Proof.
apply/SIM.lazard_subgroup_invariantP=> g.
pose hval := (sgval g) ^ paper_reorientation.
have hh : hval \in SourceH.
  rewrite /SourceH /paper_source_subgroup /hval memJ_conjg.
  exact: subgP g.
pose h : [subg SourceH] := subg SourceH hval.
have hE : sgval h = hval := subgK hval hh.
have hp := SIM.lazard_subgroup_invariant_val_fixed p h.
rewrite /paper_reoriented_value -SM.symmetric_mpoly_left_actionM.
have hgt : sgval g * paper_reorientation =
    paper_reorientation * sgval h.
  by rewrite hE /hval conjgE mulgA mulgV mul1g.
by rewrite hgt SM.symmetric_mpoly_left_actionM hp.
Qed.

Definition paper_reoriented_invariant (p : SourceInv) : TargetInv :=
  @SIM.LazardSubgroupInvariant F n H
    (paper_reoriented_value p) (paper_reoriented_value_invariant p).

Lemma paper_reoriented_invariant_val (p : SourceInv) :
  SIM.lazard_subgroup_invariant_val (paper_reoriented_invariant p) =
    paper_reoriented_value p.
Proof. reflexivity. Qed.

Definition paper_unoriented_value (p : TargetInv) :
    SM.symmetric_polynomial_module F n :=
  SM.symmetric_mpoly_left_action (paper_reorientation^-1)%g
    (SIM.lazard_subgroup_invariant_val p).

Lemma paper_unoriented_value_invariant (p : TargetInv) :
  paper_unoriented_value p
    \in SIM.lazard_subgroup_invariant_pred (F := F) SourceH.
Proof.
apply/SIM.lazard_subgroup_invariantP=> h.
pose gval := (sgval h) ^ (paper_reorientation^-1)%g.
have hg : gval \in H.
  move: (subgP h).
  by rewrite /SourceH /paper_source_subgroup mem_conjg /gval.
pose g : [subg H] := subg H gval.
have gE : sgval g = gval := subgK gval hg.
have hp := SIM.lazard_subgroup_invariant_val_fixed p g.
rewrite /paper_unoriented_value -SM.symmetric_mpoly_left_actionM.
have hgt : sgval h * (paper_reorientation^-1)%g =
    (paper_reorientation^-1)%g * sgval g.
  by rewrite gE /gval conjgE mulgA mulgV mul1g.
by rewrite hgt SM.symmetric_mpoly_left_actionM hp.
Qed.

Definition paper_unoriented_invariant (p : TargetInv) : SourceInv :=
  @SIM.LazardSubgroupInvariant F n SourceH
    (paper_unoriented_value p) (paper_unoriented_value_invariant p).

Lemma paper_unoriented_invariant_val (p : TargetInv) :
  SIM.lazard_subgroup_invariant_val (paper_unoriented_invariant p) =
    paper_unoriented_value p.
Proof. reflexivity. Qed.

Lemma paper_reoriented_unorientedK (p : TargetInv) :
  paper_reoriented_invariant (paper_unoriented_invariant p) = p.
Proof.
apply: SIM.lazard_subgroup_invariant_val_injective.
by rewrite paper_reoriented_invariant_val /paper_reoriented_value
  paper_unoriented_invariant_val /paper_unoriented_value
  -SM.symmetric_mpoly_left_actionM mulgV
  SM.symmetric_mpoly_left_action1.
Qed.

Lemma paper_unoriented_reorientedK (p : SourceInv) :
  paper_unoriented_invariant (paper_reoriented_invariant p) = p.
Proof.
apply: SIM.lazard_subgroup_invariant_val_injective.
by rewrite paper_unoriented_invariant_val /paper_unoriented_value
  paper_reoriented_invariant_val /paper_reoriented_value
  -SM.symmetric_mpoly_left_actionM mulVg
  SM.symmetric_mpoly_left_action1.
Qed.

Lemma paper_reoriented_invariant_injective :
  injective paper_reoriented_invariant.
Proof.
move=> p q hpq.
have h := congr1 paper_unoriented_invariant hpq.
by rewrite !paper_unoriented_reorientedK in h.
Qed.

Fact paper_reoriented_invariant_is_linear :
  forall (a : Coeff) (p q : SourceInv),
    paper_reoriented_invariant (@GRing.scale Coeff SourceModule a p + q) =
      @GRing.scale Coeff TargetModule a (paper_reoriented_invariant p) +
        paper_reoriented_invariant q.
Proof.
move=> a p q.
apply: SIM.lazard_subgroup_invariant_val_injective.
rewrite !paper_reoriented_invariant_val /paper_reoriented_value /=.
by rewrite SM.symmetric_mpoly_left_actionD
  SM.symmetric_mpoly_left_actionZ.
Qed.

Definition paper_reoriented_invariant_linear :
    {linear SourceModule -> TargetModule} :=
  HB.pack paper_reoriented_invariant
    (GRing.isLinear.Build Coeff SourceModule TargetModule *:%R
      paper_reoriented_invariant paper_reoriented_invariant_is_linear).

Lemma paper_reoriented_invariant_linearE p :
  paper_reoriented_invariant_linear p = paper_reoriented_invariant p.
Proof. reflexivity. Qed.

Definition fixed_orientation_index : finType := SourceIndex.

Definition fixed_orientation_degree
    (g : fixed_orientation_index) : nat := source_degree g.

Definition fixed_orientation_generator
    (g : fixed_orientation_index) : TargetInv :=
  paper_reoriented_invariant (source_generator g).

Lemma fixed_orientation_generator_degree_le
    (g : fixed_orientation_index) :
  (fixed_orientation_degree g <= IM.lazard_degree_bound n)%N.
Proof.
exact: T2.lazard_theorem_two_generator_degree_le.
Qed.

Lemma fixed_orientation_generator_homogeneous
    (g : fixed_orientation_index) :
  SIM.lazard_invariant_homogeneous (fixed_orientation_generator g)
    (fixed_orientation_degree g).
Proof.
rewrite /SIM.lazard_invariant_homogeneous
  /fixed_orientation_generator paper_reoriented_invariant_val
  /paper_reoriented_value.
apply: SM.symmetric_mpoly_left_action_homogeneous.
exact: (T2.lazard_theorem_two_generator_homogeneous
  paper_source_card_neq0 g).
Qed.

Lemma fixed_orientation_generator_valE
    (g : fixed_orientation_index) :
  SIM.lazard_subgroup_invariant_val (fixed_orientation_generator g) =
    @paper_oriented_root_polynomial F n SourceH (source_generator g).
Proof.
by rewrite /fixed_orientation_generator
  paper_reoriented_invariant_val /paper_reoriented_value
  /paper_oriented_root_polynomial /paper_reorientation
  /SM.symmetric_mpoly_left_action /IM.mpoly_left_action invgK.
Qed.

Theorem fixed_orientation_generator_leading_normal_form
    (g : fixed_orientation_index) :
  fixed_orientation_leading_normal_form
    (SIM.lazard_subgroup_invariant_val (fixed_orientation_generator g))
    (fixed_orientation_degree g).
Proof.
rewrite fixed_orientation_generator_valE.
apply: (@intrinsic_leading_normal_form_displayed
  F n SourceH (source_generator g) (fixed_orientation_degree g)).
exact: (LT.lazard_theorem_two_generator_leading_normal_form
  (F := F) (n := n) (H := SourceH)
  paper_source_card_neq0 g).
Qed.

(** The actual leading monomial of every internally constructed generator,
    under the complete paper Lemma-2 block-order hypotheses. *)
Theorem fixed_orientation_generator_actual_combined_leading
    (O : OI.admissible_monomial_order n)
    (HO : OI.paper_lemma_two_order_hypotheses O)
    (C : OP.decidable_admissible_order O)
    (g : fixed_orientation_index) :
  let q := SIM.lazard_subgroup_invariant_val
      (fixed_orientation_generator g) in
  OI.is_leading_monomial O (OP.formal_artin_remainder F n q)
      (OP.combined_leading_monomial C (OP.formal_artin_remainder F n q)) /\
  OI.combined_root_degree
      (OP.combined_leading_monomial C
        (OP.formal_artin_remainder F n q)) =
        fixed_orientation_degree g /\
  (OP.combined_leading_monomial C
      (OP.formal_artin_remainder F n q)).2 = 0%MM.
Proof.
simpl.
apply: fixed_orientation_actual_combined_leading_paper_order.
- exact: HO.
- exact: fixed_orientation_generator_leading_normal_form g.
Qed.

Theorem fixed_orientation_generators_span (p : TargetInv) :
  exists c : fixed_orientation_index -> Coeff,
    p = \sum_g c g *: (fixed_orientation_generator g : TargetModule).
Proof.
have [_ hspan] := LT.lazard_paper_lemma_two_proved
  (F := F) (H := SourceH) paper_source_card_neq0.
have [c hc] := hspan (paper_unoriented_invariant p).
exists c.
have hc' : paper_unoriented_invariant p =
    \sum_g @GRing.scale Coeff SourceModule
      (c g) (source_generator g) := hc.
have hmapped := congr1 paper_reoriented_invariant_linear hc'.
rewrite linear_sum in hmapped.
have hsum :
    \sum_g paper_reoriented_invariant_linear
      (@GRing.scale Coeff SourceModule (c g) (source_generator g)) =
    \sum_g @GRing.scale Coeff TargetModule (c g)
      (paper_reoriented_invariant_linear (source_generator g)).
  apply: eq_bigr => g _.
  exact: (GRing.linearZZ paper_reoriented_invariant_linear
    (c g) (source_generator g)).
rewrite hsum in hmapped.
rewrite !paper_reoriented_invariant_linearE
  paper_reoriented_unorientedK in hmapped.
exact: hmapped.
Qed.

(** Reorientation preserves the linear independence proved by the internally
    constructed Theorem-2 family.  Thus the family used by the literal
    Lemma-2 endpoint is an actual basis, not merely an advertised spanning
    list. *)
Theorem fixed_orientation_generators_independent
    (c : fixed_orientation_index -> Coeff) :
  (\sum_g c g *: (fixed_orientation_generator g : TargetModule) = 0) ->
  forall g, c g = 0.
Proof.
move=> hzero.
apply: (T2.lazard_theorem_two_independent
  (F := F) (n := n) (H := SourceH)
  paper_source_card_neq0 (c := c)).
apply: paper_reoriented_invariant_injective.
rewrite /T2.lazard_theorem_two_reconstruct.
change (paper_reoriented_invariant_linear
    (\sum_g c g *: (source_generator g : SourceModule)) =
  paper_reoriented_invariant_linear 0).
rewrite linear_sum linear0.
have hsum :
    \sum_g paper_reoriented_invariant_linear
      (@GRing.scale Coeff SourceModule (c g) (source_generator g)) =
    \sum_g @GRing.scale Coeff TargetModule (c g)
      (fixed_orientation_generator g).
  apply: eq_bigr => g _.
  rewrite (GRing.linearZZ paper_reoriented_invariant_linear
    (c g) (source_generator g)).
  by rewrite paper_reoriented_invariant_linearE
    /fixed_orientation_generator.
rewrite hsum.
exact: hzero.
Qed.

Theorem fixed_orientation_generators_coefficients_unique
    (c e : fixed_orientation_index -> Coeff) :
  (\sum_g c g *: (fixed_orientation_generator g : TargetModule) =
    \sum_g e g *: (fixed_orientation_generator g : TargetModule)) ->
  forall g, c g = e g.
Proof.
move=> hce g.
  have hzero :
    \sum_i (c i - e i) *:
      (fixed_orientation_generator i : TargetModule) = 0.
  under [LHS] eq_bigr => i _ do rewrite scalerBl.
  rewrite big_split hce.
  rewrite sumrN.
  exact: addrN _.
have hg := fixed_orientation_generators_independent hzero g.
have hadd := congr1 (fun z => z + e g) hg.
by move: hadd; rewrite subrK add0r.
Qed.

(** Corrected arbitrary-degree, fixed-subgroup, fixed-variable-orientation
    Lemma 2.  The first conjunct supplies the literal unique normal forms;
    the second is generation over the full symmetric coefficient ring. *)
Definition fixed_orientation_paper_lemma_two : Prop :=
  (forall g : fixed_orientation_index,
    (fixed_orientation_degree g <= IM.lazard_degree_bound n)%N /\
    SIM.lazard_invariant_homogeneous (fixed_orientation_generator g)
      (fixed_orientation_degree g) /\
    fixed_orientation_leading_normal_form
      (SIM.lazard_subgroup_invariant_val (fixed_orientation_generator g))
      (fixed_orientation_degree g)) /\
  (forall p : TargetInv, exists c : fixed_orientation_index -> Coeff,
    p = \sum_g c g *: (fixed_orientation_generator g : TargetModule)).

Theorem fixed_orientation_paper_lemma_two_proved :
  fixed_orientation_paper_lemma_two.
Proof.
split.
- move=> g; split.
  + exact: fixed_orientation_generator_degree_le.
  + split.
    * exact: fixed_orientation_generator_homogeneous.
    * exact: fixed_orientation_generator_leading_normal_form.
- exact: fixed_orientation_generators_span.
Qed.

(** One theorem combining the finite homogeneous generating family, its
    internally derived unique [J]-normal forms, and the actual leading term
    for a chosen complete paper block order. *)
Definition fixed_orientation_paper_lemma_two_for_order
    (O : OI.admissible_monomial_order n)
    (HO : OI.paper_lemma_two_order_hypotheses O)
    (C : OP.decidable_admissible_order O) : Prop :=
  (forall g : fixed_orientation_index,
    (fixed_orientation_degree g <= IM.lazard_degree_bound n)%N /\
    SIM.lazard_invariant_homogeneous (fixed_orientation_generator g)
      (fixed_orientation_degree g) /\
    fixed_orientation_leading_normal_form
      (SIM.lazard_subgroup_invariant_val (fixed_orientation_generator g))
      (fixed_orientation_degree g) /\
    let q := SIM.lazard_subgroup_invariant_val
        (fixed_orientation_generator g) in
    OI.is_leading_monomial O (OP.formal_artin_remainder F n q)
        (OP.combined_leading_monomial C
          (OP.formal_artin_remainder F n q)) /\
    OI.combined_root_degree
        (OP.combined_leading_monomial C
          (OP.formal_artin_remainder F n q)) =
          fixed_orientation_degree g /\
    (OP.combined_leading_monomial C
        (OP.formal_artin_remainder F n q)).2 = 0%MM) /\
  (forall p : TargetInv, exists c : fixed_orientation_index -> Coeff,
    p = \sum_g c g *: (fixed_orientation_generator g : TargetModule)).

Theorem fixed_orientation_paper_lemma_two_for_order_proved
    (O : OI.admissible_monomial_order n)
    (HO : OI.paper_lemma_two_order_hypotheses O)
    (C : OP.decidable_admissible_order O) :
  fixed_orientation_paper_lemma_two_for_order HO C.
Proof.
split.
- move=> g; split.
  + exact: fixed_orientation_generator_degree_le.
  + split.
    * exact: fixed_orientation_generator_homogeneous.
    * split.
      -- exact: fixed_orientation_generator_leading_normal_form.
      -- exact: fixed_orientation_generator_actual_combined_leading HO C g.
- exact: fixed_orientation_generators_span.
Qed.

(** Prop-valued exact block-order endpoint.  Unlike the executable wrapper
    above, this statement does not require a decision procedure for the
    caller's monomial order.  Finite support and admissibility construct a
    leading monomial propositionally; the internally proved whole-top-row
    normal form then shows that every such leading monomial has the stated
    root degree and contains no formal [e] variable. *)
Definition fixed_orientation_paper_lemma_two_for_arbitrary_order
    (O : OI.admissible_monomial_order n)
    (HO : OI.paper_lemma_two_order_hypotheses O) : Prop :=
  (forall g : fixed_orientation_index,
    (fixed_orientation_degree g <= IM.lazard_degree_bound n)%N /\
    SIM.lazard_invariant_homogeneous (fixed_orientation_generator g)
      (fixed_orientation_degree g) /\
    fixed_orientation_leading_normal_form
      (SIM.lazard_subgroup_invariant_val (fixed_orientation_generator g))
      (fixed_orientation_degree g) /\
    exists a : OI.combined_monomial n,
      OI.is_leading_monomial O
        (OP.formal_artin_remainder F n
          (SIM.lazard_subgroup_invariant_val
            (fixed_orientation_generator g))) a /\
      OI.combined_root_degree a = fixed_orientation_degree g /\
      a.2 = 0%MM) /\
  (forall p : TargetInv, exists c : fixed_orientation_index -> Coeff,
    p = \sum_g c g *: (fixed_orientation_generator g : TargetModule)).

Theorem fixed_orientation_paper_lemma_two_for_arbitrary_order_proved
    (O : OI.admissible_monomial_order n)
    (HO : OI.paper_lemma_two_order_hypotheses O) :
  fixed_orientation_paper_lemma_two_for_arbitrary_order HO.
Proof.
split.
- move=> g; split.
  + exact: fixed_orientation_generator_degree_le.
  + split.
    * exact: fixed_orientation_generator_homogeneous.
    * split.
      -- exact: fixed_orientation_generator_leading_normal_form.
      -- pose q := SIM.lazard_subgroup_invariant_val
           (fixed_orientation_generator g).
         have hnormal : fixed_orientation_leading_normal_form q
             (fixed_orientation_degree g) :=
           fixed_orientation_generator_leading_normal_form g.
         have htop := fixed_orientation_literal_top_row_constant hnormal.
         have hq0 : OP.formal_artin_remainder F n q <> 0.
           move=> hzero.
           have [a [ha _]] := OI.ltr_top_exists htop.
           rewrite hzero in ha.
           exact: OI.combined_zero_not_support ha.
         have [a hlead] := OI.cls_leading_exists
           (OP.combined_leading_selection_of_order
             F (n := n) O)
           (p := OP.formal_artin_remainder F n q) hq0.
         exists a; split; first exact: hlead.
         exact: (@OI.leading_monomial_of_paper_lemma_two_order
           F n O HO (OP.formal_artin_remainder F n q)
           (fixed_orientation_degree g) a htop hlead).
- exact: fixed_orientation_generators_span.
Qed.

(** Strongest basis-shaped Prop endpoint.  The first conjunct is the exact
    arbitrary-order literal Lemma 2 above; the second records linear
    independence of the same finite family.  Together with its spanning
    conjunct this is the full internally constructed homogeneous basis
    assertion, without a caller-supplied basis or coefficient certificate. *)
Definition fixed_orientation_paper_lemma_two_basis_for_arbitrary_order
    (O : OI.admissible_monomial_order n)
    (HO : OI.paper_lemma_two_order_hypotheses O) : Prop :=
  fixed_orientation_paper_lemma_two_for_arbitrary_order HO /\
  (forall c : fixed_orientation_index -> Coeff,
    (\sum_g c g *: (fixed_orientation_generator g : TargetModule) = 0) ->
    forall g, c g = 0).

Theorem fixed_orientation_paper_lemma_two_basis_for_arbitrary_order_proved
    (O : OI.admissible_monomial_order n)
    (HO : OI.paper_lemma_two_order_hypotheses O) :
  fixed_orientation_paper_lemma_two_basis_for_arbitrary_order HO.
Proof.
split.
- exact: fixed_orientation_paper_lemma_two_for_arbitrary_order_proved.
- exact: fixed_orientation_generators_independent.
Qed.

End FixedOrientationSubgroup.

End PolynomialFormulasLazardDisplayedLeadingTermDescentGeneralBridge.
