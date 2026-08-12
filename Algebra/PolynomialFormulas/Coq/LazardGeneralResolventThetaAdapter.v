From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  QuinticThetaValues LazardGeneralResolventExplicit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * The concrete Frobenius--Dummit sextic is Lazard's generic resolvent

    The generic Coq adapter uses right cosets and assigns to [G :* x] the
    formal conjugate [mpoly_left_action x^-1 theta].  The concrete quintic
    development indexes its six values by the inverse representatives
    [(representative i)^-1].  These conventions agree exactly: the right
    coset corresponding to index [i] is

      [standard_F20 :* (representative i)^-1].

    This file constructs the actual ten-term multivariate polynomial,
    proves its exact stabilizer, enumerates those six right cosets without
    duplication, identifies every specialized generic orbit value with the
    existing [quintic_theta_value], and reindexes the full product.  The
    final theorem therefore identifies scalar extension of the generic
    paper-facing ordered resolvent with [quintic_scalar_resolvent]; no
    equality of resolvents is supplied as a certificate. *)
Module PolynomialFormulasLazardGeneralResolventThetaAdapter.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module F20 := PolynomialFormulasQuinticF20Data.
Module TO := PolynomialFormulasQuinticThetaOrbit.
Module TV := PolynomialFormulasQuinticThetaValues.
Module GC := PolynomialFormulasLazardGeneralResolventCriterion.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module Explicit := PolynomialFormulasLazardGeneralResolventExplicit.

Local Notation S5 := F20.S5.

(** ** The table-backed multivariate theta polynomial *)

(** Convert a displayed five-tuple of exponents to the multinomial index
    used by [mathcomp.multinomials]. *)
Definition quintic_exponent_monomial
    (d : F20.quintic_exponent) : 'X_{1..5} :=
  [multinom tnth d i | i < 5].

(** The sum of coefficient-one monomials attached to an arbitrary exponent
    table.  Keeping this definition table-backed makes the connection with
    [quintic_table_value] literal. *)
Definition quintic_table_mpoly (K : fieldType)
    (table : seq F20.quintic_exponent) : {mpoly K[5]} :=
  \sum_(d <- table) 'X_[K, quintic_exponent_monomial d].

(** Dummit's ten-term quartic invariant over an arbitrary field. *)
Definition lazard_theta_invariant (K : fieldType) : {mpoly K[5]} :=
  quintic_table_mpoly K F20.theta_exponent_table.

(** Coefficient change preserves the table-backed polynomial literally. *)
Lemma map_quintic_table_mpoly
    (K E : fieldType) (f : {rmorphism K -> E}) table :
  map_mpoly f (quintic_table_mpoly K table) =
    quintic_table_mpoly E table.
Proof.
rewrite /quintic_table_mpoly raddf_sum.
by apply: eq_bigr=> d _; rewrite map_mpolyX.
Qed.

Lemma map_lazard_theta_invariant
    (K E : fieldType) (f : {rmorphism K -> E}) :
  map_mpoly f (lazard_theta_invariant K) = lazard_theta_invariant E.
Proof. exact: map_quintic_table_mpoly. Qed.

(** Evaluation of the table polynomial is exactly the independently defined
    scalar table value.  In particular this proves all coefficient-change
    compatibility from definitions. *)
Lemma quintic_table_mpoly_specialize
    (K E : fieldType) (embed : {rmorphism K -> E})
    (roots : 5.-tuple E) table :
  @Explicit.lazard_mpoly_specialize K E 5 embed roots
      (quintic_table_mpoly K table) =
    TV.quintic_table_value roots table.
Proof.
rewrite Explicit.lazard_mpoly_specializeE
  /quintic_table_mpoly /TV.quintic_table_value.
rewrite !raddf_sum /=.
apply: eq_bigr=> d _.
rewrite map_mpolyX mevalX /TV.quintic_monomial_value.
apply: eq_bigr=> i _.
by rewrite /quintic_exponent_monomial mnmE.
Qed.

(** Naturality lemmas used when the ordered-root wrapper bundles roots in a
    subfield subtype and we later forget that bundling. *)
Lemma map_quintic_monomial_value
    (K E : fieldType) (f : {rmorphism K -> E})
    (roots : 5.-tuple K) d :
  f (TV.quintic_monomial_value roots d) =
    TV.quintic_monomial_value (map_tuple f roots) d.
Proof.
rewrite /TV.quintic_monomial_value rmorph_prod.
apply: eq_bigr=> i _.
by rewrite rmorphX tnth_map.
Qed.

Lemma map_quintic_table_value
    (K E : fieldType) (f : {rmorphism K -> E})
    (roots : 5.-tuple K) table :
  f (TV.quintic_table_value roots table) =
    TV.quintic_table_value (map_tuple f roots) table.
Proof.
rewrite /TV.quintic_table_value raddf_sum.
by apply: eq_bigr=> d _; rewrite map_quintic_monomial_value.
Qed.

Lemma map_quintic_theta_value
    (K E : fieldType) (f : {rmorphism K -> E})
    (roots : 5.-tuple K) i :
  f (TV.quintic_theta_value roots i) =
    TV.quintic_theta_value (map_tuple f roots) i.
Proof. exact: map_quintic_table_value. Qed.

Lemma map_quintic_scalar_resolvent
    (K E : fieldType) (f : {rmorphism K -> E})
    (roots : 5.-tuple K) :
  map_poly f (TV.quintic_scalar_resolvent roots) =
    TV.quintic_scalar_resolvent (map_tuple f roots).
Proof.
rewrite !TV.quintic_scalar_resolvent_index_product
  /TV.quintic_scalar_resolvent_by_index rmorph_prod /=.
apply: eq_bigr=> i _.
by rewrite rmorphB /= map_polyX map_polyC /= map_quintic_theta_value.
Qed.

(** ** Exact stabilizer, first over [rat] and then after scalar extension *)

Definition theta_rat_stabilizer_check : bool :=
  [forall s : S5,
    (IM.mpoly_left_action s (lazard_theta_invariant rat) ==
      lazard_theta_invariant rat) == (s \in F20.standard_F20)].

(** Closed finite computation of the stabilizer of the actual polynomial.
    [vm_compute] reduces the explicit 120-element permutation calculation in
    the kernel; it is not an axiom or an external oracle. *)
Lemma theta_rat_stabilizer_checkP : theta_rat_stabilizer_check.
Proof. vm_compute. Qed.

Theorem theta_rat_exact_stabilizer :
  @Explicit.lazard_invariant_stabilizer_exact rat 5
    F20.standard_F20 (lazard_theta_invariant rat).
Proof.
move=> s.
have /eqP hs := forallP theta_rat_stabilizer_checkP s.
split.
- move=> hp; rewrite -hs; exact/eqP: hp.
- move=> hsF; apply/eqP; rewrite hs; exact: hsF.
Qed.

(** Injectivity of coefficient change for multivariate polynomials. *)
Lemma map_mpoly_injective
    (K E : fieldType) (f : {rmorphism K -> E}) :
  injective (map_mpoly f : {mpoly K[5]} -> {mpoly E[5]}).
Proof.
move=> p q hpq; apply/mpolyP=> m.
apply: (fmorph_inj f).
move: (congr1 (fun r : {mpoly E[5]} => r@_m) hpq).
by rewrite !mcoeff_map_mpoly.
Qed.

(** Any rational coefficient embedding transports the exact stabilizer.
    This is the form used for the base-subfield coefficient type of the
    paper-facing ordered resolver. *)
Theorem lazard_theta_exact_stabilizer
    (K : fieldType) (ratrK : {rmorphism rat -> K}) :
  @Explicit.lazard_invariant_stabilizer_exact K 5
    F20.standard_F20 (lazard_theta_invariant K).
Proof.
move=> s; split.
- move=> hs.
  apply: (proj1 (theta_rat_exact_stabilizer s)).
  apply: (map_mpoly_injective ratrK).
  rewrite Explicit.map_mpoly_left_action
    !map_lazard_theta_invariant.
  exact: hs.
- move=> hsF.
  have hsrat := proj2 (theta_rat_exact_stabilizer s) hsF.
  rewrite -(@map_lazard_theta_invariant rat K ratrK)
    -Explicit.map_mpoly_left_action hsrat.
  exact: erefl.
Qed.

(** ** Orientation on the six inverse representatives *)

(** Closed table checking the orientation of all six representatives. *)
Definition theta_rat_representative_action_check : bool :=
  [forall i : 'I_6,
    IM.mpoly_left_action (F20.representative i)
        (lazard_theta_invariant rat) ==
      quintic_table_mpoly rat
        (F20.theta_table_image ((F20.representative i)^-1))].

Lemma theta_rat_representative_action_checkP :
  theta_rat_representative_action_check.
Proof. vm_compute. Qed.

(** Over [rat], the left action of a displayed representative turns the
    theta table into the table acted on by the inverse representative.  This
    finite statement is the precise bridge between [mpoly_left_action] and
    [act_exponent]. *)
Lemma theta_rat_left_action_representative (i : 'I_6) :
  IM.mpoly_left_action (F20.representative i)
      (lazard_theta_invariant rat) =
    quintic_table_mpoly rat
      (F20.theta_table_image ((F20.representative i)^-1)).
Proof.
exact/eqP: (forallP theta_rat_representative_action_checkP i).
Qed.

(** The same identity over every field reached from [rat]. *)
Lemma theta_left_action_representative
    (K : fieldType) (ratrK : {rmorphism rat -> K}) (i : 'I_6) :
  IM.mpoly_left_action (F20.representative i)
      (lazard_theta_invariant K) =
    quintic_table_mpoly K
      (F20.theta_table_image ((F20.representative i)^-1)).
Proof.
have h := congr1 (map_mpoly ratrK)
  (theta_rat_left_action_representative i).
move: h.
by rewrite Explicit.map_mpoly_left_action
  map_lazard_theta_invariant map_quintic_table_mpoly.
Qed.

(** Index [i] denotes the right coset represented by the inverse of the
    displayed left-coset representative. *)
Definition theta_right_coset (i : 'I_6) : {set S5} :=
  F20.standard_F20 :* (F20.representative i)^-1.

Lemma theta_right_coset_mem i :
  theta_right_coset i \in
    GC.lazard_right_coset_orbit F20.standard_F20.
Proof. exact: GC.lazard_right_coset_mem. Qed.

Lemma theta_right_coset_injective : injective theta_right_coset.
Proof.
move=> i j hij.
have hmem : (F20.representative i)^-1 \in
    F20.standard_F20 :* (F20.representative j)^-1.
  apply/rcoset_eqP.
  exact: hij.
move/rcosetP: hmem=> [a ha hia].
have hsame : F20.same_left_cosetb
    (F20.representative i) (F20.representative j).
  rewrite /F20.same_left_cosetb hia mulgA mulgV mulg1.
  exact: ha.
have hdistinct := forallP
  (forallP F20.representative_cosets_distinct i) j.
have hijb : i == j by move: hdistinct; rewrite hsame /=.
exact/eqP.
Qed.

(** Every right coset has the orientation-correct inverse representative. *)
Lemma theta_right_coset_onto C :
  C \in GC.lazard_right_coset_orbit F20.standard_F20 ->
  exists i : 'I_6, theta_right_coset i = C.
Proof.
case/rcosetsP=> x _ ->.
pose i := F20.representative_index x^-1.
have hx : x * F20.representative i \in F20.standard_F20.
  move: (F20.representative_indexP x^-1).
  by rewrite /F20.same_left_cosetb invgK.
exists i; symmetry.
apply/rcoset_eqP/rcosetP.
exists (x * F20.representative i); first exact: hx.
by rewrite mulgA mulgV mulg1.
Qed.

(** The generic finite right-coset enumeration is permutation-equal to the
    six inverse-representative cosets. *)
Lemma theta_right_coset_enum_perm :
  perm_eq
    (enum (GC.lazard_right_coset_orbit F20.standard_F20))
    (map theta_right_coset (enum 'I_6)).
Proof.
apply: uniq_perm.
- exact: enum_uniq.
- rewrite map_inj_uniq ?enum_uniq //.
  exact: theta_right_coset_injective.
- move=> C; rewrite mem_enum; apply/idP/mapP.
  + move=> Cmem.
    have [i hi] := theta_right_coset_onto Cmem.
    exists i; first exact: mem_enum i.
    exact: esym hi.
  + move=> [i _ ->].
    exact: theta_right_coset_mem.
Qed.

(** On the inverse-representative right coset, the generic formal value uses
    [mpoly_left_action representative], so specialization is exactly the
    existing inverse-table scalar theta value. *)
Lemma lazard_theta_specialized_value_right_coset
    (K E : fieldType) (ratrK : {rmorphism rat -> K})
    (embed : {rmorphism K -> E}) (roots : 5.-tuple E) (i : 'I_6) :
  @Explicit.lazard_specialized_orbit_value
      K E 5 embed roots F20.standard_F20
        (lazard_theta_invariant K) (theta_right_coset i) =
    TV.quintic_theta_value roots i.
Proof.
rewrite /theta_right_coset /Explicit.lazard_specialized_orbit_value
  (@Explicit.lazard_formal_orbit_value_rcoset
    K 5 F20.standard_F20 (lazard_theta_invariant K)
    (Explicit.lazard_invariant_stabilizer_exact_under
      (lazard_theta_exact_stabilizer ratrK))
    (F20.representative i)^-1).
rewrite invgK theta_left_action_representative
  quintic_table_mpoly_specialize.
exact: erefl.
Qed.

(** ** Equality of the two scalar sextics *)

Theorem lazard_theta_orbit_resolvent_eq_quintic_scalar_resolvent
    (K E : fieldType) (ratrK : {rmorphism rat -> K})
    (embed : {rmorphism K -> E}) (roots : 5.-tuple E) :
  @GC.lazard_orbit_resolvent E S5 F20.standard_F20
      (@Explicit.lazard_specialized_orbit_value
        K E 5 embed roots F20.standard_F20
          (lazard_theta_invariant K)) =
    TV.quintic_scalar_resolvent roots.
Proof.
rewrite /GC.lazard_orbit_resolvent /GC.lazard_orbit_value_sequence
  TV.quintic_scalar_resolvent_index_product
  /TV.quintic_scalar_resolvent_by_index.
apply: perm_big.
have hvalues := perm_map
  (@Explicit.lazard_specialized_orbit_value
    K E 5 embed roots F20.standard_F20 (lazard_theta_invariant K))
  theta_right_coset_enum_perm.
have hmap :
    map
      (@Explicit.lazard_specialized_orbit_value
        K E 5 embed roots F20.standard_F20 (lazard_theta_invariant K))
      (map theta_right_coset (enum 'I_6)) =
    map (TV.quintic_theta_value roots) (enum 'I_6).
  rewrite map_comp.
  apply: eq_map=> i _.
  exact: lazard_theta_specialized_value_right_coset.
by move: hvalues; rewrite hmap.
Qed.

(** Specialization of the generic universal paper resolvent is the concrete
    scalar sextic. *)
Theorem lazard_paper_theta_universal_resolvent_specializes
    (K E : fieldType) (ratrK : {rmorphism rat -> K})
    (embed : {rmorphism K -> E}) (roots : 5.-tuple E) :
  map_poly (Explicit.lazard_mpoly_specialize embed roots)
      (@Explicit.lazard_paper_universal_invariant_resolvent
        K 5 F20.standard_F20 (lazard_theta_invariant K)) =
    TV.quintic_scalar_resolvent roots.
Proof.
rewrite /Explicit.lazard_paper_universal_invariant_resolvent.
rewrite (@Explicit.lazard_universal_invariant_resolvent_specializes
  K E 5 embed roots F20.standard_F20 (lazard_theta_invariant K)).
exact: lazard_theta_orbit_resolvent_eq_quintic_scalar_resolvent.
Qed.

(** ** Paper-facing ordered-root resolver *)

Section OrderedRootAdapter.

Variable L : splittingFieldType rat.
Variables (K E : {subfield L}).
Hypothesis galois_K_E : galois K E.

Let ratrK : {rmorphism rat -> subvs_of K} := in_alg (subvs_of K).
Local Notation base_embed :=
  (@GC.lazard_base_embedding rat L K E galois_K_E).

Variable basePolynomial : {poly subvs_of K}.
Variable roots : 5.-tuple (subvs_of E).
Hypothesis root_presentation :
  @Explicit.lazard_ordered_root_presentation
    rat L K E galois_K_E 5 basePolynomial roots.

(** The exact requested adapter: scalar extension of the generic
    paper-facing ordered resolvent formed from the explicit rational theta
    is the scalar sextic of the supplied exact root tuple. *)
Theorem lazard_paper_ordered_theta_resolvent_map_eq_scalar_resolvent :
  map_poly base_embed
    (@Explicit.lazard_paper_ordered_base_resolvent
      rat L K E galois_K_E 5 F20.standard_F20
      (lazard_theta_invariant (subvs_of K))
      (lazard_theta_exact_stabilizer ratrK)
      basePolynomial roots root_presentation) =
    TV.quintic_scalar_resolvent roots.
Proof.
rewrite (@Explicit.lazard_paper_ordered_base_resolvent_map
  rat L K E galois_K_E 5 F20.standard_F20
  (lazard_theta_invariant (subvs_of K))
  (lazard_theta_exact_stabilizer ratrK)
  basePolynomial roots root_presentation).
rewrite /Explicit.lazard_explicit_orbit_resolvent
  /Explicit.lazard_explicit_orbit_value.
exact: (@lazard_theta_orbit_resolvent_eq_quintic_scalar_resolvent
  (subvs_of K) (subvs_of E) ratrK base_embed roots).
Qed.

End OrderedRootAdapter.

Print Assumptions theta_rat_exact_stabilizer.
Print Assumptions lazard_theta_exact_stabilizer.
Print Assumptions lazard_theta_specialized_value_right_coset.
Print Assumptions lazard_theta_orbit_resolvent_eq_quintic_scalar_resolvent.
Print Assumptions lazard_paper_ordered_theta_resolvent_map_eq_scalar_resolvent.

End PolynomialFormulasLazardGeneralResolventThetaAdapter.
