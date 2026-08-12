From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticThetaGaloisBridge
  LazardGeneralResolventCriterion LazardGeneralResolventExplicit
  LazardQuinticRootAlternateRecovery
  LazardQuinticRootCoherentAlternateInvariantF20.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Corrected alternate descent in a common Galois overfield.

    Lazard evaluates the root formula after adjoining both the five roots
    and a primitive fifth root of unity.  The two sorts of generators need
    not already lie in the same minimal splitting field.  This file works in
    any finite Galois overfield [E/K] containing both of them.

    Crucially, the action on the ordered roots is not a premise.  A complete
    square-free linear factorization of the original polynomial proves that
    every relative Galois automorphism permutes the tuple.  A base-field
    theta value and injectivity of the six theta values then conjugate that
    permutation into the standard Frobenius subgroup [F20].  The corrected
    projection is simultaneously invariant under [F20] on the roots and
    under all four possible images of the primitive fifth root.  Hence it is
    fixed by [Gal(E/K)] and descends to [K]. *)
Module PolynomialFormulasLazardQuinticCoherentAlternateCompositumDescent.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.

Module TV := PolynomialFormulasQuinticThetaValues.
Module TGB := PolynomialFormulasQuinticThetaGaloisBridge.
Module GC := PolynomialFormulasLazardGeneralResolventCriterion.
Module GE := PolynomialFormulasLazardGeneralResolventExplicit.
Module RA := PolynomialFormulasLazardQuinticRootAlternateRecovery.
Module CAI :=
  PolynomialFormulasLazardQuinticRootCoherentAlternateInvariantF20.

Section CommonGaloisOverfield.

Variables (F : fieldType) (L : splittingFieldType F).
Variables (K E : {subfield L}).
Hypothesis galois_K_E : galois K E.

Variable basePolynomial : {poly subvs_of K}.
Variable roots : 5.-tuple (subvs_of E).
Hypothesis root_presentation :
  @GE.lazard_ordered_root_presentation
    F L K E galois_K_E 5 basePolynomial roots.

Local Notation base_embed :=
  (@GC.lazard_base_embedding F L K E galois_K_E).
Local Notation gal_action :=
  (@GC.lazard_galois_action F L E).
Local Notation ordered_perm :=
  (@GE.lazard_ordered_gal_perm
    F L K E galois_K_E 5 basePolynomial roots root_presentation).

(** Select the ordering corresponding to the rational resolvent root. *)
Definition lazard_compositum_selected_roots (i : 'I_6) :
    5.-tuple (subvs_of E) :=
  TV.permute_quintic_roots ((representative i)^-1) roots.

(** The selected ordering turns the raw Galois permutation into its
    conjugate by the theta representative. *)
Lemma lazard_compositum_selected_roots_gal
    (i : 'I_6) (g : gal_of E) (gEK : g \in 'Gal(E / K)%G) :
  map_tuple (gal_action g) (lazard_compositum_selected_roots i) =
    TV.permute_quintic_roots
      ((ordered_perm g) ^ representative i)
      (lazard_compositum_selected_roots i).
Proof.
apply: eq_from_tnth=> k.
rewrite tnth_map /lazard_compositum_selected_roots
  !TV.tnth_permute_quintic_roots.
rewrite -(@GE.lazard_ordered_gal_permP
  F L K E galois_K_E 5 basePolynomial roots root_presentation
  g gEK ((representative i)^-1 k)).
rewrite conjg_permE.
by rewrite permK.
Qed.

(** The raw ordered tuple transforms by the permutation extracted from its
    proved complete factorization. *)
Lemma lazard_compositum_roots_gal
    (g : gal_of E) (gEK : g \in 'Gal(E / K)%G) :
  map_tuple (gal_action g) roots =
    TV.permute_quintic_roots (ordered_perm g) roots.
Proof.
apply: eq_from_tnth=> k.
rewrite tnth_map TV.tnth_permute_quintic_roots.
exact: esym (@GE.lazard_ordered_gal_permP
  F L K E galois_K_E 5 basePolynomial roots root_presentation
  g gEK k).
Qed.

Variables (i : 'I_6) (q : subvs_of K).
Hypothesis selected_theta_base :
  TV.quintic_theta_value roots i = base_embed q.
Hypothesis theta_values_injective :
  injective (TV.quintic_theta_value roots).

(** A base-field theta value forces every conjugated root permutation into
    the standard [F20]. *)
Lemma lazard_compositum_selected_gal_perm_mem_standard_F20
    (g : gal_of E) (gEK : g \in 'Gal(E / K)%G) :
  ((ordered_perm g) ^ representative i) \in standard_F20.
Proof.
have hfixed :
    gal_action g (TV.quintic_theta_value roots i) =
      TV.quintic_theta_value roots i.
  rewrite selected_theta_base.
  apply: (proj2 (@GC.lazard_galois_base_fixed_iff
    F L K E galois_K_E (base_embed q))).
  by exists q.
have hgal :
    gal_action g (TV.quintic_theta_value roots i) =
      TV.quintic_theta_value roots
        (TV.quintic_theta_index_action (ordered_perm g) i).
  rewrite TGB.quintic_theta_value_map
    (lazard_compositum_roots_gal gEK).
  exact: TV.quintic_theta_value_permute.
have hindex :
    TV.quintic_theta_index_action (ordered_perm g) i = i.
  apply: theta_values_injective.
  exact: eq_trans (esym hgal) hfixed.
have hconjugate :
    ordered_perm g \in
      (standard_F20 :^ (representative i)^-1).
  apply/TGB.quintic_theta_index_action_fixedP.
  exact: hindex.
by move: hconjugate; rewrite mem_conjgV.
Qed.

Variable omega : subvs_of E.
Hypothesis omega_primitive : 5.-primitive_root omega.

(** The corrected alternate coordinate is fixed by every relative Galois
    automorphism.  The image of [omega] is derived from primitivity, rather
    than being supplied as a separate cyclotomic-action certificate. *)
Theorem lazard_compositum_coherent_alternate_value_fixed
    (j : 'I_4) (g : gal_of E) (gEK : g \in 'Gal(E / K)%G) :
  gal_action g
      (RA.lazard_root_coherent_alternate_projection_values
        omega (lazard_compositum_selected_roots i) j) =
    RA.lazard_root_coherent_alternate_projection_values
      omega (lazard_compositum_selected_roots i) j.
Proof.
rewrite CAI.lazard_root_coherent_alternate_projection_values_map.
rewrite (lazard_compositum_selected_roots_gal gEK).
pose s := ((ordered_perm g) ^ representative i).
have hs : s \in standard_F20.
  exact: lazard_compositum_selected_gal_perm_mem_standard_F20 gEK.
have homega :=
  CAI.primitive_fifth_rmorphism_image_cases omega_primitive (gal_action g).
have homega_value :
    RA.lazard_root_coherent_alternate_projection_values
        (gal_action g omega)
        (TV.permute_quintic_roots s
          (lazard_compositum_selected_roots i)) j =
      RA.lazard_root_coherent_alternate_projection_values
        omega
        (TV.permute_quintic_roots s
          (lazard_compositum_selected_roots i)) j.
  case: homega=> [->|[->|[->|->]]].
  - reflexivity.
  - exact: CAI.lazard_root_coherent_alternate_projection_values_squared.
  - exact: CAI.lazard_root_coherent_alternate_projection_values_cubed.
  - exact: CAI.lazard_root_coherent_alternate_projection_values_fourth.
rewrite homega_value.
exact: CAI.lazard_root_coherent_alternate_projection_values_standard_F20.
Qed.

(** Full common-overfield descent: each corrected alternate coordinate is
    the image of an actual element of the original coefficient field. *)
Theorem exists_base_lazard_compositum_coherent_alternate_value
    (j : 'I_4) :
  exists a : subvs_of K,
    RA.lazard_root_coherent_alternate_projection_values
        omega (lazard_compositum_selected_roots i) j = base_embed a.
Proof.
apply: (proj1 (@GC.lazard_galois_base_fixed_iff
  F L K E galois_K_E
  (RA.lazard_root_coherent_alternate_projection_values
    omega (lazard_compositum_selected_roots i) j))).
exact: lazard_compositum_coherent_alternate_value_fixed.
Qed.

(** Membership form usable by a subsequent radical-tower construction.
    The chosen subfield [B] may be any concrete realization of the embedded
    coefficient field; the only structural fact needed here is that it
    contains every value of the canonical embedding [K -> E].  In
    particular, no four-coordinate descent certificate is passed to the
    radical formula: it is derived coordinatewise from the common-overfield
    Galois theorem above. *)
Theorem lazard_compositum_coherent_alternate_projection_data_in
    (B : {subfield (subvs_of E)})
    (base_embedding_mem : forall a : subvs_of K, base_embed a \in B) :
  forall j : 'I_4,
    RA.lazard_root_coherent_alternate_projection_values
      omega (lazard_compositum_selected_roots i) j \in B.
Proof.
move=> j.
have [a ha] := exists_base_lazard_compositum_coherent_alternate_value j.
rewrite ha.
exact: base_embedding_mem a.
Qed.

End CommonGaloisOverfield.

Print Assumptions lazard_compositum_selected_roots_gal.
Print Assumptions
  lazard_compositum_selected_gal_perm_mem_standard_F20.
Print Assumptions lazard_compositum_coherent_alternate_value_fixed.
Print Assumptions
  exists_base_lazard_compositum_coherent_alternate_value.
Print Assumptions
  lazard_compositum_coherent_alternate_projection_data_in.

End PolynomialFormulasLazardQuinticCoherentAlternateCompositumDescent.
