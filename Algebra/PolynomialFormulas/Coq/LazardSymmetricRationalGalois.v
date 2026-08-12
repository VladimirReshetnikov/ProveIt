From HB Require Import structures.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantFiniteFree LazardInvariantArtinSuccessor
  LazardSymmetricRationalFiniteExtension.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Splitting-field and full-Galois packaging for symmetric rational
    functions.

    The preceding finite-extension bridge realizes

      K(e_1,...,e_n) <= K(X_1,...,X_n)

    as a finite extension of degree [n!], with a localized reverse-Artin
    basis and a faithful action of ['S_n].  Here we make the normality
    argument completely explicit.  For each basis vector we multiply the
    linear factors belonging to its full permutation orbit.  Every
    coefficient of that orbit product is fixed, hence belongs to the base
    field by the rational fundamental theorem of symmetric functions.  The
    combined root list contains the reverse-Artin basis (use the identity
    permutation), so adjoining those roots gives the whole rational-function
    field.

    After installing MathComp's splitting-field mixin, the inverse-indexed
    permutation action is an honest group morphism into [gal_of].  Its fixed
    field is exactly the elementary-symmetric field, and [gal_fixedField]
    therefore identifies its image with the full Galois group.  No Galois or
    normality premise is introduced. *)
Module PolynomialFormulasLazardSymmetricRationalGalois.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module AS := PolynomialFormulasLazardInvariantArtinSuccessor.
Module FE := PolynomialFormulasLazardSymmetricRationalFiniteExtension.

Section SymmetricRationalGalois.

Variables (K : fieldType) (n : nat).

Local Notation MP := {mpoly K[n]}.
Local Notation ESRF :=
  (FE.lazard_elementary_symmetric_rational_field K n).
Local Notation RFE :=
  (FE.lazard_rational_function_extension K n).
Local Notation ArtinD :=
  (AS.lazard_reverse_artin_finite_free_decomposition K n).
Local Notation ArtinI := (FF.ffd_index ArtinD).

(**************************************************************************)
(** * Orbit polynomials over the fixed field *)

Definition lazard_fraction_orbit_polynomial (x : RFE) : {poly RFE} :=
  \prod_(s : 'S_n)
    ('X - (FE.lazard_fraction_permutation_AEnd K n s x)%:P).

(** Applying a permutation to all coefficients only left-translates the
    finite index set ['S_n]. *)
Lemma lazard_fraction_orbit_polynomial_fixed (t : 'S_n) x :
  map_poly (FE.lazard_fraction_permutation_AEnd K n t)
      (lazard_fraction_orbit_polynomial x) =
    lazard_fraction_orbit_polynomial x.
Proof.
rewrite /lazard_fraction_orbit_polynomial rmorph_prod.
under [LHS] eq_bigr => s _ do
  rewrite map_polyXsubC
    -FE.lazard_fraction_permutation_AEnd_actionM.
by rewrite (reindex_inj (mulgI t)).
Qed.

Definition lazard_artin_orbit_polynomial : {poly RFE} :=
  \prod_(i : ArtinI)
    lazard_fraction_orbit_polynomial
      (FE.lazard_fraction_artin_basis K n i).

Lemma lazard_artin_orbit_polynomial_fixed (t : 'S_n) :
  map_poly (FE.lazard_fraction_permutation_AEnd K n t)
      lazard_artin_orbit_polynomial =
    lazard_artin_orbit_polynomial.
Proof.
rewrite /lazard_artin_orbit_polynomial rmorph_prod.
under [LHS] eq_bigr => i _ do
  rewrite lazard_fraction_orbit_polynomial_fixed.
by [].
Qed.

(** The fixed-field theorem applies coefficientwise, so the orbit product is
    literally a polynomial over the base subfield of the field extension. *)
Lemma lazard_artin_orbit_polynomial_over_base :
  lazard_artin_orbit_polynomial
    \is a polyOver (1%VS : {vspace RFE}).
Proof.
apply/polyOverP=> i.
apply/FE.lazard_full_symmetric_fixed_fieldP.
move=> s.
rewrite -FE.lazard_fraction_permutation_AEndE.
have hs := congr1 (fun p : {poly RFE} => p`_i)
  (lazard_artin_orbit_polynomial_fixed s).
by rewrite coef_map in hs.
Qed.

(**************************************************************************)
(** * The displayed roots generate the complete extension *)

Definition lazard_artin_orbit_roots : seq RFE :=
  flatten
    [seq [seq FE.lazard_fraction_permutation_AEnd K n s
                  (FE.lazard_fraction_artin_basis K n i)
                | s : 'S_n]
       | i : ArtinI].

Lemma lazard_artin_orbit_polynomialE :
  lazard_artin_orbit_polynomial =
    \prod_(z <- lazard_artin_orbit_roots) ('X - z%:P).
Proof.
rewrite /lazard_artin_orbit_polynomial
  /lazard_fraction_orbit_polynomial /lazard_artin_orbit_roots.
by rewrite big_flatten !big_map !big_enum.
Qed.

(** The identity element occurs in every orbit, hence the displayed roots
    contain every localized reverse-Artin basis vector. *)
Lemma lazard_fraction_artin_basis_mem_orbit_roots i :
  FE.lazard_fraction_artin_basis K n i
    \in lazard_artin_orbit_roots.
Proof.
apply/flatten_mapP; exists i; first exact: mem_enum i.
apply/mapP; exists (1 : 'S_n); first exact: mem_enum 1.
by rewrite FE.lazard_fraction_permutation_AEnd_action1.
Qed.

Lemma lazard_artin_orbit_roots_generate :
  <<(1%VS : {vspace RFE}) & lazard_artin_orbit_roots>>%VS =
    ({:RFE} : {vspace RFE}).
Proof.
apply/eqP; rewrite eqEsubv subvf.
apply/subvP=> x _.
rewrite (FE.lazard_localized_artin_reconstruct K n x).
apply: memv_suml=> i _.
rewrite memvZ //.
exact: seqv_sub_adjoin
  (lazard_fraction_artin_basis_mem_orbit_roots i).
Qed.

Theorem lazard_artin_orbit_splitting_field_for :
  splittingFieldFor (1%VS : {vspace RFE})
    lazard_artin_orbit_polynomial ({:RFE} : {vspace RFE}).
Proof.
exists lazard_artin_orbit_roots.
- by rewrite -lazard_artin_orbit_polynomialE eqpxx.
- exact: lazard_artin_orbit_roots_generate.
Qed.

Theorem lazard_symmetric_rational_splitting_field_axiom :
  splitting_field_axiom ESRF RFE.
Proof.
exists lazard_artin_orbit_polynomial.
- exact: lazard_artin_orbit_polynomial_over_base.
- exact: lazard_artin_orbit_splitting_field_for.
Qed.

HB.instance Definition _ :=
  FieldExt_isSplittingField.Build ESRF RFE
    lazard_symmetric_rational_splitting_field_axiom.

Definition lazard_symmetric_rational_splitting_field :
    splittingFieldType ESRF :=
  RFE.

(**************************************************************************)
(** * The full Galois group is the symmetric group *)

Local Notation FullRFE := ({:RFE} : {vspace RFE}).
Local Notation GalFull := (gal_of FullRFE).

(** MathComp composes algebra endomorphisms in categorical order:
    [(f * g) x = g (f x)].  The original variable permutation is a left
    action, so inserting an inverse produces a genuine group morphism. *)
Definition lazard_permutation_galois (s : 'S_n) : GalFull :=
  gal FullRFE
    (FE.lazard_fraction_permutation_AEnd K n s^-1).

Lemma lazard_permutation_galoisE s x :
  lazard_permutation_galois s x =
    FE.lazard_fraction_permutation_AEnd K n s^-1 x.
Proof.
by rewrite /lazard_permutation_galois galK ?memvf ?subvf.
Qed.

Lemma lazard_permutation_galoisM :
  {morph lazard_permutation_galois : s t / (s * t)%g}.
Proof.
move=> s t; apply/eqP/gal_eqP=> x hx.
rewrite galM // !lazard_permutation_galoisE invMg.
exact: FE.lazard_fraction_permutation_AEnd_actionM.
Qed.

Canonical lazard_permutation_galois_morphism :=
  Morphism lazard_permutation_galoisM.

Lemma lazard_permutation_galois_injective :
  injective lazard_permutation_galois.
Proof.
move=> s t hst.
apply: invg_inj.
apply: FE.lazard_fraction_permutation_AEnd_injective.
apply/val_inj/lfunP=> x.
have hx := congr1 (fun g : GalFull => g x) hst.
by rewrite !lazard_permutation_galoisE in hx.
Qed.

Lemma lazard_permutation_galois_injm :
  'injm lazard_permutation_galois_morphism.
Proof.
apply/injmP=> s t _ _.
exact: lazard_permutation_galois_injective.
Qed.

Definition lazard_permutation_galois_image : {group GalFull} :=
  (lazard_permutation_galois_morphism @* [set: 'S_n])%G.

Lemma lazard_permutation_galois_mem_image s :
  lazard_permutation_galois s
    \in lazard_permutation_galois_image.
Proof.
apply/morphimP; exists s; first exact: in_setT.
by [].
Qed.

Lemma lazard_permutation_galois_image_card :
  #|lazard_permutation_galois_image| = n`!.
Proof.
rewrite /lazard_permutation_galois_image
  (card_injm lazard_permutation_galois_injm) ?subsetT //.
by rewrite cardsT card_Sn.
Qed.

Lemma lazard_permutation_galois_image_sub_full :
  lazard_permutation_galois_image
    \subset 'Gal(FullRFE / (1%VS : {vspace RFE})).
Proof.
apply/subsetP=> g /morphimP[s _ ->].
rewrite gal_kHom ?sub1v //.
exact: k1AHom.
Qed.

(** Fixed by the image means fixed by every original variable permutation:
    to recover the action of [s], use the image element indexed by [s^-1]. *)
Theorem lazard_permutation_galois_image_fixed_field :
  fixedField lazard_permutation_galois_image =
    (1%VS : {subfield RFE}).
Proof.
apply/eqP; rewrite eqEsubv; apply/andP; split.
- apply/subvP=> x /mem_fixedFieldP[_ fixed_x].
  apply/FE.lazard_full_symmetric_fixed_fieldP.
  move=> s.
  rewrite -FE.lazard_fraction_permutation_AEndE.
  have hs := fixed_x (lazard_permutation_galois s^-1)
    (lazard_permutation_galois_mem_image s^-1).
  by rewrite lazard_permutation_galoisE invgK in hs.
- apply/subvP=> x base_x.
  apply/fixedFieldP; first exact: memvf x.
  move=> g image_g.
  apply: fixed_gal (sub1v FullRFE) _ base_x.
  exact: (subsetP lazard_permutation_galois_image_sub_full g image_g).
Qed.

Theorem lazard_full_symmetric_rational_galois_group :
  'Gal(FullRFE / (1%VS : {vspace RFE})) =
    lazard_permutation_galois_image.
Proof.
rewrite -lazard_permutation_galois_image_fixed_field.
exact: gal_fixedField.
Qed.

Theorem lazard_symmetric_rational_extension_galois :
  galois (1%VS : {vspace RFE}) FullRFE.
Proof.
rewrite -lazard_permutation_galois_image_fixed_field.
exact: fixedField_galois.
Qed.

Theorem lazard_full_symmetric_rational_galois_group_card :
  #|'Gal(FullRFE / (1%VS : {vspace RFE}))| = n`!.
Proof.
by rewrite lazard_full_symmetric_rational_galois_group
  lazard_permutation_galois_image_card.
Qed.

Theorem lazard_symmetric_group_full_galois_isomorphism :
  isom [set: 'S_n]
    'Gal(FullRFE / (1%VS : {vspace RFE}))
    lazard_permutation_galois_morphism.
Proof.
apply/isomP; split.
- exact: lazard_permutation_galois_injm.
- rewrite lazard_full_symmetric_rational_galois_group.
  by [].
Qed.

End SymmetricRationalGalois.

End PolynomialFormulasLazardSymmetricRationalGalois.
