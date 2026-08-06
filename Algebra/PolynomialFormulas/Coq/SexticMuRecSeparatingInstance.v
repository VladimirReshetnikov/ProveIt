(* ===================================================================== *)
(*  Canonical sextic separating search through a transparent coding.     *)
(*                                                                       *)
(*  Unlike MathComp's abstract [pickle]/[unpickle] enumeration,           *)
(*  [projected_parameter] is the concrete inverse of the primitive-       *)
(*  recursive vector coding used by the MuRec development.               *)
(* ===================================================================== *)

From Stdlib Require Import Arith Bool Lia Vector.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import abel.

From Undecidability.Shared.Libs.DLW Require Import pos vec.
From Undecidability.MuRec.Util Require Import recalg recomp ra_recomp.

From PolynomialFormulas Require Import
  AbelRuffini QuinticRadicalDecidability SexticRecursiveCore
  SexticSparseResolvents SexticSeparatingSearch SexticSeparatingSelector
  SexticRationalRootSearch SexticDescriptorGaloisCriterion
  SexticCanonicalVieta SexticMuRecComputability
  SexticMuRecSeparatingSearch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

Module PolynomialFormulasSexticMuRecSeparatingInstance.

Module SRC := PolynomialFormulasSexticRecursiveCore.
Module SR := PolynomialFormulasSexticSparseResolvents.
Module SS := PolynomialFormulasSexticSeparatingSearch.
Module SEL := PolynomialFormulasSexticSeparatingSelector.
Module CV := PolynomialFormulasSexticCanonicalVieta.
Module RR := PolynomialFormulasSexticRationalRootSearch.
Module DGC := PolynomialFormulasSexticDescriptorGaloisCriterion.
Module MR := PolynomialFormulasSexticMuRecSeparatingSearch.

Import LeanProofs.PolynomialFormulasAbelRuffini.

(* --------------------------------------------------------------------- *)
(* The primitive-recursive parameter enumeration.                        *)

Definition projected_parameter (code : nat) : SR.parameter :=
  [tuple
    vec_pos (project 2 code) pos0;
    vec_pos (project 2 code) pos1].

Definition parameter_vector (x : SR.parameter) : Vector.t nat 2 :=
  tnth x ord0 ## tnth x ord_max ## vec_nil.

Definition projected_parameter_code (x : SR.parameter) : nat :=
  inject (parameter_vector x).

Lemma projected_parameter_codeK x :
  projected_parameter (projected_parameter_code x) = x.
Proof.
  rewrite /projected_parameter_code /projected_parameter
    /parameter_vector project_inject.
  apply: eq_from_tnth=> i.
  case: i=> [[|[|i]] hi] //=.
  - have -> : @Ordinal 2 0 hi = ord0 by apply/val_inj.
    by [].
  - have -> : @Ordinal 2 1 hi = ord_max by apply/val_inj.
    by [].
Qed.

Theorem projected_parameter_surjective (x : SR.parameter) :
  exists code, projected_parameter code = x.
Proof.
  exists (projected_parameter_code x).
  exact: projected_parameter_codeK.
Qed.

Definition canonical_sextic_roots (f : SRC.monic_sextic) : 6.-tuple algC :=
  @DGC.sextic_complex_root_tuple
    (CV.rational_monic_sextic f) (CV.size_rational_monic_sextic f).

(* --------------------------------------------------------------------- *)
(* Guarded pair/triple tests and their unconditional termination.        *)

Definition pair_projected_collisionb
    (f : SRC.monic_sextic) (index : nat) : bool :=
  SS.pair_separatesb f (projected_parameter index).

Definition triple_projected_collisionb
    (f : SRC.monic_sextic) (index : nat) : bool :=
  SS.triple_separatesb f (projected_parameter index).

Definition pair_projected_total_separatesb
    (f : SRC.monic_sextic) (index : nat) : bool :=
  SRC.has_bounded_proper_factor f || pair_projected_collisionb f index.

Definition triple_projected_total_separatesb
    (f : SRC.monic_sextic) (index : nat) : bool :=
  SRC.has_bounded_proper_factor f || triple_projected_collisionb f index.

Lemma pair_projected_total_separates_eventually (f : SRC.monic_sextic) :
  exists index, pair_projected_total_separatesb f index = true.
Proof.
  case hfactor: (SRC.has_bounded_proper_factor f).
  - exists 0%N.
    by rewrite /pair_projected_total_separatesb hfactor.
  - have [old_index hold] := @SEL.pair_separating_eventually_true
      (canonical_sextic_roots f) f (CV.canonical_monic_sextic_vieta f)
      (CV.canonical_sextic_complex_roots_injective hfactor).
    have [index hindex] :=
      projected_parameter_surjective (SS.parameter_at old_index).
    exists index.
    rewrite /pair_projected_total_separatesb
      /pair_projected_collisionb hfactor /= hindex.
    exact hold.
Qed.

Lemma triple_projected_total_separates_eventually (f : SRC.monic_sextic) :
  exists index, triple_projected_total_separatesb f index = true.
Proof.
  case hfactor: (SRC.has_bounded_proper_factor f).
  - exists 0%N.
    by rewrite /triple_projected_total_separatesb hfactor.
  - have [old_index hold] := @SEL.triple_separating_eventually_true
      (canonical_sextic_roots f) f (CV.canonical_monic_sextic_vieta f)
      (CV.canonical_sextic_complex_roots_injective hfactor).
    have [index hindex] :=
      projected_parameter_surjective (SS.parameter_at old_index).
    exists index.
    rewrite /triple_projected_total_separatesb
      /triple_projected_collisionb hfactor /= hindex.
    exact hold.
Qed.

(* --------------------------------------------------------------------- *)
(* Certified least indices and the parameters they enumerate.            *)

Definition pair_projected_separating_index
    (f : SRC.monic_sextic) : nat :=
  @SEL.first_true_index (fun index => pair_projected_total_separatesb f index)
    (pair_projected_total_separates_eventually f).

Definition triple_projected_separating_index
    (f : SRC.monic_sextic) : nat :=
  @SEL.first_true_index
    (fun index => triple_projected_total_separatesb f index)
    (triple_projected_total_separates_eventually f).

Definition pair_projected_separating_parameter
    (f : SRC.monic_sextic) : SR.parameter :=
  projected_parameter (pair_projected_separating_index f).

Definition triple_projected_separating_parameter
    (f : SRC.monic_sextic) : SR.parameter :=
  projected_parameter (triple_projected_separating_index f).

Lemma pair_projected_separating_indexP f :
  pair_projected_total_separatesb f
    (pair_projected_separating_index f) = true.
Proof. exact: SEL.first_true_indexP. Qed.

Lemma triple_projected_separating_indexP f :
  triple_projected_total_separatesb f
    (triple_projected_separating_index f) = true.
Proof. exact: SEL.first_true_indexP. Qed.

Lemma pair_projected_separating_index_minimal f index :
  pair_projected_total_separatesb f index = true ->
  Nat.le (pair_projected_separating_index f) index.
Proof. exact: SEL.first_true_index_minimal. Qed.

Lemma triple_projected_separating_index_minimal f index :
  triple_projected_total_separatesb f index = true ->
  Nat.le (triple_projected_separating_index f) index.
Proof. exact: SEL.first_true_index_minimal. Qed.

Lemma pair_projected_separating_parameter_injective f
    (hfactor : SRC.has_bounded_proper_factor f = false) :
  SS.pair_descriptor_injective (canonical_sextic_roots f)
    (pair_projected_separating_parameter f).
Proof.
  apply: (elimT (@SS.pair_separatesP
    (canonical_sextic_roots f) f
    (pair_projected_separating_parameter f)
    (CV.canonical_monic_sextic_vieta f))).
  have htotal := pair_projected_separating_indexP f.
  move: htotal.
  by rewrite /pair_projected_separating_parameter
    /pair_projected_total_separatesb /pair_projected_collisionb hfactor.
Qed.

Lemma triple_projected_separating_parameter_injective f
    (hfactor : SRC.has_bounded_proper_factor f = false) :
  SS.triple_descriptor_injective (canonical_sextic_roots f)
    (triple_projected_separating_parameter f).
Proof.
  apply: (elimT (@SS.triple_separatesP
    (canonical_sextic_roots f) f
    (triple_projected_separating_parameter f)
    (CV.canonical_monic_sextic_vieta f))).
  have htotal := triple_projected_separating_indexP f.
  move: htotal.
  by rewrite /triple_projected_separating_parameter
    /triple_projected_total_separatesb /triple_projected_collisionb hfactor.
Qed.

(* --------------------------------------------------------------------- *)
(* The existing generic sextic criterion instantiated at these parameters. *)

Definition projected_irreducible_resolventb
    (f : SRC.monic_sextic) : bool :=
  RR.pair_scaled_rational_rootb f
      (pair_projected_separating_parameter f) ||
  RR.triple_scaled_rational_rootb f
      (triple_projected_separating_parameter f).

Theorem projected_sextic_scaled_resolvent_solvableP f
    (hfactor : SRC.has_bounded_proper_factor f = false) :
  reflect
    (solvable 'Gal({: numfield (CV.rational_monic_sextic f)} / 1%AS))
    (projected_irreducible_resolventb f).
Proof.
  exact: (@DGC.sextic_scaled_resolvent_solvableP
    (CV.rational_monic_sextic f) (CV.size_rational_monic_sextic f)
    (CV.rational_monic_sextic_irreducible hfactor) f
    (pair_projected_separating_parameter f)
    (triple_projected_separating_parameter f)
    (CV.canonical_monic_sextic_vieta f)
    (pair_projected_separating_parameter_injective hfactor)
    (triple_projected_separating_parameter_injective hfactor)).
Qed.

Lemma projected_rational_monic_sextic_neq0 (f : SRC.monic_sextic) :
  CV.rational_monic_sextic f != 0.
Proof.
  apply/eqP=> hzero.
  by move: (CV.size_rational_monic_sextic f); rewrite hzero size_poly0.
Qed.

Theorem projected_irreducible_resolvent_radicalP f
    (hfactor : SRC.has_bounded_proper_factor f = false) :
  reflect
    (radical_formula_solves (CV.rational_monic_sextic f))
    (projected_irreducible_resolventb f).
Proof.
  apply: (equivP (projected_sextic_scaled_resolvent_solvableP hfactor)).
  split.
  - move=> hsolvable.
    have hradical := elimT
      (AbelGaloisPolyRat (CV.rational_monic_sextic f)) hsolvable.
    exact: (solvable_formula (projected_rational_monic_sextic_neq0 f)).1
      hradical.
  - move=> hformula.
    have hradical :=
      (solvable_formula (projected_rational_monic_sextic_neq0 f)).2
        hformula.
    exact: introT (AbelGaloisPolyRat (CV.rational_monic_sextic f))
      hradical.
Qed.

(* --------------------------------------------------------------------- *)
(* MuRec seam for the concrete coefficient representation.               *)
(*                                                                       *)
(* A later coefficient compiler may choose its own decoder from six      *)
(* natural codes to a monic sextic.  The only remaining obligations are  *)
(* exhibited below as ordinary theorem arguments: a program for the      *)
(* factor guard and a program for the pair or triple collision test,      *)
(* together with their relational correctness proofs.  No recursive      *)
(* function is postulated or treated specially by the kernel.            *)

Definition projected_encoded_factor_guard
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (values : Vector.t nat 6) : bool :=
  SRC.has_bounded_proper_factor (decode values).

Definition pair_projected_encoded_collision
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (index : nat) (values : Vector.t nat 6) : bool :=
  pair_projected_collisionb (decode values) index.

Definition triple_projected_encoded_collision
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (index : nat) (values : Vector.t nat 6) : bool :=
  triple_projected_collisionb (decode values) index.

Definition pair_projected_encoded_test
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (index : nat) (values : Vector.t nat 6) : bool :=
  orb (projected_encoded_factor_guard decode values)
    (pair_projected_encoded_collision decode index values).

Definition triple_projected_encoded_test
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (index : nat) (values : Vector.t nat 6) : bool :=
  orb (projected_encoded_factor_guard decode values)
    (triple_projected_encoded_collision decode index values).

Lemma pair_projected_encoded_eventually
    (decode : Vector.t nat 6 -> SRC.monic_sextic) values :
  exists index, pair_projected_encoded_test decode index values = true.
Proof.
  change (exists index,
    pair_projected_total_separatesb (decode values) index = true).
  exact: pair_projected_total_separates_eventually.
Qed.

Lemma triple_projected_encoded_eventually
    (decode : Vector.t nat 6 -> SRC.monic_sextic) values :
  exists index, triple_projected_encoded_test decode index values = true.
Proof.
  change (exists index,
    triple_projected_total_separatesb (decode values) index = true).
  exact: triple_projected_total_separates_eventually.
Qed.

Definition pair_projected_encoded_index
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (values : Vector.t nat 6) : nat :=
  MR.certified_first_true (pair_projected_encoded_test decode)
    (pair_projected_encoded_eventually decode) values.

Definition triple_projected_encoded_index
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (values : Vector.t nat 6) : nat :=
  MR.certified_first_true (triple_projected_encoded_test decode)
    (triple_projected_encoded_eventually decode) values.

Lemma pair_projected_encoded_indexE decode values :
  pair_projected_encoded_index decode values =
    pair_projected_separating_index (decode values).
Proof.
  rewrite /pair_projected_encoded_index /MR.certified_first_true
    /pair_projected_separating_index.
  exact: SEL.first_true_index_proof_irrelevant.
Qed.

Lemma triple_projected_encoded_indexE decode values :
  triple_projected_encoded_index decode values =
    triple_projected_separating_index (decode values).
Proof.
  rewrite /triple_projected_encoded_index /MR.certified_first_true
    /triple_projected_separating_index.
  exact: SEL.first_true_index_proof_irrelevant.
Qed.

Definition pair_projected_encoded_vector_relation
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (values : Vector.t nat 6) (out : nat) : Prop :=
  out = pair_projected_encoded_index decode values.

Definition triple_projected_encoded_vector_relation
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (values : Vector.t nat 6) (out : nat) : Prop :=
  out = triple_projected_encoded_index decode values.

Definition pair_projected_encoded_code_relation
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = pair_projected_encoded_index decode (project 6 (vec_head code)).

Definition triple_projected_encoded_code_relation
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = triple_projected_encoded_index decode (project 6 (vec_head code)).

Theorem pair_projected_encoded_vector_relation_murec
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (guard_program : recalg 6) (collision_program : recalg 7)
    (Hguard : forall values,
      ⟦guard_program⟧ values
        (bool_to_nat (projected_encoded_factor_guard decode values)))
    (Hcollision : MR.recalg_boolean_spec
      (pair_projected_encoded_collision decode) collision_program) :
  MuRec_computable (pair_projected_encoded_vector_relation decode).
Proof.
  unfold pair_projected_encoded_vector_relation,
    pair_projected_encoded_index.
  exact: (@MR.guarded_first_true_vector_relation_murec 6
    (projected_encoded_factor_guard decode)
    (pair_projected_encoded_collision decode)
    guard_program collision_program Hguard Hcollision
    (pair_projected_encoded_eventually decode)).
Qed.

Theorem triple_projected_encoded_vector_relation_murec
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (guard_program : recalg 6) (collision_program : recalg 7)
    (Hguard : forall values,
      ⟦guard_program⟧ values
        (bool_to_nat (projected_encoded_factor_guard decode values)))
    (Hcollision : MR.recalg_boolean_spec
      (triple_projected_encoded_collision decode) collision_program) :
  MuRec_computable (triple_projected_encoded_vector_relation decode).
Proof.
  unfold triple_projected_encoded_vector_relation,
    triple_projected_encoded_index.
  exact: (@MR.guarded_first_true_vector_relation_murec 6
    (projected_encoded_factor_guard decode)
    (triple_projected_encoded_collision decode)
    guard_program collision_program Hguard Hcollision
    (triple_projected_encoded_eventually decode)).
Qed.

Theorem pair_projected_encoded_code_relation_murec
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (guard_program : recalg 6) (collision_program : recalg 7)
    (Hguard : forall values,
      ⟦guard_program⟧ values
        (bool_to_nat (projected_encoded_factor_guard decode values)))
    (Hcollision : MR.recalg_boolean_spec
      (pair_projected_encoded_collision decode) collision_program) :
  MuRec_computable (pair_projected_encoded_code_relation decode).
Proof.
  unfold pair_projected_encoded_code_relation,
    pair_projected_encoded_index.
  exact: (@MR.guarded_first_true_code_relation_murec 6
    (projected_encoded_factor_guard decode)
    (pair_projected_encoded_collision decode)
    guard_program collision_program Hguard Hcollision
    (pair_projected_encoded_eventually decode)).
Qed.

Theorem triple_projected_encoded_code_relation_murec
    (decode : Vector.t nat 6 -> SRC.monic_sextic)
    (guard_program : recalg 6) (collision_program : recalg 7)
    (Hguard : forall values,
      ⟦guard_program⟧ values
        (bool_to_nat (projected_encoded_factor_guard decode values)))
    (Hcollision : MR.recalg_boolean_spec
      (triple_projected_encoded_collision decode) collision_program) :
  MuRec_computable (triple_projected_encoded_code_relation decode).
Proof.
  unfold triple_projected_encoded_code_relation,
    triple_projected_encoded_index.
  exact: (@MR.guarded_first_true_code_relation_murec 6
    (projected_encoded_factor_guard decode)
    (triple_projected_encoded_collision decode)
    guard_program collision_program Hguard Hcollision
    (triple_projected_encoded_eventually decode)).
Qed.

Lemma pair_projected_encoded_code_roundtrip decode values out :
  pair_projected_encoded_code_relation decode
      (inject values ## vec_nil) out <->
  pair_projected_encoded_vector_relation decode values out.
Proof.
  unfold pair_projected_encoded_code_relation,
    pair_projected_encoded_vector_relation.
  cbn [vec_head].
  rewrite project_inject.
  reflexivity.
Qed.

Lemma triple_projected_encoded_code_roundtrip decode values out :
  triple_projected_encoded_code_relation decode
      (inject values ## vec_nil) out <->
  triple_projected_encoded_vector_relation decode values out.
Proof.
  unfold triple_projected_encoded_code_relation,
    triple_projected_encoded_vector_relation.
  cbn [vec_head].
  rewrite project_inject.
  reflexivity.
Qed.

End PolynomialFormulasSexticMuRecSeparatingInstance.
