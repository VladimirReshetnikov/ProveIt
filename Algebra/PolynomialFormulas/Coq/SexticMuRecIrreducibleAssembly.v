(* ===================================================================== *)
(*  Generic Mu-recursive assembly of the irreducible sextic branch.      *)
(*                                                                       *)
(*  The four expensive arity-eight Boolean cores (pair/triple collision  *)
(*  and pair/triple rational-root tests) remain explicit parameters.     *)
(*  Index projection, guarded minimization, selection, disjunction,      *)
(*  vector coding, and the semantic comparison are all proved here.      *)
(* ===================================================================== *)

From Stdlib Require Import Arith Bool Lia Vector.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import abel.

From Undecidability.Shared.Libs.DLW
  Require Import utils_nat pos vec.
From Undecidability.MuRec.Util
  Require Import recalg ra_utils recomp ra_recomp.

From PolynomialFormulas Require Import
  AbelRuffini SexticRecursiveCore SexticRationalRootSearch
  SexticCanonicalVieta
  SexticMuRecComputability SexticMuRecFactorDecision
  SexticMuRecSeparatingSearch SexticMuRecSeparatingInstance
  SexticMuRecFinalAssembly.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PolynomialFormulasSexticMuRecIrreducibleAssembly.

Module SRC := PolynomialFormulasSexticRecursiveCore.
Module RR := PolynomialFormulasSexticRationalRootSearch.
Module CV := PolynomialFormulasSexticCanonicalVieta.
Module FD := PolynomialFormulasSexticMuRecFactorDecision.
Module MR := PolynomialFormulasSexticMuRecSeparatingSearch.
Module MSI := PolynomialFormulasSexticMuRecSeparatingInstance.
Module FA := PolynomialFormulasSexticMuRecFinalAssembly.

Import LeanProofs.PolynomialFormulasAbelRuffini.

Local Notation "'⟦' f '⟧'" := (@ra_rel _ f) (at level 0).

(* --------------------------------------------------------------------- *)
(* Project an index to the two parameter coordinates consumed by a core. *)

(** The common arity-eight convention is
    [f0,...,f5,x0,x1], where [(x0,x1)] is [projected_parameter index]. *)
Definition projected_core_arguments
    (index : nat) (values : Vector.t nat 6) : Vector.t nat 8 :=
  vec_pos values pos0 ## vec_pos values pos1 ##
  vec_pos values pos2 ## vec_pos values pos3 ##
  vec_pos values pos4 ## vec_pos values pos5 ##
  vec_pos (project 2 index) pos0 ##
  vec_pos (project 2 index) pos1 ## vec_nil.

Definition projected_core_boolean
    (core : Vector.t nat 8 -> bool)
    (index : nat) (values : Vector.t nat 6) : bool :=
  core (projected_core_arguments index values).

Definition core_boolean_spec
    (core : Vector.t nat 8 -> bool)
    (program : recalg 8) : Prop :=
  forall values,
    ⟦program⟧ values (bool_to_nat (core values)).

Definition ra_projected_x0 : recalg 7 :=
  ra_comp (@ra_project 2 pos0) (ra_proj pos0 ## vec_nil).

Definition ra_projected_x1 : recalg 7 :=
  ra_comp (@ra_project 2 pos1) (ra_proj pos0 ## vec_nil).

Lemma ra_projected_x0_correct index values :
  ⟦ra_projected_x0⟧ (index ## values)
    (vec_pos (project 2 index) pos0).
Proof.
unfold ra_projected_x0.
eapply ra_comp1_val; [exact: ra_proj_val | exact: ra_project_val].
Qed.

Lemma ra_projected_x1_correct index values :
  ⟦ra_projected_x1⟧ (index ## values)
    (vec_pos (project 2 index) pos1).
Proof.
unfold ra_projected_x1.
eapply ra_comp1_val; [exact: ra_proj_val | exact: ra_project_val].
Qed.

Definition ra_projected_core_arguments : Vector.t (recalg 7) 8 :=
  ra_proj pos1 ## ra_proj pos2 ## ra_proj pos3 ##
  ra_proj pos4 ## ra_proj pos5 ## ra_proj pos6 ##
  ra_projected_x0 ## ra_projected_x1 ## vec_nil.

Definition ra_projected_boolean_core
    (core_program : recalg 8) : recalg 7 :=
  ra_comp core_program ra_projected_core_arguments.

Theorem ra_projected_boolean_core_correct
    (core : Vector.t nat 8 -> bool)
    (core_program : recalg 8)
    (Hcore : core_boolean_spec core core_program) index values :
  ⟦ra_projected_boolean_core core_program⟧ (index ## values)
    (bool_to_nat (projected_core_boolean core index values)).
Proof.
unfold ra_projected_boolean_core, projected_core_boolean.
exists (projected_core_arguments index values); split.
- exact: Hcore.
- intro variable; analyse pos variable;
    cbn [ra_projected_core_arguments projected_core_arguments
      vec_pos pos_S_inv].
  + exact: ra_proj_val.
  + exact: ra_proj_val.
  + exact: ra_proj_val.
  + exact: ra_proj_val.
  + exact: ra_proj_val.
  + exact: ra_proj_val.
  + exact: ra_projected_x0_correct.
  + exact: ra_projected_x1_correct.
Qed.

Corollary ra_projected_boolean_core_spec
    (core : Vector.t nat 8 -> bool)
    (core_program : recalg 8)
    (Hcore : core_boolean_spec core core_program) :
  MR.recalg_boolean_spec
    (projected_core_boolean core)
    (ra_projected_boolean_core core_program).
Proof. exact: (ra_projected_boolean_core_correct Hcore). Qed.

(* --------------------------------------------------------------------- *)
(* Guarded least-index search on the six encoded monic coefficients.     *)

Definition encoded_factor_guard (values : Vector.t nat 6) : bool :=
  encoded_monic_has_proper_factorb values.

Lemma ra_encoded_factor_guard_correct values :
  ⟦ra_encoded_monic_has_proper_factor⟧ values
    (bool_to_nat (encoded_factor_guard values)).
Proof.
unfold encoded_factor_guard, ra_encoded_monic_has_proper_factor.
rewrite -encoded_monic_has_proper_factor_indicator.
exact: compile_nat_expression_correct.
Qed.

Definition guarded_projected_test
    (collision_core : Vector.t nat 8 -> bool)
    (index : nat) (values : Vector.t nat 6) : bool :=
  encoded_factor_guard values ||
    projected_core_boolean collision_core index values.

Definition ra_guarded_projected_test
    (collision_program : recalg 8) : recalg 7 :=
  MR.ra_guarded_boolean
    ra_encoded_monic_has_proper_factor
    (ra_projected_boolean_core collision_program).

Lemma ra_guarded_projected_test_spec
    (collision_core : Vector.t nat 8 -> bool)
    (collision_program : recalg 8)
    (Hcollision : core_boolean_spec collision_core collision_program) :
  MR.recalg_boolean_spec
    (guarded_projected_test collision_core)
    (ra_guarded_projected_test collision_program).
Proof.
unfold guarded_projected_test, ra_guarded_projected_test.
apply MR.ra_guarded_boolean_correct.
- exact: ra_encoded_factor_guard_correct.
- exact: (ra_projected_boolean_core_spec Hcollision).
Qed.

Definition guarded_projected_eventually
    (collision_core : Vector.t nat 8 -> bool) : Prop :=
  forall values : Vector.t nat 6, exists index,
    guarded_projected_test collision_core index values = true.

Definition selected_projected_index
    (collision_core : Vector.t nat 8 -> bool)
    (eventually : guarded_projected_eventually collision_core)
    (values : Vector.t nat 6) : nat :=
  MR.certified_first_true
    (guarded_projected_test collision_core) eventually values.

Arguments selected_projected_index
  collision_core eventually values : clear implicits.

Definition ra_selected_projected_index
    (collision_program : recalg 8) : recalg 6 :=
  MR.ra_first_true (ra_guarded_projected_test collision_program).

Lemma ra_selected_projected_index_correct
    (collision_core : Vector.t nat 8 -> bool)
    (collision_program : recalg 8)
    (Hcollision : core_boolean_spec collision_core collision_program)
    (eventually : guarded_projected_eventually collision_core) values :
  ⟦ra_selected_projected_index collision_program⟧ values
    (selected_projected_index collision_core eventually values).
Proof.
unfold ra_selected_projected_index, selected_projected_index.
apply MR.ra_first_true_correct.
exact: (ra_guarded_projected_test_spec Hcollision).
Qed.

Definition selected_projected_index_relation
    (collision_core : Vector.t nat 8 -> bool)
    (eventually : guarded_projected_eventually collision_core)
    (values : Vector.t nat 6) (out : nat) : Prop :=
  out = selected_projected_index collision_core eventually values.

Arguments selected_projected_index_relation
  collision_core eventually values out : clear implicits.

Theorem selected_projected_index_relation_murec
    (collision_core : Vector.t nat 8 -> bool)
    (collision_program : recalg 8)
    (Hcollision : core_boolean_spec collision_core collision_program)
    (eventually : guarded_projected_eventually collision_core) :
  MuRec_computable
    (selected_projected_index_relation collision_core eventually).
Proof.
unfold selected_projected_index_relation.
refine (@recalg_graph_murec 6
  (selected_projected_index collision_core eventually)
  (ra_selected_projected_index collision_program) _).
exact: (ra_selected_projected_index_correct Hcollision eventually).
Qed.

(* --------------------------------------------------------------------- *)
(* Run a projected Boolean at the computed least index.                  *)

Definition ra_at_selected_index
    (index_program : recalg 6) (test_program : recalg 7) : recalg 6 :=
  ra_comp test_program (index_program ## ra_identity_arguments 6).

Lemma ra_at_selected_index_correct
    (index_program : recalg 6) (test_program : recalg 7)
    (index : Vector.t nat 6 -> nat)
    (test : nat -> Vector.t nat 6 -> nat)
    (Hindex : forall values, ⟦index_program⟧ values (index values))
    (Htest : forall selected values,
      ⟦test_program⟧ (selected ## values) (test selected values))
    values :
  ⟦ra_at_selected_index index_program test_program⟧ values
    (test (index values) values).
Proof.
unfold ra_at_selected_index.
exists (index values ## values); split.
- exact: Htest.
- intro variable; analyse pos variable; cbn.
  + exact: Hindex.
  + unfold ra_identity_arguments; repeat rewrite vec_pos_set.
    exact: ra_proj_val.
  all: unfold ra_identity_arguments; repeat rewrite vec_pos_set;
    exact: ra_proj_val.
Qed.

Definition selected_projected_rootb
    (collision_core : Vector.t nat 8 -> bool)
    (eventually : guarded_projected_eventually collision_core)
    (root_core : Vector.t nat 8 -> bool)
    (values : Vector.t nat 6) : bool :=
  projected_core_boolean root_core
    (selected_projected_index collision_core eventually values) values.

Arguments selected_projected_rootb
  collision_core eventually root_core values : clear implicits.

Definition ra_selected_projected_root
    (collision_program root_program : recalg 8) : recalg 6 :=
  ra_at_selected_index
    (ra_selected_projected_index collision_program)
    (ra_projected_boolean_core root_program).

Lemma ra_selected_projected_root_correct
    (collision_core root_core : Vector.t nat 8 -> bool)
    (collision_program root_program : recalg 8)
    (Hcollision : core_boolean_spec collision_core collision_program)
    (Hroot : core_boolean_spec root_core root_program)
    (eventually : guarded_projected_eventually collision_core) values :
  ⟦ra_selected_projected_root collision_program root_program⟧ values
    (bool_to_nat
      (selected_projected_rootb
        collision_core eventually root_core values)).
Proof.
unfold ra_selected_projected_root, selected_projected_rootb.
apply (ra_at_selected_index_correct
  (ra_selected_projected_index_correct Hcollision eventually)
  (ra_projected_boolean_core_correct Hroot)).
Qed.

(* --------------------------------------------------------------------- *)
(* Pair/triple assembly and Boolean disjunction.                         *)

Definition pair_selected_index := selected_projected_index.
Definition triple_selected_index := selected_projected_index.

Arguments pair_selected_index
  collision_core eventually values : clear implicits.
Arguments triple_selected_index
  collision_core eventually values : clear implicits.

Definition pair_selected_rootb := selected_projected_rootb.
Definition triple_selected_rootb := selected_projected_rootb.

Arguments pair_selected_rootb
  collision_core eventually root_core values : clear implicits.
Arguments triple_selected_rootb
  collision_core eventually root_core values : clear implicits.

Definition ra_pair_selected_index := ra_selected_projected_index.
Definition ra_triple_selected_index := ra_selected_projected_index.

Definition ra_pair_selected_root := ra_selected_projected_root.
Definition ra_triple_selected_root := ra_selected_projected_root.

Definition encoded_irreducible_resolventb
    (pair_collision_core : Vector.t nat 8 -> bool)
    (pair_eventually : guarded_projected_eventually pair_collision_core)
    (pair_root_core : Vector.t nat 8 -> bool)
    (triple_collision_core : Vector.t nat 8 -> bool)
    (triple_eventually :
      guarded_projected_eventually triple_collision_core)
    (triple_root_core : Vector.t nat 8 -> bool)
    (values : Vector.t nat 6) : bool :=
  pair_selected_rootb pair_collision_core pair_eventually
      pair_root_core values ||
  triple_selected_rootb triple_collision_core triple_eventually
      triple_root_core values.

Arguments encoded_irreducible_resolventb
  pair_collision_core pair_eventually pair_root_core
  triple_collision_core triple_eventually triple_root_core values
  : clear implicits.

Definition ra_encoded_irreducible_resolvent
    (pair_collision_program pair_root_program : recalg 8)
    (triple_collision_program triple_root_program : recalg 8) : recalg 6 :=
  FA.ra_boolean_or
    (ra_pair_selected_root pair_collision_program pair_root_program)
    (ra_triple_selected_root
      triple_collision_program triple_root_program).

Lemma ra_encoded_irreducible_resolvent_correct
    (pair_collision_core pair_root_core : Vector.t nat 8 -> bool)
    (pair_collision_program pair_root_program : recalg 8)
    (Hpair_collision :
      core_boolean_spec pair_collision_core pair_collision_program)
    (Hpair_root : core_boolean_spec pair_root_core pair_root_program)
    (pair_eventually : guarded_projected_eventually pair_collision_core)
    (triple_collision_core triple_root_core : Vector.t nat 8 -> bool)
    (triple_collision_program triple_root_program : recalg 8)
    (Htriple_collision :
      core_boolean_spec triple_collision_core triple_collision_program)
    (Htriple_root : core_boolean_spec triple_root_core triple_root_program)
    (triple_eventually :
      guarded_projected_eventually triple_collision_core) values :
  ⟦ra_encoded_irreducible_resolvent
      pair_collision_program pair_root_program
      triple_collision_program triple_root_program⟧ values
    (bool_to_nat
      (encoded_irreducible_resolventb
        pair_collision_core pair_eventually pair_root_core
        triple_collision_core triple_eventually triple_root_core values)).
Proof.
unfold ra_encoded_irreducible_resolvent,
  encoded_irreducible_resolventb.
apply (FA.ra_boolean_or_correct
  (ra_selected_projected_root_correct
    Hpair_collision Hpair_root pair_eventually)
  (ra_selected_projected_root_correct
    Htriple_collision Htriple_root triple_eventually)).
Qed.

Definition encoded_irreducible_resolvent_relation
    (pair_collision_core : Vector.t nat 8 -> bool)
    (pair_eventually : guarded_projected_eventually pair_collision_core)
    (pair_root_core : Vector.t nat 8 -> bool)
    (triple_collision_core : Vector.t nat 8 -> bool)
    (triple_eventually :
      guarded_projected_eventually triple_collision_core)
    (triple_root_core : Vector.t nat 8 -> bool)
    (values : Vector.t nat 6) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_irreducible_resolventb
      pair_collision_core pair_eventually pair_root_core
      triple_collision_core triple_eventually triple_root_core values).

Arguments encoded_irreducible_resolvent_relation
  pair_collision_core pair_eventually pair_root_core
  triple_collision_core triple_eventually triple_root_core values out
  : clear implicits.

Theorem encoded_irreducible_resolvent_relation_murec
    (pair_collision_core pair_root_core : Vector.t nat 8 -> bool)
    (pair_collision_program pair_root_program : recalg 8)
    (Hpair_collision :
      core_boolean_spec pair_collision_core pair_collision_program)
    (Hpair_root : core_boolean_spec pair_root_core pair_root_program)
    (pair_eventually : guarded_projected_eventually pair_collision_core)
    (triple_collision_core triple_root_core : Vector.t nat 8 -> bool)
    (triple_collision_program triple_root_program : recalg 8)
    (Htriple_collision :
      core_boolean_spec triple_collision_core triple_collision_program)
    (Htriple_root : core_boolean_spec triple_root_core triple_root_program)
    (triple_eventually :
      guarded_projected_eventually triple_collision_core) :
  MuRec_computable
    (encoded_irreducible_resolvent_relation
      pair_collision_core pair_eventually pair_root_core
      triple_collision_core triple_eventually triple_root_core).
Proof.
unfold encoded_irreducible_resolvent_relation.
refine (@recalg_graph_murec 6
  (fun values => bool_to_nat
    (encoded_irreducible_resolventb
      pair_collision_core pair_eventually pair_root_core
      triple_collision_core triple_eventually triple_root_core values))
  (ra_encoded_irreducible_resolvent
    pair_collision_program pair_root_program
    triple_collision_program triple_root_program) _).
exact (ra_encoded_irreducible_resolvent_correct
  Hpair_collision Hpair_root pair_eventually
  Htriple_collision Htriple_root triple_eventually).
Qed.

Definition ra_encoded_irreducible_resolvent_code
    (pair_collision_program pair_root_program : recalg 8)
    (triple_collision_program triple_root_program : recalg 8) : recalg 1 :=
  ra_comp
    (ra_encoded_irreducible_resolvent
      pair_collision_program pair_root_program
      triple_collision_program triple_root_program)
    (ra_vec_project 6).

Lemma ra_encoded_irreducible_resolvent_code_correct
    (pair_collision_core pair_root_core : Vector.t nat 8 -> bool)
    (pair_collision_program pair_root_program : recalg 8)
    (Hpair_collision :
      core_boolean_spec pair_collision_core pair_collision_program)
    (Hpair_root : core_boolean_spec pair_root_core pair_root_program)
    (pair_eventually : guarded_projected_eventually pair_collision_core)
    (triple_collision_core triple_root_core : Vector.t nat 8 -> bool)
    (triple_collision_program triple_root_program : recalg 8)
    (Htriple_collision :
      core_boolean_spec triple_collision_core triple_collision_program)
    (Htriple_root : core_boolean_spec triple_root_core triple_root_program)
    (triple_eventually :
      guarded_projected_eventually triple_collision_core) code :
  ⟦ra_encoded_irreducible_resolvent_code
      pair_collision_program pair_root_program
      triple_collision_program triple_root_program⟧
    (code ## vec_nil)
    (bool_to_nat
      (encoded_irreducible_resolventb
        pair_collision_core pair_eventually pair_root_core
        triple_collision_core triple_eventually triple_root_core
        (project 6 code))).
Proof.
unfold ra_encoded_irreducible_resolvent_code.
exists (project 6 code); split.
- exact (ra_encoded_irreducible_resolvent_correct
    Hpair_collision Hpair_root pair_eventually
    Htriple_collision Htriple_root triple_eventually (project 6 code)).
- intro variable; rewrite vec_pos_set.
  exact: ra_vec_project_val_at.
Qed.

Definition encoded_irreducible_resolvent_code_relation
    (pair_collision_core : Vector.t nat 8 -> bool)
    (pair_eventually : guarded_projected_eventually pair_collision_core)
    (pair_root_core : Vector.t nat 8 -> bool)
    (triple_collision_core : Vector.t nat 8 -> bool)
    (triple_eventually :
      guarded_projected_eventually triple_collision_core)
    (triple_root_core : Vector.t nat 8 -> bool)
    (code : Vector.t nat 1) (out : nat) : Prop :=
  out = bool_to_nat
    (encoded_irreducible_resolventb
      pair_collision_core pair_eventually pair_root_core
      triple_collision_core triple_eventually triple_root_core
      (project 6 (vec_head code))).

Arguments encoded_irreducible_resolvent_code_relation
  pair_collision_core pair_eventually pair_root_core
  triple_collision_core triple_eventually triple_root_core code out
  : clear implicits.

Theorem encoded_irreducible_resolvent_code_relation_murec
    (pair_collision_core pair_root_core : Vector.t nat 8 -> bool)
    (pair_collision_program pair_root_program : recalg 8)
    (Hpair_collision :
      core_boolean_spec pair_collision_core pair_collision_program)
    (Hpair_root : core_boolean_spec pair_root_core pair_root_program)
    (pair_eventually : guarded_projected_eventually pair_collision_core)
    (triple_collision_core triple_root_core : Vector.t nat 8 -> bool)
    (triple_collision_program triple_root_program : recalg 8)
    (Htriple_collision :
      core_boolean_spec triple_collision_core triple_collision_program)
    (Htriple_root : core_boolean_spec triple_root_core triple_root_program)
    (triple_eventually :
      guarded_projected_eventually triple_collision_core) :
  MuRec_computable
    (encoded_irreducible_resolvent_code_relation
      pair_collision_core pair_eventually pair_root_core
      triple_collision_core triple_eventually triple_root_core).
Proof.
unfold encoded_irreducible_resolvent_code_relation.
refine (@recalg_graph_murec 1
  (fun code => bool_to_nat
    (encoded_irreducible_resolventb
      pair_collision_core pair_eventually pair_root_core
      triple_collision_core triple_eventually triple_root_core
      (project 6 (vec_head code))))
  (ra_encoded_irreducible_resolvent_code
    pair_collision_program pair_root_program
    triple_collision_program triple_root_program) _).
intro values; vec split values with code; vec nil values.
exact (ra_encoded_irreducible_resolvent_code_correct
  Hpair_collision Hpair_root pair_eventually
  Htriple_collision Htriple_root triple_eventually code).
Qed.

(* --------------------------------------------------------------------- *)
(* Conditional semantic bridge on canonical monic coefficient encodings. *)

Definition pair_collision_core_exact
    (core : Vector.t nat 8 -> bool) : Prop :=
  forall (f : SRC.monic_sextic) index,
    SRC.has_bounded_proper_factor f = false ->
    projected_core_boolean core index
        (FD.encode_monic_sextic_coefficients f) =
    MSI.pair_projected_collisionb f index.

Definition triple_collision_core_exact
    (core : Vector.t nat 8 -> bool) : Prop :=
  forall (f : SRC.monic_sextic) index,
    SRC.has_bounded_proper_factor f = false ->
    projected_core_boolean core index
        (FD.encode_monic_sextic_coefficients f) =
    MSI.triple_projected_collisionb f index.

Definition pair_root_core_exact
    (core : Vector.t nat 8 -> bool) : Prop :=
  forall (f : SRC.monic_sextic) index,
    SRC.has_bounded_proper_factor f = false ->
    projected_core_boolean core index
        (FD.encode_monic_sextic_coefficients f) =
    RR.pair_scaled_rational_rootb f (MSI.projected_parameter index).

Definition triple_root_core_exact
    (core : Vector.t nat 8 -> bool) : Prop :=
  forall (f : SRC.monic_sextic) index,
    SRC.has_bounded_proper_factor f = false ->
    projected_core_boolean core index
        (FD.encode_monic_sextic_coefficients f) =
    RR.triple_scaled_rational_rootb f (MSI.projected_parameter index).

Lemma pair_guarded_projected_test_mathcomp
    (pair_collision_core : Vector.t nat 8 -> bool)
    (Hpair_collision : pair_collision_core_exact pair_collision_core)
    (f : SRC.monic_sextic) index
    (hfactor : SRC.has_bounded_proper_factor f = false) :
  guarded_projected_test pair_collision_core index
      (FD.encode_monic_sextic_coefficients f) =
  MSI.pair_projected_total_separatesb f index.
Proof.
rewrite /guarded_projected_test /encoded_factor_guard
  /MSI.pair_projected_total_separatesb
  FD.encoded_monic_has_proper_factorb_mathcomp hfactor /=.
exact: Hpair_collision.
Qed.

Lemma triple_guarded_projected_test_mathcomp
    (triple_collision_core : Vector.t nat 8 -> bool)
    (Htriple_collision :
      triple_collision_core_exact triple_collision_core)
    (f : SRC.monic_sextic) index
    (hfactor : SRC.has_bounded_proper_factor f = false) :
  guarded_projected_test triple_collision_core index
      (FD.encode_monic_sextic_coefficients f) =
  MSI.triple_projected_total_separatesb f index.
Proof.
rewrite /guarded_projected_test /encoded_factor_guard
  /MSI.triple_projected_total_separatesb
  FD.encoded_monic_has_proper_factorb_mathcomp hfactor /=.
exact: Htriple_collision.
Qed.

Lemma pair_selected_index_mathcomp
    (pair_collision_core : Vector.t nat 8 -> bool)
    (pair_eventually : guarded_projected_eventually pair_collision_core)
    (Hpair_collision : pair_collision_core_exact pair_collision_core)
    (f : SRC.monic_sextic)
    (hfactor : SRC.has_bounded_proper_factor f = false) :
  pair_selected_index pair_collision_core pair_eventually
      (FD.encode_monic_sextic_coefficients f) =
  MSI.pair_projected_separating_index f.
Proof.
apply Nat.le_antisymm.
- apply MR.certified_first_true_minimal.
  rewrite (@pair_guarded_projected_test_mathcomp
    pair_collision_core Hpair_collision f
    (MSI.pair_projected_separating_index f) hfactor).
  exact: MSI.pair_projected_separating_indexP.
- apply MSI.pair_projected_separating_index_minimal.
  rewrite -(@pair_guarded_projected_test_mathcomp
    pair_collision_core Hpair_collision f _ hfactor).
  exact: MR.certified_first_trueP.
Qed.

Lemma triple_selected_index_mathcomp
    (triple_collision_core : Vector.t nat 8 -> bool)
    (triple_eventually :
      guarded_projected_eventually triple_collision_core)
    (Htriple_collision :
      triple_collision_core_exact triple_collision_core)
    (f : SRC.monic_sextic)
    (hfactor : SRC.has_bounded_proper_factor f = false) :
  triple_selected_index triple_collision_core triple_eventually
      (FD.encode_monic_sextic_coefficients f) =
  MSI.triple_projected_separating_index f.
Proof.
apply Nat.le_antisymm.
- apply MR.certified_first_true_minimal.
  rewrite (@triple_guarded_projected_test_mathcomp
    triple_collision_core Htriple_collision f
    (MSI.triple_projected_separating_index f) hfactor).
  exact: MSI.triple_projected_separating_indexP.
- apply MSI.triple_projected_separating_index_minimal.
  rewrite -(@triple_guarded_projected_test_mathcomp
    triple_collision_core Htriple_collision f _ hfactor).
  exact: MR.certified_first_trueP.
Qed.

Lemma pair_selected_rootb_mathcomp
    (pair_collision_core pair_root_core : Vector.t nat 8 -> bool)
    (pair_eventually : guarded_projected_eventually pair_collision_core)
    (Hpair_collision : pair_collision_core_exact pair_collision_core)
    (Hpair_root : pair_root_core_exact pair_root_core)
    (f : SRC.monic_sextic)
    (hfactor : SRC.has_bounded_proper_factor f = false) :
  pair_selected_rootb pair_collision_core pair_eventually
      pair_root_core (FD.encode_monic_sextic_coefficients f) =
  RR.pair_scaled_rational_rootb f
    (MSI.pair_projected_separating_parameter f).
Proof.
rewrite /pair_selected_rootb /selected_projected_rootb
  /MSI.pair_projected_separating_parameter.
have hindex := pair_selected_index_mathcomp
  pair_eventually Hpair_collision hfactor.
rewrite /pair_selected_index in hindex.
rewrite hindex.
exact (Hpair_root f (MSI.pair_projected_separating_index f) hfactor).
Qed.

Lemma triple_selected_rootb_mathcomp
    (triple_collision_core triple_root_core : Vector.t nat 8 -> bool)
    (triple_eventually :
      guarded_projected_eventually triple_collision_core)
    (Htriple_collision :
      triple_collision_core_exact triple_collision_core)
    (Htriple_root : triple_root_core_exact triple_root_core)
    (f : SRC.monic_sextic)
    (hfactor : SRC.has_bounded_proper_factor f = false) :
  triple_selected_rootb triple_collision_core triple_eventually
      triple_root_core (FD.encode_monic_sextic_coefficients f) =
  RR.triple_scaled_rational_rootb f
    (MSI.triple_projected_separating_parameter f).
Proof.
rewrite /triple_selected_rootb /selected_projected_rootb
  /MSI.triple_projected_separating_parameter.
have hindex := triple_selected_index_mathcomp
  triple_eventually Htriple_collision hfactor.
rewrite /triple_selected_index in hindex.
rewrite hindex.
exact (Htriple_root f (MSI.triple_projected_separating_index f) hfactor).
Qed.

Theorem encoded_irreducible_resolventb_mathcomp
    (pair_collision_core pair_root_core : Vector.t nat 8 -> bool)
    (pair_eventually : guarded_projected_eventually pair_collision_core)
    (Hpair_collision : pair_collision_core_exact pair_collision_core)
    (Hpair_root : pair_root_core_exact pair_root_core)
    (triple_collision_core triple_root_core : Vector.t nat 8 -> bool)
    (triple_eventually :
      guarded_projected_eventually triple_collision_core)
    (Htriple_collision :
      triple_collision_core_exact triple_collision_core)
    (Htriple_root : triple_root_core_exact triple_root_core)
    (f : SRC.monic_sextic)
    (hfactor : SRC.has_bounded_proper_factor f = false) :
  encoded_irreducible_resolventb
      pair_collision_core pair_eventually pair_root_core
      triple_collision_core triple_eventually triple_root_core
      (FD.encode_monic_sextic_coefficients f) =
  MSI.projected_irreducible_resolventb f.
Proof.
rewrite /encoded_irreducible_resolventb
  /MSI.projected_irreducible_resolventb.
rewrite (pair_selected_rootb_mathcomp pair_eventually
  Hpair_collision Hpair_root hfactor).
rewrite (triple_selected_rootb_mathcomp triple_eventually
  Htriple_collision Htriple_root hfactor).
reflexivity.
Qed.

Theorem encoded_irreducible_resolventP
    (pair_collision_core pair_root_core : Vector.t nat 8 -> bool)
    (pair_eventually : guarded_projected_eventually pair_collision_core)
    (Hpair_collision : pair_collision_core_exact pair_collision_core)
    (Hpair_root : pair_root_core_exact pair_root_core)
    (triple_collision_core triple_root_core : Vector.t nat 8 -> bool)
    (triple_eventually :
      guarded_projected_eventually triple_collision_core)
    (Htriple_collision :
      triple_collision_core_exact triple_collision_core)
    (Htriple_root : triple_root_core_exact triple_root_core)
    (f : SRC.monic_sextic)
    (hfactor : SRC.has_bounded_proper_factor f = false) :
  reflect
    (radical_formula_solves
      (CV.rational_monic_sextic f))
    (encoded_irreducible_resolventb
      pair_collision_core pair_eventually pair_root_core
      triple_collision_core triple_eventually triple_root_core
      (FD.encode_monic_sextic_coefficients f)).
Proof.
rewrite (encoded_irreducible_resolventb_mathcomp
  pair_eventually Hpair_collision Hpair_root
  triple_eventually Htriple_collision Htriple_root hfactor).
exact: MSI.projected_irreducible_resolvent_radicalP.
Qed.

End PolynomialFormulasSexticMuRecIrreducibleAssembly.

Print Assumptions
  PolynomialFormulasSexticMuRecIrreducibleAssembly.ra_projected_boolean_core_correct.
Print Assumptions
  PolynomialFormulasSexticMuRecIrreducibleAssembly.selected_projected_index_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecIrreducibleAssembly.ra_encoded_irreducible_resolvent_correct.
Print Assumptions
  PolynomialFormulasSexticMuRecIrreducibleAssembly.encoded_irreducible_resolvent_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecIrreducibleAssembly.encoded_irreducible_resolvent_code_relation_murec.
Print Assumptions
  PolynomialFormulasSexticMuRecIrreducibleAssembly.encoded_irreducible_resolventb_mathcomp.
Print Assumptions
  PolynomialFormulasSexticMuRecIrreducibleAssembly.encoded_irreducible_resolventP.
