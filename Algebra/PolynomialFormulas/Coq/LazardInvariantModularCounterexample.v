From mathcomp Require Import all_ssreflect all_fingroup all_algebra.

From PolynomialFormulas Require Import
  LazardInvariantSubgroupModule LazardInvariantSubgroupTheoremTwo.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A finite modular obstruction to Lazard's unrestricted Theorem 2.

    Over the three-element field let the regular cyclic group [C6] rotate
    six variables.  In degree seven there are 132 monomial orbits.  The 159
    products of an elementary symmetric polynomial with a lower-degree orbit
    sum span a subspace of rank 115.  Thus the degree-seven quotient by
    [(e1,...,e6)] has dimension 17.  Graded freeness over the symmetric
    coefficient ring would force the Hilbert-numerator coefficient 16.

    Everything below is the literal finite orbit/product matrix.  [vm_compute]
    evaluates MathComp's proved matrix-rank algorithm over ['F_3]; no external
    rank certificate or native-code escape is used.

    The final theorem records the corrected uniform hypothesis: the finite
    subgroup order must be nonzero in the ground field.  The characteristic-
    zero result already exported by the development is its convenient main
    specialization. *)
Module PolynomialFormulasLazardInvariantModularCounterexample.

Import GRing.Theory.
Local Open Scope ring_scope.

Module SIM := PolynomialFormulasLazardInvariantSubgroupModule.
Module T2 := PolynomialFormulasLazardInvariantSubgroupTheoremTwo.

Local Notation Exponent := (6.-tuple nat).
Local Notation F3 := 'F_3.

(** Weak compositions of [total] into [slots] entries. *)
Fixpoint weak_compositions (slots total : nat) : seq (slots.-tuple nat) :=
  match slots as s return seq (s.-tuple nat) with
  | 0 => if total == 0 then [:: [tuple]] else [::]
  | s.+1 =>
      flatten
        [seq [seq [tuple of first :: tail]
                    | tail <- weak_compositions s (total - first)]
          | first <- iota 0 total.+1]
  end.

Definition rotate_exponent (a : Exponent) (k : nat) : Exponent :=
  [tuple tnth a (inord ((i + k) %% 6)) | i < 6].

Definition exponent_code (a : Exponent) : nat :=
  \sum_(i < 6) tnth a i * 8 ^ (i : nat).

Definition exponent_min (a b : Exponent) : Exponent :=
  if exponent_code b < exponent_code a then b else a.

Definition cyclic_orbit (a : Exponent) : seq Exponent :=
  undup [seq rotate_exponent a k | k <- iota 0 6].

Definition canonical_exponent (a : Exponent) : Exponent :=
  foldl exponent_min a (cyclic_orbit a).

(** The base-eight code is injective on every degree used here, because all
    exponents are at most seven. *)
Definition orbit_representatives (degree : nat) : seq Exponent :=
  undup [seq canonical_exponent a | a <- weak_compositions 6 degree].

Definition add_exponent (a b : Exponent) : Exponent :=
  [tuple tnth a i + tnth b i | i < 6].

Definition elementary_exponents (degree : nat) : seq Exponent :=
  [seq a <- weak_compositions 6 degree |
    [forall i : 'I_6, tnth a i <= 1]].

Definition product_monomials
    (source : Exponent) (elementary_degree : nat) : seq Exponent :=
  flatten
    [seq [seq add_exponent a e | e <- elementary_exponents elementary_degree]
      | a <- cyclic_orbit source].

(** Coefficient of [target] in
    [e_i * (the orbit sum of source)], reduced in ['F_3]. *)
Definition product_coefficient
    (source : Exponent) (elementary_degree : nat) (target : Exponent) : F3 :=
  (count (pred1 target) (product_monomials source elementary_degree))%:R.

Definition product_sources (target_degree : nat) : seq (nat * Exponent) :=
  flatten
    [seq [seq (elementary_degree, source)
                | source <- orbit_representatives
                    (target_degree - elementary_degree)]
      | elementary_degree <- iota 1 (minn 6 target_degree)].

Definition zero_exponent : Exponent := [tuple 0; 0; 0; 0; 0; 0].

Definition product_matrix (target_degree : nat) :
    'M[F3]_(size (product_sources target_degree),
      size (orbit_representatives target_degree)) :=
  \matrix_(r, c)
    let source := nth (1, zero_exponent) (product_sources target_degree) r in
    let target := nth zero_exponent (orbit_representatives target_degree) c in
    product_coefficient source.2 source.1 target.

Definition invariant_orbit_count (degree : nat) : nat :=
  size (orbit_representatives degree).

Definition product_span_rank (degree : nat) : nat :=
  \rank (product_matrix degree).

Definition invariant_quotient_dimension (degree : nat) : nat :=
  invariant_orbit_count degree - product_span_rank degree.

Lemma cyclic_six_degree_seven_orbit_count :
  invariant_orbit_count 7 = 132.
Proof. vm_compute. Qed.

Lemma cyclic_six_degree_seven_product_count :
  size (product_sources 7) = 159.
Proof. vm_compute. Qed.

Lemma cyclic_six_degree_seven_product_rank :
  product_span_rank 7 = 115.
Proof. vm_compute. Qed.

Lemma cyclic_six_degree_seven_invariant_quotient_dimension :
  invariant_quotient_dimension 7 = 17.
Proof. vm_compute. Qed.

(** Coefficients in the polynomial ring on [e1,...,e6], with the usual
    weights [1,...,6]. *)
Definition elementary_weight (a : Exponent) : nat :=
  \sum_(i < 6) i.+1 * tnth a i.

Definition coefficient_exponents (degree : nat) : seq Exponent :=
  flatten [seq weak_compositions 6 s | s <- iota 0 degree.+1].

Definition symmetric_monomial_count (degree : nat) : nat :=
  count (fun a => elementary_weight a == degree)
    (coefficient_exponents degree).

Definition append_forced_free_count
    (counts : seq nat) (degree : nat) : seq nat :=
  let old_contribution :=
    \sum_(j < size counts)
      nth 0 counts j * symmetric_monomial_count (degree - j) in
  rcons counts (invariant_orbit_count degree - old_contribution).

Definition forced_free_generator_counts_up_to (degree : nat) : seq nat :=
  foldl append_forced_free_count [::] (iota 0 degree.+1).

Definition forced_free_generator_count (degree : nat) : nat :=
  nth 0 (forced_free_generator_counts_up_to degree) degree.

Lemma cyclic_six_degree_seven_forced_free_generator_count :
  forced_free_generator_count 7 = 16.
Proof. vm_compute. Qed.

Definition degree_seven_free_compatibility : Prop :=
  invariant_quotient_dimension 7 = forced_free_generator_count 7.

Theorem cyclic_six_char_three_not_degree_seven_free_compatible :
  ~ degree_seven_free_compatibility.
Proof.
rewrite /degree_seven_free_compatibility
  cyclic_six_degree_seven_invariant_quotient_dimension
  cyclic_six_degree_seven_forced_free_generator_count.
by [].
Qed.

(** Corrected nonmodular form of Lazard's Theorem 2.  The construction in
    [LazardInvariantSubgroupTheoremTwo] already keeps this exact hypothesis
    explicit; its public characteristic-zero theorem merely derives it. *)
Theorem lazard_theorem_two_nonmodular_statement
    (F : fieldType) (n : nat) (H : {group 'S_n})
    (cardH_neq0 : (#|[subg H]|%:R : F) != 0) :
  inhabited (@SIM.lazard_homogeneous_invariant_basis F n H).
Proof.
constructor.
exact: T2.lazard_subgroup_invariant_homogeneous_finite_free cardH_neq0.
Qed.

End PolynomialFormulasLazardInvariantModularCounterexample.
