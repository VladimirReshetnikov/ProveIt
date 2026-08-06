From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import map_gal char0 abel.
From PolynomialFormulas Require Import SexticRecursiveCore
  SexticFactorCompleteness SexticSparseResolvents SexticNewtonPowerSums
  SexticComputedResolvents SexticRationalRootSearch SexticSeparatingSearch
  SexticSeparatingSelector SexticVietaBridge SexticGaloisAction
  SexticDescriptorGaloisCriterion SexticTotalSeparatingSelector.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Notation ratrC := (@ratr algC).

Module PolynomialFormulasSexticCanonicalVieta.

Import PolynomialFormulasSexticRecursiveCore.
Import PolynomialFormulasSexticFactorCompleteness.
Import PolynomialFormulasSexticSparseResolvents.
Import PolynomialFormulasSexticNewtonPowerSums.
Import PolynomialFormulasSexticComputedResolvents.
Import PolynomialFormulasSexticRationalRootSearch.
Import PolynomialFormulasSexticSeparatingSearch.
Import PolynomialFormulasSexticSeparatingSelector.
Import PolynomialFormulasSexticVietaBridge.
Import PolynomialFormulasSexticGaloisAction.
Import PolynomialFormulasSexticDescriptorGaloisCriterion.
Import PolynomialFormulasSexticTotalSeparatingSelector.

(** The rational polynomial canonically attached to the transparent monic
    coefficient tuple. *)
Definition rational_monic_sextic (f : monic_sextic) : {poly rat} :=
  map_poly (intr : int -> rat) (monic_polynomial f).

Lemma size_rational_monic_sextic f :
  size (rational_monic_sextic f) = 7%N.
Proof.
by rewrite /rational_monic_sextic size_rat_int_poly size_monic_polynomial.
Qed.

Lemma rational_monic_sextic_monic f :
  rational_monic_sextic f \is monic.
Proof.
apply: monic_map.
exact: monic_polynomial_monic.
Qed.

(** Mapping the canonical [numfield] roots to [algC] turns the associated
    factorization supplied by MathComp-Abel into an equality: both sides are
    monic. *)
Lemma sextic_complex_root_factorization (p : {poly rat})
    (p_size : size p = 7%N) (p_monic : p \is monic) :
  map_poly ratrC p =
    \prod_(r <- @sextic_complex_root_tuple p p_size) ('X - r%:P).
Proof.
apply/eqP.
rewrite -eqp_monic ?monic_map ?monic_prod_XsubC //.
have h : map_poly (numfield_inC p) (map_poly (@ratr (numfield p)) p) %=
    map_poly (numfield_inC p)
      (\prod_(x <- sextic_root_seq p) ('X - x%:P)).
  by rewrite eqp_map (@sextic_ratr_factorization p p_size).
move: h.
rewrite -map_poly_comp map_prod_XsubC.
have hiota_rat : (numfield_inC p) \o (@ratr (numfield p)) =1 ratrC.
  by move=> q; rewrite /= fmorph_rat.
rewrite (eq_map_poly hiota_rat).
rewrite /sextic_complex_root_tuple /sextic_root_tuple /=.
by rewrite big_map.
Qed.

(** The exact factorization premise expected by the generic Vieta bridge. *)
Lemma canonical_monic_sextic_factorization (f : monic_sextic) :
  map_poly (intr : int -> algC) (monic_polynomial f) =
    \prod_(r <- @sextic_complex_root_tuple
      (rational_monic_sextic f) (size_rational_monic_sextic f))
      ('X - r%:P).
Proof.
rewrite -(sextic_complex_root_factorization
  (size_rational_monic_sextic f) (rational_monic_sextic_monic f)).
rewrite /rational_monic_sextic -map_poly_comp.
apply: eq_map_poly=> z /=.
by rewrite ratr_int.
Qed.

(** Vieta in precisely the coordinates consumed by the total separating
    selector and by [sextic_scaled_resolvent_solvableP]. *)
Theorem canonical_monic_sextic_vieta (f : monic_sextic) :
  @cast_int_values algC (monic_elementary_values f) =
    elementary_values (@sextic_complex_root_tuple
      (rational_monic_sextic f) (size_rational_monic_sextic f)).
Proof.
apply: monic_sextic_vieta.
exact: canonical_monic_sextic_factorization.
Qed.

(** In the branch where the transparent factor search found no proper
    factor, the rational polynomial used to build the canonical splitting
    field is irreducible. *)
Lemma rational_monic_sextic_irreducible (f : monic_sextic)
    (hfactor : has_bounded_proper_factor f = false) :
  irreducible_poly (rational_monic_sextic f).
Proof.
apply: (proj2 (irreducible_rat_int (monic_polynomial f))).
exact: no_bounded_proper_factor_irreducible hfactor.
Qed.

Lemma canonical_sextic_complex_roots_injective (f : monic_sextic)
    (hfactor : has_bounded_proper_factor f = false) :
  injective (tnth (@sextic_complex_root_tuple
    (rational_monic_sextic f) (size_rational_monic_sextic f))).
Proof.
exact: (@sextic_complex_root_tuple_injective
  (rational_monic_sextic f) (size_rational_monic_sextic f)
  (rational_monic_sextic_irreducible hfactor)).
Qed.

(** These are unconditional termination certificates for the guarded
    coefficient searches.  On a reducible input the guard succeeds at zero;
    otherwise Vieta and separability of the canonical roots supply the
    algebraic termination proof. *)
Lemma pair_total_separates_eventually (f : monic_sextic) :
  exists n, pair_total_separatesb f n = true.
Proof.
case hfactor: (has_bounded_proper_factor f).
- exists 0%N.
  by rewrite /pair_total_separatesb hfactor.
- exact: (@pair_total_separates_eventually_of_roots
    (@sextic_complex_root_tuple
      (rational_monic_sextic f) (size_rational_monic_sextic f)) f
    (canonical_monic_sextic_vieta f)
    (canonical_sextic_complex_roots_injective hfactor)).
Qed.

Lemma triple_total_separates_eventually (f : monic_sextic) :
  exists n, triple_total_separatesb f n = true.
Proof.
case hfactor: (has_bounded_proper_factor f).
- exists 0%N.
  by rewrite /triple_total_separatesb hfactor.
- exact: (@triple_total_separates_eventually_of_roots
    (@sextic_complex_root_tuple
      (rational_monic_sextic f) (size_rational_monic_sextic f)) f
    (canonical_monic_sextic_vieta f)
    (canonical_sextic_complex_roots_injective hfactor)).
Qed.

(** Proof arguments are erased by extraction; the resulting program is the
    direct least-index recursive search from [first_true_index]. *)
Definition pair_total_separating_index (f : monic_sextic) : nat :=
  @first_true_index (fun n => pair_total_separatesb f n)
    (pair_total_separates_eventually f).

Definition triple_total_separating_index (f : monic_sextic) : nat :=
  @first_true_index (fun n => triple_total_separatesb f n)
    (triple_total_separates_eventually f).

Definition pair_total_separating_parameter (f : monic_sextic) : parameter :=
  parameter_at (pair_total_separating_index f).

Definition triple_total_separating_parameter
    (f : monic_sextic) : parameter :=
  parameter_at (triple_total_separating_index f).

Lemma pair_total_separating_indexP f :
  pair_total_separatesb f (pair_total_separating_index f) = true.
Proof. exact: first_true_indexP. Qed.

Lemma triple_total_separating_indexP f :
  triple_total_separatesb f (triple_total_separating_index f) = true.
Proof. exact: first_true_indexP. Qed.

Lemma pair_total_separating_parameter_injective f
    (hfactor : has_bounded_proper_factor f = false) :
  pair_descriptor_injective
    (@sextic_complex_root_tuple
      (rational_monic_sextic f) (size_rational_monic_sextic f))
    (pair_total_separating_parameter f).
Proof.
apply: (elimT (@pair_separatesP
  (@sextic_complex_root_tuple
    (rational_monic_sextic f) (size_rational_monic_sextic f))
  f (pair_total_separating_parameter f)
  (canonical_monic_sextic_vieta f))).
have htotal := pair_total_separating_indexP f.
move: htotal.
by rewrite /pair_total_separating_parameter /pair_total_separatesb hfactor.
Qed.

Lemma triple_total_separating_parameter_injective f
    (hfactor : has_bounded_proper_factor f = false) :
  triple_descriptor_injective
    (@sextic_complex_root_tuple
      (rational_monic_sextic f) (size_rational_monic_sextic f))
    (triple_total_separating_parameter f).
Proof.
apply: (elimT (@triple_separatesP
  (@sextic_complex_root_tuple
    (rational_monic_sextic f) (size_rational_monic_sextic f))
  f (triple_total_separating_parameter f)
  (canonical_monic_sextic_vieta f))).
have htotal := triple_total_separating_indexP f.
move: htotal.
by rewrite /triple_total_separating_parameter /triple_total_separatesb
  hfactor.
Qed.

(** The irreducible branch of the executable sextic test, with every
    semantic side condition discharged from the coefficient tuple. *)
Theorem canonical_sextic_scaled_resolvent_solvableP f
    (hfactor : has_bounded_proper_factor f = false) :
  reflect
    (solvable 'Gal({: numfield (rational_monic_sextic f)} / 1%AS))
    (pair_scaled_rational_rootb f (pair_total_separating_parameter f) ||
      triple_scaled_rational_rootb f
        (triple_total_separating_parameter f)).
Proof.
exact: (@sextic_scaled_resolvent_solvableP
  (rational_monic_sextic f) (size_rational_monic_sextic f)
  (rational_monic_sextic_irreducible hfactor) f
  (pair_total_separating_parameter f)
  (triple_total_separating_parameter f)
  (canonical_monic_sextic_vieta f)
  (pair_total_separating_parameter_injective hfactor)
  (triple_total_separating_parameter_injective hfactor)).
Qed.

End PolynomialFormulasSexticCanonicalVieta.
