From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Stdlib Require Import Ring.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import map_gal char0 abel.
From PolynomialFormulas Require Import
  AbelRuffini QuinticF20Data QuinticThetaValues QuinticChapman
  QuinticPaddedSymmetrization
  QuinticThetaGaloisBridge QuinticRecursiveFactor
  QuinticGaloisAction QuinticFiveCycle QuinticRadicalDecidability
  ReducibleRadicalSemantics SexticRecursiveCore SexticComputedResolvents
  SexticPowerSumSymmetric SexticNewtonPowerSums SexticVietaBridge
  SexticRationalRootSearch SexticHomogeneousRootSearch.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The exact coefficient-level Frobenius--Dummit decision for a monic
    integer quintic. *)
Module PolynomialFormulasQuinticCanonicalDecision.

Import GRing.Theory.
Import Num.Theory.
Import LeanProofs.PolynomialFormulasAbelRuffini.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasQuinticThetaValues.
Import PolynomialFormulasQuinticChapman.
Import PolynomialFormulasQuinticPaddedSymmetrization.
Import PolynomialFormulasQuinticThetaGaloisBridge.
Import PolynomialFormulasQuinticGaloisAction.
Import PolynomialFormulasQuinticFiveCycle.
Import PolynomialFormulasQuinticRadicalDecidability.
Import PolynomialFormulasReducibleRadicalSemantics.
Import PolynomialFormulasSexticRecursiveCore.
Import PolynomialFormulasSexticComputedResolvents.
Import PolynomialFormulasSexticPowerSumSymmetric.
Import PolynomialFormulasSexticNewtonPowerSums.
Import PolynomialFormulasSexticVietaBridge.
Import PolynomialFormulasSexticHomogeneousRootSearch.
Import PolynomialFormulasSexticRationalRootSearch.
Import PolynomialFormulasQuinticRecursiveFactor.

Local Open Scope ring_scope.

Definition rational_monic_quintic (f : monic_quintic) : {poly rat} :=
  map_poly (intr : int -> rat) (quintic_polynomial f).

Lemma size_rational_monic_quintic f :
  size (rational_monic_quintic f) = 6%N.
Proof.
by rewrite /rational_monic_quintic size_rat_int_poly
  size_quintic_polynomial.
Qed.

Lemma rational_monic_quintic_monic f :
  rational_monic_quintic f \is monic.
Proof.
apply: monic_map.
exact: quintic_polynomial_monic.
Qed.

Lemma rational_monic_quintic_irreducible f
    (hfactor : has_bounded_proper_factor f = false) :
  irreducible_poly (rational_monic_quintic f).
Proof.
have hirrb : quintic_irreducibleb f.
  by rewrite /quintic_irreducibleb hfactor.
exact: (elimT (quintic_irreducible_ratP f) hirrb).
Qed.

Section ScaledResolventCorrectness.

Variable R : comNzRingType.

(** The executable ascending integer coefficient list is exactly the scalar
    Dummit resolvent, multiplied by the nonzero homogeneous scale used to
    make all coefficients symmetric integral expressions. *)
Theorem quintic_scaled_resolvent_poly_correct roots f :
  @cast_int_values R
      (monic_elementary_values (quintic_sextic_embedding f)) =
      elementary_values (pad_quintic_roots roots) ->
  map_poly (intr : int -> R)
      (coefficient_list_poly_int (quintic_scaled_resolvent f)) =
    (120%:R * \prod_(j : 'I_5) tnth roots j) *:
      quintic_scalar_resolvent roots.
Proof.
move=> hvieta; apply/polyP=> i.
rewrite coef_map coefficient_list_poly_int_coef coefZ.
case hi: (i < 7)%N.
- rewrite (nth_quintic_scaled_resolvent f (Ordinal hi)).
  rewrite -mulrA.
  exact: (@quintic_scaled_resolvent_coefficient_correct
    R roots f (Ordinal hi) hvieta).
- have h7i : (7 <= i)%N by rewrite leqNgt hi.
  rewrite nth_default ?size_quintic_scaled_resolvent //.
  rewrite nth_default ?size_quintic_scalar_resolvent //.
  by rewrite mulr0.
Qed.

End ScaledResolventCorrectness.

Section ScaledResolventRoots.

Variable K : fieldType.
Variable ratrK : {rmorphism rat -> K}.

Definition quintic_semantic_has_rational_root
    (roots : 5.-tuple K) : Prop :=
  exists q : rat,
    root (quintic_scalar_resolvent roots) (ratrK q).

Lemma int_poly_horner_fmorph (p : {poly int}) q :
  (map_poly (intr : int -> K) p).[ratrK q] =
    ratrK ((map_poly (intr : int -> rat) p).[q]).
Proof.
rewrite -horner_map -map_poly_comp.
apply: (congr1 (fun r : {poly K} => r.[ratrK q])).
apply/polyP=> i.
by rewrite !coef_map /= rmorph_int.
Qed.

Theorem quintic_scaled_resolvent_has_rational_root_correct roots f :
  @cast_int_values K
      (monic_elementary_values (quintic_sextic_embedding f)) =
      elementary_values (pad_quintic_roots roots) ->
  120%:R * \prod_(j : 'I_5) tnth roots j != 0 ->
  has_rational_root (quintic_scaled_resolvent f) <->
    quintic_semantic_has_rational_root roots.
Proof.
move=> hvieta hscale; split=> [[q hq]|[q hq]]; exists q.
- have hp := congr1 (fun p : {poly K} => p.[ratrK q])
    (@quintic_scaled_resolvent_poly_correct K roots f hvieta).
  rewrite int_poly_horner_fmorph hq rmorph0 hornerZ in hp.
  apply/rootP.
  have hprod :
      (120%:R * \prod_(j : 'I_5) tnth roots j) *
        (quintic_scalar_resolvent roots).[ratrK q] = 0
      by exact: esym hp.
  move/eqP: hprod.
  rewrite mulf_eq0 (negPf hscale) /=.
  by move=> /eqP.
- move/rootP: hq=> hq.
  have hp := congr1 (fun p : {poly K} => p.[ratrK q])
    (@quintic_scaled_resolvent_poly_correct K roots f hvieta).
  rewrite int_poly_horner_fmorph hornerZ hq mulr0 in hp.
  apply: (fmorph_inj ratrK).
  by rewrite rmorph0.
Qed.

Theorem quintic_scaled_semantic_rational_rootP roots f
    (hvieta : @cast_int_values K
      (monic_elementary_values (quintic_sextic_embedding f)) =
      elementary_values (pad_quintic_roots roots))
    (hscale : 120%:R * \prod_(j : 'I_5) tnth roots j != 0) :
  reflect (quintic_semantic_has_rational_root roots)
    (bounded_homogeneous_rootb (quintic_scaled_resolvent f)).
Proof.
apply: (iffP (homogeneous_rational_rootP (quintic_scaled_resolvent f))).
- exact: (proj1 (@quintic_scaled_resolvent_has_rational_root_correct
    roots f hvieta hscale)).
- exact: (proj2 (@quintic_scaled_resolvent_has_rational_root_correct
    roots f hvieta hscale)).
Qed.

End ScaledResolventRoots.

Section QuinticTupleLemmas.

Variable R : comNzRingType.

Lemma quintic_root_sumE (roots : 5.-tuple R) :
  \sum_(i : 'I_5) tnth roots i =
    tnth roots o0 + tnth roots o1 + tnth roots o2 +
      tnth roots o3 + tnth roots o4.
Proof.
rewrite !big_ord_recl !big_ord0.
have h0 : (@ord0 4) = o0 by apply: val_inj.
have h1 : lift (@ord0 4) (@ord0 3) = o1 by apply: val_inj.
have h2 : lift (@ord0 4) (lift (@ord0 3) (@ord0 2)) = o2
  by apply: val_inj.
have h3 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2) (@ord0 1))) = o3
  by apply: val_inj.
have h4 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2) (lift (@ord0 1) (@ord0 0)))) = o4
  by apply: val_inj.
by rewrite h4 h3 h2 h1 h0 addr0 !addrA.
Qed.

Lemma quintic_root_sum_permute (roots : 5.-tuple R) (s : S5) :
  \sum_(i : 'I_5) tnth (permute_quintic_roots s roots) i =
    \sum_(i : 'I_5) tnth roots i.
Proof.
under [LHS]eq_bigr=> i _ do rewrite tnth_permute_quintic_roots.
rewrite (reindex_inj (@perm_inj _ s^-1)) /=.
under [LHS]eq_bigr=> i _ do rewrite permKV.
reflexivity.
Qed.

Lemma root_esymm_pad_quintic_ord0 (roots : 5.-tuple R) :
  root_esymm (pad_quintic_roots roots) ord0 =
    tnth roots o0 + tnth roots o1 + tnth roots o2 +
      tnth roots o3 + tnth roots o4.
Proof.
rewrite -root_power_sum_one /root_power_sum big_ord_recr /=.
under eq_bigr=> i _ do
  rewrite tnth_pad_quintic_roots_in expr1.
rewrite tnth_pad_quintic_roots_last expr1 addr0.
exact: quintic_root_sumE.
Qed.

Lemma quintic_theta_value_injective_permute (roots : 5.-tuple R) s :
  injective
      (quintic_theta_value (permute_quintic_roots s roots)) ->
    injective (quintic_theta_value roots).
Proof.
move=> hinj i j hij.
have hpre :
    quintic_theta_index_action (s^-1)%g i =
      quintic_theta_index_action (s^-1)%g j.
  apply: hinj.
  rewrite !quintic_theta_value_permute.
  rewrite -!quintic_theta_index_action_mul mulVg.
  by rewrite !quintic_theta_index_action_one.
exact: (@quintic_theta_index_action_injective (s^-1)%g i j hpre).
Qed.

End QuinticTupleLemmas.

Section CanonicalRoots.

Variable f : monic_quintic.
Let p := rational_monic_quintic f.
Let p_size : size p = 6%N := size_rational_monic_quintic f.
Let L := numfield p.
Let ratrL : {rmorphism rat -> L} := char0_ratr (char_numfield p).
Let roots : 5.-tuple L := @quintic_root_tuple p p_size.

Lemma canonical_quintic_numfield_factorization :
  map_poly ratrL p =
    \prod_(r <- roots) ('X - r%:P : {poly L}).
Proof.
have hpmonic : p \is monic.
  exact: rational_monic_quintic_monic.
have hmapmonic : map_poly ratrL p \is monic.
  exact: (monic_map ratrL hpmonic).
have hprodmonic :
    (\prod_(r <- roots) ('X - r%:P : {poly L})) \is monic.
  exact: monic_prod_XsubC.
apply/eqP.
move: (@quintic_ratr_factorization p p_size).
rewrite /ratrL char0_ratrE.
by rewrite (eqp_monic hmapmonic hprodmonic).
Qed.

Lemma prod_XsubC_pad_quintic_roots :
  \prod_(r <- pad_quintic_roots roots) ('X - r%:P : {poly L}) =
    'X * \prod_(r <- roots) ('X - r%:P : {poly L}).
Proof.
rewrite -(map_tnth_enum (pad_quintic_roots roots)) big_map big_enum.
rewrite -(map_tnth_enum roots) big_map big_enum.
rewrite !big_ord_recl !big_ord0.
rewrite /pad_quintic_roots !tnth_mktuple /=.
have h0 : (inord 0 : 'I_5) = ord0.
  apply: val_inj; exact: (@inordK 4 0 isT).
have h1 : (inord (bump 0 0) : 'I_5) = lift ord0 ord0
  by apply: val_inj; exact: (@inordK 4 1 isT).
have h2 : (inord (bump 0 (bump 0 0)) : 'I_5) =
    lift ord0 (lift ord0 ord0)
  by apply: val_inj; exact: (@inordK 4 2 isT).
have h3 : (inord (bump 0 (bump 0 (bump 0 0))) : 'I_5) =
    lift ord0 (lift ord0 (lift ord0 ord0))
  by apply: val_inj; exact: (@inordK 4 3 isT).
have h4 : (inord (bump 0 (bump 0 (bump 0 (bump 0 0)))) : 'I_5) =
    lift ord0 (lift ord0 (lift ord0 (lift ord0 ord0)))
  by apply: val_inj; exact: (@inordK 4 4 isT).
rewrite h0 h1 h2 h3 h4 subr0 !mulr1.
rewrite [(_ * 'X)]mulrC.
do 4! rewrite [(_ * ('X * _))]mulrCA.
reflexivity.
Qed.

Lemma canonical_quintic_padded_factorization :
  map_poly (intr : int -> L)
      (monic_polynomial (quintic_sextic_embedding f)) =
    \prod_(r <- pad_quintic_roots roots) ('X - r%:P : {poly L}).
Proof.
change (map_poly (intr : {rmorphism int -> L})
    (monic_polynomial (quintic_sextic_embedding f)) =
  \prod_(r <- pad_quintic_roots roots) ('X - r%:P : {poly L})).
rewrite quintic_embedding_identity rmorphM /= map_polyX.
rewrite prod_XsubC_pad_quintic_roots.
congr ('X * _).
transitivity (map_poly ratrL
  (map_poly (intr : int -> rat) (quintic_polynomial f))).
- rewrite -map_poly_comp.
  apply: eq_map_poly=> z.
  by rewrite /= rmorph_int.
- exact: canonical_quintic_numfield_factorization.
Qed.

Theorem canonical_quintic_padded_vieta :
  @cast_int_values L
      (monic_elementary_values (quintic_sextic_embedding f)) =
    elementary_values (pad_quintic_roots roots).
Proof.
apply: monic_sextic_vieta.
exact: canonical_quintic_padded_factorization.
Qed.

Lemma canonical_quintic_root_sum_rational :
  exists q : rat,
    tnth roots o0 + tnth roots o1 + tnth roots o2 +
      tnth roots o3 + tnth roots o4 = ratrL q.
Proof.
have hv := congr1 (fun values : 6.-tuple L => tnth values ord0)
  canonical_quintic_padded_vieta.
rewrite /cast_int_values tnth_mktuple tnth_elementary_values
  root_esymm_pad_quintic_ord0 in hv.
exists ((tnth
  (monic_elementary_values (quintic_sextic_embedding f)) ord0)%:~R : rat).
rewrite rmorph_int.
exact: esym hv.
Qed.

Lemma canonical_quintic_all_roots (k : 'I_5) :
  root (map_poly ratrL p) (tnth roots k).
Proof.
by rewrite canonical_quintic_numfield_factorization
  root_prod_XsubC mem_tnth.
Qed.

(** The converse direction is just as important for a root-producing
    formula: every root in the canonical splitting field occurs in the
    five-entry tuple.  This is multiplicity-aware through the exact monic
    factorization above; irreducibility is not needed for the set-level
    statement. *)
Theorem canonical_quintic_root_iff_exists_index (x : L) :
  root (map_poly ratrL p) x <->
    exists k : 'I_5, x = tnth roots k.
Proof.
rewrite canonical_quintic_numfield_factorization root_prod_XsubC.
split.
- by move=> /tnthP [k hx]; exists k.
- by move=> [k hx]; apply/tnthP; exists k.
Qed.

(** Public soundness-and-completeness package for the canonical root vector.
    The first conjunct says that every displayed entry is a root; the second
    says that the vector omits no root of the quintic in its splitting
    field. *)
Theorem canonical_quintic_root_vector_correct :
  (forall k : 'I_5, root (map_poly ratrL p) (tnth roots k)) /\
  (forall x : L, root (map_poly ratrL p) x ->
    exists k : 'I_5, x = tnth roots k).
Proof.
split.
- exact: canonical_quintic_all_roots.
- move=> x.
  exact: (proj1 (canonical_quintic_root_iff_exists_index x)).
Qed.

Theorem canonical_quintic_theta_value_injective
    (p_irr : irreducible_poly p) :
  injective (quintic_theta_value roots).
Proof.
have [s [sigma [hsigma_bijective hsigma]]] :=
  @irreducible_quintic_five_cycle_automorphism p p_size p_irr.
have hroots' :
    injective (tnth (@reindexed_quintic_roots p p_size s)).
  move=> i j.
  rewrite /reindexed_quintic_roots !tnth_permute_quintic_roots.
  move=> hij.
  apply: (@perm_inj _ s).
  exact: (@quintic_root_tuple_injective p p_size p_irr _ _ hij).
have hall_roots' : forall k : 'I_5,
    root (map_poly ratrL p)
      (tnth (@reindexed_quintic_roots p p_size s) k).
  move=> k.
  rewrite /reindexed_quintic_roots tnth_permute_quintic_roots.
  exact: canonical_quintic_all_roots.
have hsum' : exists q : rat,
    tnth (@reindexed_quintic_roots p p_size s) o0 +
      tnth (@reindexed_quintic_roots p p_size s) o1 +
      tnth (@reindexed_quintic_roots p p_size s) o2 +
      tnth (@reindexed_quintic_roots p p_size s) o3 +
      tnth (@reindexed_quintic_roots p p_size s) o4 = ratrL q.
  have [q hq] := canonical_quintic_root_sum_rational.
  exists q.
  rewrite -quintic_root_sumE /reindexed_quintic_roots.
  rewrite quintic_root_sum_permute quintic_root_sumE.
  exact: hq.
have hinj' :=
  @quintic_theta_value_injective_of_five_cycle_automorphism
    p L ratrL (@reindexed_quintic_roots p p_size s)
    p_size p_irr hroots' hall_roots' hsum'
    sigma hsigma_bijective hsigma.
apply: (@quintic_theta_value_injective_permute L roots s).
exact: hinj'.
Qed.

Lemma canonical_quintic_root_nonzero
    (p_irr : irreducible_poly p) (i : 'I_5) :
  tnth roots i != 0.
Proof.
apply/eqP=> hroot0.
have hrootL : root (map_poly ratrL p) (tnth roots i).
  by rewrite canonical_quintic_numfield_factorization
    root_prod_XsubC mem_tnth.
rewrite hroot0 -(rmorph0 ratrL) mapf_root in hrootL.
have hXdiv : 'X %| p.
  by move: hrootL; rewrite -['X]subr0 root_factor_theorem.
have hXp : 'X %= p.
  apply: p_irr=> //.
  by rewrite size_polyX.
have hsize := eqp_size hXp.
by move: hsize; rewrite size_polyX p_size.
Qed.

Lemma canonical_quintic_root_product_nonzero
    (p_irr : irreducible_poly p) :
  \prod_(i : 'I_5) tnth roots i != 0.
Proof.
apply/prodf_neq0=> i _.
exact: canonical_quintic_root_nonzero p_irr i.
Qed.

Lemma canonical_quintic_resolvent_scale_nonzero
    (p_irr : irreducible_poly p) :
  120%:R * \prod_(i : 'I_5) tnth roots i != 0.
Proof.
apply: mulf_neq0.
- have h120 : ratrL (120%:R : rat) != 0.
    by rewrite fmorph_eq0 pnatr_eq0.
  by move: h120; rewrite rmorph_nat.
- exact: canonical_quintic_root_product_nonzero p_irr.
Qed.

Theorem canonical_irreducible_quintic_scaled_resolvent_solvableP
    (p_irr : irreducible_poly p) :
  reflect (solvable 'Gal({:L} / 1%AS))
    (bounded_homogeneous_rootb (quintic_scaled_resolvent f)).
Proof.
apply: (equivP (@quintic_scaled_semantic_rational_rootP
  L (in_alg L) roots f canonical_quintic_padded_vieta
  (canonical_quintic_resolvent_scale_nonzero p_irr))).
exact: (@quintic_scalar_resolvent_has_rational_root_iff_galois_solvable
  p p_size p_irr (canonical_quintic_theta_value_injective p_irr)).
Qed.

Theorem canonical_irreducible_quintic_scaled_resolvent_radicalP
    (p_irr : irreducible_poly p) :
  reflect (radical_formula_solves p)
    (bounded_homogeneous_rootb (quintic_scaled_resolvent f)).
Proof.
apply: (equivP
  (canonical_irreducible_quintic_scaled_resolvent_solvableP p_irr)).
split.
- move=> hsolv.
  apply: (elimT (quintic_every_root_has_radical_expressionP p_size)).
  exact: hsolv.
- move=> hradical.
  exact: (introT (quintic_every_root_has_radical_expressionP p_size)
    hradical).
Qed.

End CanonicalRoots.

(** The promised coefficient-only decision.  The first disjunct is the
    exhaustive bounded factor search.  On the irreducible branch, the second
    disjunct is exactly rational-root search on the computed scaled Dummit
    resolvent. *)
Definition quintic_radicalb (f : monic_quintic) : bool :=
  has_bounded_proper_factor f ||
    bounded_homogeneous_rootb (quintic_scaled_resolvent f).

Theorem quintic_radicalP (f : monic_quintic) :
  reflect (radical_formula_solves (rational_monic_quintic f))
    (quintic_radicalb f).
Proof.
rewrite /quintic_radicalb.
case hfactor: (has_bounded_proper_factor f).
- rewrite /=.
  apply: ReflectT.
  apply: reducible_monic_quintic_tuple_radical_formula.
  have hfactor_true : has_bounded_proper_factor f by rewrite hfactor.
  exact: (elimT (has_bounded_proper_factor_ratP f) hfactor_true).
- rewrite /=.
  have p_irr := @rational_monic_quintic_irreducible f hfactor.
  exact: (@canonical_irreducible_quintic_scaled_resolvent_radicalP
    f p_irr).
Qed.

End PolynomialFormulasQuinticCanonicalDecision.
