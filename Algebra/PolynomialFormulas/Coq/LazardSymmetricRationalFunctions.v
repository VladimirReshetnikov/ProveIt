From HB Require Import structures.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import LazardInvariantMultinomials.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Denominator symmetrization for symmetric rational functions.

    MathComp multinomials proves the fundamental theorem for symmetric
    *polynomials*, but does not package the corresponding fixed-field theorem
    for fractions.  The construction below fills its algebraic core.  For a
    fraction [p/q] fixed by all variable permutations, let

      [Q = product_s (s . q)]

    be the orbit norm of its denominator and let [P] be [p] times the product
    with the identity factor omitted.  Then [P*q = p*Q] in cross-multiplied
    form, [Q] is symmetric, and invariance of [p/q] forces [P] symmetric as
    well.  The polynomial fundamental theorem therefore writes both [P] and
    [Q] in the elementary symmetric polynomials.

    The development first lifts variable permutations through MathComp's
    quotient construction to honest ring automorphisms of [{fraction R}].
    It then connects quotient fixedness to a nonzero numerator/denominator
    presentation and proves the literal fixed-predicate iff
    elementary-symmetric-fraction-range statement. *)
Module PolynomialFormulasLazardSymmetricRationalFunctions.

Import GRing.Theory.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module IM := PolynomialFormulasLazardInvariantMultinomials.

Section SymmetricFractions.

Variables (K : fieldType) (n : nat).

Local Notation MP := {mpoly K[n]}.
Local Notation RF := {fraction MP}.
Local Notation "p %:RF" := (@FracField.tofrac MP p)
  (at level 2, format "p %:RF").

Definition lazard_polynomial_permutation (s : 'S_n) (p : MP) : MP :=
  IM.mpoly_left_action s p.

Lemma lazard_polynomial_permutation1 p :
  lazard_polynomial_permutation 1 p = p.
Proof. exact: IM.mpoly_left_action1. Qed.

Lemma lazard_polynomial_permutationM s t p :
  lazard_polynomial_permutation (s * t) p =
    lazard_polynomial_permutation s
      (lazard_polynomial_permutation t p).
Proof. exact: IM.mpoly_left_actionM. Qed.

Lemma lazard_polynomial_permutation0 s :
  lazard_polynomial_permutation s 0 = 0.
Proof. exact: IM.mpoly_left_action0. Qed.

Lemma lazard_polynomial_permutationD s :
  {morph lazard_polynomial_permutation s : x y / x + y}.
Proof. exact: IM.mpoly_left_actionD. Qed.

Lemma lazard_polynomial_permutationN s :
  {morph lazard_polynomial_permutation s : x / - x}.
Proof. exact: IM.mpoly_left_actionN. Qed.

Lemma lazard_polynomial_permutation_mul s :
  {morph lazard_polynomial_permutation s : x y / x * y}.
Proof. exact: IM.mpoly_left_action_mul. Qed.

Lemma lazard_polynomial_permutation1r s :
  lazard_polynomial_permutation s 1 = 1.
Proof.
rewrite /lazard_polynomial_permutation /IM.mpoly_left_action.
exact: msym1.
Qed.

Lemma lazard_polynomial_permutation_prod s
    (I : finType) (P : pred I) (f : I -> MP) :
  lazard_polynomial_permutation s (\prod_(i | P i) f i) =
    \prod_(i | P i) lazard_polynomial_permutation s (f i).
Proof.
rewrite /lazard_polynomial_permutation /IM.mpoly_left_action.
exact: rmorph_prod.
Qed.

Lemma lazard_polynomial_permutation_injective s :
  injective (lazard_polynomial_permutation s).
Proof.
move=> p q hpq.
have := congr1 (lazard_polynomial_permutation s^-1) hpq.
by rewrite -!lazard_polynomial_permutationM mulVg
  !lazard_polynomial_permutation1.
Qed.

Lemma lazard_polynomial_permutation_eq0 s p :
  (lazard_polynomial_permutation s p == 0) = (p == 0).
Proof.
apply/idP/idP.
- move/eqP=> hp; apply/eqP.
  apply: lazard_polynomial_permutation_injective s.
  by rewrite hp lazard_polynomial_permutation0.
- move/eqP=> ->; apply/eqP.
  exact: lazard_polynomial_permutation0.
Qed.

Lemma lazard_polynomial_permutation_neq0 s p :
  (lazard_polynomial_permutation s p != 0) = (p != 0).
Proof. by rewrite lazard_polynomial_permutation_eq0. Qed.

(**************************************************************************)
(** * The induced action on the quotient fraction field *)

Import FracField.

Definition lazard_ratio_permutation (s : 'S_n) (r : {ratio MP}) :
    {ratio MP} :=
  Ratio (lazard_polynomial_permutation s \n_r)
    (lazard_polynomial_permutation s \d_r).

Lemma lazard_ratio_permutation_num s r :
  \n_(lazard_ratio_permutation s r) =
    lazard_polynomial_permutation s \n_r.
Proof.
rewrite /lazard_ratio_permutation numer_Ratio //.
by rewrite lazard_polynomial_permutation_neq0 denom_ratioP.
Qed.

Lemma lazard_ratio_permutation_den s r :
  \d_(lazard_ratio_permutation s r) =
    lazard_polynomial_permutation s \d_r.
Proof.
rewrite /lazard_ratio_permutation denom_Ratio //.
by rewrite lazard_polynomial_permutation_neq0 denom_ratioP.
Qed.

Definition lazard_fraction_permutation_fun (s : 'S_n) : RF -> RF :=
  lift_op1 RF (lazard_ratio_permutation s).

Lemma lazard_fraction_permutation_pi s :
  {morph \pi : r / lazard_ratio_permutation s r >->
    lazard_fraction_permutation_fun s r}.
Proof.
move=> r; unlock lazard_fraction_permutation_fun.
apply/eqmodP=> /=.
rewrite equivfE !lazard_ratio_permutation_num
  !lazard_ratio_permutation_den.
rewrite -!lazard_polynomial_permutation_mul.
rewrite (inj_eq (lazard_polynomial_permutation_injective s)).
by apply/eqP; exact: equivf_r r.
Qed.

Canonical lazard_fraction_permutation_pi_morph s :=
  PiMorph1 (lazard_fraction_permutation_pi s).

(** The lifted quotient operation restricts to the original permutation on
    the embedded polynomial ring. *)
Lemma lazard_fraction_permutation_fun_tofrac s p :
  lazard_fraction_permutation_fun s p%:RF =
    (lazard_polynomial_permutation s p)%:RF.
Proof.
unlock FracField.tofrac.
rewrite piE /lazard_ratio_permutation
  !numer_Ratio ?oner_neq0 // !denom_Ratio ?oner_neq0 //.
by rewrite lazard_polynomial_permutation1r.
Qed.

Lemma lazard_ratio_permutation1 r :
  lazard_ratio_permutation 1 r = r.
Proof.
rewrite /lazard_ratio_permutation !lazard_polynomial_permutation1.
exact: Ratio_numden.
Qed.

Lemma lazard_ratio_permutationM s t r :
  lazard_ratio_permutation (s * t) r =
    lazard_ratio_permutation s (lazard_ratio_permutation t r).
Proof.
apply: val_inj; congr (_, _).
- rewrite !lazard_ratio_permutation_num.
  exact: lazard_polynomial_permutationM.
- rewrite !lazard_ratio_permutation_den.
  exact: lazard_polynomial_permutationM.
Qed.

Lemma lazard_fraction_permutation_fun1 x :
  lazard_fraction_permutation_fun 1 x = x.
Proof.
elim/quotW: x=> r.
by rewrite !piE lazard_ratio_permutation1.
Qed.

Lemma lazard_fraction_permutation_funM s t x :
  lazard_fraction_permutation_fun (s * t) x =
    lazard_fraction_permutation_fun s
      (lazard_fraction_permutation_fun t x).
Proof.
elim/quotW: x=> r.
by rewrite !piE lazard_ratio_permutationM.
Qed.

Lemma lazard_ratio_permutation_add s r u :
  lazard_ratio_permutation s (addf r u) =
    addf (lazard_ratio_permutation s r)
      (lazard_ratio_permutation s u).
Proof.
apply: val_inj; congr (_, _).
- rewrite lazard_ratio_permutation_num /addf numer_Ratio
      ?mulf_neq0 ?denom_ratioP //.
  rewrite numer_Ratio
      ?mulf_neq0 ?lazard_polynomial_permutation_neq0 ?denom_ratioP //.
  rewrite !lazard_ratio_permutation_num !lazard_ratio_permutation_den.
  by rewrite lazard_polynomial_permutationD
    !lazard_polynomial_permutation_mul.
- rewrite lazard_ratio_permutation_den /addf denom_Ratio
      ?mulf_neq0 ?denom_ratioP //.
  rewrite denom_Ratio
      ?mulf_neq0 ?lazard_polynomial_permutation_neq0 ?denom_ratioP //.
  rewrite !lazard_ratio_permutation_den.
  exact: lazard_polynomial_permutation_mul.
Qed.

Lemma lazard_ratio_permutation_opp s r :
  lazard_ratio_permutation s (oppf r) =
    oppf (lazard_ratio_permutation s r).
Proof.
apply: val_inj; congr (_, _).
- rewrite lazard_ratio_permutation_num /oppf numer_Ratio ?denom_ratioP //.
  rewrite numer_Ratio
    ?lazard_polynomial_permutation_neq0 ?denom_ratioP //.
  rewrite lazard_ratio_permutation_num.
  exact: lazard_polynomial_permutationN.
- rewrite lazard_ratio_permutation_den /oppf denom_Ratio ?denom_ratioP //.
  rewrite denom_Ratio
    ?lazard_polynomial_permutation_neq0 ?denom_ratioP //.
  exact: lazard_ratio_permutation_den.
Qed.

Lemma lazard_ratio_permutation_mul s r u :
  lazard_ratio_permutation s (mulf r u) =
    mulf (lazard_ratio_permutation s r)
      (lazard_ratio_permutation s u).
Proof.
apply: val_inj; congr (_, _).
- rewrite lazard_ratio_permutation_num /mulf numer_Ratio
      ?mulf_neq0 ?denom_ratioP //.
  rewrite numer_Ratio
      ?mulf_neq0 ?lazard_polynomial_permutation_neq0 ?denom_ratioP //.
  rewrite !lazard_ratio_permutation_num.
  exact: lazard_polynomial_permutation_mul.
- rewrite lazard_ratio_permutation_den /mulf denom_Ratio
      ?mulf_neq0 ?denom_ratioP //.
  rewrite denom_Ratio
      ?mulf_neq0 ?lazard_polynomial_permutation_neq0 ?denom_ratioP //.
  rewrite !lazard_ratio_permutation_den.
  exact: lazard_polynomial_permutation_mul.
Qed.

Lemma lazard_fraction_permutation_funD s :
  {morph lazard_fraction_permutation_fun s : x y / x + y}.
Proof.
move=> x y; elim/quotW: x=> r; elim/quotW: y=> u.
by rewrite !piE lazard_ratio_permutation_add.
Qed.

Lemma lazard_fraction_permutation_funN s :
  {morph lazard_fraction_permutation_fun s : x / - x}.
Proof.
move=> x; elim/quotW: x=> r.
by rewrite !piE lazard_ratio_permutation_opp.
Qed.

Lemma lazard_fraction_permutation_funB s :
  {morph lazard_fraction_permutation_fun s : x y / x - y}.
Proof.
move=> x y.
by rewrite !subr_eq_addr lazard_fraction_permutation_funD
  lazard_fraction_permutation_funN.
Qed.

Lemma lazard_fraction_permutation_fun_mul s :
  {morph lazard_fraction_permutation_fun s : x y / x * y}.
Proof.
move=> x y; elim/quotW: x=> r; elim/quotW: y=> u.
by rewrite !piE lazard_ratio_permutation_mul.
Qed.

Lemma lazard_fraction_permutation_fun1r s :
  lazard_fraction_permutation_fun s 1 = 1.
Proof.
change lazard_fraction_permutation_fun s (1%:RF) = 1%:RF.
by rewrite lazard_fraction_permutation_fun_tofrac
  lazard_polynomial_permutation1r.
Qed.

Fact lazard_fraction_permutation_is_zmod_morphism s :
  zmod_morphism (lazard_fraction_permutation_fun s).
Proof. exact: lazard_fraction_permutation_funB. Qed.

Fact lazard_fraction_permutation_is_monoid_morphism s :
  monoid_morphism (lazard_fraction_permutation_fun s).
Proof.
split.
- exact: lazard_fraction_permutation_fun1r.
- exact: lazard_fraction_permutation_fun_mul.
Qed.

Definition lazard_fraction_permutation (s : 'S_n) : {rmorphism RF -> RF} :=
  HB.pack (lazard_fraction_permutation_fun s)
    (GRing.isZmodMorphism.Build _ _ (lazard_fraction_permutation_fun s)
      (lazard_fraction_permutation_is_zmod_morphism s))
    (GRing.isMonoidMorphism.Build _ _ (lazard_fraction_permutation_fun s)
      (lazard_fraction_permutation_is_monoid_morphism s)).

Lemma lazard_fraction_permutationE s x :
  lazard_fraction_permutation s x =
    lazard_fraction_permutation_fun s x.
Proof. by []. Qed.

Lemma lazard_fraction_permutation1 x :
  lazard_fraction_permutation 1 x = x.
Proof. exact: lazard_fraction_permutation_fun1. Qed.

Lemma lazard_fraction_permutationM s t x :
  lazard_fraction_permutation (s * t) x =
    lazard_fraction_permutation s (lazard_fraction_permutation t x).
Proof. exact: lazard_fraction_permutation_funM. Qed.

Lemma lazard_fraction_permutation_tofrac s p :
  lazard_fraction_permutation s p%:RF =
    (lazard_polynomial_permutation s p)%:RF.
Proof. exact: lazard_fraction_permutation_fun_tofrac. Qed.

Lemma lazard_fraction_permutation_div_tofrac s p q
    (q0 : q != 0) :
  lazard_fraction_permutation s (p%:RF / q%:RF) =
    (lazard_polynomial_permutation s p)%:RF /
      (lazard_polynomial_permutation s q)%:RF.
Proof.
have qFunit : q%:RF \in GRing.unit.
  by rewrite unitfE tofrac_eq0.
rewrite (rmorph_div qFunit).
by rewrite !lazard_fraction_permutation_tofrac.
Qed.

(** Every quotient element has an ordinary nonzero numerator/denominator
    presentation.  This exposes the representation hidden by the quotient
    type without choosing any extra normalization. *)
Lemma lazard_fraction_presentation (x : RF) :
  exists p q : MP, q != 0 /\ x = p%:RF / q%:RF.
Proof.
elim/quotW: x=> r.
exists \n_r, \d_r; split; first exact: denom_ratioP.
symmetry.
unlock FracField.tofrac.
rewrite !piE /FracField.invf /FracField.mulf
  !numden_Ratio ?(oner_neq0, mulf_neq0, denom_ratioP) //.
by rewrite !mulr1 !mul1r Ratio_numden.
Qed.

(** Literal fixedness for the quotient action. *)
Definition lazard_symmetric_fraction (x : RF) : Prop :=
  forall s : 'S_n, lazard_fraction_permutation s x = x.

(** Literal membership in the fraction field generated by the elementary
    symmetric polynomials, expressed through the injective substitution
    [sym_eval]. *)
Definition lazard_elementary_symmetric_fraction (x : RF) : Prop :=
  exists u v : MP,
    IM.sym_eval v != 0 /\
    x = (IM.sym_eval u)%:RF / (IM.sym_eval v)%:RF.

(** The full orbit norm of a polynomial denominator. *)
Definition lazard_denominator_orbit_norm (q : MP) : MP :=
  \prod_(s : 'S_n) lazard_polynomial_permutation s q.

(** Left multiplication reindexes the full permutation group. *)
Lemma lazard_denominator_orbit_norm_fixed t q :
  lazard_polynomial_permutation t (lazard_denominator_orbit_norm q) =
    lazard_denominator_orbit_norm q.
Proof.
rewrite /lazard_denominator_orbit_norm
  lazard_polynomial_permutation_prod.
under [LHS] eq_bigr => s _ do
  rewrite -lazard_polynomial_permutationM.
by rewrite (reindex_inj (mulgI t)).
Qed.

Lemma lazard_denominator_orbit_norm_symmetric q :
  lazard_denominator_orbit_norm q \is symmetric.
Proof.
apply/IM.full_symmetricP=> s.
exact: lazard_denominator_orbit_norm_fixed.
Qed.

Lemma lazard_denominator_orbit_norm_neq0 q :
  q != 0 -> lazard_denominator_orbit_norm q != 0.
Proof.
move=> q0; apply/prodf_neq0=> s _.
by rewrite lazard_polynomial_permutation_neq0.
Qed.

(** The product of all denominator conjugates except the identity one. *)
Definition lazard_denominator_cofactor (q : MP) : MP :=
  \prod_(s : 'S_n | s != 1%g) lazard_polynomial_permutation s q.

Lemma lazard_denominator_orbit_norm_split q :
  lazard_denominator_orbit_norm q =
    q * lazard_denominator_cofactor q.
Proof.
by rewrite /lazard_denominator_orbit_norm
  /lazard_denominator_cofactor (bigD1 (1%g : 'S_n)) //=
  lazard_polynomial_permutation1.
Qed.

Definition lazard_symmetrized_numerator (p q : MP) : MP :=
  p * lazard_denominator_cofactor q.

Lemma lazard_symmetrized_numerator_mul_denominator p q :
  lazard_symmetrized_numerator p q * q =
    p * lazard_denominator_orbit_norm q.
Proof.
rewrite /lazard_symmetrized_numerator
  lazard_denominator_orbit_norm_split.
by ring.
Qed.

(** Direct fraction-presentation form of invariance.  The transformed
    denominator is nonzero because every polynomial permutation is
    injective. *)
Definition lazard_symmetric_fraction_pair (p q : MP) : Prop :=
  q != 0 /\
  forall s : 'S_n,
    (lazard_polynomial_permutation s p)%:RF /
      (lazard_polynomial_permutation s q)%:RF = p%:RF / q%:RF.

(** Fraction invariance is equivalently the denominator-free family of
    cross-multiplication identities. *)
Lemma lazard_symmetric_fraction_pair_iff_cross p q :
  lazard_symmetric_fraction_pair p q <->
  q != 0 /\
  forall s : 'S_n,
    lazard_polynomial_permutation s p * q =
      p * lazard_polynomial_permutation s q.
Proof.
split.
- move=> [q0 invariant]; split=> // s.
  have sq0 : lazard_polynomial_permutation s q != 0.
    by rewrite lazard_polynomial_permutation_neq0.
  have sqF0 : (lazard_polynomial_permutation s q)%:RF != 0.
    by rewrite tofrac_eq0.
  have qF0 : q%:RF != 0 by rewrite tofrac_eq0.
  have hfrac :
      (lazard_polynomial_permutation s p)%:RF /
          (lazard_polynomial_permutation s q)%:RF ==
        p%:RF / q%:RF.
    exact/eqP: invariant s.
  move: hfrac.
  by rewrite (eqr_div sqF0 qF0) -!rmorphM tofrac_eq => /eqP.
- move=> [q0 cross]; split=> // s.
  have sq0 : lazard_polynomial_permutation s q != 0.
    by rewrite lazard_polynomial_permutation_neq0.
  have sqF0 : (lazard_polynomial_permutation s q)%:RF != 0.
    by rewrite tofrac_eq0.
  have qF0 : q%:RF != 0 by rewrite tofrac_eq0.
  apply/eqP.
  rewrite (eqr_div sqF0 qF0) -!rmorphM tofrac_eq.
  exact/eqP: cross s.
Qed.

(** The denominator-symmetrized numerator is fixed by every permutation.
    The proof avoids polynomial division: apply a permutation to
    [P*q = p*Q], use fixedness of [Q], cross-multiply once more, and cancel
    the two nonzero denominator factors in the integral domain. *)
Lemma lazard_symmetrized_numerator_fixed p q
    (q0 : q != 0)
    (cross : forall s : 'S_n,
      lazard_polynomial_permutation s p * q =
        p * lazard_polynomial_permutation s q)
    t :
  lazard_polynomial_permutation t
      (lazard_symmetrized_numerator p q) =
    lazard_symmetrized_numerator p q.
Proof.
set P := lazard_symmetrized_numerator p q.
set Q := lazard_denominator_orbit_norm q.
have Pq : P * q = p * Q.
  by rewrite /P /Q lazard_symmetrized_numerator_mul_denominator.
have acted := congr1 (lazard_polynomial_permutation t) Pq.
have Qt : lazard_polynomial_permutation t Q = Q.
  by rewrite /Q lazard_denominator_orbit_norm_fixed.
rewrite !lazard_polynomial_permutation_mul Qt in acted.
have tq0 : lazard_polynomial_permutation t q != 0.
  by rewrite lazard_polynomial_permutation_neq0.
apply: (mulfI (mulf_neq0 tq0 q0)).
transitivity
  (q * (lazard_polynomial_permutation t P *
    lazard_polynomial_permutation t q)); first by ring.
rewrite acted.
transitivity
  (Q * (lazard_polynomial_permutation t p * q)); first by ring.
rewrite cross.
transitivity
  (lazard_polynomial_permutation t q * (p * Q)); first by ring.
rewrite -Pq.
by ring.
Qed.

Lemma lazard_symmetrized_numerator_symmetric p q
    (q0 : q != 0)
    (cross : forall s : 'S_n,
      lazard_polynomial_permutation s p * q =
        p * lazard_polynomial_permutation s q) :
  lazard_symmetrized_numerator p q \is symmetric.
Proof.
apply/IM.full_symmetricP=> s.
exact: lazard_symmetrized_numerator_fixed q0 cross.
Qed.

(** The original and symmetrized numerator/denominator pairs represent the
    same fraction. *)
Lemma lazard_symmetrized_fractionE p q (q0 : q != 0) :
  p%:RF / q%:RF =
    (lazard_symmetrized_numerator p q)%:RF /
      (lazard_denominator_orbit_norm q)%:RF.
Proof.
have Q0 := lazard_denominator_orbit_norm_neq0 q0.
have qF0 : q%:RF != 0 by rewrite tofrac_eq0.
have QF0 : (lazard_denominator_orbit_norm q)%:RF != 0.
  by rewrite tofrac_eq0.
apply/eqP.
rewrite (eqr_div qF0 QF0) -!rmorphM tofrac_eq.
apply/eqP.
exact: esym (lazard_symmetrized_numerator_mul_denominator p q).
Qed.

(** Rational form of the fundamental theorem of symmetric functions.
    Both resulting numerator and nonzero denominator are explicit
    elementary-symmetric substitutions. *)
Theorem lazard_symmetric_fraction_elementary_coordinates p q :
  lazard_symmetric_fraction_pair p q ->
  exists u v : MP,
    IM.sym_eval v != 0 /\
    p%:RF / q%:RF = (IM.sym_eval u)%:RF / (IM.sym_eval v)%:RF.
Proof.
move=> invariant.
have [q0 cross] :=
  (proj1 (lazard_symmetric_fraction_pair_iff_cross p q)) invariant.
have Psym := lazard_symmetrized_numerator_symmetric q0 cross.
have Qsym := lazard_denominator_orbit_norm_symmetric q.
move/IM.sym_eval_imageP: Psym=> [u uP].
move/IM.sym_eval_imageP: Qsym=> [v vQ].
exists u, v; split.
- rewrite vQ.
  exact: lazard_denominator_orbit_norm_neq0 q0.
- rewrite uP vQ.
  exact: lazard_symmetrized_fractionE q0.
Qed.

(** The quotient-level fixedness predicate agrees with the pair-level
    predicate used by denominator symmetrization. *)
Lemma lazard_symmetric_fraction_pair_of_fixed p q
    (q0 : q != 0)
    (fixed : lazard_symmetric_fraction (p%:RF / q%:RF)) :
  lazard_symmetric_fraction_pair p q.
Proof.
split=> // s.
rewrite -lazard_fraction_permutation_div_tofrac //.
exact: fixed s.
Qed.

Lemma lazard_symmetric_fraction_fixed_of_pair p q :
  lazard_symmetric_fraction_pair p q ->
  lazard_symmetric_fraction (p%:RF / q%:RF).
Proof.
move=> [q0 invariant] s.
rewrite lazard_fraction_permutation_div_tofrac //.
exact: invariant s.
Qed.

(** Rational fundamental theorem of symmetric functions, now stated on the
    actual quotient fraction field: a rational function is fixed by every
    variable permutation iff it is a fraction in the elementary symmetric
    polynomials. *)
Theorem lazard_symmetric_fraction_fixed_iff_elementary x :
  lazard_symmetric_fraction x <->
  lazard_elementary_symmetric_fraction x.
Proof.
split.
- move=> fixed.
  have [p [q [q0 hx]]] := lazard_fraction_presentation x.
  rewrite hx in fixed *.
  have pair := lazard_symmetric_fraction_pair_of_fixed q0 fixed.
  have [u [v [v0 huv]]] :=
    lazard_symmetric_fraction_elementary_coordinates pair.
  exists u, v; split=> //.
  exact: huv.
- move=> [u [v [v0 ->]]] s.
  rewrite lazard_fraction_permutation_div_tofrac //.
  have hu : lazard_polynomial_permutation s (IM.sym_eval u) =
      IM.sym_eval u.
    move/IM.full_symmetricP: (IM.sym_eval_symmetric u)=> h.
    exact: h s.
  have hv : lazard_polynomial_permutation s (IM.sym_eval v) =
      IM.sym_eval v.
    move/IM.full_symmetricP: (IM.sym_eval_symmetric v)=> h.
    exact: h s.
  by rewrite hu hv.
Qed.

End SymmetricFractions.

End PolynomialFormulasLazardSymmetricRationalFunctions.
