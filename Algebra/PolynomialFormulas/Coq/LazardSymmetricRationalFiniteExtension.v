From HB Require Import structures.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantFiniteFree LazardInvariantSymmetricModule
  LazardInvariantArtinSuccessor LazardSymmetricRationalFunctions.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Finite-extension bridge for the symmetric rational-function field.

    Let [MP = K[X_1,...,X_n]], let [ESRF] be an abstract copy of
    [Frac(MP)], and embed [ESRF] in a second copy [RFE] of [Frac(MP)] by
    applying elementary-symmetric substitution to numerator and denominator.
    The reverse Artin basis of [MP] over [K[e_1,...,e_n]] localizes to a
    basis of [RFE] over [ESRF].

    This file deliberately separates that finite-extension theorem from the
    companion Galois wrapper.  No finiteness or Galois hypothesis is
    postulated: the fraction embedding is lifted through MathComp's quotient,
    and spanning and independence are obtained by denominator clearing from
    the already proved reverse-Artin decomposition.

    The final comment records the API-level construction used by the companion
    file to obtain a [splittingFieldType] and identify its full automorphism
    group with ['S_n]. *)
Module PolynomialFormulasLazardSymmetricRationalFiniteExtension.

Import GRing.Theory.
Import FracField.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module SM := PolynomialFormulasLazardInvariantSymmetricModule.
Module AS := PolynomialFormulasLazardInvariantArtinSuccessor.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module SRF := PolynomialFormulasLazardSymmetricRationalFunctions.

Section FiniteExtension.

Variables (K : fieldType) (n : nat).

Local Notation MP := {mpoly K[n]}.
Local Notation RawRF := {fraction MP}.

(** Distinct reducible wrappers are used so that the elementary-fraction
    field and the ambient rational-function field can carry different scalar
    structures without changing the underlying quotient representation. *)
Definition lazard_elementary_symmetric_rational_field : Type := RawRF.
Definition lazard_rational_function_extension : Type := RawRF.

Local Notation ESRF := lazard_elementary_symmetric_rational_field.
Local Notation RFE := lazard_rational_function_extension.

HB.instance Definition _ := GRing.Field.on ESRF.
HB.instance Definition _ := GRing.Field.on RFE.

Local Notation "p %:ESRF" := (@FracField.tofrac MP p)
  (at level 2, format "p %:ESRF").
Local Notation "p %:RFE" := (@FracField.tofrac MP p)
  (at level 2, format "p %:RFE").

(**************************************************************************)
(** * Extending elementary-symmetric substitution to fraction fields *)

Lemma lazard_sym_eval_eq0 p :
  (IM.sym_eval p == 0) = (p == 0).
Proof.
apply/idP/idP.
- move/eqP=> hp; apply/eqP.
  apply: IM.sym_eval_injective.
  by rewrite hp IM.sym_eval0.
- move/eqP=> ->; apply/eqP.
  exact: IM.sym_eval0.
Qed.

Lemma lazard_sym_eval_neq0 p :
  (IM.sym_eval p != 0) = (p != 0).
Proof. by rewrite lazard_sym_eval_eq0. Qed.

Lemma lazard_sym_evalN : {morph @IM.sym_eval K n : x / - x}.
Proof. exact: rmorphN. Qed.

Definition lazard_ratio_sym_eval (r : {ratio MP}) : {ratio MP} :=
  Ratio (IM.sym_eval \n_r) (IM.sym_eval \d_r).

Lemma lazard_ratio_sym_eval_num r :
  \n_(lazard_ratio_sym_eval r) = IM.sym_eval \n_r.
Proof.
rewrite /lazard_ratio_sym_eval numer_Ratio //.
by rewrite lazard_sym_eval_neq0 denom_ratioP.
Qed.

Lemma lazard_ratio_sym_eval_den r :
  \d_(lazard_ratio_sym_eval r) = IM.sym_eval \d_r.
Proof.
rewrite /lazard_ratio_sym_eval denom_Ratio //.
by rewrite lazard_sym_eval_neq0 denom_ratioP.
Qed.

Definition lazard_elementary_fraction_embedding_fun : ESRF -> RFE :=
  lift_op1 RFE lazard_ratio_sym_eval.

Lemma lazard_elementary_fraction_embedding_pi :
  {morph \pi : r / lazard_ratio_sym_eval r >->
    lazard_elementary_fraction_embedding_fun r}.
Proof.
move=> r; unlock lazard_elementary_fraction_embedding_fun.
apply/eqmodP=> /=.
rewrite equivfE !lazard_ratio_sym_eval_num !lazard_ratio_sym_eval_den.
rewrite -!IM.sym_evalM (inj_eq IM.sym_eval_injective).
by apply/eqP; exact: equivf_r r.
Qed.

Canonical lazard_elementary_fraction_embedding_pi_morph :=
  PiMorph1 lazard_elementary_fraction_embedding_pi.

Lemma lazard_elementary_fraction_embedding_fun_tofrac p :
  lazard_elementary_fraction_embedding_fun p%:ESRF =
    (IM.sym_eval p)%:RFE.
Proof.
unlock FracField.tofrac.
rewrite piE /lazard_ratio_sym_eval
  !numer_Ratio ?oner_neq0 // !denom_Ratio ?oner_neq0 //.
by rewrite IM.sym_eval1.
Qed.

Lemma lazard_ratio_sym_eval_add r u :
  lazard_ratio_sym_eval (addf r u) =
    addf (lazard_ratio_sym_eval r) (lazard_ratio_sym_eval u).
Proof.
apply: val_inj; congr (_, _).
- rewrite lazard_ratio_sym_eval_num /addf numer_Ratio
      ?mulf_neq0 ?denom_ratioP //.
  rewrite numer_Ratio
      ?mulf_neq0 ?lazard_sym_eval_neq0 ?denom_ratioP //.
  rewrite !lazard_ratio_sym_eval_num !lazard_ratio_sym_eval_den.
  by rewrite IM.sym_evalD !IM.sym_evalM.
- rewrite lazard_ratio_sym_eval_den /addf denom_Ratio
      ?mulf_neq0 ?denom_ratioP //.
  rewrite denom_Ratio
      ?mulf_neq0 ?lazard_sym_eval_neq0 ?denom_ratioP //.
  rewrite !lazard_ratio_sym_eval_den.
  exact: IM.sym_evalM.
Qed.

Lemma lazard_ratio_sym_eval_opp r :
  lazard_ratio_sym_eval (oppf r) = oppf (lazard_ratio_sym_eval r).
Proof.
apply: val_inj; congr (_, _).
- rewrite lazard_ratio_sym_eval_num /oppf numer_Ratio ?denom_ratioP //.
  rewrite numer_Ratio ?lazard_sym_eval_neq0 ?denom_ratioP //.
  rewrite lazard_ratio_sym_eval_num.
  exact: lazard_sym_evalN.
- rewrite lazard_ratio_sym_eval_den /oppf denom_Ratio ?denom_ratioP //.
  rewrite denom_Ratio ?lazard_sym_eval_neq0 ?denom_ratioP //.
  exact: lazard_ratio_sym_eval_den.
Qed.

Lemma lazard_ratio_sym_eval_mul r u :
  lazard_ratio_sym_eval (mulf r u) =
    mulf (lazard_ratio_sym_eval r) (lazard_ratio_sym_eval u).
Proof.
apply: val_inj; congr (_, _).
- rewrite lazard_ratio_sym_eval_num /mulf numer_Ratio
      ?mulf_neq0 ?denom_ratioP //.
  rewrite numer_Ratio
      ?mulf_neq0 ?lazard_sym_eval_neq0 ?denom_ratioP //.
  rewrite !lazard_ratio_sym_eval_num.
  exact: IM.sym_evalM.
- rewrite lazard_ratio_sym_eval_den /mulf denom_Ratio
      ?mulf_neq0 ?denom_ratioP //.
  rewrite denom_Ratio
      ?mulf_neq0 ?lazard_sym_eval_neq0 ?denom_ratioP //.
  rewrite !lazard_ratio_sym_eval_den.
  exact: IM.sym_evalM.
Qed.

Lemma lazard_elementary_fraction_embedding_funD :
  {morph lazard_elementary_fraction_embedding_fun : x y / x + y}.
Proof.
move=> x y; elim/quotW: x=> r; elim/quotW: y=> u.
by rewrite !piE lazard_ratio_sym_eval_add.
Qed.

Lemma lazard_elementary_fraction_embedding_funN :
  {morph lazard_elementary_fraction_embedding_fun : x / - x}.
Proof.
move=> x; elim/quotW: x=> r.
by rewrite !piE lazard_ratio_sym_eval_opp.
Qed.

Lemma lazard_elementary_fraction_embedding_funB :
  {morph lazard_elementary_fraction_embedding_fun : x y / x - y}.
Proof.
move=> x y.
by rewrite !subr_eq_addr lazard_elementary_fraction_embedding_funD
  lazard_elementary_fraction_embedding_funN.
Qed.

Lemma lazard_elementary_fraction_embedding_fun_mul :
  {morph lazard_elementary_fraction_embedding_fun : x y / x * y}.
Proof.
move=> x y; elim/quotW: x=> r; elim/quotW: y=> u.
by rewrite !piE lazard_ratio_sym_eval_mul.
Qed.

Lemma lazard_elementary_fraction_embedding_fun1 :
  lazard_elementary_fraction_embedding_fun 1 = 1.
Proof.
change lazard_elementary_fraction_embedding_fun (1%:ESRF) = 1%:RFE.
by rewrite lazard_elementary_fraction_embedding_fun_tofrac IM.sym_eval1.
Qed.

Fact lazard_elementary_fraction_embedding_is_zmod_morphism :
  zmod_morphism lazard_elementary_fraction_embedding_fun.
Proof. exact: lazard_elementary_fraction_embedding_funB. Qed.

Fact lazard_elementary_fraction_embedding_is_monoid_morphism :
  monoid_morphism lazard_elementary_fraction_embedding_fun.
Proof.
split.
- exact: lazard_elementary_fraction_embedding_fun1.
- exact: lazard_elementary_fraction_embedding_fun_mul.
Qed.

Definition lazard_elementary_fraction_embedding : {rmorphism ESRF -> RFE} :=
  HB.pack lazard_elementary_fraction_embedding_fun
    (GRing.isZmodMorphism.Build _ _ lazard_elementary_fraction_embedding_fun
      lazard_elementary_fraction_embedding_is_zmod_morphism)
    (GRing.isMonoidMorphism.Build _ _ lazard_elementary_fraction_embedding_fun
      lazard_elementary_fraction_embedding_is_monoid_morphism).

Lemma lazard_elementary_fraction_embeddingE x :
  lazard_elementary_fraction_embedding x =
    lazard_elementary_fraction_embedding_fun x.
Proof. by []. Qed.

Lemma lazard_elementary_fraction_embedding_tofrac p :
  lazard_elementary_fraction_embedding p%:ESRF =
    (IM.sym_eval p)%:RFE.
Proof. exact: lazard_elementary_fraction_embedding_fun_tofrac. Qed.

Lemma lazard_elementary_fraction_embedding_div_tofrac p q
    (q0 : q != 0) :
  lazard_elementary_fraction_embedding (p%:ESRF / q%:ESRF) =
    (IM.sym_eval p)%:RFE / (IM.sym_eval q)%:RFE.
Proof.
have qFunit : q%:ESRF \in GRing.unit.
  by rewrite unitfE tofrac_eq0.
rewrite (rmorph_div qFunit).
by rewrite !lazard_elementary_fraction_embedding_tofrac.
Qed.

Lemma lazard_elementary_fraction_embedding_injective :
  injective lazard_elementary_fraction_embedding.
Proof. exact: fmorph_inj. Qed.

(**************************************************************************)
(** * Image and fixed-field characterization *)

Lemma lazard_elementary_fraction_embedding_image x :
  (exists a : ESRF, lazard_elementary_fraction_embedding a = x) <->
  SRF.lazard_elementary_symmetric_fraction K n x.
Proof.
split.
- move=> [a <-].
  have [p [q [q0 ha]]] := SRF.lazard_fraction_presentation K n a.
  exists p, q; split.
  * by rewrite lazard_sym_eval_neq0.
  * rewrite ha lazard_elementary_fraction_embedding_div_tofrac //.
- move=> [p [q [q0 ->]]].
  have qsource0 : q != 0 by rewrite -lazard_sym_eval_neq0.
  exists (p%:ESRF / q%:ESRF).
  by rewrite lazard_elementary_fraction_embedding_div_tofrac.
Qed.

Theorem lazard_full_symmetric_fixed_field_image x :
  SRF.lazard_symmetric_fraction K n x <->
  exists a : ESRF, lazard_elementary_fraction_embedding a = x.
Proof.
rewrite SRF.lazard_symmetric_fraction_fixed_iff_elementary.
exact: iff_sym (lazard_elementary_fraction_embedding_image x).
Qed.

(**************************************************************************)
(** * The induced algebra structure *)

Definition lazard_elementary_fraction_scale (a : ESRF) (x : RFE) : RFE :=
  lazard_elementary_fraction_embedding a * x.

Local Infix "*E:" := lazard_elementary_fraction_scale (at level 40).

Fact lazard_elementary_fraction_scaleA a b x :
  a *E: (b *E: x) = (a * b) *E: x.
Proof.
by rewrite /lazard_elementary_fraction_scale rmorphM mulrA.
Qed.

Fact lazard_elementary_fraction_scale1 x : 1 *E: x = x.
Proof. by rewrite /lazard_elementary_fraction_scale rmorph1 mul1r. Qed.

Fact lazard_elementary_fraction_scaleDr a x y :
  a *E: (x + y) = a *E: x + a *E: y.
Proof. exact: mulrDr. Qed.

Fact lazard_elementary_fraction_scaleDl x a b :
  (a + b) *E: x = a *E: x + b *E: x.
Proof.
by rewrite /lazard_elementary_fraction_scale rmorphD mulrDl.
Qed.

HB.instance Definition _ := GRing.Zmodule_isLmodule.Build ESRF RFE
  lazard_elementary_fraction_scaleA lazard_elementary_fraction_scale1
  lazard_elementary_fraction_scaleDr lazard_elementary_fraction_scaleDl.

Lemma lazard_elementary_fraction_scaleE a x :
  a *: x = lazard_elementary_fraction_embedding a * x :> RFE.
Proof. by []. Qed.

Fact lazard_elementary_fraction_scaleAl a x y :
  a *E: (x * y) = (a *E: x) * y.
Proof. exact: mulrA. Qed.

HB.instance Definition _ := GRing.Lmodule_isLalgebra.Build ESRF RFE
  lazard_elementary_fraction_scaleAl.

Fact lazard_elementary_fraction_scaleAr a x y :
  a *E: (x * y) = x * (a *E: y).
Proof. exact: mulrCA. Qed.

HB.instance Definition _ := GRing.Lalgebra_isAlgebra.Build ESRF RFE
  lazard_elementary_fraction_scaleAr.

(**************************************************************************)
(** * Uniform fraction presentations and common denominators *)

Definition lazard_fraction_pair_ok (x : RawRF) (pq : MP * MP) : bool :=
  (pq.2 != 0) && (x == pq.1%:RFE / pq.2%:RFE).

Lemma lazard_fraction_pair_exists x :
  exists pq : MP * MP, lazard_fraction_pair_ok x pq.
Proof.
have [p [q [q0 hx]]] := SRF.lazard_fraction_presentation K n x.
exists (p, q).
by apply/andP; split=> //; apply/eqP.
Qed.

Definition lazard_chosen_fraction_pair (x : RawRF) : MP * MP :=
  sval (sigW (lazard_fraction_pair_exists x)).

Lemma lazard_chosen_fraction_pairP x :
  lazard_fraction_pair_ok x (lazard_chosen_fraction_pair x).
Proof.
exact: (proj2_sig (sigW (lazard_fraction_pair_exists x))).
Qed.

Definition lazard_chosen_fraction_numerator (x : RawRF) : MP :=
  (lazard_chosen_fraction_pair x).1.

Definition lazard_chosen_fraction_denominator (x : RawRF) : MP :=
  (lazard_chosen_fraction_pair x).2.

Lemma lazard_chosen_fraction_denominator_neq0 x :
  lazard_chosen_fraction_denominator x != 0.
Proof.
move/andP: (lazard_chosen_fraction_pairP x)=> [hx _].
exact: hx.
Qed.

Lemma lazard_chosen_fractionE x :
  x = (lazard_chosen_fraction_numerator x)%:RFE /
      (lazard_chosen_fraction_denominator x)%:RFE.
Proof.
move/andP: (lazard_chosen_fraction_pairP x)=> [_ /eqP hx].
exact: hx.
Qed.

(** Every finite family of fractions admits one polynomial denominator.
    This is the only choice used in the independence proof; it is MathComp's
    ordinary constructive choice on the decidable quotient equality. *)
Lemma lazard_common_fraction_denominator
    (I : finType) (c : I -> ESRF) :
  exists (u : I -> MP) (v : MP),
    v != 0 /\
    forall i, c i = (u i)%:ESRF / v%:ESRF.
Proof.
pose p i := lazard_chosen_fraction_numerator (c i).
pose q i := lazard_chosen_fraction_denominator (c i).
pose v := \prod_i q i.
pose u i := p i * \prod_(j | j != i) q j.
have q0 i : q i != 0.
  exact: lazard_chosen_fraction_denominator_neq0 (c i).
have v0 : v != 0.
  rewrite /v.
  by apply/prodf_neq0=> i _; exact: q0 i.
exists u, v; split=> // i.
rewrite (lazard_chosen_fractionE (c i)).
have qiF0 : (q i)%:ESRF != 0 by rewrite tofrac_eq0 q0.
have vF0 : v%:ESRF != 0 by rewrite tofrac_eq0 v0.
apply/eqP.
rewrite (eqr_div qiF0 vF0) -!rmorphM tofrac_eq.
apply/eqP.
rewrite /u /v (bigD1 i) //=.
by ring.
Qed.

(**************************************************************************)
(** * Localization of the reverse Artin basis *)

Local Notation ArtinD :=
  (AS.lazard_reverse_artin_finite_free_decomposition K n).
Local Notation ArtinI := (FF.ffd_index ArtinD).

Definition lazard_fraction_artin_basis (i : ArtinI) : RFE :=
  (FF.ffd_basis ArtinD i : MP)%:RFE.

Lemma lazard_fraction_artin_basis_card : #|ArtinI| = n`!.
Proof. exact: AS.lazard_reverse_artin_index_card. Qed.

(** Polynomial reconstruction written without the symmetric-module wrapper.
    This is exactly [ffd_reconstruct], with its scalar action unfolded. *)
Lemma lazard_reverse_artin_polynomial_reconstruct (p : MP) :
  p = \sum_i
    IM.sym_eval
      (FF.ffd_coeff ArtinD
        (p : SM.symmetric_polynomial_module K n) i) *
    (FF.ffd_basis ArtinD i : MP).
Proof.
rewrite {1}(FF.ffd_reconstruct ArtinD
  (p : SM.symmetric_polynomial_module K n)).
apply: eq_bigr=> i _.
exact: SM.symmetric_scalarE.
Qed.

Definition lazard_fraction_numerator (x : RFE) : MP :=
  lazard_chosen_fraction_numerator x.

Definition lazard_fraction_denominator (x : RFE) : MP :=
  lazard_chosen_fraction_denominator x.

Lemma lazard_fraction_denominator_neq0 x :
  lazard_fraction_denominator x != 0.
Proof. exact: lazard_chosen_fraction_denominator_neq0 x. Qed.

Lemma lazard_fraction_presentationE x :
  x = (lazard_fraction_numerator x)%:RFE /
      (lazard_fraction_denominator x)%:RFE.
Proof. exact: lazard_chosen_fractionE x. Qed.

Definition lazard_fraction_symmetric_denominator (x : RFE) : MP :=
  SRF.lazard_denominator_orbit_norm (lazard_fraction_denominator x).

Definition lazard_fraction_symmetric_denominator_coordinate
    (x : RFE) : MP :=
  sval (IM.symmetric_coordinates
    (SRF.lazard_denominator_orbit_norm_symmetric
      (lazard_fraction_denominator x))).

Lemma lazard_fraction_symmetric_denominator_coordinateE x :
  IM.sym_eval (lazard_fraction_symmetric_denominator_coordinate x) =
    lazard_fraction_symmetric_denominator x.
Proof.
rewrite /lazard_fraction_symmetric_denominator_coordinate
  /lazard_fraction_symmetric_denominator.
case: (IM.symmetric_coordinates
  (SRF.lazard_denominator_orbit_norm_symmetric
    (lazard_fraction_denominator x)))=> v [hv _] /=.
exact: hv.
Qed.

Lemma lazard_fraction_symmetric_denominator_coordinate_neq0 x :
  lazard_fraction_symmetric_denominator_coordinate x != 0.
Proof.
rewrite -lazard_sym_eval_neq0
  lazard_fraction_symmetric_denominator_coordinateE.
exact: SRF.lazard_denominator_orbit_norm_neq0
  (lazard_fraction_denominator_neq0 x).
Qed.

Definition lazard_fraction_symmetric_numerator (x : RFE) : MP :=
  SRF.lazard_symmetrized_numerator
    (lazard_fraction_numerator x) (lazard_fraction_denominator x).

Definition lazard_localized_artin_coefficient
    (x : RFE) (i : ArtinI) : ESRF :=
  let a := FF.ffd_coeff ArtinD
    (lazard_fraction_symmetric_numerator x :
      SM.symmetric_polynomial_module K n) i in
  a%:ESRF / (lazard_fraction_symmetric_denominator_coordinate x)%:ESRF.

Lemma lazard_localized_artin_coefficient_embeddingE x i :
  lazard_elementary_fraction_embedding
      (lazard_localized_artin_coefficient x i) =
    (IM.sym_eval (FF.ffd_coeff ArtinD
      (lazard_fraction_symmetric_numerator x :
        SM.symmetric_polynomial_module K n) i))%:RFE /
    (lazard_fraction_symmetric_denominator x)%:RFE.
Proof.
rewrite /lazard_localized_artin_coefficient
  lazard_elementary_fraction_embedding_div_tofrac
    ?lazard_fraction_symmetric_denominator_coordinate_neq0 //.
by rewrite lazard_fraction_symmetric_denominator_coordinateE.
Qed.

Theorem lazard_localized_artin_reconstruct x :
  x = \sum_i
    (lazard_localized_artin_coefficient x i) *:
      lazard_fraction_artin_basis i.
Proof.
rewrite lazard_fraction_presentationE.
rewrite SRF.lazard_symmetrized_fractionE
  ?lazard_fraction_denominator_neq0 //.
set P := lazard_fraction_symmetric_numerator x.
set Q := lazard_fraction_symmetric_denominator x.
have Q0 : Q != 0.
  exact: SRF.lazard_denominator_orbit_norm_neq0
    (lazard_fraction_denominator_neq0 x).
have QF0 : Q%:RFE != 0 by rewrite tofrac_eq0 Q0.
have hP := lazard_reverse_artin_polynomial_reconstruct P.
have hPF := congr1 (@FracField.tofrac MP) hP.
rewrite rmorph_sum in hPF.
under [RHS] eq_bigr in hPF => i _ do rewrite rmorphM.
apply: (mulfI QF0).
rewrite (mulrC Q%:RFE (P%:RFE / Q%:RFE)) divfK //.
rewrite mulr_sumr.
under [RHS] eq_bigr => i _ do
  rewrite lazard_elementary_fraction_scaleE
    lazard_localized_artin_coefficient_embeddingE
    /lazard_fraction_artin_basis
    mulrA (mulrC Q%:RFE (_ / Q%:RFE)) divfK //.
exact: hPF.
Qed.

(** Denominator clearing reduces every ESRF-linear relation among the
    localized Artin monomials to an MP-linear relation among the polynomial
    Artin monomials.  Thus localization preserves independence. *)
Theorem lazard_localized_artin_independent (c : ArtinI -> ESRF) :
  (\sum_i (c i) *: lazard_fraction_artin_basis i = 0) ->
  forall i, c i = 0.
Proof.
move=> hc.
have [u [v [v0 huv]]] := lazard_common_fraction_denominator c.
have sv0 : IM.sym_eval v != 0 by rewrite lazard_sym_eval_neq0.
have svF0 : (IM.sym_eval v)%:RFE != 0 by rewrite tofrac_eq0 sv0.
have hc' := hc.
under [LHS] eq_bigr in hc' => i _ do
  rewrite lazard_elementary_fraction_scaleE (huv i)
    lazard_elementary_fraction_embedding_div_tofrac //.
have hcleared := congr1 (fun z : RFE => (IM.sym_eval v)%:RFE * z) hc'.
rewrite mulr0 mulr_sumr in hcleared.
under [LHS] eq_bigr in hcleared => i _ do
  rewrite mulrA (mulrC (IM.sym_eval v)%:RFE
    ((IM.sym_eval (u i))%:RFE / (IM.sym_eval v)%:RFE))
    divfK //.
have hpoly :
    \sum_i IM.sym_eval (u i) * (FF.ffd_basis ArtinD i : MP) = 0.
  apply/eqP.
  rewrite -tofrac_eq0.
  apply/eqP.
  rewrite rmorph_sum.
  under [LHS] eq_bigr => i _ do rewrite rmorphM.
  exact: hcleared.
have hmodule :
    \sum_i (u i) *: FF.ffd_basis ArtinD i = 0.
  change
    (\sum_i IM.sym_eval (u i) * (FF.ffd_basis ArtinD i : MP) = 0).
  exact: hpoly.
have hu0 := FF.ffd_basis_independent ArtinD hmodule.
move=> i.
rewrite (huv i) (hu0 i) rmorph0 zero_div.
Qed.

Lemma lazard_localized_artin_unique x (c : ArtinI -> ESRF) :
  x = \sum_i (c i) *: lazard_fraction_artin_basis i ->
  forall i, c i = lazard_localized_artin_coefficient x i.
Proof.
move=> hx i.
apply/eqP; rewrite -subr_eq0; apply/eqP.
apply: (lazard_localized_artin_independent
  (c := fun j => c j - lazard_localized_artin_coefficient x j)).
under [LHS] eq_bigr => j _ do
  rewrite subr_eq_addr scalerDl scaleNr.
rewrite big_split sumrN -hx -lazard_localized_artin_reconstruct subrr.
Qed.

(** An actual finite-free decomposition over the abstract elementary
    fraction field.  Its fields are all proved above; in particular, no
    coordinate functional is supplied as an axiom. *)
Definition lazard_localized_artin_finite_free_decomposition :
    FF.finite_free_decomposition ESRF RFE :=
  {| FF.ffd_index := ArtinI;
     FF.ffd_basis := lazard_fraction_artin_basis;
     FF.ffd_coeff := lazard_localized_artin_coefficient;
     FF.ffd_reconstruct := lazard_localized_artin_reconstruct;
     FF.ffd_unique := lazard_localized_artin_unique |}.

Local Notation LocalizedD :=
  lazard_localized_artin_finite_free_decomposition.

(**************************************************************************)
(** * A MathComp finite-dimensional vector and field extension *)

Definition lazard_artin_fraction_to_row (x : RFE) :
    'rV[ESRF]_(#|ArtinI|) :=
  \row_j FF.ffd_coeff LocalizedD x (enum_val j).

Definition lazard_artin_row_to_fraction
    (r : 'rV[ESRF]_(#|ArtinI|)) : RFE :=
  \sum_i r 0 (enum_rank i) *: FF.ffd_basis LocalizedD i.

Lemma lazard_artin_fraction_to_row_is_linear :
  linear lazard_artin_fraction_to_row.
Proof.
move=> a x y; apply/rowP=> j.
by rewrite !mxE FF.ffd_coeffD FF.ffd_coeffZ.
Qed.

Lemma lazard_artin_fraction_to_rowK :
  cancel lazard_artin_fraction_to_row lazard_artin_row_to_fraction.
Proof.
move=> x.
rewrite /lazard_artin_row_to_fraction /lazard_artin_fraction_to_row.
under [LHS] eq_bigr => i _ do rewrite mxE enum_rankK.
exact/esym: FF.ffd_reconstruct.
Qed.

Lemma lazard_artin_row_to_fractionK :
  cancel lazard_artin_row_to_fraction lazard_artin_fraction_to_row.
Proof.
move=> r; apply/rowP=> j.
rewrite /lazard_artin_fraction_to_row /lazard_artin_row_to_fraction
  !mxE FF.ffd_coeff_sum.
under [LHS] eq_bigr => i _ do
  rewrite FF.ffd_coeffZ FF.ffd_coeff_basis.
rewrite (bigD1 (enum_val j)) //= eqxx mulr1 enum_valK.
rewrite big1 ?addr0 // => i hij.
by rewrite eq_sym (negbTE hij) mulr0.
Qed.

Lemma lazard_rational_function_extension_vector_axiom :
  Vector.axiom #|ArtinI| RFE.
Proof.
exists lazard_artin_fraction_to_row.
- exact: lazard_artin_fraction_to_row_is_linear.
- exists lazard_artin_row_to_fraction.
  * exact: lazard_artin_fraction_to_rowK.
  * exact: lazard_artin_row_to_fractionK.
Qed.

HB.instance Definition _ := Lmodule_hasFinDim.Build ESRF RFE
  lazard_rational_function_extension_vector_axiom.

(** The requested finite extension.  Its inherited algebra map is the
    quotient-lifted elementary-symmetric fraction embedding above. *)
Definition lazard_symmetric_rational_field_extension : fieldExtType ESRF :=
  RFE.

Lemma lazard_symmetric_rational_in_algE a :
  in_alg RFE a = lazard_elementary_fraction_embedding a.
Proof.
by rewrite in_algE lazard_elementary_fraction_scaleE mulr1.
Qed.

Lemma lazard_symmetric_rational_base_fieldP x :
  reflect
    (exists a : ESRF, lazard_elementary_fraction_embedding a = x)
    (x \in (1%VS : {vspace RFE})).
Proof.
apply: (iffP vlineP).
- move=> [a ->]; exists a.
  by rewrite lazard_elementary_fraction_scaleE mulr1.
- move=> [a <-]; apply/vlineP; exists a.
  by rewrite lazard_elementary_fraction_scaleE mulr1.
Qed.

Lemma lazard_full_symmetric_fixed_fieldP x :
  reflect (SRF.lazard_symmetric_fraction K n x)
    (x \in (1%VS : {vspace RFE})).
Proof.
apply: (iffP lazard_symmetric_rational_base_fieldP).
- move=> hx.
  exact: (proj2 (lazard_full_symmetric_fixed_field_image x) hx).
- move/(proj1 (lazard_full_symmetric_fixed_field_image x))=> hx.
  exact/lazard_symmetric_rational_base_fieldP: hx.
Qed.

Lemma lazard_symmetric_rational_field_extension_degree :
  \dim {:RFE} = n`!.
Proof.
rewrite dimvf.
exact: lazard_fraction_artin_basis_card.
Qed.

(**************************************************************************)
(** * Permutations as base-linear algebra endomorphisms *)

(** Distinct indeterminates remain distinct before localization.  Keeping
    this lemma at arbitrary arity (including the vacuous zero-variable case)
    lets faithfulness below be proved without importing the successor-only
    version used elsewhere in the Lazard development. *)
Lemma lazard_mpoly_variable_injective :
  injective (fun i : 'I_n => ('X_i : MP)).
Proof.
move=> i j hij.
have hs := congr1 (fun p : MP => msupp p) hij.
rewrite !msuppX in hs.
have hu : U_(i)%MM = U_(j)%MM.
  move: (congr1 (head U_(i)%MM) hs).
  by [].
have hub : U_(i)%MM == U_(j)%MM.
  by apply/eqP.
move: hub.
by rewrite eq_mnm1 => /eqP.
Qed.

(** The inverse here is not cosmetic: [msym] is right-oriented, whereas
    [IM.mpoly_left_action] was deliberately defined as a left action. *)
Lemma lazard_mpoly_left_actionX (s : 'S_n) (i : 'I_n) :
  IM.mpoly_left_action s ('X_i : MP) = ('X_(s^-1 i) : MP).
Proof.
rewrite /IM.mpoly_left_action msymX invgK.
congr 'X_[_].
apply/mnmP=> j.
rewrite !mnmE !mnm1E.
apply/eqP/eqP=> h.
- by rewrite h permK.
- by rewrite -h permKV.
Qed.

Lemma lazard_fraction_permutation_embedding_fixed
    (s : 'S_n) (a : ESRF) :
  SRF.lazard_fraction_permutation K n s
      (lazard_elementary_fraction_embedding a) =
    lazard_elementary_fraction_embedding a.
Proof.
apply: (proj2 (lazard_full_symmetric_fixed_field_image
  (lazard_elementary_fraction_embedding a))).
by exists a.
Qed.

Definition lazard_fraction_permutation_extension
    (s : 'S_n) (x : RFE) : RFE :=
  SRF.lazard_fraction_permutation K n s x.

Lemma lazard_fraction_permutation_extension_scalable s :
  scalable (lazard_fraction_permutation_extension s).
Proof.
move=> a x.
rewrite /lazard_fraction_permutation_extension
  !lazard_elementary_fraction_scaleE rmorphM
  lazard_fraction_permutation_embedding_fixed.
Qed.

Definition lazard_fraction_permutation_lrmorphism
    (s : 'S_n) : {lrmorphism RFE -> RFE} :=
  HB.pack
    (GRing.RMorphism.sort (SRF.lazard_fraction_permutation K n s))
    (GRing.isScalable.Build ESRF RFE RFE _
      (SRF.lazard_fraction_permutation K n s)
      (lazard_fraction_permutation_extension_scalable s)).

Definition lazard_fraction_permutation_AEnd
    (s : 'S_n) : 'AEnd(RFE) :=
  linfun_ahom (lazard_fraction_permutation_lrmorphism s).

Lemma lazard_fraction_permutation_AEndE s x :
  lazard_fraction_permutation_AEnd s x =
    SRF.lazard_fraction_permutation K n s x.
Proof. by rewrite /lazard_fraction_permutation_AEnd lfunE. Qed.

Lemma lazard_fraction_permutation_AEnd_action1 x :
  lazard_fraction_permutation_AEnd (1 : 'S_n) x = x.
Proof.
rewrite lazard_fraction_permutation_AEndE.
exact: SRF.lazard_fraction_permutation1.
Qed.

Lemma lazard_fraction_permutation_AEnd_actionM s t x :
  lazard_fraction_permutation_AEnd (s * t) x =
    lazard_fraction_permutation_AEnd s
      (lazard_fraction_permutation_AEnd t x).
Proof.
rewrite !lazard_fraction_permutation_AEndE.
exact: SRF.lazard_fraction_permutationM.
Qed.

(** Faithfulness is already available at the [fieldExtType] stage.  If two
    endomorphisms agree, evaluate them on each embedded variable, use
    injectivity of the polynomial-to-fraction map, and recover the inverse
    permutations from their values on indices. *)
Lemma lazard_fraction_permutation_AEnd_injective :
  injective lazard_fraction_permutation_AEnd.
Proof.
move=> s t hst.
have inverse_value_eq (j : 'I_n) : s^-1 j = t^-1 j.
  have hX := congr1
    (fun f : 'AEnd(RFE) => f (('X_j : MP)%:RFE)) hst.
  rewrite !lazard_fraction_permutation_AEndE
    !SRF.lazard_fraction_permutation_tofrac
    /SRF.lazard_polynomial_permutation
    !lazard_mpoly_left_actionX in hX.
  apply: lazard_mpoly_variable_injective.
  apply/eqP.
  rewrite -tofrac_eq.
  exact/eqP: hX.
apply/permP=> i.
apply: (perm_inj s^-1).
by rewrite permK inverse_value_eq permK.
Qed.

(** The Galois packaging performed in
    [LazardSymmetricRationalGalois] is intentionally not hidden behind a
    premise.  Its construction proceeds as follows:

    1. form, for every localized Artin basis element [b_i], the orbit
       polynomial [prod_s ('X - (s b_i)%:P)]; its coefficients are fixed by
       every permutation, hence [lazard_full_symmetric_fixed_field_image]
       supplies their unique ESRF preimages;
    2. take the product of those orbit polynomials.  It splits in [RFE], and
       its root list contains every [b_i] via [s = 1], so the basis spanning
       theorem proves [splittingFieldFor 1 p {:RFE}];
    3. install [FieldExt_isSplittingField.Build].  The faithful image has
       order [n!] and the proved extension degree is [n!].  Then
       [dim_fixedField], [gal_fixedField], and [fixedField_galois] identify
       the full Galois group with that image.

    This file supplies all finite-extension and faithfulness input to that
    companion construction; the companion contains the concrete MathComp
    [polyOver], splitting-field, fixed-field, and [gal_of] wrappers. *)

End FiniteExtension.

End PolynomialFormulasLazardSymmetricRationalFiniteExtension.
