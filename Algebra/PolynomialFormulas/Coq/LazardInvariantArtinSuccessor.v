From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantFiniteFree LazardInvariantMultinomials
  LazardInvariantMpolyUnivariate LazardInvariantVietaReduction
  LazardInvariantSymmetricModule LazardInvariantSymmetricSuccessor.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The finite-free induction hidden behind the usual statement of the
    Artin basis theorem.

    At the successor step, [muni] writes an [(n+1)]-variable polynomial as a
    polynomial in its last variable.  The preceding finite-free
    decomposition is applied coefficientwise.  Each old basis component has
    symmetric coefficients, so [LazardInvariantSymmetricSuccessor] reduces
    it uniquely to powers [1,X,...,X^n] over the next symmetric ring.  This
    constructs both the new coordinates and their uniqueness; neither is an
    input to this file.

    Iterating the construction gives the reverse-staircase Artin monomials.
    Reversing variables would give the convention used by
    [IM.artin_index], but Lazard's theorem only needs the resulting finite
    homogeneous basis and its degree bound. *)
Module PolynomialFormulasLazardInvariantArtinSuccessor.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope mpoly_scope.

Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module MU := PolynomialFormulasLazardInvariantMpolyUnivariate.
Module VR := PolynomialFormulasLazardInvariantVietaReduction.
Module SM := PolynomialFormulasLazardInvariantSymmetricModule.
Module SS := PolynomialFormulasLazardInvariantSymmetricSuccessor.

Section OneStep.

Variables (F : fieldType) (n : nat).
Local Notation m := n.+1.
Local Notation Old := {mpoly F[n]}.
Local Notation Next := {mpoly F[m]}.
Local Notation OldModule :=
  (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
    F n).
Local Notation NextModule :=
  (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
    F m).
Local Notation lastX := ('X_(ord_max) : Next).

Variable D : @FF.finite_free_decomposition Old OldModule.

Definition lazard_successor_index : finType :=
  (FF.ffd_index D * 'I_m)%type.

Lemma lazard_successor_index_card :
  #|lazard_successor_index| = #|FF.ffd_index D| * m.
Proof.
by rewrite /lazard_successor_index card_prod card_ord.
Qed.

Definition lazard_old_coordinate_polynomial
    (p : NextModule) (a : FF.ffd_index D) : {poly Old} :=
  \poly_(j < size (@muni n F p))
    (@IM.sym_eval F n (FF.ffd_coeff D ((@muni n F p)`_j) a)).

Lemma lazard_old_coordinate_polynomial_symmetric p a i :
  (lazard_old_coordinate_polynomial p a)`_i \is symmetric.
Proof.
rewrite /lazard_old_coordinate_polynomial coef_poly.
case: ifP => _.
- exact: IM.sym_eval_symmetric.
- exact: rpred0.
Qed.

(** Coefficientwise application of the preceding decomposition, regrouped
    as one univariate polynomial for each old basis vector. *)
Lemma lazard_old_coordinate_polynomials_reconstruct p :
  @muni n F p =
    \sum_a lazard_old_coordinate_polynomial p a *
      (FF.ffd_basis D a)%:P.
Proof.
apply/polyP=> j.
rewrite [RHS]coef_sum.
case: (ltnP j (size (@muni n F p))) => hj.
- under [RHS] eq_bigr => a _ do
    rewrite coefMC /lazard_old_coordinate_polynomial coef_poly hj.
  move: (FF.ffd_reconstruct D ((@muni n F p)`_j)).
  under [X in _ = X] eq_bigr => a _ do
    rewrite SM.symmetric_scalarE.
  exact.
- rewrite nth_default //.
  apply/esym/big1=> a _.
  rewrite coefMC /lazard_old_coordinate_polynomial coef_poly.
  have hj' : ~~ ((j < size (@muni n F p))%N) by rewrite -leqNgt.
  by rewrite (negbTE hj') mul0r.
Qed.

Definition lazard_successor_coordinate
    (p : NextModule) (ak : lazard_successor_index) : Next :=
  @SS.lazard_symmetric_successor_coordinate F n
    (lazard_old_coordinate_polynomial p ak.1)
    (lazard_old_coordinate_polynomial_symmetric p ak.1) ak.2.

Definition lazard_successor_basis
    (ak : lazard_successor_index) : NextModule :=
  mwiden (FF.ffd_basis D ak.1) * lastX ^+ (ak.2 : nat).

(** The bounded polynomial associated with an arbitrary proposed coordinate
    family.  [inord] is harmless because the bounded polynomial consults the
    function only below [m = n+1]. *)
Definition lazard_successor_coordinate_block
    (c : lazard_successor_index -> Next) (a : FF.ffd_index D) :
    {poly Next} :=
  @VR.lazard_last_vieta_bounded_polynomial F n
    (fun k => c (a, inord k)).

Lemma lazard_successor_canonical_blockE p a :
  lazard_successor_coordinate_block
      (lazard_successor_coordinate p) a =
    @VR.lazard_last_vieta_bounded_polynomial F n
      (@SS.lazard_symmetric_successor_coordinate F n
        (lazard_old_coordinate_polynomial p a)
        (lazard_old_coordinate_polynomial_symmetric p a)).
Proof.
rewrite /lazard_successor_coordinate_block
  /lazard_successor_coordinate.
apply/polyP=> k.
rewrite !coef_poly.
case hk: ((k < m)%N) => //.
by rewrite inordK //.
Qed.

Lemma lazard_successor_realize_boundedE (c : nat -> Next) :
  @SS.lazard_symmetric_successor_realize F n
      (@VR.lazard_last_vieta_bounded_polynomial F n c) =
    \sum_(k < m)
      @muni n F (@IM.sym_eval F m (c k)) * 'X^k.
Proof.
rewrite /VR.lazard_last_vieta_bounded_polynomial poly_def.
change ((SS.PolynomialFormulasLazardInvariantSymmetricSuccessor_lazard_symmetric_successor_realize__canonical__GRing_RMorphism
    F n) (\sum_(i < m) c i *: 'X^i) =
  \sum_(k < m) @muni n F (@IM.sym_eval F m (c k)) * 'X^k).
rewrite rmorph_sum.
change ((\sum_(k < m)
  @SS.lazard_symmetric_successor_realize F n (c k *: 'X^k)) =
  \sum_(k < m) @muni n F (@IM.sym_eval F m (c k)) * 'X^k).
apply: eq_bigr => k _.
by rewrite -mul_polyC SS.lazard_symmetric_successor_realizeM
  SS.lazard_symmetric_successor_realizeC
  SS.lazard_symmetric_successor_realize_expr
  SS.lazard_symmetric_successor_realizeX.
Qed.

Lemma lazard_successor_coordinate_block_realizeE
    (c : lazard_successor_index -> Next) a :
  @SS.lazard_symmetric_successor_realize F n
      (lazard_successor_coordinate_block c a) =
    \sum_(k < m)
      @muni n F (@IM.sym_eval F m (c (a, k))) * 'X^k.
Proof.
rewrite /lazard_successor_coordinate_block
  lazard_successor_realize_boundedE.
apply: eq_bigr => k _.
by rewrite inord_val.
Qed.

(** Flattening a double successor-coordinate sum and then applying [muni]
    gives an old-basis expansion whose coefficients are successor
    realizations. *)
Lemma lazard_successor_coordinate_sum_muni
    (c : lazard_successor_index -> Next) :
  @muni n F
      (\sum_ak (c ak) *: lazard_successor_basis ak) =
    \sum_a
      @SS.lazard_symmetric_successor_realize F n
        (lazard_successor_coordinate_block c a) *
          (FF.ffd_basis D a)%:P.
Proof.
have muni_lastXn k :
    @muni n F (lastX ^+ k) = ('X : {poly Old}) ^+ k.
  elim: k => [|k ih].
  - by rewrite !expr0 muni1.
  - by rewrite !exprS muniM ih MU.muni_lastX.
rewrite [LHS]raddf_sum /=.
change (\sum_(ak : (FF.ffd_index D * 'I_m)%type)
    @muni n F (c ak *: lazard_successor_basis ak) =
  \sum_a
    @SS.lazard_symmetric_successor_realize F n
      (lazard_successor_coordinate_block c a) *
        (FF.ffd_basis D a)%:P).
have hpair :
    (\sum_(ak : (FF.ffd_index D * 'I_m)%type)
      @muni n F (c ak *: lazard_successor_basis ak)) =
    \sum_(a : FF.ffd_index D) \sum_(k : 'I_m)
      @muni n F (c (a, k) *: lazard_successor_basis (a, k)).
  rewrite pair_bigA.
  apply: eq_bigr => ak _.
  by case: ak.
rewrite hpair.
apply: eq_bigr => a _.
transitivity
  (\sum_(k : 'I_m)
    (@muni n F (@IM.sym_eval F m (c (a, k))) * 'X^(k : nat)) *
      (FF.ffd_basis D a)%:P).
- apply: eq_bigr => k _.
  rewrite SM.symmetric_scalarE /lazard_successor_basis
    !muniM MU.muni_mwiden muni_lastXn.
  rewrite -mulrA.
  by rewrite (mulrC (FF.ffd_basis D a)%:P
    (('X : {poly Old}) ^+ (k : nat))).
- rewrite -mulr_suml -lazard_successor_coordinate_block_realizeE.
  exact: erefl.
Qed.

(** Old-basis uniqueness works coefficientwise for polynomial blocks.  The
    only side condition is proved image symmetry, not supplied coordinates. *)
Lemma lazard_old_polynomial_blocks_unique p
    (u : FF.ffd_index D -> {poly Old})
    (hu : forall a i, (u a)`_i \is symmetric) :
  @muni n F p = \sum_a u a * (FF.ffd_basis D a)%:P ->
  forall a, u a = lazard_old_coordinate_polynomial p a.
Proof.
move=> hrepresentation a.
apply/polyP=> j.
pose source (b : FF.ffd_index D) : Old :=
  sval (IM.symmetric_coordinates (hu b j)).
have sourceE b : @IM.sym_eval F n (source b) = (u b)`_j.
  rewrite /source.
  case: (IM.symmetric_coordinates (hu b j)) => t [ht _] /=.
  exact: ht.
have hcoefficient := congr1 (fun q : {poly Old} => q`_j)
  hrepresentation.
rewrite [RHS]coef_sum in hcoefficient.
have hold :
    ((@muni n F p)`_j : OldModule) =
      \sum_b (source b) *: FF.ffd_basis D b.
  under [RHS] eq_bigr => b _ do
    rewrite SM.symmetric_scalarE sourceE -coefMC.
  exact: hcoefficient.
have hsource : source a = FF.ffd_coeff D ((@muni n F p)`_j) a :=
  FF.ffd_coeff_unique (D := D) hold a.
rewrite /lazard_old_coordinate_polynomial coef_poly.
case: (ltnP j (size (@muni n F p))) => hj.
- by rewrite -sourceE hsource.
- rewrite -sourceE hsource.
  by rewrite nth_default // FF.ffd_coeff0 IM.sym_eval0.
Qed.

Theorem lazard_successor_coordinates_reconstruct p :
  p = \sum_ak
    (lazard_successor_coordinate p ak) *:
      lazard_successor_basis ak.
Proof.
apply: MU.muni_injective.
rewrite lazard_successor_coordinate_sum_muni.
under [RHS] eq_bigr => a _ do
  rewrite lazard_successor_canonical_blockE.
under [RHS] eq_bigr => a _ do
  rewrite -(@SS.lazard_symmetric_successor_coordinates_reconstruct F n
    (lazard_old_coordinate_polynomial p a)
    (lazard_old_coordinate_polynomial_symmetric p a)).
exact: lazard_old_coordinate_polynomials_reconstruct.
Qed.

Theorem lazard_successor_coordinates_unique p
    (c : lazard_successor_index -> Next) :
  p = \sum_ak (c ak) *: lazard_successor_basis ak ->
  forall ak, c ak = lazard_successor_coordinate p ak.
Proof.
move=> hrepresentation [a k].
have hmuni :
    @muni n F p =
      \sum_b
        @SS.lazard_symmetric_successor_realize F n
          (lazard_successor_coordinate_block c b) *
            (FF.ffd_basis D b)%:P.
  rewrite hrepresentation.
  exact: lazard_successor_coordinate_sum_muni.
have hblock := lazard_old_polynomial_blocks_unique
  (u := fun b =>
    @SS.lazard_symmetric_successor_realize F n
      (lazard_successor_coordinate_block c b))
  (fun b i => SS.lazard_symmetric_successor_coefficients_symmetric
    (lazard_successor_coordinate_block c b) i)
  hmuni a.
have hcanonical :
    @SS.lazard_symmetric_successor_realize F n
      (@VR.lazard_last_vieta_bounded_polynomial F n
        (@SS.lazard_symmetric_successor_coordinate F n
          (lazard_old_coordinate_polynomial p a)
          (lazard_old_coordinate_polynomial_symmetric p a))) =
      lazard_old_coordinate_polynomial p a.
  symmetry.
  exact: (@SS.lazard_symmetric_successor_coordinates_reconstruct F n
    (lazard_old_coordinate_polynomial p a)
    (lazard_old_coordinate_polynomial_symmetric p a)).
have hblocks :
    lazard_successor_coordinate_block c a =
      @VR.lazard_last_vieta_bounded_polynomial F n
        (@SS.lazard_symmetric_successor_coordinate F n
          (lazard_old_coordinate_polynomial p a)
          (lazard_old_coordinate_polynomial_symmetric p a)).
  apply: (SS.lazard_symmetric_successor_small_injective
    (q := lazard_successor_coordinate_block c a)
    (r := @VR.lazard_last_vieta_bounded_polynomial F n
      (@SS.lazard_symmetric_successor_coordinate F n
        (lazard_old_coordinate_polynomial p a)
        (lazard_old_coordinate_polynomial_symmetric p a)))).
  - exact: VR.lazard_last_vieta_bounded_polynomial_size.
  - exact: VR.lazard_last_vieta_bounded_polynomial_size.
  - by rewrite hblock hcanonical.
move: (congr1 (fun q : {poly Next} => q`_(k : nat)) hblocks).
rewrite /lazard_successor_coordinate_block
  /VR.lazard_last_vieta_bounded_polynomial !coef_poly ltn_ord
  /lazard_successor_coordinate inord_val.
exact.
Qed.

Definition lazard_successor_finite_free_decomposition :
    @FF.finite_free_decomposition Next NextModule :=
  {| FF.ffd_index := lazard_successor_index;
     FF.ffd_basis := lazard_successor_basis;
     FF.ffd_coeff := lazard_successor_coordinate;
     FF.ffd_reconstruct := lazard_successor_coordinates_reconstruct;
     FF.ffd_unique := lazard_successor_coordinates_unique |}.

End OneStep.

Section IteratedArtinBasis.

Variable F : fieldType.
Local Notation ZeroModule :=
  (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
    F 0).

Lemma lazard_zero_polynomial_symmetric (p : {mpoly F[0]}) :
  p \is symmetric.
Proof.
apply/issymP=> s.
by rewrite (permS0 s) msym1m.
Qed.

Definition lazard_zero_symmetric_coordinate
    (p : ZeroModule) : {mpoly F[0]} :=
  sval (IM.symmetric_coordinates (lazard_zero_polynomial_symmetric p)).

Lemma lazard_zero_symmetric_coordinateE p :
  IM.sym_eval (lazard_zero_symmetric_coordinate p) = p.
Proof.
rewrite /lazard_zero_symmetric_coordinate.
case: (IM.symmetric_coordinates
  (lazard_zero_polynomial_symmetric p)) => t [ht _] /=.
exact: ht.
Qed.

Definition lazard_zero_artin_basis (_ : 'I_1) :
    ZeroModule := 1.

Definition lazard_zero_artin_coefficient
    (p : ZeroModule) (_ : 'I_1) :
    {mpoly F[0]} :=
  lazard_zero_symmetric_coordinate p.

Lemma lazard_zero_artin_reconstruct p :
  p = \sum_(i : 'I_1)
    (lazard_zero_artin_coefficient p i) *:
      lazard_zero_artin_basis i.
Proof.
rewrite big_ord1 /lazard_zero_artin_coefficient
  /lazard_zero_artin_basis SM.symmetric_scalarE mulr1.
symmetry.
exact: lazard_zero_symmetric_coordinateE.
Qed.

Lemma lazard_zero_artin_unique p (c : 'I_1 -> {mpoly F[0]}) :
  p = \sum_i (c i) *: lazard_zero_artin_basis i ->
  forall i, c i = lazard_zero_artin_coefficient p i.
Proof.
move=> hrepresentation i.
have -> : i = ord0 by apply/val_inj; rewrite ord1.
move: hrepresentation.
rewrite big_ord1 /lazard_zero_artin_basis SM.symmetric_scalarE mulr1
  /lazard_zero_artin_coefficient => hrepresentation.
apply: IM.sym_eval_injective.
by rewrite lazard_zero_symmetric_coordinateE -hrepresentation.
Qed.

Definition lazard_zero_artin_finite_free_decomposition :
    @FF.finite_free_decomposition {mpoly F[0]}
      (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
        F 0) :=
  {| FF.ffd_index := 'I_1;
     FF.ffd_basis := lazard_zero_artin_basis;
     FF.ffd_coeff := lazard_zero_artin_coefficient;
     FF.ffd_reconstruct := lazard_zero_artin_reconstruct;
     FF.ffd_unique := lazard_zero_artin_unique |}.

Fixpoint lazard_reverse_artin_finite_free_decomposition (n : nat) :
    @FF.finite_free_decomposition {mpoly F[n]}
      (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
        F n) :=
  match n as k return
      @FF.finite_free_decomposition {mpoly F[k]}
        (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
          F k) with
  | 0 => lazard_zero_artin_finite_free_decomposition
  | k.+1 =>
      lazard_successor_finite_free_decomposition
        (lazard_reverse_artin_finite_free_decomposition k)
  end.

Fixpoint lazard_reverse_artin_exponent (n : nat) :
    FF.ffd_index (lazard_reverse_artin_finite_free_decomposition n) ->
      'X_{1..n} :=
  match n as k return
      FF.ffd_index (lazard_reverse_artin_finite_free_decomposition k) ->
        'X_{1..k} with
  | 0 => fun _ => 0%MM
  | k.+1 => fun ai =>
      (mnmwiden (@lazard_reverse_artin_exponent k ai.1) +
        U_(ord_max) *+ (ai.2 : nat))%MM
  end.

Lemma lazard_reverse_artin_index_card : forall n,
  #|FF.ffd_index (lazard_reverse_artin_finite_free_decomposition n)| = n`!.
Proof.
elim=> [|n ih].
- by rewrite /lazard_reverse_artin_finite_free_decomposition
    /lazard_zero_artin_finite_free_decomposition card_ord.
- rewrite /lazard_reverse_artin_finite_free_decomposition /=
    /lazard_successor_finite_free_decomposition
    lazard_successor_index_card ih factS mulnC.
  by rewrite mulnE.
Qed.

Lemma lazard_reverse_artin_basisE : forall n
    (a : FF.ffd_index (lazard_reverse_artin_finite_free_decomposition n)),
  FF.ffd_basis (lazard_reverse_artin_finite_free_decomposition n) a =
    'X_[F, @lazard_reverse_artin_exponent n a].
Proof.
elim=> [|n ih] a.
- by rewrite /lazard_reverse_artin_finite_free_decomposition
    /lazard_zero_artin_finite_free_decomposition
    /lazard_zero_artin_basis /lazard_reverse_artin_exponent mpolyX0.
- case: a => a i.
  rewrite /lazard_reverse_artin_finite_free_decomposition /=
    /lazard_successor_finite_free_decomposition
    /lazard_successor_basis /lazard_reverse_artin_exponent /=
    ih mwidenX mpolyXn -mpolyXD.
  change ('X_[F, (mnmwiden (@lazard_reverse_artin_exponent n a) +
    U_(ord_max) *+ (i : nat))%MM] =
    'X_[F, (mnmwiden (@lazard_reverse_artin_exponent n a) +
      U_(ord_max) *+ (i : nat))%MM]).
  exact: erefl.
Qed.

Lemma lazard_mdeg_mnmwiden n (u : 'X_{1..n}) :
  mdeg (mnmwiden u) = mdeg u.
Proof.
rewrite !mdegE big_ord_recr /= mnmwiden_ordmax addn0.
apply: eq_bigr => i _.
exact: mnmwiden_widen.
Qed.

Definition lazard_reverse_artin_degree n
    (a : FF.ffd_index (lazard_reverse_artin_finite_free_decomposition n)) :=
  mdeg (@lazard_reverse_artin_exponent n a).

Lemma lazard_reverse_artin_degreeS n
    (a : FF.ffd_index (lazard_reverse_artin_finite_free_decomposition n))
    (i : 'I_n.+1) :
  @lazard_reverse_artin_degree n.+1 (a, i) =
    (@lazard_reverse_artin_degree n a + (i : nat))%N.
Proof.
rewrite /lazard_reverse_artin_degree
  /lazard_reverse_artin_exponent /= mdegD
  lazard_mdeg_mnmwiden mdegMn mdeg1 mul1n.
by rewrite addnE.
Qed.

Lemma lazard_degree_boundS n :
  IM.lazard_degree_bound n.+1 = (IM.lazard_degree_bound n + n)%N.
Proof.
by rewrite !IM.lazard_degree_bound_binomial binS bin1.
Qed.

Lemma lazard_reverse_artin_degree_le : forall n
    (a : FF.ffd_index (lazard_reverse_artin_finite_free_decomposition n)),
  (lazard_reverse_artin_degree a <= IM.lazard_degree_bound n)%N.
Proof.
elim=> [|n ih] a.
- by rewrite /lazard_reverse_artin_degree
    /lazard_reverse_artin_exponent mdeg0
    /IM.lazard_degree_bound mul0n.
- case: a => a i.
  rewrite lazard_reverse_artin_degreeS lazard_degree_boundS.
  apply: leq_add.
  - exact: ih.
  - by move: (ltn_ord i); rewrite ltnS.
Qed.

Lemma lazard_reverse_artin_basis_homogeneous n
    (a : FF.ffd_index (lazard_reverse_artin_finite_free_decomposition n)) :
  SM.symmetric_module_homogeneous
    (FF.ffd_basis (lazard_reverse_artin_finite_free_decomposition n) a)
    (lazard_reverse_artin_degree a).
Proof.
rewrite /SM.symmetric_module_homogeneous lazard_reverse_artin_basisE
  /lazard_reverse_artin_degree dhomogX eqxx.
exact: isT.
Qed.

(** Unconditional ambient Artin decomposition over the full symmetric ring.
    Its recursive index is the reverse-staircase convention, and every basis
    vector has the precise homogeneous degree used below. *)
  Definition lazard_reverse_artin_homogeneous_decomposition n :
    @FF.homogeneous_finite_free_decomposition
      {mpoly F[n]}
      (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
        F n)
      (SM.symmetric_module_homogeneous (R := F) (n := n))
      (IM.lazard_degree_bound n) :=
  {| FF.hffd_free := lazard_reverse_artin_finite_free_decomposition n;
     FF.hffd_degree := lazard_reverse_artin_degree (n := n);
     FF.hffd_basis_homogeneous :=
       lazard_reverse_artin_basis_homogeneous (n := n);
     FF.hffd_degree_le := lazard_reverse_artin_degree_le (n := n) |}.

End IteratedArtinBasis.

End PolynomialFormulasLazardInvariantArtinSuccessor.
