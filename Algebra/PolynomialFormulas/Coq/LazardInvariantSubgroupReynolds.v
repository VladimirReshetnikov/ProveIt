From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantFiniteFree LazardInvariantMultinomials
  LazardInvariantSymmetricModule
  LazardInvariantHomogeneousCoordinates LazardInvariantSubgroupModule.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Reynolds averaging on the exact symmetric-coefficient module used in
    Lazard's Theorem 2.

    Unlike the finite-dimensional field-linear averaging module, this
    construction averages multivariate polynomials while retaining linearity
    over the full symmetric polynomial ring.  Its only division hypothesis
    is the visible nonvanishing of the subgroup order. *)
Module PolynomialFormulasLazardInvariantSubgroupReynolds.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module SM := PolynomialFormulasLazardInvariantSymmetricModule.
Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module HC := PolynomialFormulasLazardInvariantHomogeneousCoordinates.
Module SIM := PolynomialFormulasLazardInvariantSubgroupModule.

(** Characteristic zero supplies the visible averaging denominator
    hypothesis for every finite subgroup. *)
Lemma lazard_subgroup_card_neq0_of_pchar0
    (F : fieldType) n (H : {group 'S_n})
    (pchar0F : [pchar F] =i pred0) :
  (#|[subg H]|%:R : F) != 0.
Proof.
move/pcharf0P: pchar0F => hchar.
by rewrite hchar -lt0n cardG_gt0.
Qed.

Section Reynolds.

Variables (F : fieldType) (n : nat) (H : {group 'S_n}).
Hypothesis cardH_neq0 : (#|[subg H]|%:R : F) != 0.

Local Notation SymModule :=
  (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
    F n).

(** The inverse group order, represented as a symmetric coefficient. *)
Definition lazard_reynolds_scalar : {mpoly F[n]} :=
  ((#|[subg H]|%:R : F)^-1)%:MP.

(** Normalized average of the subgroup action. *)
Definition lazard_subgroup_reynolds
    (p : SM.symmetric_polynomial_module F n) :
    SM.symmetric_polynomial_module F n :=
  SM.symmetric_scalar lazard_reynolds_scalar
    (\sum_(g : [subg H])
      SM.symmetric_mpoly_left_action (sgval g) p).

Lemma lazard_subgroup_reynoldsD p q :
  lazard_subgroup_reynolds (p + q) =
    lazard_subgroup_reynolds p + lazard_subgroup_reynolds q.
Proof.
rewrite /lazard_subgroup_reynolds /SM.symmetric_scalar.
under eq_bigr => g _ do
  rewrite SM.symmetric_mpoly_left_actionD.
by rewrite big_split mulrDr.
Qed.

Lemma lazard_subgroup_reynoldsZ (a : {mpoly F[n]})
    (p : SM.symmetric_polynomial_module F n) :
  lazard_subgroup_reynolds (SM.symmetric_scalar a p) =
    SM.symmetric_scalar a (lazard_subgroup_reynolds p).
Proof.
rewrite /lazard_subgroup_reynolds.
under eq_bigr => g _ do
  rewrite SM.symmetric_mpoly_left_actionZ.
have hsum :
    (\sum_(g : [subg H])
      SM.symmetric_scalar a
        (SM.symmetric_mpoly_left_action (sgval g) p)) =
    SM.symmetric_scalar a
      (\sum_(g : [subg H])
        SM.symmetric_mpoly_left_action (sgval g) p).
  by rewrite /SM.symmetric_scalar mulr_sumr.
rewrite hsum /SM.symmetric_scalar !mulrA.
by rewrite [(IM.sym_eval lazard_reynolds_scalar * IM.sym_eval a)%R]mulrC.
Qed.

Fact lazard_subgroup_reynolds_is_linear :
  forall (a : {mpoly F[n]}) p q,
    lazard_subgroup_reynolds (SM.symmetric_scalar a p + q) =
      SM.symmetric_scalar a (lazard_subgroup_reynolds p) +
        lazard_subgroup_reynolds q.
Proof.
move=> a p q.
by rewrite lazard_subgroup_reynoldsD lazard_subgroup_reynoldsZ.
Qed.

Definition lazard_subgroup_reynolds_linear :
    {linear SymModule -> SymModule | *:%R} :=
  HB.pack lazard_subgroup_reynolds
    (GRing.isLinear.Build {mpoly F[n]} SymModule SymModule *:%R
      lazard_subgroup_reynolds lazard_subgroup_reynolds_is_linear).

Lemma lazard_subgroup_reynolds_linearE p :
  lazard_subgroup_reynolds_linear p = lazard_subgroup_reynolds p.
Proof. reflexivity. Qed.

(** Reynolds averaging preserves the ordinary homogeneous degree. *)
Lemma lazard_subgroup_reynolds_homogeneous p d :
  (p : {mpoly F[n]}) \is d.-homog ->
  (lazard_subgroup_reynolds p : {mpoly F[n]}) \is d.-homog.
Proof.
move=> hp.
rewrite /lazard_subgroup_reynolds /SM.symmetric_scalar
  /lazard_reynolds_scalar /IM.sym_eval comp_mpolyC mul_mpolyC.
apply: dhomogZ.
apply: rpred_sum => g _.
exact: SM.symmetric_mpoly_left_action_homogeneous hp.
Qed.

(** In the constructed ambient Artin basis, Reynolds' matrix is
    degree-triangular.  This is derived from homogeneous coordinates and is
    not a matrix-shape certificate. *)
Theorem lazard_subgroup_reynolds_artin_matrix_triangular i j :
  (FF.hffd_degree (SIM.lazard_ambient_artin_homogeneous_decomposition F n) j <
    FF.hffd_degree (SIM.lazard_ambient_artin_homogeneous_decomposition F n) i)%N ->
  FF.ffd_coeff
    (FF.hffd_free
      (SIM.lazard_ambient_artin_homogeneous_decomposition F n))
    (lazard_subgroup_reynolds
      (FF.ffd_basis
        (FF.hffd_free
          (SIM.lazard_ambient_artin_homogeneous_decomposition F n)) j)) i = 0.
Proof.
apply: (@HC.lazard_degree_preserving_matrix_triangular F n
  (IM.lazard_degree_bound n)
  (SIM.lazard_ambient_artin_homogeneous_decomposition F n)
  lazard_subgroup_reynolds).
move=> p d.
exact: lazard_subgroup_reynolds_homogeneous.
Qed.

(** Every equal-degree diagonal block is already defined over the ground
    field.  This is the precise input consumed by the finite-dimensional
    Reynolds block argument. *)
Theorem lazard_subgroup_reynolds_artin_matrix_constant i j :
  FF.hffd_degree (SIM.lazard_ambient_artin_homogeneous_decomposition F n) i =
    FF.hffd_degree (SIM.lazard_ambient_artin_homogeneous_decomposition F n) j ->
  exists r : F,
    FF.ffd_coeff
      (FF.hffd_free
        (SIM.lazard_ambient_artin_homogeneous_decomposition F n))
      (lazard_subgroup_reynolds
        (FF.ffd_basis
          (FF.hffd_free
            (SIM.lazard_ambient_artin_homogeneous_decomposition F n)) j)) i =
      r%:MP.
Proof.
apply: (@HC.lazard_degree_preserving_matrix_constant F n
  (IM.lazard_degree_bound n)
  (SIM.lazard_ambient_artin_homogeneous_decomposition F n)
  lazard_subgroup_reynolds).
move=> p d.
exact: lazard_subgroup_reynolds_homogeneous.
Qed.

Local Notation Artin :=
  (SIM.lazard_ambient_artin_homogeneous_decomposition F n).
Local Notation B := (FF.hffd_free Artin).
Local Notation degree := (FF.hffd_degree Artin).

(** A name for the full Reynolds matrix entry.  Keeping this definition
    separate from its ground-field diagonal part makes the triangular
    idempotence calculation below readable. *)
Definition lazard_subgroup_reynolds_artin_entry
    (i j : FF.ffd_index B) : {mpoly F[n]} :=
  FF.ffd_coeff B
    (lazard_subgroup_reynolds (FF.ffd_basis B j)) i.

(** A deterministic ground-field representative of each Artin-matrix
    entry.  Away from equal degrees this is merely its constant
    coefficient; on an equal-degree block the next lemma proves that it is
    the whole entry.  This removes any use of choice when constructing the
    finite diagonal matrices. *)
Definition lazard_subgroup_reynolds_artin_scalar
    (i j : FF.ffd_index B) : F :=
  (lazard_subgroup_reynolds_artin_entry i j)@_0%MM.

Lemma lazard_subgroup_reynolds_artin_matrix_constantE i j :
  degree i = degree j ->
  lazard_subgroup_reynolds_artin_entry i j =
    (lazard_subgroup_reynolds_artin_scalar i j)%:MP.
Proof.
move=> hij.
have [r hr] := lazard_subgroup_reynolds_artin_matrix_constant hij.
change (lazard_subgroup_reynolds_artin_entry i j = r%:MP) in hr.
by rewrite /lazard_subgroup_reynolds_artin_scalar !hr
  mcoeffC eqxx mulr1.
Qed.

(** The finite ground-field matrix of the degree-[d] diagonal block.  The
    ambient Artin index is enumerated so standard MathComp finite linear
    algebra can be applied without introducing a supplied block basis. *)
Definition lazard_subgroup_reynolds_degree_block_matrix (d : nat) :
    'M[F]_(#|FF.ffd_index B|) :=
  \matrix_(i, j)
    if (FF.hffd_degree Artin (enum_val i) == d) &&
       (FF.hffd_degree Artin (enum_val j) == d)
    then lazard_subgroup_reynolds_artin_scalar (enum_val i) (enum_val j)
    else 0.

Lemma lazard_subgroup_reynolds_degree_block_matrixE d i j :
  lazard_subgroup_reynolds_degree_block_matrix d i j =
    if (FF.hffd_degree Artin (enum_val i) == d) &&
       (FF.hffd_degree Artin (enum_val j) == d)
    then lazard_subgroup_reynolds_artin_scalar (enum_val i) (enum_val j)
    else 0.
Proof. by rewrite /lazard_subgroup_reynolds_degree_block_matrix mxE. Qed.

(** Multiplying two full Reynolds entries through an intermediate Artin
    index contributes to the degree-[d] diagonal block exactly when that
    intermediate index also has degree [d].  If its degree is smaller, the
    left entry vanishes; if it is larger, the right entry vanishes. *)
Lemma lazard_subgroup_reynolds_artin_entry_product_degreeE d i j k :
  degree i = d -> degree j = d ->
  (lazard_subgroup_reynolds_artin_entry i k *
      lazard_subgroup_reynolds_artin_entry k j)%R =
    if degree k == d then
      (lazard_subgroup_reynolds_artin_scalar i k *
       lazard_subgroup_reynolds_artin_scalar k j)%:MP
    else 0.
Proof.
move=> hi hj.
case hkd: (degree k == d).
- have hik : degree i = degree k by rewrite hi (eqP hkd).
  have hkj : degree k = degree j by rewrite (eqP hkd) hj.
  rewrite (lazard_subgroup_reynolds_artin_matrix_constantE hik)
    (lazard_subgroup_reynolds_artin_matrix_constantE hkj).
  by rewrite mpolyCM.
- have hneq : degree k != d by rewrite hkd.
  case hle: (degree k <= d)%N.
  + have hlt : (degree k < degree i)%N.
      by rewrite hi ltn_neqAle hneq hle.
    rewrite /lazard_subgroup_reynolds_artin_entry
      (lazard_subgroup_reynolds_artin_matrix_triangular hlt).
    exact: mul0r.
  + have hlt : (degree j < degree k)%N.
      by rewrite hj ltnNge hle.
    rewrite /lazard_subgroup_reynolds_artin_entry
      (lazard_subgroup_reynolds_artin_matrix_triangular hlt).
    exact: mulr0.
Qed.

(** Constants embed injectively into multivariate polynomials. *)
Lemma lazard_mpolyC_injective :
  injective (fun r : F => (r%:MP : {mpoly F[n]})).
Proof.
move=> a b hab.
have := congr1 (fun p : {mpoly F[n]} => p@_0%MM) hab.
by rewrite !mcoeffC !eqxx !mulr1.
Qed.

(** Left multiplication merely reindexes the subgroup sum. *)
Lemma lazard_subgroup_reynolds_action_invariant
    (h : [subg H]) p :
  SM.symmetric_mpoly_left_action (sgval h)
      (lazard_subgroup_reynolds p) =
    lazard_subgroup_reynolds p.
Proof.
rewrite /lazard_subgroup_reynolds
  SM.symmetric_mpoly_left_actionZ
  SM.symmetric_mpoly_left_action_sum.
apply: congr1.
transitivity
  (\sum_(g : [subg H])
    SM.symmetric_mpoly_left_action (sgval (h * g)) p).
- apply: eq_bigr=> g _.
  by rewrite -SM.symmetric_mpoly_left_actionM -sgvalM.
- symmetry.
  exact: (@reindex_inj
    (SM.symmetric_polynomial_module F n) +%R 0 _
    (fun g : [subg H] => h * g) xpredT
    (fun g => SM.symmetric_mpoly_left_action (sgval g) p)
    (mulgI h)).
Qed.

(** Averaging fixes every invariant polynomial. *)
Lemma lazard_subgroup_reynolds_fix_invariant p :
  p \in SIM.lazard_subgroup_invariant_pred (F := F) H ->
  lazard_subgroup_reynolds p = p.
Proof.
move/SIM.lazard_subgroup_invariantP=> hp.
have cardH_enum_neq0 := cardH_neq0.
rewrite cardsT cardT in cardH_enum_neq0.
rewrite /lazard_subgroup_reynolds.
under eq_bigr => g _ do rewrite hp.
rewrite sumr_const cardT /SM.symmetric_scalar
  /lazard_reynolds_scalar /IM.sym_eval comp_mpolyC mul_mpolyC.
rewrite -(@scaler_nat F {mpoly F[n]}
  _ (p : {mpoly F[n]})) scalerA cardsT cardT
  (mulVf cardH_enum_neq0).
exact: scale1r.
Qed.

Lemma lazard_subgroup_reynolds_idempotent p :
  lazard_subgroup_reynolds (lazard_subgroup_reynolds p) =
    lazard_subgroup_reynolds p.
Proof.
apply: lazard_subgroup_reynolds_fix_invariant.
apply/SIM.lazard_subgroup_invariantP=> h.
exact: lazard_subgroup_reynolds_action_invariant.
Qed.

(** Matrix form of idempotence in the constructed Artin basis. *)
Lemma lazard_subgroup_reynolds_artin_matrix_idempotent_entry i j :
  \sum_k
      FF.ffd_coeff B
        (lazard_subgroup_reynolds (FF.ffd_basis B k)) i *
      FF.ffd_coeff B
        (lazard_subgroup_reynolds (FF.ffd_basis B j)) k =
    FF.ffd_coeff B
      (lazard_subgroup_reynolds (FF.ffd_basis B j)) i.
Proof.
transitivity
  (FF.ffd_coeff B
    (lazard_subgroup_reynolds
      (\sum_k
        (FF.ffd_coeff B
          (lazard_subgroup_reynolds (FF.ffd_basis B j)) k) *:
        FF.ffd_basis B k)) i).
- change ((\sum_k
      FF.ffd_coeff B
        (lazard_subgroup_reynolds (FF.ffd_basis B k)) i *
      FF.ffd_coeff B
        (lazard_subgroup_reynolds (FF.ffd_basis B j)) k) =
    FF.ffd_coeff B
      (lazard_subgroup_reynolds_linear
        (\sum_k
          (FF.ffd_coeff B
            (lazard_subgroup_reynolds (FF.ffd_basis B j)) k) *:
          FF.ffd_basis B k)) i).
  have hlinear :
      lazard_subgroup_reynolds_linear
        (\sum_k
          (FF.ffd_coeff B
            (lazard_subgroup_reynolds (FF.ffd_basis B j)) k) *:
          FF.ffd_basis B k) =
      \sum_k
        (FF.ffd_coeff B
          (lazard_subgroup_reynolds (FF.ffd_basis B j)) k) *:
        lazard_subgroup_reynolds_linear (FF.ffd_basis B k).
    rewrite linear_sum.
    apply: eq_bigr=> k _.
    exact: linearZ _ _.
  rewrite hlinear FF.ffd_coeff_sum.
  apply: eq_bigr=> k _.
  rewrite [RHS]FF.ffd_coeffZ lazard_subgroup_reynolds_linearE.
  by rewrite mulrC.
- have hreconstruct :
      (\sum_k
        (FF.ffd_coeff B
          (lazard_subgroup_reynolds (FF.ffd_basis B j)) k) *:
        FF.ffd_basis B k) =
      lazard_subgroup_reynolds (FF.ffd_basis B j).
    symmetry.
    exact: FF.ffd_reconstruct.
  by rewrite hreconstruct lazard_subgroup_reynolds_idempotent.
Qed.

(** The scalar diagonal block inherits idempotence from the full Reynolds
    matrix.  This is where triangularity rules out every intermediate Artin
    degree other than [d]. *)
Lemma lazard_subgroup_reynolds_artin_scalar_idempotent d i j :
  degree i = d -> degree j = d ->
  \sum_k
      (if degree k == d then
         lazard_subgroup_reynolds_artin_scalar i k *
         lazard_subgroup_reynolds_artin_scalar k j
       else 0) =
    lazard_subgroup_reynolds_artin_scalar i j.
Proof.
move=> hi hj.
have hij : degree i = degree j by rewrite hi hj.
have hfull := lazard_subgroup_reynolds_artin_matrix_idempotent_entry i j.
have hfull' :
    (\sum_(k : FF.ffd_index B)
      (if degree k == d then
         (((lazard_subgroup_reynolds_artin_scalar i k *
          lazard_subgroup_reynolds_artin_scalar k j)%R)%:MP :
            {mpoly F[n]})
       else (0 : {mpoly F[n]}))) =
      ((lazard_subgroup_reynolds_artin_scalar i j)%:MP :
        {mpoly F[n]}).
  transitivity (\sum_k
    (lazard_subgroup_reynolds_artin_entry i k *
    lazard_subgroup_reynolds_artin_entry k j)%R).
  - apply: eq_bigr=> k _.
    symmetry.
    exact: (lazard_subgroup_reynolds_artin_entry_product_degreeE
      (d := d) (i := i) (j := j) k hi hj).
  - change ((\sum_k
      (FF.ffd_coeff B
        (lazard_subgroup_reynolds (FF.ffd_basis B k)) i *
      FF.ffd_coeff B
        (lazard_subgroup_reynolds (FF.ffd_basis B j)) k)%R) =
      ((lazard_subgroup_reynolds_artin_scalar i j)%:MP :
        {mpoly F[n]})).
    rewrite hfull.
    exact: lazard_subgroup_reynolds_artin_matrix_constantE hij.
apply: lazard_mpolyC_injective.
rewrite rmorph_sum.
transitivity
  (\sum_(k : FF.ffd_index B)
    if degree k == d then
      (((lazard_subgroup_reynolds_artin_scalar i k *
        lazard_subgroup_reynolds_artin_scalar k j)%R)%:MP :
          {mpoly F[n]})
    else (0 : {mpoly F[n]})).
- apply: eq_bigr=> k _.
  case: ifP=> hkd; by rewrite ?rmorph0.
- exact: hfull'.
Qed.

(** Consequently every explicitly constructed ground-field degree block is
    an idempotent matrix.  No rank, basis, or matrix-shape certificate is an
    input to this result. *)
Theorem lazard_subgroup_reynolds_degree_block_matrix_idempotent d :
  lazard_subgroup_reynolds_degree_block_matrix d *m
      lazard_subgroup_reynolds_degree_block_matrix d =
    lazard_subgroup_reynolds_degree_block_matrix d.
Proof.
apply/matrixP=> i j.
rewrite !mxE.
case hi: (degree (enum_val i) == d).
- case hj: (degree (enum_val j) == d).
  + rewrite /=.
    transitivity
      (\sum_(k < #|FF.ffd_index B|)
        if degree (enum_val k) == d then
          (lazard_subgroup_reynolds_artin_scalar
              (enum_val i) (enum_val k) *
           lazard_subgroup_reynolds_artin_scalar
              (enum_val k) (enum_val j))%R
        else 0).
    * apply: eq_bigr=> k _.
      rewrite !lazard_subgroup_reynolds_degree_block_matrixE hi hj /=.
      case hk: (degree (enum_val k) == d);
        by rewrite /= ?mul0r ?mulr0.
    * transitivity
        (\sum_(k : FF.ffd_index B)
          if degree k == d then
            (lazard_subgroup_reynolds_artin_scalar (enum_val i) k *
             lazard_subgroup_reynolds_artin_scalar k (enum_val j))%R
          else 0).
      - symmetry.
        exact: (@big_enum_val F 0 +%R (FF.ffd_index B) xpredT
          (fun k =>
            if degree k == d then
              (lazard_subgroup_reynolds_artin_scalar (enum_val i) k *
               lazard_subgroup_reynolds_artin_scalar k (enum_val j))%R
            else 0)).
      - exact: lazard_subgroup_reynolds_artin_scalar_idempotent
          (eqP hi) (eqP hj).
  + rewrite /=.
    apply: big1=> k _.
    by rewrite !lazard_subgroup_reynolds_degree_block_matrixE hj
      andbF mulr0.
- rewrite /=.
  apply: big1=> k _.
  by rewrite !lazard_subgroup_reynolds_degree_block_matrixE hi
    andFb mul0r.
Qed.

Local Notation N := (#|FF.ffd_index B|).

(** View the transpose of the degree block as a linear endomorphism of row
    vectors.  Transposition aligns MathComp's right-multiplication convention
    with our matrix convention: rows are output Artin coordinates and columns
    are input coordinates. *)
Definition lazard_subgroup_reynolds_degree_block_linear d :
    {linear 'rV[F]_N -> 'rV[F]_N} :=
  let f := @mulmxr F 1 N N
    (lazard_subgroup_reynolds_degree_block_matrix d)^T in
  HB.pack f
    (GRing.isLinear.Build F 'rV[F]_N 'rV[F]_N *:%R f
      (@mulmxr_is_linear F 1 N N
        (lazard_subgroup_reynolds_degree_block_matrix d)^T)).

Lemma lazard_subgroup_reynolds_degree_block_linearE d v :
  lazard_subgroup_reynolds_degree_block_linear d v =
    v *m (lazard_subgroup_reynolds_degree_block_matrix d)^T.
Proof. reflexivity. Qed.

Lemma lazard_subgroup_reynolds_degree_block_linear_idempotent d v :
  lazard_subgroup_reynolds_degree_block_linear d
      (lazard_subgroup_reynolds_degree_block_linear d v) =
    lazard_subgroup_reynolds_degree_block_linear d v.
Proof.
by rewrite !lazard_subgroup_reynolds_degree_block_linearE -mulmxA
  -trmx_mul lazard_subgroup_reynolds_degree_block_matrix_idempotent.
Qed.

(** The finite-dimensional ground-field image and MathComp's concrete basis
    for it. *)
Definition lazard_subgroup_reynolds_degree_block_image d :
    {vspace 'rV[F]_N} :=
  limg (linfun (lazard_subgroup_reynolds_degree_block_linear d)).

Definition lazard_subgroup_reynolds_degree_block_basis d :=
  vbasis (lazard_subgroup_reynolds_degree_block_image d).

Lemma lazard_subgroup_reynolds_degree_block_basisP d :
  basis_of (lazard_subgroup_reynolds_degree_block_image d)
    (lazard_subgroup_reynolds_degree_block_basis d).
Proof. exact: vbasisP. Qed.

Lemma lazard_subgroup_reynolds_degree_block_image_fixed d v :
  v \in lazard_subgroup_reynolds_degree_block_image d ->
  lazard_subgroup_reynolds_degree_block_linear d v = v.
Proof.
move/memv_imgP=> [u _ ->].
rewrite !lfunE.
exact: lazard_subgroup_reynolds_degree_block_linear_idempotent.
Qed.

(** Every vector in the degree-[d] image is supported only on Artin indices
    of degree [d]. *)
Lemma lazard_subgroup_reynolds_degree_block_linear_support d v j :
  degree (enum_val j) != d ->
  (lazard_subgroup_reynolds_degree_block_linear d v) 0 j = 0.
Proof.
move=> hj.
rewrite lazard_subgroup_reynolds_degree_block_linearE mxE.
apply: big1=> k _.
by rewrite mxE lazard_subgroup_reynolds_degree_block_matrixE
  (negbTE hj) andFb mulr0.
Qed.

Lemma lazard_subgroup_reynolds_degree_block_image_support d v :
  v \in lazard_subgroup_reynolds_degree_block_image d ->
  forall j, degree (enum_val j) != d -> v 0 j = 0.
Proof.
move=> hv j hj.
rewrite -(lazard_subgroup_reynolds_degree_block_image_fixed hv).
exact: lazard_subgroup_reynolds_degree_block_linear_support hj.
Qed.

Lemma lazard_subgroup_reynolds_degree_block_basis_mem d
    (i : 'I_(\dim (lazard_subgroup_reynolds_degree_block_image d))) :
  tnth (lazard_subgroup_reynolds_degree_block_basis d) i
    \in lazard_subgroup_reynolds_degree_block_image d.
Proof. exact: vbasis_mem (mem_tnth i _). Qed.

Lemma lazard_subgroup_reynolds_degree_block_basis_fixed d
    (i : 'I_(\dim (lazard_subgroup_reynolds_degree_block_image d))) :
  lazard_subgroup_reynolds_degree_block_linear d
      (tnth (lazard_subgroup_reynolds_degree_block_basis d) i) =
    tnth (lazard_subgroup_reynolds_degree_block_basis d) i.
Proof.
exact: lazard_subgroup_reynolds_degree_block_image_fixed
  (lazard_subgroup_reynolds_degree_block_basis_mem i).
Qed.

Lemma lazard_subgroup_reynolds_degree_block_basis_support d
    (i : 'I_(\dim (lazard_subgroup_reynolds_degree_block_image d))) j :
  degree (enum_val j) != d ->
  tnth (lazard_subgroup_reynolds_degree_block_basis d) i 0 j = 0.
Proof.
exact: lazard_subgroup_reynolds_degree_block_image_support
  (lazard_subgroup_reynolds_degree_block_basis_mem i) j.
Qed.

(** Interpret a ground-field row vector as an ambient Artin combination.
    Coefficients are embedded as constants in the symmetric coefficient
    ring. *)
Definition lazard_subgroup_reynolds_artin_vector
    (v : 'rV[F]_N) : SM.symmetric_polynomial_module F n :=
  \sum_(j < N) (v 0 j)%:MP *: FF.ffd_basis B (enum_val j).

Lemma lazard_subgroup_reynolds_artin_vector_coeff v j :
  FF.ffd_coeff B (lazard_subgroup_reynolds_artin_vector v) (enum_val j) =
    (v 0 j)%:MP.
Proof.
rewrite /lazard_subgroup_reynolds_artin_vector FF.ffd_coeff_sum
  (bigD1 j) //= FF.ffd_coeffZ FF.ffd_coeff_basis eqxx mulr1.
rewrite big1 ?addr0 // => k hkj.
rewrite FF.ffd_coeffZ FF.ffd_coeff_basis.
have henum : enum_val j != enum_val k.
  apply/negP=> /eqP heq.
  by move: hkj; rewrite (enum_val_inj heq) eqxx.
by rewrite (negbTE henum) mulr0.
Qed.

(** Support in one Artin degree makes the associated ambient vector
    homogeneous in that same degree. *)
Lemma lazard_subgroup_reynolds_artin_vector_homogeneous d
    (v : 'rV[F]_N) :
  (forall j, degree (enum_val j) != d -> v 0 j = 0) ->
  (lazard_subgroup_reynolds_artin_vector v : {mpoly F[n]}) \is d.-homog.
Proof.
move=> hv.
rewrite /lazard_subgroup_reynolds_artin_vector.
apply: rpred_sum=> j _.
case hj: (degree (enum_val j) == d).
- rewrite SM.symmetric_scalarE /IM.sym_eval comp_mpolyC mul_mpolyC.
  apply: dhomogZ.
  have hb := FF.hffd_basis_is_homogeneous (D := Artin) (enum_val j).
  by move: hb; rewrite (eqP hj).
- have hj' : degree (enum_val j) != d by rewrite hj.
  rewrite (hv j hj') scale0r.
  exact: rpred0.
Qed.

(** Reynolds applied to an Artin coordinate row has the expected matrix
    expansion. *)
Lemma lazard_subgroup_reynolds_artin_vector_reynolds_coeff v i :
  FF.ffd_coeff B
      (lazard_subgroup_reynolds
        (lazard_subgroup_reynolds_artin_vector v)) i =
    \sum_(j < N)
      (v 0 j)%:MP *
        lazard_subgroup_reynolds_artin_entry i (enum_val j).
Proof.
change (FF.ffd_coeff B
    (lazard_subgroup_reynolds_linear
      (\sum_(j < N) (v 0 j)%:MP *: FF.ffd_basis B (enum_val j))) i =
    \sum_(j < N)
      ((v 0 j)%:MP *
        lazard_subgroup_reynolds_artin_entry i (enum_val j))%R).
rewrite linear_sum FF.ffd_coeff_sum.
apply: eq_bigr=> j _.
by rewrite linearZ FF.ffd_coeffZ
  lazard_subgroup_reynolds_linearE
  /lazard_subgroup_reynolds_artin_entry.
Qed.

(** On the selected degree block, lifting an image vector through Reynolds
    preserves its top Artin coordinates exactly. *)
Lemma lazard_subgroup_reynolds_artin_vector_top_coeff d v
    (hv : v \in lazard_subgroup_reynolds_degree_block_image d) i
    (hi : degree (enum_val i) = d) :
  FF.ffd_coeff B
      (lazard_subgroup_reynolds
        (lazard_subgroup_reynolds_artin_vector v)) (enum_val i) =
    (v 0 i)%:MP.
Proof.
rewrite lazard_subgroup_reynolds_artin_vector_reynolds_coeff.
transitivity
  (((\sum_(j < N)
      (v 0 j *
        lazard_subgroup_reynolds_artin_scalar
          (enum_val i) (enum_val j))%R)%:MP : {mpoly F[n]})).
- rewrite rmorph_sum.
  apply: eq_bigr=> j _.
  case hj: (degree (enum_val j) == d).
  + have hij : degree (enum_val i) = degree (enum_val j).
      by rewrite hi (eqP hj).
    rewrite (lazard_subgroup_reynolds_artin_matrix_constantE hij).
    by rewrite rmorphM.
  + have hj' : degree (enum_val j) != d by rewrite hj.
    have hvj := lazard_subgroup_reynolds_degree_block_image_support
      (j := j) hv hj'.
    by rewrite hvj rmorph0 !mul0r.
- apply: congr1.
  transitivity
    ((lazard_subgroup_reynolds_degree_block_linear d v) 0 i).
  + rewrite lazard_subgroup_reynolds_degree_block_linearE mxE.
    apply: eq_bigr=> j _.
    rewrite mxE lazard_subgroup_reynolds_degree_block_matrixE.
    have hi' : degree (enum_val i) == d by rewrite hi.
    rewrite hi' /=.
    case hj: (degree (enum_val j) == d)=> //.
    have hj' : degree (enum_val j) != d by rewrite hj.
    have hv0 : v 0 j = 0 :=
      lazard_subgroup_reynolds_degree_block_image_support
        (j := j) hv hj'.
    by rewrite hv0 !mul0r.
  + by rewrite (lazard_subgroup_reynolds_degree_block_image_fixed hv).
Qed.

Lemma lazard_subgroup_reynolds_mem_invariant p :
  lazard_subgroup_reynolds p
    \in SIM.lazard_subgroup_invariant_pred (F := F) H.
Proof.
apply/SIM.lazard_subgroup_invariantP=> h.
exact: lazard_subgroup_reynolds_action_invariant.
Qed.

(** The average, bundled as an inhabitant of the exact invariant module. *)
Definition lazard_subgroup_reynolds_invariant
    (p : SM.symmetric_polynomial_module F n) :
    SIM.lazard_subgroup_invariant_module F H :=
  @SIM.LazardSubgroupInvariant F n H (lazard_subgroup_reynolds p)
    (lazard_subgroup_reynolds_mem_invariant p).

Lemma lazard_subgroup_reynolds_invariant_val p :
  SIM.lazard_subgroup_invariant_val
      (lazard_subgroup_reynolds_invariant p) =
    lazard_subgroup_reynolds p.
Proof. by []. Qed.

(** Lift one vector of a constant diagonal-block image to an actual
    homogeneous invariant polynomial. *)
Definition lazard_subgroup_reynolds_degree_block_lift d
    (i : 'I_(\dim (lazard_subgroup_reynolds_degree_block_image d))) :
    SIM.lazard_subgroup_invariant_module F H :=
  lazard_subgroup_reynolds_invariant
    (lazard_subgroup_reynolds_artin_vector
      (tnth (lazard_subgroup_reynolds_degree_block_basis d) i)).

Lemma lazard_subgroup_reynolds_degree_block_lift_homogeneous d
    (i : 'I_(\dim (lazard_subgroup_reynolds_degree_block_image d))) :
  SIM.lazard_invariant_homogeneous
    (lazard_subgroup_reynolds_degree_block_lift (d := d) i) d.
Proof.
rewrite /SIM.lazard_invariant_homogeneous
  /lazard_subgroup_reynolds_degree_block_lift
  lazard_subgroup_reynolds_invariant_val.
apply: lazard_subgroup_reynolds_homogeneous.
apply: lazard_subgroup_reynolds_artin_vector_homogeneous=> j hj.
exact: (lazard_subgroup_reynolds_degree_block_basis_support
  (d := d) (j := j) i hj).
Qed.

Lemma lazard_subgroup_reynolds_degree_block_lift_top_coeff d
    (i : 'I_(\dim (lazard_subgroup_reynolds_degree_block_image d))) j
    (hj : degree (enum_val j) = d) :
  FF.ffd_coeff B
    (SIM.lazard_subgroup_invariant_val
        (lazard_subgroup_reynolds_degree_block_lift (d := d) i))
      (enum_val j) =
    (tnth (lazard_subgroup_reynolds_degree_block_basis d) i 0 j)%:MP.
Proof.
rewrite /lazard_subgroup_reynolds_degree_block_lift
  lazard_subgroup_reynolds_invariant_val.
exact: (lazard_subgroup_reynolds_artin_vector_top_coeff
  (d := d) (i := j)
  (lazard_subgroup_reynolds_degree_block_basis_mem i) hj).
Qed.

(** A single finite type collecting all block-basis vectors in degrees at
    most Lazard's Artin bound.  The second ordinal is retained only when it
    lies below the actual dimension of the corresponding image block. *)
Definition lazard_subgroup_reynolds_generator_pred
    (di : 'I_(IM.lazard_degree_bound n).+1 * 'I_N) : bool :=
  (di.2 < \dim
    (lazard_subgroup_reynolds_degree_block_image di.1))%N.

Definition lazard_subgroup_reynolds_generator_index : finType :=
  {di : 'I_(IM.lazard_degree_bound n).+1 * 'I_N |
    lazard_subgroup_reynolds_generator_pred di}.

Definition lazard_subgroup_reynolds_generator_degree
    (g : lazard_subgroup_reynolds_generator_index) : nat :=
  (val g).1.

Definition lazard_subgroup_reynolds_generator_block_index
    (g : lazard_subgroup_reynolds_generator_index) :
    'I_(\dim (lazard_subgroup_reynolds_degree_block_image
      (lazard_subgroup_reynolds_generator_degree g))) :=
  @Ordinal _ (val (val g).2) (valP g).

Definition lazard_subgroup_reynolds_generator
    (g : lazard_subgroup_reynolds_generator_index) :
    SIM.lazard_subgroup_invariant_module F H :=
  lazard_subgroup_reynolds_degree_block_lift
    (lazard_subgroup_reynolds_generator_block_index g).

Lemma lazard_subgroup_reynolds_generator_homogeneous
    (g : lazard_subgroup_reynolds_generator_index) :
  SIM.lazard_invariant_homogeneous
    (lazard_subgroup_reynolds_generator g)
    (lazard_subgroup_reynolds_generator_degree g).
Proof.
exact: lazard_subgroup_reynolds_degree_block_lift_homogeneous.
Qed.

Lemma lazard_subgroup_reynolds_generator_degree_le
    (g : lazard_subgroup_reynolds_generator_index) :
  (lazard_subgroup_reynolds_generator_degree g <=
    IM.lazard_degree_bound n)%N.
Proof.
by rewrite -ltnS; exact: valP (val g).1.
Qed.

End Reynolds.

End PolynomialFormulasLazardInvariantSubgroupReynolds.
