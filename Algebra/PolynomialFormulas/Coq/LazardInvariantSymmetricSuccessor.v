From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantMultinomials LazardInvariantMpolyUnivariate
  LazardInvariantVietaReduction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The elementary-symmetric successor map needed by the Artin induction.

    A polynomial with formal [n+1]-variable symmetric coefficients is first
    realized at the last root and then viewed by [muni] as a polynomial in
    that root.  The recursive lift below expresses every elementary
    symmetric polynomial in the first [n] roots using the [n+1]-variable
    elementary symmetric coefficients and the last root.  This is the
    generator-level surjectivity step for

      [Sym_n[X_n] = Sym_(n+1)[X_n] / (Vieta)].

    No freeness or coordinate hypothesis is assumed here. *)
Module PolynomialFormulasLazardInvariantSymmetricSuccessor.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope mpoly_scope.

Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module MU := PolynomialFormulasLazardInvariantMpolyUnivariate.
Module VR := PolynomialFormulasLazardInvariantVietaReduction.

Section SymmetricSuccessor.

Variables (R : comRingType) (n : nat).
Local Notation m := n.+1.
Local Notation Old := {mpoly R[n]}.
Local Notation SymNext := {mpoly R[m]}.

(** The Vieta realization transported through the multivariate/univariate
    equivalence. *)
Definition lazard_symmetric_successor_realize
    (q : {poly SymNext}) : {poly Old} :=
  muni (@VR.lazard_last_variable_realize R n q).

Lemma lazard_symmetric_successor_realize0 :
  lazard_symmetric_successor_realize 0 = 0.
Proof.
by rewrite /lazard_symmetric_successor_realize
  VR.lazard_last_variable_realize0 muni0.
Qed.

Lemma lazard_symmetric_successor_realize1 :
  lazard_symmetric_successor_realize 1 = 1.
Proof.
by rewrite /lazard_symmetric_successor_realize
  VR.lazard_last_variable_realize1 muni1.
Qed.

Lemma lazard_symmetric_successor_realizeD :
  {morph lazard_symmetric_successor_realize : q r / q + r}.
Proof.
by move=> q r; rewrite /lazard_symmetric_successor_realize
  VR.lazard_last_variable_realizeD muniD.
Qed.

Lemma lazard_symmetric_successor_realizeN :
  {morph lazard_symmetric_successor_realize : q / - q}.
Proof.
by move=> q; rewrite /lazard_symmetric_successor_realize
  VR.lazard_last_variable_realizeN muniN.
Qed.

Lemma lazard_symmetric_successor_realizeB :
  {morph lazard_symmetric_successor_realize : q r / q - r}.
Proof.
by move=> q r; rewrite /lazard_symmetric_successor_realize
  VR.lazard_last_variable_realizeB muniB.
Qed.

Lemma lazard_symmetric_successor_realizeM :
  {morph lazard_symmetric_successor_realize : q r / q * r}.
Proof.
by move=> q r; rewrite /lazard_symmetric_successor_realize
  VR.lazard_last_variable_realizeM muniM.
Qed.

Lemma lazard_symmetric_successor_realize_expr q k :
  lazard_symmetric_successor_realize (q ^+ k) =
    lazard_symmetric_successor_realize q ^+ k.
Proof.
elim: k => [|k ih].
- by rewrite !expr0 lazard_symmetric_successor_realize1.
- by rewrite !exprS lazard_symmetric_successor_realizeM ih.
Qed.

Lemma lazard_symmetric_successor_realizeC c :
  lazard_symmetric_successor_realize c%:P =
    muni (@IM.sym_eval R m c).
Proof.
by rewrite /lazard_symmetric_successor_realize
  VR.lazard_last_variable_realizeC.
Qed.

Lemma lazard_symmetric_successor_realizeX :
  lazard_symmetric_successor_realize 'X =
    ('X : {poly Old}).
Proof.
by rewrite /lazard_symmetric_successor_realize
  VR.lazard_last_variable_realizeX MU.muni_lastX.
Qed.

(** Splitting the elementary symmetric recurrence at the last variable and
    applying [muni]. *)
Lemma lazard_muni_mesym_successor k :
  muni (mesym m R k.+1) =
    (mesym n R k.+1)%:P + (mesym n R k)%:P * 'X.
Proof.
rewrite (mesymSS R n k) muniD muniM.
by rewrite !MU.muni_mwiden MU.muni_lastX.
Qed.

(** Formal lift of the [k]-th elementary symmetric polynomial in the first
    [n] roots.  The recurrence is [e'_k = e_k - e'_(k-1) X_n]. *)
Fixpoint lazard_previous_esymm_lift (k : nat) : {poly SymNext} :=
  match k with
  | 0 => 1
  | j.+1 =>
      (@VR.lazard_esymm_coordinate R n j.+1)%:P -
        lazard_previous_esymm_lift j * 'X
  end.

Theorem lazard_previous_esymm_liftE k :
  lazard_symmetric_successor_realize
      (lazard_previous_esymm_lift k) =
    (mesym n R k)%:P.
Proof.
elim: k => [|k ih].
- by rewrite /= lazard_symmetric_successor_realize1 mesym0E.
- rewrite /= lazard_symmetric_successor_realizeB
    lazard_symmetric_successor_realizeM
    lazard_symmetric_successor_realizeC
    lazard_symmetric_successor_realizeX
    (@VR.lazard_esymm_coordinateE R n k.+1) ih.
  by rewrite lazard_muni_mesym_successor addrK.
Qed.

(** Bundle the proved laws so MathComp can transport finite products and
    powers through the successor realization. *)
Fact lazard_symmetric_successor_realize_is_additive :
  additive lazard_symmetric_successor_realize.
Proof.
exact: lazard_symmetric_successor_realizeB.
Qed.

HB.instance Definition _ := GRing.isAdditive.Build
  {poly SymNext} {poly Old} lazard_symmetric_successor_realize
  lazard_symmetric_successor_realize_is_additive.

Fact lazard_symmetric_successor_realize_is_multiplicative :
  multiplicative lazard_symmetric_successor_realize.
Proof.
split.
- move=> q r; exact: lazard_symmetric_successor_realizeM.
- exact: lazard_symmetric_successor_realize1.
Qed.

HB.instance Definition _ := GRing.isMultiplicative.Build
  {poly SymNext} {poly Old} lazard_symmetric_successor_realize
  lazard_symmetric_successor_realize_is_multiplicative.

Lemma lazard_sym_evalC (c : R) :
  @IM.sym_eval R n (c%:MP : Old) = (c%:MP : Old).
Proof.
exact: comp_mpolyC.
Qed.

(** Splitting a fully symmetric polynomial in [n+1] variables at the last
    variable leaves coefficients symmetric in the first [n] variables.  We
    prove this for the explicit elementary-symmetric presentation used by
    [sym_eval], rather than postulating closure of the successor image. *)
Lemma lazard_muni_sym_eval_monomial_polyOver
    (u : 'X_{1..m}) :
  muni (@IM.sym_eval R m ('X_[R, u]))
    \in polyOver (@symmetric n R).
Proof.
rewrite /IM.sym_eval comp_mpolyX rmorph_prod /=.
pose S := mpoly_symmetric_pred__canonical__GRing_SemiringClosed n R.
change ((\prod_(i < m)
  muni (tnth (IM.elementary_symmetric_tuple R m) i ^+ u i))
    \is a polyOver S).
apply/rpred_prod => i _.
rewrite rmorphXn.
apply: rpredX.
rewrite /IM.elementary_symmetric_tuple tnth_mktuple.
change (muni (mesym m R i.+1) \is a polyOver S).
rewrite lazard_muni_mesym_successor.
apply: rpredD.
- by rewrite polyOverC; exact: mesym_sym.
- apply: rpredM; last exact: polyOverX.
  by rewrite polyOverC; exact: mesym_sym.
Qed.

Lemma lazard_muni_sym_eval_polyOver (t : SymNext) :
  muni (@IM.sym_eval R m t) \in polyOver (@symmetric n R).
Proof.
pose S := mpoly_symmetric_pred__canonical__GRing_SemiringClosed n R.
change (muni (@IM.sym_eval R m t) \is a polyOver S).
elim/mpolyind: t => [|c u p hu hc ih].
- by rewrite IM.sym_eval0 muni0; exact: rpred0.
- have hC : @IM.sym_eval R m (c%:MP : SymNext) =
      (c%:MP : SymNext).
    exact: comp_mpolyC.
  rewrite -mul_mpolyC IM.sym_evalD IM.sym_evalM hC muniD muniM muniC.
  apply: rpredD; last exact: ih.
  apply: rpredM; last exact: lazard_muni_sym_eval_monomial_polyOver.
  rewrite polyOverC.
  have hconstant := @IM.sym_eval_symmetric R n (c%:MP).
  by rewrite lazard_sym_evalC in hconstant.
Qed.

(** Every successor realization has coefficientwise symmetry.  This is the
    invariant needed to feed a block back into the preceding finite-free
    coordinate decomposition. *)
Theorem lazard_symmetric_successor_coefficients_symmetric
    (q : {poly SymNext}) i :
  (lazard_symmetric_successor_realize q)`_i \is symmetric.
Proof.
pose S := mpoly_symmetric_pred__canonical__GRing_SemiringClosed n R.
have hpolyOver :
    lazard_symmetric_successor_realize q
      \is a polyOver S.
  elim/poly_ind: q => [|q c ih].
  - by rewrite lazard_symmetric_successor_realize0; exact: rpred0.
  - rewrite lazard_symmetric_successor_realizeD
      lazard_symmetric_successor_realizeM
      lazard_symmetric_successor_realizeX
      lazard_symmetric_successor_realizeC.
    apply: rpredD; last exact: lazard_muni_sym_eval_polyOver.
    exact: rpredM ih (polyOverX S).
move/polyOverP: hpolyOver => hcoeff.
exact: hcoeff i.
Qed.

(** Base coefficients are unchanged by the successor realization. *)
Lemma lazard_symmetric_successor_realize_baseC (c : R) :
  lazard_symmetric_successor_realize
      ((c%:MP : SymNext)%:P) =
    ((c%:MP : Old)%:P).
Proof.
by rewrite lazard_symmetric_successor_realizeC
  /IM.sym_eval comp_mpolyC muniC.
Qed.

Definition lazard_previous_esymm_generator (i : 'I_n) :
    {poly SymNext} :=
  lazard_previous_esymm_lift i.+1.

(** Evaluate an abstract polynomial in the elementary symmetric generators
    of the first [n] variables at their explicit successor lifts. *)
Definition lazard_previous_symmetric_lift (t : Old) : {poly SymNext} :=
  mmap (polyC \o (@mpolyC m R))
    lazard_previous_esymm_generator t.

Lemma lazard_previous_symmetric_lift_monomial
    (u : 'X_{1..n}) :
  lazard_symmetric_successor_realize
      (mmap1 lazard_previous_esymm_generator u) =
    (@IM.sym_eval R n ('X_[R, u]))%:P.
Proof.
rewrite /mmap1 rmorph_prod /=.
under [LHS] eq_bigr => i _ do
  rewrite rmorphXn /lazard_previous_esymm_generator.
change ((\prod_(i < n)
  (lazard_symmetric_successor_realize
    (lazard_previous_esymm_lift i.+1)) ^+ u i) =
  (@IM.sym_eval R n ('X_[R, u]))%:P).
under [LHS] eq_bigr => i _ do
  rewrite lazard_previous_esymm_liftE.
rewrite /IM.sym_eval comp_mpolyX rmorph_prod /=.
apply: eq_bigr => i _.
by rewrite /IM.elementary_symmetric_tuple
  tnth_mktuple rmorphXn.
Qed.

(** Every polynomial in the elementary symmetric functions of the first
    [n] variables has an explicit preimage over the next symmetric ring. *)
Theorem lazard_previous_symmetric_liftE t :
  lazard_symmetric_successor_realize
      (lazard_previous_symmetric_lift t) =
    (@IM.sym_eval R n t)%:P.
Proof.
elim/mpolyind: t => [|c u p hu hc ih].
- by rewrite /lazard_previous_symmetric_lift mmap0
    lazard_symmetric_successor_realize0 IM.sym_eval0 polyC0.
- rewrite /lazard_previous_symmetric_lift mmapD mmapZ mmapX /=.
  rewrite lazard_symmetric_successor_realizeD
    lazard_symmetric_successor_realizeM
    lazard_symmetric_successor_realize_baseC
    lazard_previous_symmetric_lift_monomial ih.
  rewrite -mul_mpolyC IM.sym_evalD IM.sym_evalM lazard_sym_evalC.
  by rewrite rmorphD rmorphM.
Qed.

(** Hence the successor realization is surjective onto the polynomials whose
    coefficients are symmetric in the first [n] variables.  The preimage is
    constructed coefficient by coefficient from the fundamental theorem of
    symmetric polynomials and the explicit lifts above. *)
Theorem lazard_symmetric_successor_surjective
    (u : {poly Old})
    (hu : forall i, u`_i \is symmetric) :
  {q : {poly SymNext} |
    lazard_symmetric_successor_realize q = u}.
Proof.
pose old_coordinate (i : 'I_(size u)) : Old :=
  sval (IM.symmetric_coordinates
    (p := u`_i) (hu i)).
have old_coordinateE (i : 'I_(size u)) :
    @IM.sym_eval R n (old_coordinate i) = u`_i.
  rewrite /old_coordinate.
  case: (IM.symmetric_coordinates
    (p := u`_i) (hu i)) => t [ht _] /=.
  exact: ht.
pose q : {poly SymNext} :=
  \sum_(i < size u)
    lazard_previous_symmetric_lift (old_coordinate i) * 'X^i.
exists q.
rewrite /q rmorph_sum /=.
change ((\sum_(i < size u)
  lazard_symmetric_successor_realize
    (lazard_previous_symmetric_lift (old_coordinate i) * 'X^i)) = u).
under [LHS] eq_bigr => i _ do
  rewrite lazard_symmetric_successor_realizeM
    lazard_previous_symmetric_liftE
    lazard_symmetric_successor_realize_expr
    lazard_symmetric_successor_realizeX old_coordinateE.
rewrite -[RHS]coefK poly_def.
apply: eq_bigr => i _.
by rewrite mul_polyC.
Qed.

End SymmetricSuccessor.

Section SymmetricSuccessorKernel.

Variables (F : fieldType) (n : nat).
Local Notation m := n.+1.
Local Notation Ambient := {mpoly F[m]}.
Local Notation SymNext := {mpoly F[m]}.
Local Notation lastX := ('X_(ord_max) : Ambient).

Definition lazard_successor_mapped_polynomial
    (q : {poly SymNext}) : {poly Ambient} :=
  map_poly (@IM.sym_eval F m) q.

Lemma lazard_root_variable_injective :
  injective (fun i : 'I_m => ('X_i : Ambient)).
Proof.
move=> i j hij.
have hs := congr1 (fun p : Ambient => msupp p) hij.
rewrite !msuppX in hs.
have hu : U_(i)%MM = U_(j)%MM.
  move: (congr1 (head U_(i)%MM) hs).
  by [].
have hub : U_(i)%MM == U_(j)%MM.
  by apply/eqP.
move: hub.
by rewrite eq_mnm1 => /eqP.
Qed.

Definition lazard_root_variables : seq Ambient :=
  [seq ('X_i : Ambient) | i <- enum 'I_m].

Lemma lazard_root_variables_size :
  size lazard_root_variables = m.
Proof.
by rewrite /lazard_root_variables size_map size_enum_ord.
Qed.

Lemma lazard_root_variables_uniq :
  uniq lazard_root_variables.
Proof.
rewrite /lazard_root_variables map_inj_uniq ?enum_uniq //.
exact: lazard_root_variable_injective.
Qed.

(** A coefficient produced by [sym_eval] is fixed by every variable
    permutation, so coefficientwise permutation fixes the mapped
    univariate polynomial. *)
Lemma lazard_successor_mapped_polynomial_fixed q
    (s : perm.perm_of 'I_m) :
  map_poly (msym s) (lazard_successor_mapped_polynomial q) =
    lazard_successor_mapped_polynomial q.
Proof.
apply/polyP=> i.
rewrite /lazard_successor_mapped_polynomial !coef_map /=.
move/issymP: (IM.sym_eval_symmetric (q`_i)) => hfixed.
exact: hfixed s.
Qed.

Lemma lazard_msym_tperm_lastX (j : 'I_m) :
  msym (tperm ord_max j) lastX = ('X_j : Ambient).
Proof.
change (msym (tperm ord_max j) ('X_[F, U_(ord_max)]) =
  'X_[F, U_(j)]).
by rewrite /msym mmapX mmap1U tpermL.
Qed.

(** A zero at the last variable transports to a zero at every variable. *)
Lemma lazard_successor_mapped_root
    (q : {poly SymNext})
    (hrealize : @VR.lazard_last_variable_realize F n q = 0)
    (j : 'I_m) :
  root (lazard_successor_mapped_polynomial q) ('X_j : Ambient).
Proof.
apply/rootP.
change ((lazard_successor_mapped_polynomial q).[lastX] = 0)
  in hrealize.
have htransport := congr1 (msym (tperm ord_max j)) hrealize.
move: htransport.
rewrite -horner_map lazard_successor_mapped_polynomial_fixed.
change ((lazard_successor_mapped_polynomial q).[
    msym (tperm ord_max j) lastX] =
  msym (tperm ord_max j) 0 ->
  (lazard_successor_mapped_polynomial q).[('X_j : Ambient)] = 0).
by rewrite lazard_msym_tperm_lastX msym0.
Qed.

Lemma lazard_successor_mapped_all_roots
    (q : {poly SymNext})
    (hrealize : @VR.lazard_last_variable_realize F n q = 0) :
  all (root (lazard_successor_mapped_polynomial q))
    lazard_root_variables.
Proof.
apply/allP=> z.
rewrite /lazard_root_variables.
case/mapP=> j _ ->.
exact: lazard_successor_mapped_root hrealize j.
Qed.

Lemma lazard_successor_mapped_polynomial_size q :
  size (lazard_successor_mapped_polynomial q) = size q.
Proof.
exact: (size_map_inj_poly (@IM.sym_eval_injective F m)
  (@IM.sym_eval0 F m) q).
Qed.

(** The crucial bounded injectivity theorem.  A degree-at-most-[n]
    polynomial in the last root with fully symmetric coefficients cannot
    vanish unless every coefficient is zero: symmetry supplies all [n+1]
    distinct variable roots, and the integral-domain root bound closes the
    argument. *)
Theorem lazard_symmetric_successor_bounded_injective
    (q : {poly SymNext}) :
  (size q <= m)%N ->
  @lazard_symmetric_successor_realize F n q = 0 ->
  q = 0.
Proof.
move=> hsize hstep.
have hrealize : @VR.lazard_last_variable_realize F n q = 0.
  apply: MU.muni_injective.
  by move: hstep; rewrite /lazard_symmetric_successor_realize muni0.
have hmapped0 : lazard_successor_mapped_polynomial q = 0.
  apply: roots_geq_poly_eq0.
  - exact: lazard_successor_mapped_all_roots hrealize.
  - exact: lazard_root_variables_uniq.
  - by rewrite lazard_root_variables_size
      lazard_successor_mapped_polynomial_size.
apply: (map_inj_poly (@IM.sym_eval_injective F m) (@IM.sym_eval0 F m)).
rewrite map_poly0.
change (lazard_successor_mapped_polynomial q = 0).
exact: hmapped0.
Qed.

Lemma lazard_symmetric_successor_remainderE q :
  @lazard_symmetric_successor_realize F n
      (@VR.lazard_last_vieta_remainder F n q) =
    @lazard_symmetric_successor_realize F n q.
Proof.
by rewrite /lazard_symmetric_successor_realize
  VR.lazard_last_vieta_remainder_realize.
Qed.

Lemma lazard_symmetric_successor_relation0 :
  @lazard_symmetric_successor_realize F n
      (@VR.lazard_last_vieta_polynomial F n) = 0.
Proof.
by rewrite /lazard_symmetric_successor_realize
  VR.lazard_last_vieta_polynomial_realize0 muni0.
Qed.

(** Exact kernel theorem: over a field, the only relation between the next
    symmetric coefficients and the last root is the monic Vieta relation. *)
Theorem lazard_symmetric_successor_kernel q :
  @lazard_symmetric_successor_realize F n q = 0 <->
  exists a, q = a * (@VR.lazard_last_vieta_polynomial F n).
Proof.
split.
- move=> hq.
  have hremstep :
      @lazard_symmetric_successor_realize F n
        (@VR.lazard_last_vieta_remainder F n q) = 0.
    by rewrite lazard_symmetric_successor_remainderE hq.
  have hremle :
      (size (@VR.lazard_last_vieta_remainder F n q) <= m)%N.
    by move: (@VR.lazard_last_vieta_remainder_size F n q); rewrite ltnS.
  have hrem0 := lazard_symmetric_successor_bounded_injective
    hremle hremstep.
  exact: (proj1 (@VR.lazard_last_vieta_remainder_eq0_iff_multiple
    F n q) hrem0).
- move=> [a ->].
  by rewrite lazard_symmetric_successor_realizeM
    lazard_symmetric_successor_relation0 mulr0.
Qed.

Corollary lazard_symmetric_successor_small_injective
    (q r : {poly SymNext}) :
  (size q <= m)%N -> (size r <= m)%N ->
  @lazard_symmetric_successor_realize F n q =
    @lazard_symmetric_successor_realize F n r ->
  q = r.
Proof.
move=> hq hr hqr.
have hdiffsize : (size ((q - r)%R) <= m)%N.
  apply: leq_trans (@size_polyD _ q (- r)) _.
  by rewrite size_polyN geq_max hq hr.
have hdiff0 : q - r = 0.
  apply: (lazard_symmetric_successor_bounded_injective
    (q := (q - r)%R)).
  - exact: hdiffsize.
  - by rewrite lazard_symmetric_successor_realizeB hqr subrr.
exact: subr0_eq hdiff0.
Qed.

(** Choose the explicit preimage constructed above and reduce it to the
    unique bounded representative.  The resulting normal form is independent
    of the chosen preimage by the kernel theorem, although the definition can
    simply use the canonical sigma witness returned by the construction. *)
Definition lazard_symmetric_successor_preimage
    (u : {poly {mpoly F[n]}})
    (hu : forall i, u`_i \is symmetric) : {poly SymNext} :=
  sval (@lazard_symmetric_successor_surjective F n u hu).

Arguments lazard_symmetric_successor_preimage _ _ : clear implicits.

Lemma lazard_symmetric_successor_preimageE u hu :
  @lazard_symmetric_successor_realize F n
      (lazard_symmetric_successor_preimage u hu) = u.
Proof.
rewrite /lazard_symmetric_successor_preimage.
case: (@lazard_symmetric_successor_surjective F n u hu) => q hq /=.
exact: hq.
Qed.

Definition lazard_symmetric_successor_normal_form
    (u : {poly {mpoly F[n]}})
    (hu : forall i, u`_i \is symmetric) : {poly SymNext} :=
  @VR.lazard_last_vieta_remainder F n
    (lazard_symmetric_successor_preimage u hu).

Arguments lazard_symmetric_successor_normal_form _ _ : clear implicits.

Lemma lazard_symmetric_successor_normal_form_size u hu :
  (size (lazard_symmetric_successor_normal_form u hu) <= m)%N.
Proof.
rewrite /lazard_symmetric_successor_normal_form.
by move: (@VR.lazard_last_vieta_remainder_size F n
  (lazard_symmetric_successor_preimage u hu)); rewrite ltnS.
Qed.

Lemma lazard_symmetric_successor_normal_formE u hu :
  @lazard_symmetric_successor_realize F n
      (lazard_symmetric_successor_normal_form u hu) = u.
Proof.
by rewrite /lazard_symmetric_successor_normal_form
  lazard_symmetric_successor_remainderE
  lazard_symmetric_successor_preimageE.
Qed.

Definition lazard_symmetric_successor_coordinate u hu (i : nat) :
    SymNext :=
  (lazard_symmetric_successor_normal_form u hu)`_i.

Arguments lazard_symmetric_successor_coordinate _ _ _ : clear implicits.

Lemma lazard_symmetric_successor_normal_form_coordinates u hu :
  lazard_symmetric_successor_normal_form u hu =
    @VR.lazard_last_vieta_bounded_polynomial F n
      (lazard_symmetric_successor_coordinate u hu).
Proof.
rewrite /lazard_symmetric_successor_normal_form
  /lazard_symmetric_successor_coordinate.
exact: VR.lazard_last_vieta_remainder_coordinates.
Qed.

(** Exact reconstruction over the next symmetric ring. *)
Theorem lazard_symmetric_successor_coordinates_reconstruct u hu :
  u = @lazard_symmetric_successor_realize F n
    (@VR.lazard_last_vieta_bounded_polynomial F n
      (lazard_symmetric_successor_coordinate u hu)).
Proof.
rewrite -lazard_symmetric_successor_normal_form_coordinates.
exact/esym/lazard_symmetric_successor_normal_formE.
Qed.

(** Exact uniqueness of the [0,...,n] coefficient block. *)
Theorem lazard_symmetric_successor_coordinates_unique u hu c :
  u = @lazard_symmetric_successor_realize F n
      (@VR.lazard_last_vieta_bounded_polynomial F n c) ->
  forall i, (i < m)%N ->
    c i = lazard_symmetric_successor_coordinate u hu i.
Proof.
move=> hrepresentation i hi.
have hbounded :
    (size (@VR.lazard_last_vieta_bounded_polynomial F n c) <= m)%N.
  exact: VR.lazard_last_vieta_bounded_polynomial_size.
have hnormal :
    @VR.lazard_last_vieta_bounded_polynomial F n c =
      lazard_symmetric_successor_normal_form u hu.
  apply: (lazard_symmetric_successor_small_injective
    (q := @VR.lazard_last_vieta_bounded_polynomial F n c)
    (r := lazard_symmetric_successor_normal_form u hu)).
  - exact: hbounded.
  - exact: lazard_symmetric_successor_normal_form_size.
  - by rewrite -hrepresentation lazard_symmetric_successor_normal_formE.
move: (congr1 (fun p : {poly SymNext} => p`_i) hnormal).
by rewrite /VR.lazard_last_vieta_bounded_polynomial
  /lazard_symmetric_successor_coordinate coef_poly hi.
Qed.

End SymmetricSuccessorKernel.

End PolynomialFormulasLazardInvariantSymmetricSuccessor.
