From mathcomp Require Import all_ssreflect all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantMultinomials LazardInvariantFiniteFree
  LazardInvariantArtinSuccessor LazardInvariantVietaReduction.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The literal degree-five instance of Lazard's displayed basis [J].

    The outer polynomial variables are the roots [x0,...,x4].  The inner
    polynomial variables are the formal elementary-symmetric coefficients
    [e1,...,e5].  This file deliberately says "quintic": it does not disguise
    a fixed finite computation as the all-degrees version of Lemma 1.

    We prove the two explicit changes of generators between [J] and
    [(sigma_i-e_i)], check the paper-order leading monomials and reduced
    tails on the actual multinomial supports, and then derive the formal
    quotient normal form from the Artin basis. *)
Module PolynomialFormulasLazardDisplayedGroebnerQuintic.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope mpoly_scope.
Local Open Scope multi_scope.

Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module AS := PolynomialFormulasLazardInvariantArtinSuccessor.
Module SM := PolynomialFormulasLazardInvariantSymmetricModule.
Module VR := PolynomialFormulasLazardInvariantVietaReduction.

Local Notation Coeff := {mpoly rat[5]}.
Local Notation Ambient := {mpoly Coeff[5]}.
Local Notation RootRing := {mpoly rat[5]}.

Definition q0 : 'I_5 := @Ordinal 5 0 isT.
Definition q1 : 'I_5 := @Ordinal 5 1 isT.
Definition q2 : 'I_5 := @Ordinal 5 2 isT.
Definition q3 : 'I_5 := @Ordinal 5 3 isT.
Definition q4 : 'I_5 := @Ordinal 5 4 isT.

Definition x (i : 'I_5) : Ambient := 'X_i.
Definition e (i : 'I_5) : Ambient := (('X_i : Coeff))%:MP.

Local Notation x0 := (x q0).
Local Notation x1 := (x q1).
Local Notation x2 := (x q2).
Local Notation x3 := (x q3).
Local Notation x4 := (x q4).
Local Notation e1 := (e q0).
Local Notation e2 := (e q1).
Local Notation e3 := (e q2).
Local Notation e4 := (e q3).
Local Notation e5 := (e q4).

(** Expanded elementary symmetric polynomials. *)
Definition sigma1 : Ambient := x0 + x1 + x2 + x3 + x4.
Definition sigma2 : Ambient :=
  x0*x1 + x0*x2 + x0*x3 + x0*x4 + x1*x2 +
  x1*x3 + x1*x4 + x2*x3 + x2*x4 + x3*x4.
Definition sigma3 : Ambient :=
  x0*x1*x2 + x0*x1*x3 + x0*x1*x4 + x0*x2*x3 + x0*x2*x4 +
  x0*x3*x4 + x1*x2*x3 + x1*x2*x4 + x1*x3*x4 + x2*x3*x4.
Definition sigma4 : Ambient :=
  x0*x1*x2*x3 + x0*x1*x2*x4 + x0*x1*x3*x4 +
  x0*x2*x3*x4 + x1*x2*x3*x4.
Definition sigma5 : Ambient := x0*x1*x2*x3*x4.

Definition vieta_relations : 5.-tuple Ambient :=
  [tuple sigma1-e1; sigma2-e2; sigma3-e3; sigma4-e4; sigma5-e5].

Definition vieta_relation (i : 'I_5) : Ambient :=
  tnth vieta_relations i.

(** The expanded [sigma_i] above are the library elementary-symmetric
    multinomials, so these really are Lazard's generators
    [sigma_(i+1)-e_(i+1)]. *)
Theorem vieta_relation_mesym i :
  vieta_relation i = mesym 5 Coeff i.+1 - e i.
Proof.
case: i=> [[|[|[|[|[|i]]]]] hi] //=; vm_compute.
Qed.

(** Evaluate formal coefficient variables by elementary-symmetric
    substitution while leaving the five root variables fixed.  The generic
    [mmap] operation performs both coefficient and variable evaluation in one
    ring morphism, so no nested-polynomial flattening axiom is involved. *)
Definition formal_specialization (p : Ambient) : RootRing :=
  mmap (@IM.sym_eval rat 5) (fun i => ('X_i : RootRing)) p.

Lemma formal_specialization0 : formal_specialization 0 = 0.
Proof. exact: mmap0. Qed.

Lemma formal_specializationD :
  {morph formal_specialization : p q / p + q}.
Proof. exact: mmapD. Qed.

Lemma formal_specializationN :
  {morph formal_specialization : p / - p}.
Proof. exact: mmapN. Qed.

Lemma formal_specializationB :
  {morph formal_specialization : p q / p - q}.
Proof. exact: mmapB. Qed.

Lemma formal_specializationM :
  {morph formal_specialization : p q / p * q}.
Proof. exact: mmapM. Qed.

Lemma formal_specialization_e i :
  formal_specialization (e i) = mesym 5 rat i.+1.
Proof.
rewrite /formal_specialization /e mmapC /IM.sym_eval
  /IM.elementary_symmetric_tuple comp_mpolyXU.
by rewrite -tnth_nth tnth_mktuple.
Qed.

Lemma formal_specialization_mesym k :
  formal_specialization (mesym 5 Coeff k) = mesym 5 rat k.
Proof.
rewrite /formal_specialization !mesymE raddf_sum.
apply: eq_bigr => u _.
by rewrite mmapX mmap1_id.
Qed.

Theorem formal_specialization_vieta_relation i :
  formal_specialization (vieta_relation i) = 0.
Proof.
rewrite vieta_relation_mesym formal_specializationB
  formal_specialization_mesym formal_specialization_e subrr.
exact: erefl.
Qed.

(** The five complete-homogeneous relations displayed in Lazard's paper. *)
Definition displayed_relations : 5.-tuple Ambient := [tuple
  x0^+5 - e1*x0^+4 + e2*x0^+3 - e3*x0^+2 + e4*x0 - e5;

  (x0^+4 + x0^+3*x1 + x0^+2*x1^+2 + x0*x1^+3 + x1^+4) -
    e1*(x0^+3 + x0^+2*x1 + x0*x1^+2 + x1^+3) +
    e2*(x0^+2 + x0*x1 + x1^+2) - e3*(x0+x1) + e4;

  (x0^+3 + x0^+2*x1 + x0^+2*x2 + x0*x1^+2 + x0*x1*x2 +
    x0*x2^+2 + x1^+3 + x1^+2*x2 + x1*x2^+2 + x2^+3) -
    e1*(x0^+2 + x0*x1 + x0*x2 + x1^+2 + x1*x2 + x2^+2) +
    e2*(x0+x1+x2) - e3;

  (x0^+2 + x0*x1 + x0*x2 + x0*x3 + x1^+2 + x1*x2 +
    x1*x3 + x2^+2 + x2*x3 + x3^+2) - e1*(x0+x1+x2+x3) + e2;

  x0+x1+x2+x3+x4-e1].

Definition displayed_J (i : 'I_5) : Ambient :=
  tnth displayed_relations i.

(** Explicit matrices for the two changes of generators. *)
Definition j_to_vieta : 5.-tuple (5.-tuple Ambient) := [tuple
  [tuple x0^+4; -x0^+3; x0^+2; -x0; 1];
  [tuple (x0+x1)*(x0^+2+x1^+2);
    -(x0^+2+x0*x1+x1^+2); x0+x1; -1; 0];
  [tuple x0^+2+x0*x1+x0*x2+x1^+2+x1*x2+x2^+2;
    -(x0+x1+x2); 1; 0; 0];
  [tuple x0+x1+x2+x3; -1; 0; 0; 0];
  [tuple 1; 0; 0; 0; 0]].

Definition vieta_to_j : 5.-tuple (5.-tuple Ambient) := [tuple
  [tuple 0; 0; 0; 0; 1];
  [tuple 0; 0; 0; -1; x0+x1+x2+x3];
  [tuple 0; 0; 1; -(x0+x1+x2);
    x0*x1+x0*x2+x0*x3+x1*x2+x1*x3+x2*x3];
  [tuple 0; -1; x0+x1;
    -(x0*x1+x0*x2+x1*x2);
    x0*x1*x2+x0*x1*x3+x0*x2*x3+x1*x2*x3];
  [tuple 1; -x0; x0*x1; -(x0*x1*x2); x0*x1*x2*x3]].

Definition j_to_vieta_entry (i k : 'I_5) : Ambient :=
  tnth (tnth j_to_vieta i) k.

Definition vieta_to_j_entry (i k : 'I_5) : Ambient :=
  tnth (tnth vieta_to_j i) k.

Theorem displayed_J_eq_vieta_combination i :
  displayed_J i =
    \sum_k j_to_vieta_entry i k * vieta_relation k.
Proof.
case: i=> [[|[|[|[|[|i]]]]] hi] //=;
  rewrite /displayed_J /displayed_relations
    /j_to_vieta_entry /j_to_vieta /vieta_relation /vieta_relations
    /sigma1 /sigma2 /sigma3 /sigma4 /sigma5 /x /e /=;
  ring.
Qed.

Theorem vieta_relation_eq_displayed_J_combination i :
  vieta_relation i =
    \sum_k vieta_to_j_entry i k * displayed_J k.
Proof.
case: i=> [[|[|[|[|[|i]]]]] hi] //=;
  rewrite /displayed_J /displayed_relations
    /vieta_to_j_entry /vieta_to_j /vieta_relation /vieta_relations
    /sigma1 /sigma2 /sigma3 /sigma4 /sigma5 /x /e /=;
  ring.
Qed.

Theorem formal_specialization_displayed_J i :
  formal_specialization (displayed_J i) = 0.
Proof.
rewrite displayed_J_eq_vieta_combination
  /formal_specialization raddf_sum.
apply: big1 => k _.
rewrite rmorphM.
have -> : mmap (@IM.sym_eval rat 5) (fun j => ('X_j : RootRing))
    (vieta_relation k) = 0 := formal_specialization_vieta_relation k.
by rewrite mulr0.
Qed.

(** Membership in the ideal generated by a finite family, written without
    relying on a library-specific proper-ideal wrapper. *)
Definition generated_by (f : 'I_5 -> Ambient) (p : Ambient) : Prop :=
  exists c : 'I_5 -> Ambient, p = \sum_i c i * f i.

Lemma generated_by0 f : generated_by f 0.
Proof.
exists (fun _ => 0).
by rewrite big1 // => i _; rewrite mul0r.
Qed.

Lemma generated_byD f p q :
  generated_by f p -> generated_by f q -> generated_by f (p + q).
Proof.
move=> [a ->] [b ->].
exists (fun i => a i + b i).
rewrite -big_split /=.
apply: eq_bigr=> i _.
exact/esym: mulrDl.
Qed.

Lemma generated_byN f p : generated_by f p -> generated_by f (- p).
Proof.
move=> [a ->].
exists (fun i => - a i).
rewrite -sumrN.
apply: eq_bigr=> i _.
by rewrite mulNr.
Qed.

Lemma generated_byB f p q :
  generated_by f p -> generated_by f q -> generated_by f (p - q).
Proof.
move=> hp hq; rewrite subr_eq_addr.
exact: generated_byD hp (generated_byN hq).
Qed.

Lemma generated_by_mul_left f a p :
  generated_by f p -> generated_by f (a * p).
Proof.
move=> [c ->].
exists (fun i => a * c i).
rewrite mulr_sumr.
apply: eq_bigr=> i _.
by rewrite mulrA.
Qed.

Lemma generated_by_mul_right f a p :
  generated_by f p -> generated_by f (p * a).
Proof.
move=> hp.
rewrite mulrC.
exact: generated_by_mul_left hp.
Qed.

Lemma generated_by_generator f i : generated_by f (f i).
Proof.
exists (fun j => (j == i)%:R).
rewrite (bigD1 i) //= eqxx mul1r.
rewrite big1 ?addr0 // => j hji.
by rewrite (negbTE hji) mul0r.
Qed.

Lemma generated_by_change (f g : 'I_5 -> Ambient)
    (A : 'I_5 -> 'I_5 -> Ambient)
    (hA : forall i, f i = \sum_k A i k * g k) p :
  generated_by f p -> generated_by g p.
Proof.
move=> [c ->].
exists (fun k => \sum_i c i * A i k).
under [LHS] eq_bigr => i _ do rewrite hA mulr_sumr.
rewrite exchange_big.
apply: eq_bigr=> k _.
rewrite mulr_suml.
apply: eq_bigr=> i _.
by rewrite mulrA.
Qed.

Theorem displayed_generated_ideal_eq_vieta p :
  generated_by displayed_J p <-> generated_by vieta_relation p.
Proof.
split.
- exact: generated_by_change displayed_J_eq_vieta_combination.
- exact: generated_by_change vieta_relation_eq_displayed_J_combination.
Qed.

Definition vieta_congruent (p q : Ambient) : Prop :=
  generated_by vieta_relation (p - q).

Lemma vieta_congruent_refl p : vieta_congruent p p.
Proof. rewrite /vieta_congruent subrr; exact: generated_by0. Qed.

Lemma vieta_congruent_sym p q :
  vieta_congruent p q -> vieta_congruent q p.
Proof.
rewrite /vieta_congruent=> h.
have := generated_byN h.
by rewrite opprB.
Qed.

Lemma vieta_congruent_trans p q r :
  vieta_congruent p q -> vieta_congruent q r -> vieta_congruent p r.
Proof.
rewrite /vieta_congruent=> hpq hqr.
have h := generated_byD hpq hqr.
convert h using 1; ring.
Qed.

Lemma vieta_congruent_add p q r s :
  vieta_congruent p q -> vieta_congruent r s ->
  vieta_congruent (p + r) (q + s).
Proof.
rewrite /vieta_congruent=> hpq hrs.
have h := generated_byD hpq hrs.
convert h using 1; ring.
Qed.

Lemma vieta_congruent_mul p q r s :
  vieta_congruent p q -> vieta_congruent r s ->
  vieta_congruent (p * r) (q * s).
Proof.
rewrite /vieta_congruent=> hpq hrs.
have h1 := generated_by_mul_left p hrs.
have h2 := generated_by_mul_right s hpq.
have h := generated_byD h1 h2.
convert h using 1; ring.
Qed.

Lemma vieta_congruent_exp p q n :
  vieta_congruent p q -> vieta_congruent (p ^+ n) (q ^+ n).
Proof.
move=> hpq; elim: n=> [|n ih].
- exact: vieta_congruent_refl.
- rewrite !exprS.
  exact: vieta_congruent_mul hpq ih.
Qed.

Lemma vieta_congruent_sum (T : finType) (p q : T -> Ambient) :
  (forall i, vieta_congruent (p i) (q i)) ->
  vieta_congruent (\sum_i p i) (\sum_i q i).
Proof.
move=> h.
elim/big_ind2: _ => // a b c d hab hcd.
exact: vieta_congruent_add hab hcd.
Qed.

Lemma vieta_congruent_prod (T : finType) (p q : T -> Ambient) :
  (forall i, vieta_congruent (p i) (q i)) ->
  vieta_congruent (\prod_i p i) (\prod_i q i).
Proof.
move=> h.
elim/big_ind2: _ => // a b c d hab hcd.
exact: vieta_congruent_mul hab hcd.
Qed.

(** Two coefficient embeddings into the formal two-level ring: keep the
    formal [e]-variables, or substitute their elementary-symmetric values and
    lift the resulting root polynomial back to the outer ring. *)
Definition root_lift (p : RootRing) : Ambient :=
  map_mpoly (@mpolyC 5 rat) p.

Definition formal_coefficient (c : Coeff) : Ambient := c%:MP.

Definition substituted_coefficient (c : Coeff) : Ambient :=
  root_lift (IM.sym_eval c).

Lemma formal_coefficient0 : formal_coefficient 0 = 0.
Proof. by rewrite /formal_coefficient mpolyC0. Qed.

Lemma formal_coefficientD c d :
  formal_coefficient (c + d) =
    formal_coefficient c + formal_coefficient d.
Proof. exact: rmorphD. Qed.

Lemma formal_coefficientM c d :
  formal_coefficient (c * d) =
    formal_coefficient c * formal_coefficient d.
Proof. exact: rmorphM. Qed.

Lemma substituted_coefficient0 : substituted_coefficient 0 = 0.
Proof.
by rewrite /substituted_coefficient /root_lift IM.sym_eval0 raddf0.
Qed.

Lemma substituted_coefficientD c d :
  substituted_coefficient (c + d) =
    substituted_coefficient c + substituted_coefficient d.
Proof.
by rewrite /substituted_coefficient /root_lift IM.sym_evalD raddfD.
Qed.

Lemma substituted_coefficientM c d :
  substituted_coefficient (c * d) =
    substituted_coefficient c * substituted_coefficient d.
Proof.
by rewrite /substituted_coefficient /root_lift IM.sym_evalM rmorphM.
Qed.

Lemma formal_coefficient_base (c : rat) :
  formal_coefficient c%:MP = substituted_coefficient c%:MP.
Proof.
rewrite /formal_coefficient /substituted_coefficient /root_lift
  /IM.sym_eval comp_mpolyC map_mpolyC.
exact: erefl.
Qed.

Lemma formal_coefficient_X i : formal_coefficient ('X_i) = e i.
Proof. exact: erefl. Qed.

Lemma substituted_coefficient_X i :
  substituted_coefficient ('X_i) = mesym 5 Coeff i.+1.
Proof.
rewrite /substituted_coefficient /root_lift /IM.sym_eval
  /IM.elementary_symmetric_tuple comp_mpolyXU
  -tnth_nth tnth_mktuple.
exact: VR.map_mpoly_mesym.
Qed.

Lemma formal_variables_vieta_congruent i :
  vieta_congruent (formal_coefficient ('X_i))
    (substituted_coefficient ('X_i)).
Proof.
rewrite formal_coefficient_X substituted_coefficient_X
  /vieta_congruent.
have h := generated_byN (generated_by_generator vieta_relation i).
rewrite vieta_relation_mesym in h.
convert h using 1; ring.
Qed.

Lemma formal_coefficient_monomial (u : 'X_{1..5}) :
  formal_coefficient ('X_[rat, u]) =
    \prod_i (formal_coefficient ('X_i)) ^+ (u i).
Proof.
rewrite /formal_coefficient mpolyXE_id rmorph_prod.
apply: eq_bigr=> i _.
by rewrite rmorphXn.
Qed.

Lemma substituted_coefficient_monomial (u : 'X_{1..5}) :
  substituted_coefficient ('X_[rat, u]) =
    \prod_i (substituted_coefficient ('X_i)) ^+ (u i).
Proof.
rewrite /substituted_coefficient /root_lift /IM.sym_eval
  comp_mpolyX rmorph_prod.
apply: eq_bigr=> i _.
rewrite rmorphXn /IM.elementary_symmetric_tuple
  -tnth_nth tnth_mktuple /substituted_coefficient /root_lift
  /IM.sym_eval comp_mpolyXU -tnth_nth tnth_mktuple.
exact: erefl.
Qed.

Lemma formal_monomials_vieta_congruent u :
  vieta_congruent (formal_coefficient ('X_[rat, u]))
    (substituted_coefficient ('X_[rat, u])).
Proof.
rewrite formal_coefficient_monomial substituted_coefficient_monomial.
apply: vieta_congruent_prod=> i.
exact: vieta_congruent_exp (formal_variables_vieta_congruent i).
Qed.

Theorem formal_coefficients_vieta_congruent c :
  vieta_congruent (formal_coefficient c) (substituted_coefficient c).
Proof.
elim/mpolyind: c=> [|a u p hu ha ih].
- rewrite formal_coefficient0 substituted_coefficient0.
  exact: vieta_congruent_refl.
- rewrite -mul_mpolyC formal_coefficientD formal_coefficientM
    substituted_coefficientD substituted_coefficientM.
  apply: vieta_congruent_add.
  + apply: vieta_congruent_mul.
    * rewrite formal_coefficient_base.
      exact: vieta_congruent_refl.
    * exact: formal_monomials_vieta_congruent.
  + exact: ih.
Qed.

Lemma root_lift0 : root_lift 0 = 0.
Proof. by rewrite /root_lift raddf0. Qed.

Lemma root_liftD p q : root_lift (p + q) = root_lift p + root_lift q.
Proof. exact: raddfD. Qed.

Lemma root_liftM p q : root_lift (p * q) = root_lift p * root_lift q.
Proof. exact: rmorphM. Qed.

Lemma root_lift_monomial u :
  root_lift ('X_[rat, u]) = 'X_[Coeff, u].
Proof. exact: map_mpolyX. Qed.

Lemma root_lift_formal_specialization_term c u :
  root_lift
    (formal_specialization (c *: 'X_[Coeff, u])) =
  substituted_coefficient c * 'X_[Coeff, u].
Proof.
rewrite /formal_specialization mmapZ mmapX mmap1_id
  root_liftM root_lift_monomial.
exact: erefl.
Qed.

(** Every formal polynomial is congruent, modulo the Vieta generators, to
    the canonical lift of its specialization.  The proof is structural on
    the actual multinomial representation and ultimately uses only
    [e_i ≡ sigma_(i+1)]. *)
Theorem formal_polynomial_vieta_congruent p :
  vieta_congruent p (root_lift (formal_specialization p)).
Proof.
elim/mpolyind: p=> [|c u p hu hc ih].
- rewrite formal_specialization0 root_lift0.
  exact: vieta_congruent_refl.
- rewrite formal_specializationD root_liftD.
  apply: vieta_congruent_add.
  + rewrite root_lift_formal_specialization_term -mul_mpolyC.
    apply: vieta_congruent_mul.
    * exact: formal_coefficients_vieta_congruent.
    * exact: vieta_congruent_refl.
  + exact: ih.
Qed.

Theorem formal_specialization_generated_by_displayed_J p :
  generated_by displayed_J p -> formal_specialization p = 0.
Proof.
move=> [c ->].
rewrite /formal_specialization raddf_sum.
apply: big1 => i _.
rewrite rmorphM.
have -> : mmap (@IM.sym_eval rat 5) (fun j => ('X_j : RootRing))
    (displayed_J i) = 0 := formal_specialization_displayed_J i.
by rewrite mulr0.
Qed.

(** Exact kernel theorem for the formal specialization. *)
Theorem formal_specialization_kernel_generated p :
  formal_specialization p = 0 <-> generated_by displayed_J p.
Proof.
split.
- move=> hp.
  have h := formal_polynomial_vieta_congruent p.
  rewrite /vieta_congruent hp root_lift0 subr0 in h.
  exact: (displayed_generated_ideal_eq_vieta p).2 h.
- exact: formal_specialization_generated_by_displayed_J.
Qed.

(** Lazard's monomial order in five root variables: root total degree first,
    then lexicographically from [x4] back to [x0]. *)
Definition paper_lt (u v : 'X_{1..5}) : bool :=
  (mdeg u < mdeg v) ||
  ((mdeg u == mdeg v) &&
   ((u q4 < v q4) || ((u q4 == v q4) &&
    ((u q3 < v q3) || ((u q3 == v q3) &&
     ((u q2 < v q2) || ((u q2 == v q2) &&
      ((u q1 < v q1) || ((u q1 == v q1) && (u q0 < v q0)))))))))).

Definition paper_leading_monomials : 5.-tuple 'X_{1..5} := [tuple
  [multinom [tuple 5; 0; 0; 0; 0]];
  [multinom [tuple 0; 4; 0; 0; 0]];
  [multinom [tuple 0; 0; 3; 0; 0]];
  [multinom [tuple 0; 0; 0; 2; 0]];
  [multinom [tuple 0; 0; 0; 0; 1]]].

Definition paper_leading_monomial (i : 'I_5) : 'X_{1..5} :=
  tnth paper_leading_monomials i.

(** Support predicate for the paper's standard monomials
    [x0^a0 ... x4^a4] with [ai < 5-i]. *)
Definition paper_standard_monomial (u : 'X_{1..5}) : bool :=
  [forall i : 'I_5, u i < 5 - i].

Definition paper_standard (p : Ambient) : bool :=
  all paper_standard_monomial (msupp p).

Lemma paper_standardP p :
  reflect
    (forall u, u \in msupp p -> forall i : 'I_5, u i < 5 - i)
    (paper_standard p).
Proof.
apply: (iffP allP).
- move=> h u hu i.
  have /forallP := h u hu.
  exact.
- move=> h u hu; apply/forallP=> i.
  exact: h u hu i.
Qed.

Definition artin_index_of_standard (u : 'X_{1..5})
    (hu : forall i : 'I_5, u i < 5 - i) : IM.artin_index 5 :=
  [ffun i => @Ordinal (5 - i) (u i) (hu i)].

Lemma artin_exponent_of_standardE u hu :
  IM.artin_exponent (artin_index_of_standard u hu) = u.
Proof.
apply/mnmP=> i.
by rewrite /IM.artin_exponent /artin_index_of_standard mnmE ffunE.
Qed.

(** The recursive Artin basis in [LazardInvariantArtinSuccessor] introduces
    variables in the opposite order.  Reversing its variables gives exactly
    the paper-standard staircase. *)
Local Notation ReverseArtin :=
  (FF.ffd_index
    (@AS.lazard_reverse_artin_finite_free_decomposition rat 5)).

Definition paper_reverse_perm : 'S_5 := perm (@rev_ord_inj 5).

Definition paper_artin_exponent (a : ReverseArtin) : 'X_{1..5} :=
  [multinom
    (@AS.lazard_reverse_artin_exponent rat 5 a)
      ((paper_reverse_perm^-1)%g i) | i < 5].

Definition paper_artin_standard_check : bool :=
  [forall a : ReverseArtin,
    [forall i : 'I_5, paper_artin_exponent a i < 5 - i]].

Lemma paper_artin_standard_checkP : paper_artin_standard_check.
Proof. vm_compute. Qed.

Lemma paper_artin_exponent_standard a i :
  paper_artin_exponent a i < 5 - i.
Proof.
have /forallP h := paper_artin_standard_checkP.
have /forallP := h a.
exact.
Qed.

Definition paper_artin_injective_check : bool :=
  [forall a : ReverseArtin, [forall b : ReverseArtin,
    (paper_artin_exponent a == paper_artin_exponent b) == (a == b)]].

Lemma paper_artin_injective_checkP : paper_artin_injective_check.
Proof. vm_compute. Qed.

Lemma paper_artin_exponent_injective : injective paper_artin_exponent.
Proof.
move=> a b hab.
have /forallP h := paper_artin_injective_checkP.
have /forallP h := h a.
move/eqP: (h b).
by rewrite hab eqxx => /eqP.
Qed.

Fixpoint reverse_artin_zero_index (n : nat) :
    FF.ffd_index
      (@AS.lazard_reverse_artin_finite_free_decomposition rat n) :=
  match n as k return
      FF.ffd_index
        (@AS.lazard_reverse_artin_finite_free_decomposition rat k) with
  | 0 => ord0
  | k.+1 => (reverse_artin_zero_index k, ord0)
  end.

(** A concrete finite reindexing from the paper's Artin indices to the
    reversed recursive basis.  Its correctness is checked below on all 120
    indices; this is proof-producing finite computation, not an assumption. *)
Definition reverse_index_of_artin (a : IM.artin_index 5) : ReverseArtin :=
  odflt (reverse_artin_zero_index 5)
    [pick b : ReverseArtin |
      paper_artin_exponent b == IM.artin_exponent a].

Definition reverse_index_of_artin_check : bool :=
  [forall a : IM.artin_index 5,
    paper_artin_exponent (reverse_index_of_artin a) ==
      IM.artin_exponent a].

Lemma reverse_index_of_artin_checkP : reverse_index_of_artin_check.
Proof. vm_compute. Qed.

Lemma reverse_index_of_artinE a :
  paper_artin_exponent (reverse_index_of_artin a) =
    IM.artin_exponent a.
Proof.
have /forallP h := reverse_index_of_artin_checkP.
exact/eqP: h a.
Qed.

Lemma reverse_index_of_artin_injective : injective reverse_index_of_artin.
Proof.
move=> a b hab.
apply: IM.artin_exponent_injective.
by rewrite -!reverse_index_of_artinE hab.
Qed.

Lemma reverse_index_of_artin_bijective : bijective reverse_index_of_artin.
Proof.
apply: inj_card_bij reverse_index_of_artin_injective.
by rewrite IM.card_artin_index AS.lazard_reverse_artin_index_card.
Qed.

Definition paper_artin_basis (a : ReverseArtin) :
    SM.symmetric_polynomial_module rat 5 :=
  msym paper_reverse_perm
    (FF.ffd_basis
      (@AS.lazard_reverse_artin_finite_free_decomposition rat 5) a).

Lemma paper_artin_basisE a :
  paper_artin_basis a = 'X_[rat, paper_artin_exponent a].
Proof.
rewrite /paper_artin_basis AS.lazard_reverse_artin_basisE msymX
  /paper_artin_exponent.
exact: erefl.
Qed.

Lemma msym_sym_eval (s : 'S_5) (c : Coeff) :
  msym s (IM.sym_eval c) = IM.sym_eval c.
Proof.
have /issymP h := IM.sym_eval_symmetric c.
exact: h s.
Qed.

Lemma paper_artin_unreverse c a :
  msym (paper_reverse_perm^-1)%g
    (c *: paper_artin_basis a) =
  c *:
    FF.ffd_basis
      (@AS.lazard_reverse_artin_finite_free_decomposition rat 5) a.
Proof.
rewrite !SM.symmetric_scalarE /paper_artin_basis msymM
  msym_sym_eval -msymMm mulgV msym1m.
exact: erefl.
Qed.

(** The paper-oriented staircase monomials are independent over the formal
    elementary-symmetric coefficient ring.  This is derived by undoing the
    variable reversal and invoking the already proved reverse Artin basis;
    it is not a matrix-rank certificate. *)
Lemma paper_artin_basis_independent (c : ReverseArtin -> Coeff) :
  (
    \sum_a (c a) *: paper_artin_basis a = 0) ->
  forall a, c a = 0.
Proof.
move=> hzero.
have hzero' := congr1 (msym (paper_reverse_perm^-1)%g) hzero.
rewrite msym0 raddf_sum in hzero'.
under [X in \sum_a X] eq_bigr => a _ do
  rewrite paper_artin_unreverse.
exact: (FF.ffd_basis_independent
  (@AS.lazard_reverse_artin_finite_free_decomposition rat 5) hzero').
Qed.

Lemma mpoly_expansion_over_monomials
    (T : finType) (f : T -> 'X_{1..5})
    (finj : injective f) (p : Ambient)
    (hcover : forall u, u \in msupp p -> exists a, f a = u) :
  p = \sum_a (p @_ f a) *: 'X_[Coeff, f a].
Proof.
apply/mpolyP=> u.
rewrite raddf_sum.
case hsu: (u \in msupp p).
- have [a ha] := hcover u hsu.
  rewrite (bigD1 a) //= mcoeffZ mcoeffX ha eqxx mulr1.
  rewrite big1 ?addr0 // => b hba.
  rewrite mcoeffZ mcoeffX.
  have hfb : f b != u.
    apply/negP=> /eqP hfb.
    have hba' : b = a := finj (hfb.trans ha.symm).
    by move: hba; rewrite hba' eqxx.
  by rewrite (negbTE hfb) mulr0.
- have hcoeff : p @_ u = 0.
    apply/eqP.
    by rewrite mcoeff_eq0 hsu.
  rewrite hcoeff big1 // => a _.
  rewrite mcoeffZ mcoeffX.
  case hfa: (f a == u).
  + move/eqP: hfa=> ->.
    by rewrite hcoeff mul0r.
  + by rewrite hfa mulr0.
Qed.

Theorem paper_standard_expansion p :
  paper_standard p ->
  p = \sum_a (p @_ paper_artin_exponent a) *:
    'X_[Coeff, paper_artin_exponent a].
Proof.
move/paper_standardP=> hp.
apply: mpoly_expansion_over_monomials paper_artin_exponent_injective.
move=> u hu.
pose a := artin_index_of_standard u (hp u hu).
exists (reverse_index_of_artin a).
rewrite reverse_index_of_artinE /a.
exact: artin_exponent_of_standardE.
Qed.

Theorem formal_specialization_standard_expansion p :
  paper_standard p ->
  formal_specialization p =
    \sum_a (p @_ paper_artin_exponent a) *: paper_artin_basis a.
Proof.
move=> hp.
rewrite (paper_standard_expansion hp)
  /formal_specialization raddf_sum.
apply: eq_bigr=> a _.
rewrite mmapZ mmapX mmap1_id paper_artin_basisE
  SM.symmetric_scalarE.
exact: erefl.
Qed.

(** Specialization is injective on the paper-standard subspace.  This is the
    formal quotient uniqueness bridge: the coefficients remain independent
    because the reversed Artin basis was proved free over the symmetric
    coefficient ring. *)
Theorem formal_specialization_standard_injective p :
  paper_standard p -> formal_specialization p = 0 -> p = 0.
Proof.
move=> hp hzero.
have hsum := formal_specialization_standard_expansion hp.
rewrite hzero in hsum.
have hcoeff : forall a, p @_ paper_artin_exponent a = 0.
  apply: paper_artin_basis_independent.
  exact/esym: hsum.
rewrite (paper_standard_expansion hp).
apply: big1=> a _.
by rewrite hcoeff scale0r.
Qed.

Corollary formal_specialization_standard_eq p q :
  paper_standard p -> paper_standard q ->
  formal_specialization p = formal_specialization q -> p = q.
Proof.
move=> hp hq heq.
move/paper_standardP: hp=> hp.
move/paper_standardP: hq=> hq.
apply/eqP; rewrite -subr_eq0.
apply/eqP.
apply: formal_specialization_standard_injective.
- apply/paper_standardP=> u.
  move/msuppB_le; rewrite mem_cat=> /orP[hu | hu] i.
  + exact: hp u hu i.
  + exact: hq u hu i.
- by rewrite formal_specializationB heq subrr.
Qed.

(** Uniqueness of paper-standard remainders in the actual formal
    coefficient/root quotient. *)
Theorem paper_standard_remainders_unique p r s :
  paper_standard r -> paper_standard s ->
  generated_by displayed_J (p - r) ->
  generated_by displayed_J (p - s) -> r = s.
Proof.
move=> hr hs hpr hps.
have hpr0 := formal_specialization_generated_by_displayed_J hpr.
have hps0 := formal_specialization_generated_by_displayed_J hps.
rewrite formal_specializationB in hpr0 hps0.
have epr : formal_specialization p = formal_specialization r.
  apply/eqP; rewrite -subr_eq0; exact/eqP: hpr0.
have eps : formal_specialization p = formal_specialization s.
  apply/eqP; rewrite -subr_eq0; exact/eqP: hps0.
apply: formal_specialization_standard_eq hr hs.
exact: epr.symm.trans eps.
Qed.

Definition paper_artin_coordinate (q : RootRing) (a : ReverseArtin) : Coeff :=
  FF.ffd_coeff
    (@AS.lazard_reverse_artin_finite_free_decomposition rat 5)
    (msym (paper_reverse_perm^-1)%g q) a.

Lemma paper_artin_reverse c a :
  msym paper_reverse_perm
    (c *:
      FF.ffd_basis
        (@AS.lazard_reverse_artin_finite_free_decomposition rat 5) a) =
  c *: paper_artin_basis a.
Proof.
rewrite !SM.symmetric_scalarE /paper_artin_basis msymM msym_sym_eval.
exact: erefl.
Qed.

Theorem paper_artin_coordinates_reconstruct q :
  q = \sum_a (paper_artin_coordinate q a) *: paper_artin_basis a.
Proof.
have h := FF.ffd_reconstruct
  (@AS.lazard_reverse_artin_finite_free_decomposition rat 5)
  (msym (paper_reverse_perm^-1)%g q).
have h' := congr1 (msym paper_reverse_perm) h.
rewrite -msymMm mulVg msym1m raddf_sum in h'.
under [X in \sum_a X] eq_bigr => a _ do rewrite paper_artin_reverse.
exact: h'.
Qed.

Definition formal_artin_remainder (q : RootRing) : Ambient :=
  \sum_a (paper_artin_coordinate q a) *:
    'X_[Coeff, paper_artin_exponent a].

Lemma formal_artin_remainder_standard q :
  paper_standard (formal_artin_remainder q).
Proof.
apply/paper_standardP=> u.
move/msupp_sum_le/flattenP=> [s].
move/mapP=> [a _ ->] hu i.
move/msuppZ_le: hu=> /mem_msuppXP ->.
exact: paper_artin_exponent_standard.
Qed.

Lemma formal_specialization_formal_artin_remainder q :
  formal_specialization (formal_artin_remainder q) = q.
Proof.
rewrite /formal_artin_remainder /formal_specialization raddf_sum.
rewrite (paper_artin_coordinates_reconstruct q).
apply: eq_bigr=> a _.
rewrite mmapZ mmapX mmap1_id paper_artin_basisE
  SM.symmetric_scalarE.
exact: erefl.
Qed.

(** Existence of a paper-standard representative for every class in the
    formal quotient. *)
Theorem exists_paper_standard_remainder p :
  exists r, paper_standard r /\ generated_by displayed_J (p - r).
Proof.
exists (formal_artin_remainder (formal_specialization p)).
split; first exact: formal_artin_remainder_standard.
apply/(formal_specialization_kernel_generated (p :=
  p - formal_artin_remainder (formal_specialization p))).
by rewrite formal_specializationB
  formal_specialization_formal_artin_remainder subrr.
Qed.

Theorem exists_unique_paper_standard_remainder p :
  exists r,
    paper_standard r /\
    generated_by displayed_J (p - r) /\
    forall s, paper_standard s ->
      generated_by displayed_J (p - s) -> s = r.
Proof.
have [r [hr hpr]] := exists_paper_standard_remainder p.
exists r; split=> //; split=> // s hs hps.
exact: paper_standard_remainders_unique hs hr hps hpr.
Qed.

Definition displayed_leading_check (i : 'I_5) : bool :=
  (displayed_J i @_ paper_leading_monomial i == 1) &&
  all (fun u => (u == paper_leading_monomial i) ||
      paper_lt u (paper_leading_monomial i))
    (msupp (displayed_J i)).

Lemma displayed_leading_checkP i : displayed_leading_check i.
Proof.
case: i=> [[|[|[|[|[|i]]]]] hi] //=; vm_compute.
Qed.

Theorem displayed_J_leading_data i :
  displayed_J i @_ paper_leading_monomial i = 1 /\
  forall u, u \in msupp (displayed_J i) ->
    u != paper_leading_monomial i ->
    paper_lt u (paper_leading_monomial i).
Proof.
have /andP[/eqP hcoeff /allP hsupp] := displayed_leading_checkP i.
split; first exact: hcoeff.
move=> u hu hne.
have /orP [heq | hlt] := hsupp u hu; last exact: hlt.
by move: hne; rewrite (eqP heq) eqxx.
Qed.

Definition displayed_tail (i : 'I_5) : Ambient :=
  displayed_J i - 'X_[Coeff, paper_leading_monomial i].

Definition displayed_reduced_check (i : 'I_5) : bool :=
  all (fun u =>
    [forall j : 'I_5, ~~ (paper_leading_monomial j <= u)%MM])
    (msupp (displayed_tail i)).

Lemma displayed_reduced_checkP i : displayed_reduced_check i.
Proof.
case: i=> [[|[|[|[|[|i]]]]] hi] //=; vm_compute.
Qed.

Theorem displayed_J_reduced_tails i u :
  u \in msupp (displayed_tail i) -> forall j : 'I_5,
  ~~ (paper_leading_monomial j <= u)%MM.
Proof.
move=> hu j.
have /allP h := displayed_reduced_checkP i.
have /forallP := h u hu.
exact.
Qed.

(** This record isolates the finite, literal part of Lazard's degree-five
    displayed-basis calculation: exact generators, leading monomials, and
    reduced tails.  The stronger record below additionally contains the
    separately proved arbitrary formal-[e] quotient theorem. *)
Record quintic_displayed_basis_data : Prop := {
  quintic_generated_ideal : forall p,
    generated_by displayed_J p <-> generated_by vieta_relation p;
  quintic_leading_data : forall i,
    displayed_J i @_ paper_leading_monomial i = 1 /\
    forall u, u \in msupp (displayed_J i) ->
      u != paper_leading_monomial i ->
      paper_lt u (paper_leading_monomial i);
  quintic_reduced_tails : forall i u,
    u \in msupp (displayed_tail i) -> forall j : 'I_5,
      ~~ (paper_leading_monomial j <= u)%MM
}.

Theorem quintic_displayed_basis_data_proved :
  quintic_displayed_basis_data.
Proof.
constructor.
- exact: displayed_generated_ideal_eq_vieta.
- exact: displayed_J_leading_data.
- exact: displayed_J_reduced_tails.
Qed.

(** Full fixed-degree formal quotient certificate.  In addition to the
    literal reduced leading data, it records the exact specialization kernel
    and existence/uniqueness of the paper-standard remainder for every
    formal polynomial. *)
Record quintic_displayed_formal_reduced_groebner_certificate : Prop := {
  quintic_formal_generated_ideal : forall p,
    generated_by displayed_J p <-> generated_by vieta_relation p;
  quintic_formal_specialization_kernel : forall p,
    formal_specialization p = 0 <-> generated_by displayed_J p;
  quintic_formal_leading_data : forall i,
    displayed_J i @_ paper_leading_monomial i = 1 /\
    forall u, u \in msupp (displayed_J i) ->
      u != paper_leading_monomial i ->
      paper_lt u (paper_leading_monomial i);
  quintic_formal_reduced_tails : forall i u,
    u \in msupp (displayed_tail i) -> forall j : 'I_5,
      ~~ (paper_leading_monomial j <= u)%MM;
  quintic_formal_normal_form : forall p,
    exists r,
      paper_standard r /\
      generated_by displayed_J (p - r) /\
      forall s, paper_standard s ->
        generated_by displayed_J (p - s) -> s = r
}.

Theorem quintic_displayed_formal_reduced_groebner_certificate_proved :
  quintic_displayed_formal_reduced_groebner_certificate.
Proof.
constructor.
- exact: displayed_generated_ideal_eq_vieta.
- exact: formal_specialization_kernel_generated.
- exact: displayed_J_leading_data.
- exact: displayed_J_reduced_tails.
- exact: exists_unique_paper_standard_remainder.
Qed.

End PolynomialFormulasLazardDisplayedGroebnerQuintic.
