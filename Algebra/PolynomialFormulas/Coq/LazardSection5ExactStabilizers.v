From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  Fin5TransitiveClassification LazardGeneralResolventExplicit.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * The degree-two and degree-three stabilizer witnesses in Section 5

    The two displayed polynomials below have rational coefficients, as in
    Lazard's rational-function-field setting.  Their exact stabilizers and
    degrees are closed finite computations checked by the kernel.  The last
    part proves the corresponding lower bounds coefficientwise: degree at
    most two cannot distinguish a five-cycle from its reflection, while
    degree at most one cannot distinguish any permutation from a rotation.

    This source mirrors [LazardSection5ExactStabilizers.lean]. *)
Module PolynomialFormulasLazardSection5ExactStabilizers.

Import GRing.Theory.
Module F20 := PolynomialFormulasQuinticF20Data.
Module Class := PolynomialFormulasFin5TransitiveClassification.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module Exact := PolynomialFormulasLazardGeneralResolventExplicit.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Local Notation S5 := F20.S5.
Local Notation MP := {mpoly rat[5]}.

(** ** Rational witnesses with exact stabilizer *)

(** The undirected edge sum [sum_i X_i X_(i+1)]. *)
Definition quadratic_edge_sum : MP :=
  \sum_(i < 5) ('X_i * 'X_(F20.five_cycle i)).

(** The oriented cubic sum [sum_i X_i^2 X_(i+1)]. *)
Definition oriented_cubic_sum : MP :=
  \sum_(i < 5) (('X_i ^+ 2) * 'X_(F20.five_cycle i)).

Definition quadratic_edge_stabilizer_check : bool :=
  [forall s : S5,
    (IM.mpoly_left_action s quadratic_edge_sum == quadratic_edge_sum) ==
      (s \in Class.standard_D5)].

Lemma quadratic_edge_stabilizer_checkP :
  quadratic_edge_stabilizer_check.
Proof. vm_compute. Qed.

Definition oriented_cubic_stabilizer_check : bool :=
  [forall s : S5,
    (IM.mpoly_left_action s oriented_cubic_sum == oriented_cubic_sum) ==
      (s \in F20.standard_C5)].

Lemma oriented_cubic_stabilizer_checkP :
  oriented_cubic_stabilizer_check.
Proof. vm_compute. Qed.

Theorem quadratic_edge_sum_exact_stabilizer :
  @Exact.lazard_invariant_stabilizer_exact
    rat 5 Class.standard_D5 quadratic_edge_sum.
Proof.
move=> s.
have /eqP hs := forallP quadratic_edge_stabilizer_checkP s.
split.
- move=> hp; rewrite -hs; exact/eqP: hp.
- move=> hsD; apply/eqP; rewrite hs; exact: hsD.
Qed.

Theorem oriented_cubic_sum_exact_stabilizer :
  @Exact.lazard_invariant_stabilizer_exact
    rat 5 F20.standard_C5 oriented_cubic_sum.
Proof.
move=> s.
have /eqP hs := forallP oriented_cubic_stabilizer_checkP s.
split.
- move=> hp; rewrite -hs; exact/eqP: hp.
- move=> hsC; apply/eqP; rewrite hs; exact: hsC.
Qed.

Lemma quadratic_edge_sum_homogeneous :
  quadratic_edge_sum \is 2.-homog.
Proof. vm_compute. Qed.

Lemma oriented_cubic_sum_homogeneous :
  oriented_cubic_sum \is 3.-homog.
Proof. vm_compute. Qed.

(** ** Closed orbit calculations for the lower bounds *)

Definition small_exponent := 5.-tuple 'I_3.

Definition small_exponent_total (a : small_exponent) : nat :=
  \sum_(i < 5) (tnth a i : nat).

Definition act_small_exponent (s : S5) (a : small_exponent) :
    small_exponent :=
  [tuple tnth a (s^-1 i) | i < 5].

Definition reflection_degree_le_two_orbit_check : bool :=
  [forall a : small_exponent,
    (small_exponent_total a <= 2) ==>
      [exists k : 'I_5,
        act_small_exponent Class.reflection a ==
          act_small_exponent (F20.five_cycle ^+ k) a]].

Lemma reflection_degree_le_two_orbit_checkP :
  reflection_degree_le_two_orbit_check.
Proof. vm_compute. Qed.

Lemma reflection_degree_le_two_orbit a :
  small_exponent_total a <= 2 ->
  exists k : 'I_5,
    act_small_exponent Class.reflection a =
      act_small_exponent (F20.five_cycle ^+ k) a.
Proof.
move=> ha.
have h := implyP (forallP reflection_degree_le_two_orbit_checkP a) ha.
move/existsP: h=> [k /eqP hk].
by exists k.
Qed.

Definition permutation_degree_le_one_orbit_check : bool :=
  [forall s : S5, [forall a : small_exponent,
    (small_exponent_total a <= 1) ==>
      [exists k : 'I_5,
        act_small_exponent s a ==
          act_small_exponent (F20.five_cycle ^+ k) a]]].

Lemma permutation_degree_le_one_orbit_checkP :
  permutation_degree_le_one_orbit_check.
Proof. vm_compute. Qed.

Lemma permutation_degree_le_one_orbit s a :
  small_exponent_total a <= 1 ->
  exists k : 'I_5,
    act_small_exponent s a =
      act_small_exponent (F20.five_cycle ^+ k) a.
Proof.
move=> ha.
have h := implyP
  (forallP (forallP permutation_degree_le_one_orbit_checkP s) a) ha.
move/existsP: h=> [k /eqP hk].
by exists k.
Qed.

(** ** From bounded exponent tuples to arbitrary monomials *)

Definition small_exponent_of_monomial (m : 'X_{1..5}) : small_exponent :=
  [tuple inord (m i) | i < 5].

Lemma monomial_coordinate_le_degree (m : 'X_{1..5}) i :
  m i <= mdeg m.
Proof.
rewrite mdegE (bigD1 i) //=.
exact: leq_addr.
Qed.

Lemma small_exponent_of_monomialE m :
  mdeg m <= 2 -> forall i,
    (tnth (small_exponent_of_monomial m) i : nat) = m i.
Proof.
move=> hm i; rewrite /small_exponent_of_monomial tnth_mktuple.
apply: inordK.
rewrite -ltnS.
exact: leq_trans (monomial_coordinate_le_degree m i) hm.
Qed.

Lemma small_exponent_of_monomial_total m :
  mdeg m <= 2 ->
  small_exponent_total (small_exponent_of_monomial m) = mdeg m.
Proof.
move=> hm; rewrite /small_exponent_total.
under eq_bigr=> i _ do rewrite (small_exponent_of_monomialE hm i).
by rewrite -mdegE.
Qed.

Definition permuted_monomial (s : S5) (m : 'X_{1..5}) : 'X_{1..5} :=
  [multinom m (s^-1 i) | i < 5].

Lemma mdeg_permuted_monomial s m :
  mdeg (permuted_monomial s m) = mdeg m.
Proof.
rewrite !mdegE /permuted_monomial.
under [LHS] eq_bigr=> i _ do rewrite mnmE.
by rewrite (reindex_perm s^-1).
Qed.

Lemma permuted_monomial_eq_of_small_action_eq m s t :
  mdeg m <= 2 ->
  act_small_exponent s (small_exponent_of_monomial m) =
    act_small_exponent t (small_exponent_of_monomial m) ->
  permuted_monomial s m = permuted_monomial t m.
Proof.
move=> hm hst; apply/mnmP=> i.
rewrite /permuted_monomial !mnmE.
have hi := congr1 (fun a : small_exponent => tnth a i) hst.
move: hi; rewrite /act_small_exponent !tnth_mktuple.
by rewrite (small_exponent_of_monomialE hm (s^-1 i))
  (small_exponent_of_monomialE hm (t^-1 i)).
Qed.

Lemma reflection_monomial_orbit m :
  mdeg m <= 2 ->
  exists k : nat,
    permuted_monomial Class.reflection m =
      permuted_monomial (F20.five_cycle ^+ k) m.
Proof.
move=> hm.
have htotal :
    small_exponent_total (small_exponent_of_monomial m) <= 2.
  by rewrite (small_exponent_of_monomial_total hm).
case: (reflection_degree_le_two_orbit htotal)=> k hk.
exists k.
exact: permuted_monomial_eq_of_small_action_eq hm hk.
Qed.

Lemma permutation_monomial_orbit_degree_le_one s m :
  mdeg m <= 1 ->
  exists k : nat,
    permuted_monomial s m =
      permuted_monomial (F20.five_cycle ^+ k) m.
Proof.
move=> hm.
have hm2 : mdeg m <= 2 := leq_trans hm (leqnSn 1).
have htotal :
    small_exponent_total (small_exponent_of_monomial m) <= 1.
  by rewrite (small_exponent_of_monomial_total hm2).
case: (permutation_degree_le_one_orbit s htotal)=> k hk.
exists k.
exact: permuted_monomial_eq_of_small_action_eq hm2 hk.
Qed.

(** ** Coefficientwise polynomial lower bounds *)

Section Coefficients.

Variable R : fieldType.
Local Notation MPR := {mpoly R[5]}.

Lemma five_cycle_power_fixed (p : MPR) k :
  IM.mpoly_left_action F20.five_cycle p = p ->
  IM.mpoly_left_action (F20.five_cycle ^+ k) p = p.
Proof.
move=> hp; elim: k=> [|k ih].
- by rewrite expg0 IM.mpoly_left_action1.
- by rewrite expgS IM.mpoly_left_actionM hp ih.
Qed.

Lemma left_action_fixed_of_monomial_orbits (p : MPR) d s :
  p \is d.-homog ->
  IM.mpoly_left_action F20.five_cycle p = p ->
  (forall m : 'X_{1..5}, mdeg m = d ->
    exists k : nat,
      permuted_monomial s m =
        permuted_monomial (F20.five_cycle ^+ k) m) ->
  IM.mpoly_left_action s p = p.
Proof.
move=> hp hcycle horbits; apply/mpolyP=> m.
case hmd: (mdeg m == d).
- have hm : mdeg m = d by exact/eqP.
  case: (horbits m hm)=> k hk.
  have hpow := five_cycle_power_fixed hcycle k.
  have hcoeff := congr1 (fun q : MPR => q@_m) hpow.
  rewrite /IM.mpoly_left_action mcoeff_sym.
  change p@_(permuted_monomial s m) = p@_m.
  rewrite hk.
  move: hcoeff; rewrite /IM.mpoly_left_action mcoeff_sym.
  by change p@_(permuted_monomial (F20.five_cycle ^+ k) m) = p@_m.
- have hm0 : p@_m = 0.
    apply: dhomog_nemf_coeff hp.
    by rewrite hmd.
  have hsm0 : p@_(permuted_monomial s m) = 0.
    apply: dhomog_nemf_coeff hp.
    by rewrite mdeg_permuted_monomial hmd.
  rewrite /IM.mpoly_left_action mcoeff_sym.
  change p@_(permuted_monomial s m) = p@_m.
  by rewrite hsm0 hm0.
Qed.

(** Any homogeneous C5-invariant of degree at most two is fixed by the
    reflection, and hence cannot have exact C5 stabilizer in those degrees. *)
Theorem reflection_invariant_of_C5_invariant_degree_le_two
    (p : MPR) d :
  p \is d.-homog -> d <= 2 ->
  IM.mpoly_left_action F20.five_cycle p = p ->
  IM.mpoly_left_action Class.reflection p = p.
Proof.
move=> hp hd hcycle.
apply: left_action_fixed_of_monomial_orbits hp hcycle=> m hm.
apply: reflection_monomial_orbit.
by rewrite hm.
Qed.

Lemma reflection_notin_standard_C5 :
  Class.reflection \notin F20.standard_C5.
Proof. vm_compute. Qed.

(** Thus the oriented cubic realizes the first possible exact C5
    stabilizer degree: no homogeneous degree-at-most-two C5-invariant has
    exact stabilizer C5. *)
Theorem no_exact_C5_stabilizer_in_degree_le_two
    (p : MPR) d :
  p \is d.-homog -> d <= 2 ->
  (forall s : S5, s \in F20.standard_C5 ->
    IM.mpoly_left_action s p = p) ->
  ~ @Exact.lazard_invariant_stabilizer_exact
      R 5 F20.standard_C5 p.
Proof.
move=> hp hd hC hexact.
have hcycle := hC F20.five_cycle (cycle_id F20.five_cycle).
have hreflection :=
  reflection_invariant_of_C5_invariant_degree_le_two hp hd hcycle.
have hreflectionC5 := proj1 (hexact Class.reflection) hreflection.
by move: reflection_notin_standard_C5; rewrite hreflectionC5.
Qed.

Definition standard_D5_decomposition_check : bool :=
  [forall s : S5, (s \in Class.standard_D5) ==>
    [exists k : 'I_5,
      (s == F20.five_cycle ^+ k) ||
      (s == F20.five_cycle ^+ k * Class.reflection)]].

Lemma standard_D5_decomposition_checkP : standard_D5_decomposition_check.
Proof. vm_compute. Qed.

Lemma standard_D5_decomposition s :
  s \in Class.standard_D5 ->
  exists k : 'I_5,
    s = F20.five_cycle ^+ k \/
    s = F20.five_cycle ^+ k * Class.reflection.
Proof.
move=> hs.
have h := implyP (forallP standard_D5_decomposition_checkP s) hs.
move/existsP: h=> [k /orP [/eqP hk | /eqP hk]].
- by exists k; left.
- by exists k; right.
Qed.

(** Paper-facing form of the quadratic lower bound: invariance under C5 in
    degree at most two implies invariance under all of D5. *)
Theorem D5_invariant_of_C5_invariant_degree_le_two
    (p : MPR) d :
  p \is d.-homog -> d <= 2 ->
  IM.mpoly_left_action F20.five_cycle p = p ->
  forall s : S5, s \in Class.standard_D5 ->
    IM.mpoly_left_action s p = p.
Proof.
move=> hp hd hcycle.
have hreflection :=
  reflection_invariant_of_C5_invariant_degree_le_two hp hd hcycle.
move=> s hs; case: (standard_D5_decomposition hs)=> k [-> | ->].
- exact: five_cycle_power_fixed hcycle k.
- by rewrite IM.mpoly_left_actionM hreflection
    (five_cycle_power_fixed hcycle k).
Qed.

(** In degree at most one, C5-invariance already implies full S5
    invariance. *)
Theorem S5_invariant_of_C5_invariant_degree_le_one
    (p : MPR) d :
  p \is d.-homog -> d <= 1 ->
  IM.mpoly_left_action F20.five_cycle p = p ->
  forall s : S5, IM.mpoly_left_action s p = p.
Proof.
move=> hp hd hcycle s.
apply: left_action_fixed_of_monomial_orbits hp hcycle=> m hm.
apply: permutation_monomial_orbit_degree_le_one.
by rewrite hm.
Qed.

Lemma swap01_notin_standard_D5 :
  F20.swap01 \notin Class.standard_D5.
Proof. vm_compute. Qed.

(** No homogeneous D5-invariant of degree at most one can have D5 as its
    exact stabilizer. *)
Theorem no_exact_D5_stabilizer_in_degree_le_one
    (p : MPR) d :
  p \is d.-homog -> d <= 1 ->
  (forall s : S5, s \in Class.standard_D5 ->
    IM.mpoly_left_action s p = p) ->
  ~ @Exact.lazard_invariant_stabilizer_exact
      R 5 Class.standard_D5 p.
Proof.
move=> hp hd hD hexact.
have hcycle_mem : F20.five_cycle \in Class.standard_D5.
  apply: (subsetP Class.standard_C5_sub_standard_D5).
  exact: cycle_id.
have hcycle := hD F20.five_cycle hcycle_mem.
have hall := S5_invariant_of_C5_invariant_degree_le_one hp hd hcycle.
have hswap := proj1 (hexact F20.swap01) (hall F20.swap01).
by move: swap01_notin_standard_D5; rewrite hswap.
Qed.

(** ** Arbitrary-polynomial minimum-degree statements *)

(** Reassemble a bounded polynomial from its homogeneous pieces after
    proving that a permutation fixes every piece.  This removes the
    accidental homogeneity restriction from the literal minimum-degree
    claims. *)
Lemma left_action_fixed_of_homogeneous_partition
    (p : MPR) k s :
  msize p <= k ->
  (forall i : 'I_k,
    IM.mpoly_left_action s (pihomog mdeg i p) = pihomog mdeg i p) ->
  IM.mpoly_left_action s p = p.
Proof.
move=> size_p fixed_piece.
have pE := pihomog_partitionE
  (mf := mdeg) (k := k) (p := p) size_p.
rewrite [p in IM.mpoly_left_action s p]pE
  /IM.mpoly_left_action raddf_sum.
rewrite [RHS]pE.
apply: eq_bigr => i _.
exact: fixed_piece i.
Qed.

(** Every (not necessarily homogeneous) C5-invariant polynomial of total
    degree at most two is reflection invariant.  The MathComp bound
    [msize p <= 3] says exactly that every support monomial has degree
    strictly below three. *)
Theorem reflection_invariant_of_C5_invariant_total_degree_le_two
    (p : MPR) :
  msize p <= 3 ->
  IM.mpoly_left_action F20.five_cycle p = p ->
  IM.mpoly_left_action Class.reflection p = p.
Proof.
move=> size_p hcycle.
apply: left_action_fixed_of_homogeneous_partition size_p=> i.
apply: reflection_invariant_of_C5_invariant_degree_le_two pihomogP.
- by rewrite -ltnS; exact: ltn_ord i.
- by rewrite /IM.mpoly_left_action msym_pihomog hcycle.
Qed.

(** Paper-facing arbitrary-polynomial form: total degree at most two and
    C5-invariance force invariance under all of D5. *)
Theorem D5_invariant_of_C5_invariant_total_degree_le_two
    (p : MPR) :
  msize p <= 3 ->
  (forall s : S5, s \in F20.standard_C5 ->
    IM.mpoly_left_action s p = p) ->
  forall s : S5, s \in Class.standard_D5 ->
    IM.mpoly_left_action s p = p.
Proof.
move=> size_p hC.
have hcycle := hC F20.five_cycle (cycle_id F20.five_cycle).
have hreflection :=
  reflection_invariant_of_C5_invariant_total_degree_le_two
    size_p hcycle.
move=> s hs; case: (standard_D5_decomposition hs)=> k [-> | ->].
- exact: five_cycle_power_fixed hcycle k.
- by rewrite IM.mpoly_left_actionM hreflection
    (five_cycle_power_fixed hcycle k).
Qed.

(** No arbitrary polynomial of total degree at most two has exact
    stabilizer C5.  Together with [oriented_cubic_sum] this proves the
    literal minimum degree is three. *)
Theorem no_exact_C5_stabilizer_total_degree_le_two
    (p : MPR) :
  msize p <= 3 ->
  (forall s : S5, s \in F20.standard_C5 ->
    IM.mpoly_left_action s p = p) ->
  ~ @Exact.lazard_invariant_stabilizer_exact
      R 5 F20.standard_C5 p.
Proof.
move=> size_p hC hexact.
have hD := D5_invariant_of_C5_invariant_total_degree_le_two size_p hC.
have hreflection_mem : Class.reflection \in Class.standard_D5.
  rewrite /Class.standard_D5.
  apply: (subsetP (joing_subr _ _)).
  exact: cycle_id.
have hreflection := hD Class.reflection hreflection_mem.
have hreflectionC5 := proj1 (hexact Class.reflection) hreflection.
by move: reflection_notin_standard_C5; rewrite hreflectionC5.
Qed.

(** A cyclic-invariant polynomial of total degree at most one is fully
    symmetric, without a homogeneity assumption. *)
Theorem S5_invariant_of_C5_invariant_total_degree_le_one
    (p : MPR) :
  msize p <= 2 ->
  IM.mpoly_left_action F20.five_cycle p = p ->
  forall s : S5, IM.mpoly_left_action s p = p.
Proof.
move=> size_p hcycle s.
apply: left_action_fixed_of_homogeneous_partition size_p=> i.
apply: S5_invariant_of_C5_invariant_degree_le_one pihomogP.
- by rewrite -ltnS; exact: ltn_ord i.
- by rewrite /IM.mpoly_left_action msym_pihomog hcycle.
Qed.

(** No arbitrary polynomial of total degree at most one has exact
    stabilizer D5.  Together with [quadratic_edge_sum] this proves the
    literal minimum degree is two. *)
Theorem no_exact_D5_stabilizer_total_degree_le_one
    (p : MPR) :
  msize p <= 2 ->
  (forall s : S5, s \in Class.standard_D5 ->
    IM.mpoly_left_action s p = p) ->
  ~ @Exact.lazard_invariant_stabilizer_exact
      R 5 Class.standard_D5 p.
Proof.
move=> size_p hD hexact.
have hcycle_mem : F20.five_cycle \in Class.standard_D5.
  apply: (subsetP Class.standard_C5_sub_standard_D5).
  exact: cycle_id.
have hcycle := hD F20.five_cycle hcycle_mem.
have hall := S5_invariant_of_C5_invariant_total_degree_le_one
  size_p hcycle.
have hswap := proj1 (hexact F20.swap01) (hall F20.swap01).
by move: swap01_notin_standard_D5; rewrite hswap.
Qed.

End Coefficients.

End PolynomialFormulasLazardSection5ExactStabilizers.
