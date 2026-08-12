From HB Require Import structures.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From mathcomp.multinomials Require Import mpoly.
From PolynomialFormulas Require Import
  LazardInvariantFiniteFree LazardInvariantMultinomials
  LazardInvariantHomogeneousCoordinates LazardInvariantSymmetricModule
  LazardInvariantSubgroupModule
  LazardInvariantSubgroupReynolds.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The unconditional completion of Lazard's invariant-module theorem.

    The preceding Reynolds file constructs, in every Artin degree, the
    ground-field image of the constant diagonal block of the Reynolds
    idempotent and lifts its canonical [vbasis] to homogeneous invariant
    polynomials.  This file proves that those lifts form a basis over the
    full symmetric-polynomial coefficient ring.

    Spanning is proved by descending through the finite Artin-degree bound:
    at each step the lifted image basis cancels the highest remaining Artin
    coordinates.  Independence is the same descent applied to a vanishing
    linear combination.  The only field-linear input is [vbasisP]; its
    independence after scalar extension is proved explicitly with the dual
    coordinate functionals and [row_sum_delta]. *)
Module PolynomialFormulasLazardInvariantSubgroupTheoremTwo.

Import GRing.Theory.
Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope mpoly_scope.

Module FF := PolynomialFormulasLazardInvariantFiniteFree.
Module IM := PolynomialFormulasLazardInvariantMultinomials.
Module HC := PolynomialFormulasLazardInvariantHomogeneousCoordinates.
Module SM := PolynomialFormulasLazardInvariantSymmetricModule.
Module SIM := PolynomialFormulasLazardInvariantSubgroupModule.
Module SR := PolynomialFormulasLazardInvariantSubgroupReynolds.

Section Construction.

Variables (F : fieldType) (n : nat) (H : {group 'S_n}).
Hypothesis cardH_neq0 : (#|[subg H]|%:R : F) != 0.

Local Notation S := {mpoly F[n]}.
Local Notation InvModule :=
  (SIM.PolynomialFormulasLazardInvariantSubgroupModule_lazard_subgroup_invariant_module__canonical__GRing_Lmodule
    F H).
Local Notation Inv := InvModule.
Local Notation SymModule :=
  (SM.PolynomialFormulasLazardInvariantSymmetricModule_symmetric_polynomial_module__canonical__GRing_Lmodule
    F n).
Local Notation Artin :=
  (SIM.lazard_ambient_artin_homogeneous_decomposition F n).
Local Notation B := (FF.hffd_free Artin).
Local Notation degree := (FF.hffd_degree Artin).
Local Notation N := (#|FF.ffd_index B|).
Local Notation bound := (IM.lazard_degree_bound n).
Local Notation block_image :=
  (SR.lazard_subgroup_reynolds_degree_block_image
    F (n := n) H).
Local Notation block_basis :=
  (SR.lazard_subgroup_reynolds_degree_block_basis
    F (n := n) H).
Local Notation block_linear :=
  (SR.lazard_subgroup_reynolds_degree_block_linear
    F (n := n) H).
Local Notation block_lift :=
  (SR.lazard_subgroup_reynolds_degree_block_lift
    (F := F) (H := H)).

(** A dependent sum is the exact finite generator index: first choose an
    Artin degree within the universal bound, then a vector of the image
    basis of that degree block. *)
Definition lazard_theorem_two_index : finType :=
  ({d : 'I_bound.+1 &
    'I_(\dim (block_image (d : nat)))})%type.

Definition lazard_theorem_two_degree
    (g : lazard_theorem_two_index) : nat := tag g.

Definition lazard_theorem_two_generator
    (g : lazard_theorem_two_index) : Inv :=
  block_lift (tagged g).

Lemma lazard_theorem_two_generator_homogeneous
    (g : lazard_theorem_two_index) :
  SIM.lazard_invariant_homogeneous
    (lazard_theorem_two_generator g)
    (lazard_theorem_two_degree g).
Proof.
case: g=> d i /=.
exact: SR.lazard_subgroup_reynolds_degree_block_lift_homogeneous.
Qed.

Lemma lazard_theorem_two_generator_degree_le
    (g : lazard_theorem_two_index) :
  (lazard_theorem_two_degree g <= bound)%N.
Proof. by rewrite -ltnS; exact: valP (tag g). Qed.

(** Forgetting the invariant wrapper, bundled as a linear map. *)
Definition lazard_invariant_val_linear :
    {linear InvModule -> SymModule | *:%R} :=
  HB.pack (@SIM.lazard_subgroup_invariant_val F n H)
    (GRing.isLinear.Build S InvModule SymModule
      *:%R (@SIM.lazard_subgroup_invariant_val F n H)
      (SIM.lazard_subgroup_invariant_val_is_linear (F := F) (H := H))).

Lemma lazard_invariant_val_linearE p :
  lazard_invariant_val_linear p =
    SIM.lazard_subgroup_invariant_val p.
Proof. reflexivity. Qed.

(** Artin coordinates of an invariant polynomial, with the finite Artin
    index enumerated as an ordinal when matrix coordinates are needed. *)
Definition lazard_invariant_artin_coeff
    (p : Inv) (i : FF.ffd_index B) : S :=
  FF.ffd_coeff B (SIM.lazard_subgroup_invariant_val p) i.

Lemma lazard_invariant_artin_coeff0 i :
  lazard_invariant_artin_coeff (0 : Inv) i = 0.
Proof.
rewrite /lazard_invariant_artin_coeff.
change (FF.ffd_coeff B (lazard_invariant_val_linear 0) i = 0).
by rewrite linear0 FF.ffd_coeff0.
Qed.

Lemma lazard_invariant_artin_coeffD p q i :
  lazard_invariant_artin_coeff (p + q) i =
    lazard_invariant_artin_coeff p i +
    lazard_invariant_artin_coeff q i.
Proof.
rewrite /lazard_invariant_artin_coeff.
change (FF.ffd_coeff B (lazard_invariant_val_linear (p + q)) i =
  FF.ffd_coeff B (SIM.lazard_subgroup_invariant_val p) i +
  FF.ffd_coeff B (SIM.lazard_subgroup_invariant_val q) i).
by rewrite linearD FF.ffd_coeffD !lazard_invariant_val_linearE.
Qed.

Lemma lazard_invariant_artin_coeffN p i :
  lazard_invariant_artin_coeff (- p) i =
    - lazard_invariant_artin_coeff p i.
Proof.
rewrite /lazard_invariant_artin_coeff.
change (FF.ffd_coeff B (lazard_invariant_val_linear (- p)) i =
  - FF.ffd_coeff B (SIM.lazard_subgroup_invariant_val p) i).
by rewrite linearN FF.ffd_coeffN !lazard_invariant_val_linearE.
Qed.

Lemma lazard_invariant_artin_coeffB p q i :
  lazard_invariant_artin_coeff (p - q) i =
    lazard_invariant_artin_coeff p i -
    lazard_invariant_artin_coeff q i.
Proof.
change (lazard_invariant_artin_coeff (p + - q) i =
  lazard_invariant_artin_coeff p i -
    lazard_invariant_artin_coeff q i).
by rewrite lazard_invariant_artin_coeffD
  lazard_invariant_artin_coeffN.
Qed.

Lemma lazard_invariant_artin_coeffZ a p i :
  lazard_invariant_artin_coeff (a *: p) i =
    (a * lazard_invariant_artin_coeff p i)%R.
Proof.
rewrite /lazard_invariant_artin_coeff.
change (FF.ffd_coeff B
  (lazard_invariant_val_linear
    (GRing.GRing_scale__canonical__Scale_PreLaw InvModule a p)) i =
  (a * FF.ffd_coeff B (SIM.lazard_subgroup_invariant_val p) i)%R).
by rewrite linearZ FF.ffd_coeffZ !lazard_invariant_val_linearE.
Qed.

Lemma lazard_invariant_artin_coeff_sum
    (I : finType) (f : I -> Inv) i :
  lazard_invariant_artin_coeff (\sum_j f j) i =
    \sum_j lazard_invariant_artin_coeff (f j) i.
Proof.
rewrite /lazard_invariant_artin_coeff.
change (FF.ffd_coeff B (lazard_invariant_val_linear (\sum_j f j)) i =
  \sum_j FF.ffd_coeff B (SIM.lazard_subgroup_invariant_val (f j)) i).
rewrite linear_sum FF.ffd_coeff_sum.
by apply: eq_bigr=> j _; rewrite lazard_invariant_val_linearE.
Qed.

(** The fixed-point equation in ambient Artin coordinates. *)
Lemma lazard_invariant_artin_coeff_reynolds p i :
  lazard_invariant_artin_coeff p i =
    \sum_j
      lazard_invariant_artin_coeff p j *
      SR.lazard_subgroup_reynolds_artin_entry
        (F := F) H i j.
Proof.
rewrite /lazard_invariant_artin_coeff.
rewrite -{1}(SR.lazard_subgroup_reynolds_fix_invariant
  (F := F) (H := H)
  cardH_neq0
  (SIM.lazard_subgroup_invariant_valP p)).
change (FF.ffd_coeff B
    (SR.lazard_subgroup_reynolds_linear
      F (n := n) H
      (SIM.lazard_subgroup_invariant_val p)) i =
  \sum_j
    (FF.ffd_coeff B (SIM.lazard_subgroup_invariant_val p) j *
      SR.lazard_subgroup_reynolds_artin_entry
        (F := F) H i j)%R).
rewrite {1}(FF.ffd_reconstruct B
  (SIM.lazard_subgroup_invariant_val p)).
rewrite linear_sum FF.ffd_coeff_sum.
apply: eq_bigr=> j _.
by rewrite linearZ FF.ffd_coeffZ
  SR.lazard_subgroup_reynolds_linearE
  /SR.lazard_subgroup_reynolds_artin_entry.
Qed.

(** A coordinate row of the diagonal-block operator on a standard row. *)
Lemma lazard_block_linear_deltaE d (i j : 'I_N) :
  block_linear d (delta_mx 0 j) 0 i =
    SR.lazard_subgroup_reynolds_degree_block_matrix
      F (n := n) H d i j.
Proof.
rewrite SR.lazard_subgroup_reynolds_degree_block_linearE.
rewrite -rowE !mxE.
by [].
Qed.

(** The highest surviving Artin row of a fixed polynomial is fixed by the
    corresponding constant diagonal block. *)
Lemma lazard_invariant_top_block_equation p d
    (higher_zero : forall j, (d < degree j)%N ->
      lazard_invariant_artin_coeff p j = 0)
    (i : 'I_N) (hi : degree (enum_val i) = d) :
  lazard_invariant_artin_coeff p (enum_val i) =
    \sum_(j < N)
      lazard_invariant_artin_coeff p (enum_val j) *
      (block_linear d (delta_mx 0 j) 0 i)%:MP.
Proof.
rewrite lazard_invariant_artin_coeff_reynolds big_enum_val.
apply: eq_bigr=> j _.
rewrite lazard_block_linear_deltaE
  SR.lazard_subgroup_reynolds_degree_block_matrixE.
have hi' : degree (enum_val i) == d by exact/eqP.
rewrite hi' /=.
case: (ltngtP (degree (enum_val j)) d) => hj.
- have htri : (degree (enum_val j) < degree (enum_val i))%N.
    by rewrite hi.
  rewrite /SR.lazard_subgroup_reynolds_artin_entry
    (SR.lazard_subgroup_reynolds_artin_matrix_triangular
    (F := F) (n := n) H htri).
  by rewrite !mulr0.
- by rewrite (higher_zero (enum_val j) hj) !mul0r.
- have hij : degree (enum_val i) = degree (enum_val j).
    by rewrite hi hj.
  by rewrite (SR.lazard_subgroup_reynolds_artin_matrix_constantE
    (F := F) (n := n) H hij).
Qed.

(** Each projected standard row is expanded in the canonical basis of its
    ground-field image. *)
Lemma lazard_block_basis_expansion d (j : 'I_N) :
  block_linear d (delta_mx 0 j) =
    \sum_(k < \dim (block_image d))
      coord (block_basis d) k (block_linear d (delta_mx 0 j)) *:
      tnth (block_basis d) k.
Proof.
have hv : block_linear d (delta_mx 0 j) \in block_image d.
  apply/memv_imgP.
  by exists (delta_mx 0 j); [exact: memvf | rewrite lfunE].
rewrite /SR.lazard_subgroup_reynolds_degree_block_basis.
have h := coord_vbasis hv.
under [RHS] eq_bigr => k _ do rewrite (tnth_nth 0).
exact: h.
Qed.

Lemma lazard_block_basis_expansion_entry d (j i : 'I_N) :
  block_linear d (delta_mx 0 j) 0 i =
    \sum_(k < \dim (block_image d))
      coord (block_basis d) k (block_linear d (delta_mx 0 j)) *
      tnth (block_basis d) k 0 i.
Proof.
have h := congr1 (fun v : 'rV[F]_N => v 0 i)
  (lazard_block_basis_expansion d j).
move: h.
by rewrite summxE; under [RHS] eq_bigr do rewrite mxE.
Qed.

Lemma lazard_block_basis_expansion_entry_constant d (j i : 'I_N) :
  ((block_linear d (delta_mx 0 j) 0 i)%:MP : S) =
    \sum_(k < \dim (block_image d))
      ((coord (block_basis d) k
        (block_linear d (delta_mx 0 j)))%:MP : S) *
      ((tnth (block_basis d) k 0 i)%:MP : S).
Proof.
transitivity
  ((\sum_(k < \dim (block_image d))
      coord (block_basis d) k (block_linear d (delta_mx 0 j)) *
      tnth (block_basis d) k 0 i)%:MP : S).
- by rewrite (lazard_block_basis_expansion_entry d j i).
- rewrite rmorph_sum.
  apply: eq_bigr=> k _.
  by rewrite rmorphM.
Qed.

(** Explicit coefficient of the lifted degree-block basis over the full
    symmetric coefficient ring. *)
Definition lazard_invariant_top_coordinate p d
    (k : 'I_(\dim (block_image d))) : S :=
  \sum_(j < N)
    lazard_invariant_artin_coeff p (enum_val j) *
    (coord (block_basis d) k
      (block_linear d (delta_mx 0 j)))%:MP.

Lemma lazard_invariant_top_coordinate_reconstruct p d
    (higher_zero : forall j, (d < degree j)%N ->
      lazard_invariant_artin_coeff p j = 0)
    (i : 'I_N) (hi : degree (enum_val i) = d) :
  lazard_invariant_artin_coeff p (enum_val i) =
    \sum_(k < \dim (block_image d))
      lazard_invariant_top_coordinate (d := d) p k *
      (tnth (block_basis d) k 0 i)%:MP.
Proof.
rewrite (lazard_invariant_top_block_equation higher_zero hi)
  /lazard_invariant_top_coordinate.
under [RHS] eq_bigr => k _ do rewrite mulr_suml.
rewrite exchange_big.
apply: eq_bigr=> j _.
under [RHS] eq_bigr => k _ do rewrite -mulrA.
rewrite -mulr_sumr.
by rewrite -lazard_block_basis_expansion_entry_constant.
Qed.

(** Coordinates of a lift vanish above its selected Artin degree. *)
Lemma lazard_block_lift_coeff_above d
    (k : 'I_(\dim (block_image d))) j :
  (d < degree j)%N ->
  lazard_invariant_artin_coeff (block_lift k) j = 0.
Proof.
move=> hdj.
apply: (@HC.lazard_ffd_coeff_eq0_of_degree_lt F n bound Artin
  (SIM.lazard_subgroup_invariant_val (block_lift k)) d).
- exact: SR.lazard_subgroup_reynolds_degree_block_lift_homogeneous.
- exact: hdj.
Qed.

Lemma lazard_block_lift_coeff_top d
    (k : 'I_(\dim (block_image d))) (j : 'I_N)
    (hj : degree (enum_val j) = d) :
  lazard_invariant_artin_coeff (block_lift k) (enum_val j) =
    (tnth (block_basis d) k 0 j)%:MP.
Proof.
exact: SR.lazard_subgroup_reynolds_degree_block_lift_top_coeff hj.
Qed.

Definition lazard_invariant_top_combination p d : Inv :=
  \sum_(k < \dim (block_image d))
    GRing.GRing_scale__canonical__Scale_PreLaw InvModule
      (lazard_invariant_top_coordinate (d := d) p k) (block_lift k).

Lemma lazard_invariant_top_combination_coeff p d j :
  lazard_invariant_artin_coeff
      (lazard_invariant_top_combination p d) j =
    \sum_(k < \dim (block_image d))
      lazard_invariant_top_coordinate (d := d) p k *
      lazard_invariant_artin_coeff (block_lift k) j.
Proof.
rewrite /lazard_invariant_top_combination
  lazard_invariant_artin_coeff_sum.
apply: eq_bigr=> k _.
exact: lazard_invariant_artin_coeffZ.
Qed.

(** The scalar extension of each ground-field block basis remains free.
    The proof applies the ground-field dual coordinate to a row relation,
    after expanding every row in the standard [delta_mx] basis. *)
Definition lazard_block_dual d
    (k : 'I_(\dim (block_image d)))
    (v : 'rV[S]_N) : S :=
  \sum_(j < N) v 0 j *
    (coord (block_basis d) k (delta_mx 0 j))%:MP.

Lemma lazard_block_dual_constant_row d
    (k : 'I_(\dim (block_image d))) (v : 'rV[F]_N) :
  lazard_block_dual (d := d) k
      (map_mx (fun r : F => (r%:MP : S)) v) =
    ((coord (block_basis d) k v)%:MP : S).
Proof.
rewrite /lazard_block_dual.
transitivity
  ((\sum_(j < N)
      v 0 j * coord (block_basis d) k (delta_mx 0 j))%:MP : S).
- rewrite rmorph_sum.
  apply: eq_bigr=> j _.
  by rewrite !mxE rmorphM.
- apply: congr1.
  symmetry.
  rewrite {1}(row_sum_delta v) linear_sum.
  by apply: eq_bigr=> j _; rewrite linearZ.
Qed.

Lemma lazard_block_dual_sum d
    (k : 'I_(\dim (block_image d)))
    (I : finType) (f : I -> 'rV[S]_N) :
  lazard_block_dual (d := d) k (\sum_i f i) =
    \sum_i lazard_block_dual (d := d) k (f i).
Proof.
rewrite /lazard_block_dual.
under [LHS] eq_bigr => j _ do
  rewrite summxE mulr_suml.
by rewrite exchange_big.
Qed.

Lemma lazard_block_dual_scale d
    (k : 'I_(\dim (block_image d))) a (v : 'rV[S]_N) :
  lazard_block_dual (d := d) k (a *: v) =
    (a * lazard_block_dual (d := d) k v)%R.
Proof.
rewrite /lazard_block_dual mulr_sumr.
apply: eq_bigr=> j _.
by rewrite !mxE mulrA.
Qed.

Lemma lazard_block_basis_scalar_extension_free d
    (c : 'I_(\dim (block_image d)) -> S)
    (hc : forall j : 'I_N,
      \sum_(k < \dim (block_image d))
        c k * (tnth (block_basis d) k 0 j)%:MP = 0) :
  forall k, c k = 0.
Proof.
move=> k.
have hfree := basis_free
  (SR.lazard_subgroup_reynolds_degree_block_basisP
    F (n := n) H d).
transitivity
  (\sum_(l < \dim (block_image d))
    c l *
      (coord (block_basis d) k (tnth (block_basis d) l))%:MP).
- under eq_bigr => l _ do rewrite (tnth_nth 0).
  rewrite (bigD1 k) //= coord_free // eqxx mulr1.
  rewrite big1 ?addr0 // => l hlk.
  have hlk' : l != k by exact: hlk.
  by rewrite coord_free // (negbTE hlk') mulr0.
- transitivity
    (lazard_block_dual (d := d) k
      (\sum_(l < \dim (block_image d))
        c l *: map_mx (fun r : F => (r%:MP : S))
          (tnth (block_basis d) l))).
  + rewrite lazard_block_dual_sum.
    apply: eq_bigr=> l _.
    by rewrite lazard_block_dual_scale
      lazard_block_dual_constant_row.
  + rewrite /lazard_block_dual.
    rewrite big1 // => j _.
    rewrite summxE.
    under eq_bigr => l _ do rewrite !mxE.
    by rewrite hc mul0r.
Qed.

(** The global generator sum and its span predicate. *)
Definition lazard_theorem_two_reconstruct
    (c : lazard_theorem_two_index -> S) : Inv :=
  \sum_g c g *: lazard_theorem_two_generator g.

Definition lazard_theorem_two_span (p : Inv) : Prop :=
  exists c : lazard_theorem_two_index -> S,
    p = lazard_theorem_two_reconstruct c.

Lemma lazard_theorem_two_span0 :
  lazard_theorem_two_span (0 : Inv).
Proof.
exists (fun _ => 0).
rewrite /lazard_theorem_two_reconstruct.
by rewrite big1 // => g _; rewrite scale0r.
Qed.

Lemma lazard_theorem_two_spanD p q :
  lazard_theorem_two_span p -> lazard_theorem_two_span q ->
  lazard_theorem_two_span (p + q).
Proof.
move=> [c ->] [e ->].
exists (fun g => c g + e g).
rewrite /lazard_theorem_two_reconstruct.
under [RHS] eq_bigr => g _ do rewrite scalerDl.
by rewrite big_split.
Qed.

Lemma lazard_theorem_two_spanN p :
  lazard_theorem_two_span p -> lazard_theorem_two_span (- p).
Proof.
move=> [c ->].
exists (fun g => - c g).
rewrite /lazard_theorem_two_reconstruct -sumrN.
by apply: eq_bigr=> g _; rewrite scaleNr.
Qed.

Lemma lazard_theorem_two_spanB p q :
  lazard_theorem_two_span p -> lazard_theorem_two_span q ->
  lazard_theorem_two_span (p - q).
Proof.
move=> hp hq.
change (lazard_theorem_two_span (p + - q)).
exact: lazard_theorem_two_spanD hp (lazard_theorem_two_spanN hq).
Qed.

Lemma lazard_theorem_two_spanZ a p :
  lazard_theorem_two_span p -> lazard_theorem_two_span (a *: p).
Proof.
move=> [c ->].
exists (fun g => (a * c g)%R).
rewrite /lazard_theorem_two_reconstruct scaler_sumr.
by apply: eq_bigr=> g _; rewrite scalerA.
Qed.

Lemma lazard_theorem_two_generator_in_span
    (g : lazard_theorem_two_index) :
  lazard_theorem_two_span (lazard_theorem_two_generator g).
Proof.
exists (fun h => (h == g)%:R).
rewrite /lazard_theorem_two_reconstruct (bigD1 g) //= eqxx scale1r.
have -> : (\sum_(h | h != g)
    (h == g)%:R *: lazard_theorem_two_generator h) = 0.
  apply: big1=> h hhg.
  by rewrite (negbTE hhg) scale0r.
by rewrite addr0.
Qed.

Lemma lazard_invariant_top_combination_in_span
    (d : 'I_bound.+1) p :
  lazard_theorem_two_span
    (lazard_invariant_top_combination p (d : nat)).
Proof.
rewrite /lazard_invariant_top_combination.
apply: big_ind.
- exact: lazard_theorem_two_span0.
- exact: lazard_theorem_two_spanD.
- move=> k _.
  apply: lazard_theorem_two_spanZ.
  pose g : lazard_theorem_two_index := Tagged (i := d)
    (fun d0 : 'I_bound.+1 => 'I_(\dim (block_image (d0 : nat)))) k.
  have hg := lazard_theorem_two_generator_in_span g.
  rewrite /lazard_theorem_two_generator /g /= in hg.
  exact: hg.
Qed.

(** Coordinates supported strictly below [m]. *)
Definition lazard_invariant_support_below (p : Inv) (m : nat) : Prop :=
  forall i, (m <= degree i)%N -> lazard_invariant_artin_coeff p i = 0.

Lemma lazard_invariant_support_below0 p :
  lazard_invariant_support_below p 0 -> p = 0.
Proof.
move=> hp.
apply: SIM.lazard_subgroup_invariant_val_injective.
apply: (FF.ffd_eq_of_coeff_eq (D := B))=> i.
change (lazard_invariant_artin_coeff p i =
  lazard_invariant_artin_coeff (0 : Inv) i).
by rewrite hp // lazard_invariant_artin_coeff0.
Qed.

(** Cancelling the selected block lowers the Artin support by one. *)
Lemma lazard_invariant_cancel_top_support p d
    (higher_zero : forall j, (d < degree j)%N ->
      lazard_invariant_artin_coeff p j = 0) :
  lazard_invariant_support_below
    (p - lazard_invariant_top_combination p d) d.
Proof.
move=> j hdj.
rewrite lazard_invariant_artin_coeffB
  lazard_invariant_top_combination_coeff.
case: (ltngtP d (degree j))=> hj.
- rewrite higher_zero //.
  rewrite big1 ?subr0 // => k _.
  by rewrite lazard_block_lift_coeff_above // mulr0.
- have hdd : (d < d)%N := leq_ltn_trans hdj hj.
  by rewrite ltnn in hdd.
- have hdegree : degree j = d by exact: esym hj.
  pose jo : 'I_N := enum_rank j.
  have hjo : enum_val jo = j by rewrite /jo enum_rankK.
  have hjo_degree : degree (enum_val jo) = d by rewrite hjo.
  rewrite -(hjo) (lazard_invariant_top_coordinate_reconstruct
    higher_zero hjo_degree).
  have hcomb :
      \sum_(k < \dim (block_image d))
        lazard_invariant_top_coordinate (d := d) p k *
        lazard_invariant_artin_coeff (block_lift k) (enum_val jo) =
      \sum_(k < \dim (block_image d))
        lazard_invariant_top_coordinate (d := d) p k *
        (tnth (block_basis d) k 0 jo)%:MP.
    apply: eq_bigr=> k _.
    by rewrite lazard_block_lift_coeff_top.
  by rewrite hcomb subrr.
Qed.

(** Descending spanning induction. *)
Lemma lazard_invariant_span_of_support_below : forall m p,
  lazard_invariant_support_below p m ->
  lazard_theorem_two_span p.
Proof.
elim=> [p hp|m IH p hp].
- rewrite (lazard_invariant_support_below0 hp).
  exact: lazard_theorem_two_span0.
- case hmb: (m <= bound)%N.
  + have hmord : (m < bound.+1)%N by rewrite ltnS.
    pose d : 'I_bound.+1 := Ordinal hmord.
    have higher_zero j (hmj : (m < degree j)%N) :
        lazard_invariant_artin_coeff p j = 0.
      apply: hp.
      by rewrite -ltnS.
    pose q := lazard_invariant_top_combination p m.
    have hqspan : lazard_theorem_two_span q.
      have hq := lazard_invariant_top_combination_in_span d p.
      by rewrite /q /= in hq *.
    have hrsupport : lazard_invariant_support_below (p - q) m.
      exact: lazard_invariant_cancel_top_support higher_zero.
    have hrspan := IH (p - q) hrsupport.
    have hspan := lazard_theorem_two_spanD hrspan hqspan.
    by rewrite subrK in hspan.
  + apply: IH.
    move=> j hmj.
    have hjle := FF.hffd_basis_degree_bounded (D := Artin) j.
    have hbm : (bound < m)%N by rewrite ltnNge hmb.
    have hjm : (degree j < m)%N := leq_ltn_trans hjle hbm.
    have hmm : (m < m)%N := leq_ltn_trans hmj hjm.
    by rewrite ltnn in hmm.
Qed.

Lemma lazard_invariant_support_below_boundS p :
  lazard_invariant_support_below p bound.+1.
Proof.
move=> j hbj.
have hjle := FF.hffd_basis_degree_bounded (D := Artin) j.
have hbad : (bound.+1 <= bound)%N := leq_trans hbj hjle.
by rewrite ltnn in hbad.
Qed.

Theorem lazard_theorem_two_spans p :
  lazard_theorem_two_span p.
Proof.
exact: lazard_invariant_span_of_support_below
  (lazard_invariant_support_below_boundS p).
Qed.

(** Expand a global generator sum degree by degree. *)
Lemma lazard_theorem_two_reconstruct_by_degree c :
  lazard_theorem_two_reconstruct c =
    \sum_(d : 'I_bound.+1)
      \sum_(k < \dim (block_image (d : nat)))
        GRing.GRing_scale__canonical__Scale_PreLaw InvModule
          (c (Tagged (i := d)
            (fun d0 : 'I_bound.+1 =>
              'I_(\dim (block_image (d0 : nat)))) k))
          (block_lift k).
Proof.
rewrite /lazard_theorem_two_reconstruct.
rewrite sig_big_dep /=.
apply: eq_bigr=> g _.
by case: g=> d k /=.
Qed.

Lemma lazard_theorem_two_reconstruct_coeff c j :
  lazard_invariant_artin_coeff
      (lazard_theorem_two_reconstruct c) j =
    \sum_(d : 'I_bound.+1)
      \sum_(k < \dim (block_image (d : nat)))
        c (Tagged (i := d)
          (fun d0 : 'I_bound.+1 =>
            'I_(\dim (block_image (d0 : nat)))) k) *
        lazard_invariant_artin_coeff (block_lift k) j.
Proof.
rewrite lazard_theorem_two_reconstruct_by_degree
  lazard_invariant_artin_coeff_sum.
apply: eq_bigr=> d _.
rewrite lazard_invariant_artin_coeff_sum.
apply: eq_bigr=> k _.
exact: lazard_invariant_artin_coeffZ.
Qed.

(** If all coefficients in degrees at least [m] vanish, a zero global
    combination has every coefficient zero.  The successor step extracts
    the degree-[m] block and invokes scalar-extension freeness. *)
Lemma lazard_theorem_two_independent_below : forall m
    (c : lazard_theorem_two_index -> S),
  (forall g, (m <= lazard_theorem_two_degree g)%N -> c g = 0) ->
  lazard_theorem_two_reconstruct c = 0 ->
  forall g, c g = 0.
Proof.
elim=> [c hc _ g|m IH c hc hrec].
- exact: hc g (leq0n _).
- case hmb: (m <= bound)%N.
  + have hmord : (m < bound.+1)%N by rewrite ltnS.
    pose d : 'I_bound.+1 := Ordinal hmord.
    have hcomponent (j : 'I_N) (hj : degree (enum_val j) = m) :
        \sum_(k < \dim (block_image m))
          c (Tagged (i := d)
            (fun d0 : 'I_bound.+1 =>
              'I_(\dim (block_image (d0 : nat)))) k) *
          (tnth (block_basis m) k 0 j)%:MP = 0.
      have hz : lazard_invariant_artin_coeff
          (lazard_theorem_two_reconstruct c) (enum_val j) = 0.
        by rewrite hrec lazard_invariant_artin_coeff0.
      rewrite lazard_theorem_two_reconstruct_coeff (bigD1 d) //= in hz.
      have hrest :
          \sum_(e : 'I_bound.+1 | e != d)
            \sum_(k < \dim (block_image (e : nat)))
              c (Tagged (i := e)
                (fun d0 : 'I_bound.+1 =>
                  'I_(\dim (block_image (d0 : nat)))) k) *
              lazard_invariant_artin_coeff (block_lift k)
                (enum_val j) = 0.
        apply: big1=> e hed.
        apply: big1=> k _.
        case: (ltngtP (e : nat) m) => hem.
        * rewrite (lazard_block_lift_coeff_above
            (d := (e : nat)) k (j := enum_val j));
            last by rewrite hj.
          exact: mulr0.
        * have hmSe : (m.+1 <= (e : nat))%N by rewrite -ltnS.
          have hce := hc (Tagged (i := e)
            (fun d0 : 'I_bound.+1 =>
              'I_(\dim (block_image (d0 : nat)))) k) hmSe.
          by rewrite hce mul0r.
        * have hed_eq : e = d by apply/val_inj; exact: hem.
          have heq : e == d by exact/eqP.
          have hfalse : False.
            move: hed.
            by rewrite heq.
          by case: hfalse.
      rewrite hrest addr0 in hz.
      transitivity
        (\sum_(k < \dim (block_image m))
          c (Tagged (i := d)
            (fun d0 : 'I_bound.+1 =>
              'I_(\dim (block_image (d0 : nat)))) k) *
          lazard_invariant_artin_coeff (block_lift k)
            (enum_val j)).
      * apply: eq_bigr=> k _.
        by rewrite lazard_block_lift_coeff_top.
      * exact: hz.
    have hcomponent_all (j : 'I_N) :
        \sum_(k < \dim (block_image m))
          c (Tagged (i := d)
            (fun d0 : 'I_bound.+1 =>
              'I_(\dim (block_image (d0 : nat)))) k) *
          (tnth (block_basis m) k 0 j)%:MP = 0.
      case hjm: (degree (enum_val j) == m).
      - exact: hcomponent j (eqP hjm).
      - apply: big1=> k _.
        have hjneq : degree (enum_val j) != m by rewrite hjm.
        rewrite (SR.lazard_subgroup_reynolds_degree_block_basis_support
          (F := F) (n := n) (H := H) cardH_neq0
          (d := m) (j := j) k hjneq) rmorph0 mulr0.
        reflexivity.
    have hdegree : forall k : 'I_(\dim (block_image m)),
        c (Tagged (i := d)
          (fun d0 : 'I_bound.+1 =>
            'I_(\dim (block_image (d0 : nat)))) k) = 0.
      have hdegree0 := lazard_block_basis_scalar_extension_free
        (d := m)
        (c := fun k => c (Tagged (i := d)
          (fun d0 : 'I_bound.+1 =>
            'I_(\dim (block_image (d0 : nat)))) k)) hcomponent_all.
      move=> k.
      exact: hdegree0 k.
    apply: (IH c _ hrec).
    case=> e k /= hme.
    case: (ltngtP (e : nat) m) => hem.
    * have hmm : (m < m)%N := leq_ltn_trans hme hem.
      by rewrite ltnn in hmm.
    * have hmSe : (m.+1 <= (e : nat))%N by rewrite -ltnS.
      exact: hc (Tagged (i := e)
        (fun d0 : 'I_bound.+1 =>
          'I_(\dim (block_image (d0 : nat)))) k)
        hmSe.
    * have hed : e = d by apply/val_inj; exact: hem.
      subst e.
      exact: hdegree k.
  + apply: (IH c _ hrec).
    move=> g hmg.
    have hg_bound := lazard_theorem_two_generator_degree_le g.
    have hbm : (bound < m)%N by rewrite ltnNge hmb.
    have hgm : (lazard_theorem_two_degree g < m)%N :=
      leq_ltn_trans hg_bound hbm.
    have hmm : (m < m)%N := leq_ltn_trans hmg hgm.
    by rewrite ltnn in hmm.
Qed.

Theorem lazard_theorem_two_independent c :
  lazard_theorem_two_reconstruct c = 0 ->
  forall g, c g = 0.
Proof.
apply: (lazard_theorem_two_independent_below (m := bound.+1)).
move=> g hbg.
have hg := lazard_theorem_two_generator_degree_le g.
have hbad : (bound.+1 <= bound)%N := leq_trans hbg hg.
by rewrite ltnn in hbad.
Qed.

Lemma lazard_theorem_two_reconstruct_unique c e :
  lazard_theorem_two_reconstruct c =
    lazard_theorem_two_reconstruct e ->
  forall g, c g = e g.
Proof.
move=> hce g.
have hzero : lazard_theorem_two_reconstruct
    (fun g => c g - e g) = 0.
  rewrite /lazard_theorem_two_reconstruct.
  under eq_bigr => i _ do rewrite scalerBl.
  rewrite big_split sumrN.
  change (lazard_theorem_two_reconstruct c -
    lazard_theorem_two_reconstruct e = 0).
  by rewrite hce subrr.
have hg := lazard_theorem_two_independent hzero g.
have hge := congr1 (fun x : S => (x + e g)%R) hg.
by move: hge; rewrite subrK add0r.
Qed.

(** Choice is used only to package the uniquely proved coordinates as a
    function.  [xchoose] is MathComp's constructive choice operation on the
    existing [choiceType]; no logical axiom or supplied coordinate data is
    introduced. *)
Lemma lazard_theorem_two_spans_exists p :
  exists c : lazard_theorem_two_index -> S,
    p = lazard_theorem_two_reconstruct c.
Proof. exact: lazard_theorem_two_spans p. Qed.

Definition lazard_theorem_two_coordinate_pred (p : Inv)
    (c : {ffun lazard_theorem_two_index -> S}) : bool :=
  p == lazard_theorem_two_reconstruct c.

Lemma lazard_theorem_two_spans_eq p :
  exists c : {ffun lazard_theorem_two_index -> S},
    lazard_theorem_two_coordinate_pred p c.
Proof.
case: (lazard_theorem_two_spans_exists p)=> c hc.
exists [ffun g => c g].
apply/eqP.
rewrite hc /lazard_theorem_two_reconstruct.
by apply: eq_bigr=> g _; rewrite ffunE.
Qed.

Definition lazard_theorem_two_coeff (p : Inv) :
    lazard_theorem_two_index -> S :=
  xchoose (lazard_theorem_two_spans_eq p).

Lemma lazard_theorem_two_coeff_reconstruct p :
  p = lazard_theorem_two_reconstruct (lazard_theorem_two_coeff p).
Proof.
apply/eqP.
exact: xchooseP (lazard_theorem_two_spans_eq p).
Qed.

Lemma lazard_theorem_two_coeff_unique p c :
  p = lazard_theorem_two_reconstruct c ->
  forall g, c g = lazard_theorem_two_coeff p g.
Proof.
move=> hp.
apply: lazard_theorem_two_reconstruct_unique.
transitivity p.
- exact: esym hp.
- exact: lazard_theorem_two_coeff_reconstruct p.
Qed.

Definition lazard_subgroup_invariant_finite_free :
    @FF.finite_free_decomposition S Inv :=
  {| FF.ffd_index := lazard_theorem_two_index;
     FF.ffd_basis := lazard_theorem_two_generator;
     FF.ffd_coeff := lazard_theorem_two_coeff;
     FF.ffd_reconstruct := lazard_theorem_two_coeff_reconstruct;
     FF.ffd_unique := lazard_theorem_two_coeff_unique |}.

Definition lazard_subgroup_invariant_homogeneous_finite_free :
    @FF.homogeneous_finite_free_decomposition S Inv
      (SIM.lazard_invariant_homogeneous (F := F) (H := H)) bound :=
  {| FF.hffd_free := lazard_subgroup_invariant_finite_free;
     FF.hffd_degree := lazard_theorem_two_degree;
     FF.hffd_basis_homogeneous :=
       lazard_theorem_two_generator_homogeneous;
     FF.hffd_degree_le := lazard_theorem_two_generator_degree_le |}.

End Construction.

(** Lazard's Theorem 2, with no basis, coordinate, or matrix-shape
    hypotheses.  Characteristic zero is used only to invert the finite
    subgroup order in Reynolds averaging. *)
Theorem lazard_theorem_two_statement
    (F : fieldType) (n : nat) (H : {group 'S_n}) :
  @SIM.lazard_theorem_two_statement F n H.
Proof.
move=> pchar0F.
constructor.
exact: lazard_subgroup_invariant_homogeneous_finite_free
  (SR.lazard_subgroup_card_neq0_of_pchar0 H pchar0F).
Qed.

End PolynomialFormulasLazardInvariantSubgroupTheoremTwo.
