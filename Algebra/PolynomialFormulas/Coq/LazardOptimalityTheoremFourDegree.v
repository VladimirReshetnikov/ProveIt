From mathcomp Require Import
  all_ssreflect all_fingroup all_solvable all_algebra all_field.
From Abel Require Import various map_gal.
From PolynomialFormulas Require Import
  LazardOptimality LazardCyclicKummerGenerator.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The valid degree and radical-count core of Lazard's Theorem 4.

    The printed leastness assertion is false for the paper's literal
    definition of radical extension.  The tower-law calculation is valid,
    and is isolated here from the stronger claim.  The radical-count record
    below contains the actual successive square- and fifth-power membership
    proofs; a numerical degree hypothesis is never treated as a radical
    presentation. *)
Module PolynomialFormulasLazardOptimalityTheoremFourDegree.

Import GRing.Theory.
Local Open Scope group_scope.
Local Open Scope ring_scope.

Module O := PolynomialFormulasLazardOptimality.
Module KG := PolynomialFormulasLazardCyclicKummerGenerator.

Section Degree.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Implicit Types (K E : {subfield L}).

(** The tower-law arithmetic in the last sentence of Theorem 4. *)
Lemma finrank_five_mul_two_power_add K E (d e : nat) :
  (K <= E)%VS ->
  \dim K = (2 ^ d)%N ->
  \dim_K E = (5 * 2 ^ e)%N ->
  \dim E = (5 * 2 ^ (d + e))%N.
Proof.
move=> hKE hK hrel.
rewrite (dim_sup_field hKE) hrel hK expnD.
by rewrite mulnAC mulnA.
Qed.

(** Paper-shaped version: a finite Galois relative degree equals the order
    of the relative Galois group. *)
Lemma finrank_five_mul_two_power_add_of_galois_order K E (d e : nat) :
  (K <= E)%VS ->
  galois (K : {vspace L}) (E : {vspace L}) ->
  \dim K = (2 ^ d)%N ->
  #|'Gal(E / K)| = (5 * 2 ^ e)%N ->
  \dim E = (5 * 2 ^ (d + e))%N.
Proof.
move=> hKE hgal hK hcard.
apply: (finrank_five_mul_two_power_add hKE hK).
by rewrite galois_dim // hcard.
Qed.

End Degree.

Section RadicalCount.

Variables (F0 : fieldType) (L : fieldExtType F0).
Implicit Types (K E M : {subfield L}).

(** An exact-length tower obtained by adjoining one square root at each
    step. *)
Inductive square_radical_tower (K : {subfield L}) :
    nat -> {subfield L} -> Prop :=
| SquareRadicalTowerZero : square_radical_tower K 0 K
| SquareRadicalTowerStep n E :
    square_radical_tower K n E ->
    forall a : L, a ^+ 2 \in E ->
    square_radical_tower K n.+1 <<E; a>>%AS.

(** Base change inside a common ambient field preserves every displayed
    square adjunction.  Some steps may collapse, but the same square-root
    presentation remains valid, which is exactly what radical counting
    needs. *)
Lemma square_radical_tower_prodvr K n E (W : {subfield L}) :
  square_radical_tower K n E ->
  square_radical_tower (K * W)%AS n (E * W)%AS.
Proof.
move=> h; elim: h => [|m A hKA ih a ha].
- exact: SquareRadicalTowerZero.
- have hprod :
      (<<A; a>> * W)%AS = <<(A * W)%AS; a>>%AS.
    apply: val_inj.
    exact: prodv_Fadjoinl A W a.
  rewrite hprod.
  apply: (SquareRadicalTowerStep ih).
  exact: (subvP (field_subvMr A W) (a ^+ 2) ha).
Qed.

(** A square whose square is already in the base has adjunction degree at
    most two.  This is the minimal-polynomial argument, not an inference
    from the name of the tower. *)
Lemma adjoin_degree_le_two_of_square_mem K (a : L) :
  a ^+ 2 \in K -> (adjoin_degree K a <= 2)%N.
Proof.
move=> ha2.
pose q : {poly L} := 'X^2 - (a ^+ 2)%:P.
have hqover : q \is a polyOver K.
  by rewrite /q polyOverXnsubC.
have hqroot : root q a.
  by rewrite /q rootE !hornerE subrr eqxx.
have hdiv : minPoly K a %| q := minPoly_dvdp hqover hqroot.
have htwo_pos : (0 < 2)%N by [].
have hqmonic : q \is monic.
  rewrite /q.
  exact: monicXnsubC htwo_pos.
have hsize := dvdp_leq (monic_neq0 hqmonic) hdiv.
move: hsize.
by rewrite size_minPoly /q size_XnsubC // leqSS.
Qed.

(** Consequently, an [n]-step displayed square tower has total absolute
    degree at most [2^n] times that of its base. *)
Lemma square_radical_tower_dim_le K n E :
  square_radical_tower K n E ->
  (\dim E <= 2 ^ n * \dim K)%N.
Proof.
move=> h; elim: h => [|m A hKA ih a ha].
- by rewrite expn0 mul1n.
- rewrite dim_Fadjoin expnS -mulnA.
  exact: leq_mul (adjoin_degree_le_two_of_square_mem ha) ih.
Qed.

(** The terminal field of a displayed square tower contains its base. *)
Lemma square_radical_tower_terminal_sub K n E :
  square_radical_tower K n E -> (K <= E)%VS.
Proof.
move=> h; elim: h => [|m A hKA ih a ha].
- exact: subvv.
- exact: subv_trans ih (subv_adjoin A a).
Qed.

(** Remove precisely the square adjunctions which collapse after a base
    change.  The returned exponent is therefore the exponent of the actual
    relative degree, rather than the length of the possibly redundant input
    presentation.

    A surviving step has degree two: its degree is at most two by the
    minimal-polynomial argument above, is positive, and cannot be one since
    [adjoin_deg_eq1] would put its generator in the preceding field.  The
    absolute and relative dimension equalities certify collectively that no
    step in the returned presentation is collapsed. *)
Lemma square_radical_tower_compress K n E :
  square_radical_tower K n E ->
  exists e,
    (e <= n)%N /\
    square_radical_tower K e E /\
    \dim E = (2 ^ e * \dim K)%N /\
    \dim_K E = (2 ^ e)%N.
Proof.
move=> h; elim: h => [|m A hKA ih a ha].
- exists 0; split; first by [].
  split; first exact: SquareRadicalTowerZero.
  split; first by rewrite expn0 mul1n.
  by rewrite expn0 divnn ?adim_gt0.
- have [e [ele [hcompressed [hdimA hreldimA]]]] := ih.
  case haA: (a \in A).
  + have aA : a \in A by rewrite haA.
    have hadjoin : <<A; a>>%AS = A.
      apply: val_inj.
      exact: elimT Fadjoin_idP aA.
    exists e; split; first exact: leq_trans ele (leqnSn m).
    split; first by rewrite hadjoin.
    split; first by rewrite hadjoin.
    by rewrite hadjoin.
  + have hadeg_le : (adjoin_degree A a <= 2)%N :=
      adjoin_degree_le_two_of_square_mem ha.
    have hadeg_pos : (0 < adjoin_degree A a)%N.
      by rewrite adjoin_degreeE divn_gt0 ?adim_gt0 //
        dimvS ?subv_adjoin.
    have hadeg_ne_one : adjoin_degree A a != 1%N.
      by rewrite adjoin_deg_eq1 haA.
    have hadeg : adjoin_degree A a = 2%N.
      move: hadeg_le hadeg_pos hadeg_ne_one.
      by case: (adjoin_degree A a) => [|[|[|d]]].
    have hdimAa :
        \dim <<A; a>> = (2 ^ e.+1 * \dim K)%N.
      rewrite dim_Fadjoin hadeg hdimA expnS.
      exact: (mulnA 2 (2 ^ e)%N (\dim K)).
    exists e.+1; split; first exact: ele.
    split; first exact: (SquareRadicalTowerStep hcompressed ha).
    split; first exact: hdimAa.
    by rewrite hdimAa mulnK ?adim_gt0.
Qed.

End RadicalCount.

Section IndexTwoGalois.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Implicit Types (K E M : {subfield L}).

(** A supplied chain of finite Galois extensions of relative degree two.
    This is the field-theoretic form delivered by Galois correspondence;
    unlike [square_radical_tower], it does not assume radical generators. *)
Inductive index_two_galois_tower (K : {subfield L}) :
    nat -> {subfield L} -> Prop :=
| IndexTwoGaloisTowerZero : index_two_galois_tower K 0 K
| IndexTwoGaloisTowerStep n E M :
    index_two_galois_tower K n E ->
    galois E M ->
    \dim_E M = 2 ->
    index_two_galois_tower K n.+1 M.

(** Every terminal field in the supplied Galois tower contains its base.
    This small structural lemma is also the membership transport needed by
    the cyclotomic/Kummer composition. *)
Lemma index_two_galois_tower_terminal_sub K n E :
  index_two_galois_tower K n E -> (K <= E)%VS.
Proof.
move=> h; elim: h => [|m A B hKA ih hAB hdim].
- exact: subvv.
- exact: subv_trans ih (galois_subW hAB).
Qed.

(** In characteristic different from two, [-1] is the primitive square
    root of unity required by the Kummer generator theorem. *)
Lemma primitive_root_two_neg_one :
  2%:R != 0 :> L -> 2.-primitive_root (-1 : L).
Proof.
move=> twoN0; apply/'forall_eqP => -[[|[|]]] //= _; last first.
  by apply/unity_rootP; rewrite -signr_odd.
by apply/unity_rootP/eqP; rewrite expr1 eq_sym -addr_eq0 -mulr2n.
Qed.

(** Every exact index-two Galois chain produces an exact square-root chain
    of the same length.  The generators are obtained from Hilbert 90 via
    [cyclic_kummer_generator], not inferred from the dimensions. *)
Lemma index_two_galois_tower_is_square K n E :
  2%:R != 0 :> L ->
  index_two_galois_tower K n E ->
  square_radical_tower K n E.
Proof.
move=> twoN0 h; elim: h => [|m A B hKA ih hAB hdim].
- exact: SquareRadicalTowerZero.
- have hcyclic : cyclic 'Gal(B / A).
    apply/prime_cyclic.
    by rewrite -(galois_dim hAB) hdim.
  have hroot : (\dim_A B).-primitive_root (-1 : L).
    by rewrite hdim; apply: primitive_root_two_neg_one.
  have hminusA : -1 \in A by rewrite rpredN mem1v.
  have [x [_ _ hxpow hB]] :=
    KG.cyclic_kummer_generator hroot hminusA hAB hcyclic.
  have hxpow2 : x ^+ 2 \in A.
    by move: hxpow; rewrite hdim.
  rewrite hB.
  exact: (SquareRadicalTowerStep ih hxpow2).
Qed.

End IndexTwoGalois.

Section RadicalCountContinuation.

Variables (F0 : fieldType) (L : fieldExtType F0).
Implicit Types (K E M : {subfield L}).

(** Every certified square-root tower is a radical extension under the
    literal definition used by Lazard. *)
Lemma square_radical_tower_is_radical K n E :
  square_radical_tower K n E -> @O.radical_extension F0 L K E.
Proof.
move=> h; elim: h => [|m M hKM ih a ha].
- exact: O.RadicalExtensionRefl.
- apply: O.RadicalExtensionStep ih _.
  exists a, 2; split; first by [].
  split; first exact ha.
  reflexivity.
Qed.

(** Concatenate two certified square-root towers. *)
Lemma square_radical_tower_trans K E M m n :
  square_radical_tower K m E ->
  square_radical_tower E n M ->
  square_radical_tower K (m + n) M.
Proof.
move=> hKE hEM; elim: hEM => [|k N hEN ih a ha].
- by rewrite addn0.
- rewrite addnS.
  exact: (SquareRadicalTowerStep ih ha).
Qed.

(** Literal certificate that [E/K] is defined by exactly [n] square-root
    adjunctions followed by one fifth-root adjunction.  This is deliberately
    an existential-style proposition: its field/root witnesses are used only
    while proving propositions, so no forbidden projection or large
    elimination from [Prop] is required. *)
Inductive square_roots_and_fifth_root_presentation
    (K E : {subfield L}) (n : nat) : Prop :=
| SquareRootsAndFifthRootPresentation
    (middle : {subfield L})
    (tower : square_radical_tower K n middle)
    (root : L)
    (power_mem : root ^+ 5 \in middle)
    (field_eq : E = <<middle; root>>%AS).

(** Every such presentation is honestly a radical extension. *)
Lemma square_roots_and_fifth_root_is_radical K E n :
  square_roots_and_fifth_root_presentation K E n ->
  @O.radical_extension F0 L K E.
Proof.
case=> M hKM a ha ->.
apply: O.RadicalExtensionStep
  (square_radical_tower_is_radical hKM) _.
exists a, 5; split; first by [].
split; first exact ha.
reflexivity.
Qed.

(** A [d]-step cyclotomic square tower followed by an [e]-step formula
    square tower gives the claimed [d+e] count once the final fifth-power
    membership is actually proved. *)
Lemma two_square_towers_then_fifth K E M d e (a : L) :
  square_radical_tower K d E ->
  square_radical_tower E e M ->
  a ^+ 5 \in M ->
  square_roots_and_fifth_root_presentation
    K <<M; a>>%AS (d + e).
Proof.
move=> hKE hEM ha.
have htower := square_radical_tower_trans hKE hEM.
exact (@SquareRootsAndFifthRootPresentation
  K <<M; a>>%AS (d + e) M htower a ha erefl).
Qed.

End RadicalCountContinuation.

Section GaloisRadicalCount.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Implicit Types (K E M N : {subfield L}).

(** Corrected general radical-count path for Theorem 4.  Two exact Galois
    chains of index two are converted into square-root adjunctions, and the
    final cyclic degree-five layer is converted into one fifth-root
    adjunction.  Both roots-of-unity hypotheses are explicit. *)
Lemma two_index_two_galois_towers_then_fifth_kummer
    K E M N d e (w : L) :
  2%:R != 0 :> L ->
  index_two_galois_tower K d E ->
  index_two_galois_tower E e M ->
  galois M N ->
  \dim_M N = 5 ->
  5.-primitive_root w ->
  w \in M ->
  square_roots_and_fifth_root_presentation K N (d + e).
Proof.
move=> twoN0 hKE hEM hMN hdim wroot wM.
have hcyclic : cyclic 'Gal(N / M).
  apply/prime_cyclic.
  by rewrite -(galois_dim hMN) hdim.
have hrootdim : (\dim_M N).-primitive_root w by rewrite hdim.
have [p [_ _ hppow hN]] :=
  KG.cyclic_kummer_generator hrootdim wM hMN hcyclic.
have hppow5 : p ^+ 5 \in M.
  by move: hppow; rewrite hdim.
rewrite hN.
exact: (two_square_towers_then_fifth
  (index_two_galois_tower_is_square twoN0 hKE)
  (index_two_galois_tower_is_square twoN0 hEM) hppow5).
Qed.

End GaloisRadicalCount.

Section ConcreteRadicalCount.

Variables (F0 : fieldType) (L : fieldExtType F0).
Implicit Types (K : {subfield L}).

(** The literal field generated by two successive square roots and one
    fifth root. *)
Definition square_square_fifth_field K (s t p : L) : {subfield L} :=
  << << <<K; s>>%AS; t>>%AS; p>>%AS.

(** The concrete square/square/fifth pattern carries an exact two-square
    presentation.  All three power facts are ordinary hypotheses. *)
Lemma two_squares_then_fifth K (s t p : L) :
  s ^+ 2 \in K ->
  t ^+ 2 \in <<K; s>>%AS ->
  p ^+ 5 \in << <<K; s>>%AS; t>>%AS ->
  square_roots_and_fifth_root_presentation
    K (square_square_fifth_field K s t p) 2.
Proof.
move=> hs ht hp.
have hs_tower : square_radical_tower K 1 <<K; s>>%AS.
  exact: (SquareRadicalTowerStep (SquareRadicalTowerZero K) hs).
have ht_tower : square_radical_tower <<K; s>>%AS 1
    << <<K; s>>%AS; t>>%AS.
  exact: (SquareRadicalTowerStep
    (SquareRadicalTowerZero <<K; s>>%AS) ht).
exact: (two_square_towers_then_fifth hs_tower ht_tower hp).
Qed.

End ConcreteRadicalCount.

Section RadicalTowerMap.

Variables (F0 : fieldType) (L L' : fieldExtType F0).

(** Algebra embeddings preserve a displayed square-root tower, including
    its actual generators and power-membership certificates.  This lives
    after the one-ambient-field section so [L] and [L'] are generalized
    independently. *)
Lemma square_radical_tower_aimg
    (f : 'AHom(L, L')) (K : {subfield L}) n (E : {subfield L}) :
  @square_radical_tower F0 L K n E ->
  @square_radical_tower F0 L' (f @: K) n (f @: E).
Proof.
move=> h; elim: h => [|m A hKA ih a ha].
- exact: SquareRadicalTowerZero.
  - have hmap :
      ((f @: <<A; a>>%AS)%AS) = <<(f @: A); f a>>%AS.
    apply: val_inj.
    exact (aimg_adjoin f A a).
  rewrite hmap.
  apply: (SquareRadicalTowerStep ih).
  rewrite -rmorphXn.
  exact (memv_img f ha).
Qed.

End RadicalTowerMap.

Print Assumptions finrank_five_mul_two_power_add.
Print Assumptions finrank_five_mul_two_power_add_of_galois_order.
Print Assumptions square_radical_tower_aimg.
Print Assumptions square_radical_tower_prodvr.
Print Assumptions adjoin_degree_le_two_of_square_mem.
Print Assumptions square_radical_tower_dim_le.
Print Assumptions square_radical_tower_terminal_sub.
Print Assumptions square_radical_tower_compress.
Print Assumptions square_radical_tower_is_radical.
Print Assumptions index_two_galois_tower_terminal_sub.
Print Assumptions index_two_galois_tower_is_square.
Print Assumptions square_radical_tower_trans.
Print Assumptions square_roots_and_fifth_root_is_radical.
Print Assumptions two_square_towers_then_fifth.
Print Assumptions two_index_two_galois_towers_then_fifth_kummer.
Print Assumptions two_squares_then_fifth.

End PolynomialFormulasLazardOptimalityTheoremFourDegree.
