From mathcomp Require Import
  all_ssreflect all_fingroup all_solvable all_algebra all_field.
From Abel Require Import map_gal char0 abel.
From PolynomialFormulas Require Import
  LazardOptimalityTheoremFourDegree QuinticF20Data
  QuinticGaloisAction QuinticSolvableCriterion QuinticGaloisCriterion.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The subgroup and fixed-field tower behind the valid part of Lazard's
    Theorem 4.

    Containment of a transitive quintic permutation group in a conjugate of
    [F20] forces its order to be [5], [10], or [20].  Sylow theory produces
    a normal subgroup of order five, and Cauchy's theorem supplies the
    intermediate subgroup in the order-twenty case.  Galois correspondence
    then turns this honest subgroup chain into the exact index-two Galois
    tower consumed by [LazardOptimalityTheoremFourDegree].

    The terminal relative degree five is composed with the Kummer generator
    theorem only after an actual primitive fifth root in its base field is
    supplied.  In particular, this file never turns a numerical degree
    equality into a radical presentation: the roots-of-unity membership
    required by the Kummer interface remains explicit. *)
Module PolynomialFormulasLazardOptimalityTheoremFourF20Tower.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasQuinticGaloisAction.
Import PolynomialFormulasQuinticSolvableCriterion.
Import PolynomialFormulasQuinticGaloisCriterion.

Local Open Scope ring_scope.
Local Open Scope group_scope.
Local Open Scope action_scope.

Module D := PolynomialFormulasLazardOptimalityTheoremFourDegree.

(** A decreasing exact-length subgroup chain.  Each successor has relative
    index two in its predecessor. *)
Section SubgroupTower.

Variable gT : finGroupType.

Inductive index_two_subgroup_tower (G : {group gT}) :
    nat -> {group gT} -> Prop :=
| IndexTwoSubgroupTowerZero : index_two_subgroup_tower G 0 G
| IndexTwoSubgroupTowerStep n H J :
    index_two_subgroup_tower G n H ->
    J \subset H ->
    #|H : J| = 2%N ->
    index_two_subgroup_tower G n.+1 J.

Lemma index_two_subgroup_tower_terminal_sub
    (G : {group gT}) n (H : {group gT}) :
  index_two_subgroup_tower G n H -> H \subset G.
Proof.
move=> h; elim: h => [|m A B hGA ih sBA iAB] //.
exact: subset_trans sBA ih.
Qed.

End SubgroupTower.

(** Fixed-field transport.  An index-two subgroup is normal, so every
    reversed fixed-field step is Galois as well as having degree two. *)
Section FixedFieldTower.

Variables (F0 : fieldType) (L : fieldExtType F0).
Implicit Types (E K : {subfield L}).

Lemma index_two_subgroup_tower_fixedField E
    (G : {group gal_of E}) n (H : {group gal_of E}) :
  index_two_subgroup_tower G n H ->
  D.index_two_galois_tower (fixedField G) n (fixedField H).
Proof.
move=> h; elim: h => [|m A B hGA ih sBA iAB].
- exact: D.IndexTwoGaloisTowerZero.
- have galAE : galois (fixedField A) E := fixedField_galois E A.
  have nBA : B <| A := index2_normal sBA iAB.
  have nBGal : B <| 'Gal(E / fixedField A).
    by rewrite gal_fixedField.
  have galAB : galois (fixedField A) (fixedField B) :=
    normal_fixedField_galois galAE nBGal.
  have dimAB : \dim_(fixedField A) (fixedField B) = 2%N.
    have hdim := dim_fixed_galois galAE (normal_sub nBGal).
    by move: hdim; rewrite gal_fixedField iAB.
  exact: (D.IndexTwoGaloisTowerStep ih galAB dimAB).
Qed.

(** When the chain starts at the full relative Galois group, its first
    fixed field is the stated base field. *)
Lemma full_galois_subgroup_tower_fixedField K E n
    (H : {group gal_of E}) :
  galois K E ->
  index_two_subgroup_tower 'Gal(E / K) n H ->
  D.index_two_galois_tower K n (fixedField H).
Proof.
move=> galKE h.
have fixKE : fixedField 'Gal(E / K) = K :=
  elimT galois_fixedField galKE.
rewrite -fixKE.
exact: index_two_subgroup_tower_fixedField h.
Qed.

End FixedFieldTower.

(** Small arithmetic used to classify the possible transitive subgroup
    orders and to prove uniqueness of the Sylow-five subgroup. *)
Section Arithmetic.

Lemma divisor_twenty_mod_five_one n :
  (n %| 20)%N -> n %% 5 = 1%N -> n = 1%N.
Proof.
move=> nd20 nmod5.
have nle20 : n <= 20 := dvdn_leq (isT : 0 < 20)%N nd20.
move: n nle20 nd20 nmod5.
by do 21 (case=> //=).
Qed.

Lemma five_dvd_divisor_twenty_twoExponent n :
  (5 %| n)%N -> (n %| 20)%N ->
  exists e : nat, e <= 2 /\ n = (5 * 2 ^ e)%N.
Proof.
move=> fiveDn nDtwenty.
have [k nk] := dvdnP fiveDn.
have kDfour : (k %| 4)%N.
  move: nDtwenty.
  rewrite nk.
  change (k * 5 %| 4 * 5)%N.
  by rewrite dvdn_pmul2r.
have klefour : k <= 4 := dvdn_leq (isT : 0 < 4)%N kDfour.
have kcases : k = 1%N \/ k = 2%N \/ k = 4%N.
  move: k klefour kDfour.
  by do 5 (case=> //=).
case: kcases => [-> | [-> | ->]].
- exists 0%N; split=> //.
  by rewrite nk.
- exists 1%N; split=> //.
  by rewrite nk.
- exists 2%N; split=> //.
  by rewrite nk.
Qed.

End Arithmetic.

(** A group of order [5 * 2^e], for [e <= 2], has an honest [e]-step
    index-two chain down to its unique normal subgroup of order five. *)
Section FiniteGroupTower.

Variable gT : finGroupType.

Lemma normal_sylowFive_and_index_two_tower
    (G : {group gT}) (e : nat) :
  e <= 2 -> #|G| = (5 * 2 ^ e)%N ->
  exists P : {group gT},
    #|P| = 5%N /\ P <| G /\ index_two_subgroup_tower G e P.
Proof.
move=> ele2 cardG.
have cardG_dvd20 : (#|G| %| 20)%N.
  rewrite cardG.
  move: ele2.
  by case: e => [|[|[|e]]] //=.
have cardSyl5 : #|'Syl_5(G)| == 1%N.
  apply/eqP/divisor_twenty_mod_five_one.
  - exact: dvdn_trans (@card_Syl_dvd 5 gT G) cardG_dvd20.
  - exact: (@card_Syl_mod 5 gT G) isT.
have [P sylP nPG] :=
  elimT (@normal_sylowP gT 5 G) cardSyl5.
have cardP : #|P| = 5%N.
  rewrite (card_Hall sylP) cardG.
  move: ele2.
  by case: e => [|[|[|e]]] //= _; rewrite p_part.
exists P; split; first exact: cardP.
split; first exact: nPG.
move: ele2 cardG.
case: e => [|[|[|e]]] //= _ cardG.
- have PG : P = G.
    apply: val_inj; apply/eqP.
    by rewrite eqEcard (normal_sub nPG) cardP cardG.
  by rewrite PG; exact: IndexTwoSubgroupTowerZero.
- have indexGP : #|G : P| = 2%N.
    by rewrite -divgS ?(normal_sub nPG) // cardG cardP.
  exact: (IndexTwoSubgroupTowerStep
    (IndexTwoSubgroupTowerZero G) (normal_sub nPG) indexGP).
- have twoDcardG : (2 %| #|G|)%N by rewrite cardG.
  have [x xG orderx] := Cauchy (isT : prime 2) twoDcardG.
  pose C := <[x]>%G.
  pose M := P <*> C.
  have cardC : #|C| = 2%N by rewrite /C -orderE orderx.
  have sCG : C \subset G by rewrite /C cycle_subG.
  have sCN : C \subset 'N(P) :=
    subset_trans sCG (normal_norm nPG).
  have tiPC : P :&: C = 1%G.
    apply: coprime_TIg.
    by rewrite cardP cardC.
  have cardM : #|M| = 10%N.
    have joinM : (M : {set gT}) = (P * C)%g.
      exact: norm_joinEr sCN.
    rewrite joinM (TI_cardMg tiPC) cardP cardC.
    by [].
  have sPG : P \subset G := normal_sub nPG.
  have sMG : M \subset G.
    by rewrite /M join_subG sPG sCG.
  have sPM : P \subset M := joing_subl P C.
  have indexGM : #|G : M| = 2%N.
    by rewrite -divgS ?sMG // cardG cardM.
  have indexMP : #|M : P| = 2%N.
    by rewrite -divgS ?sPM // cardM cardP.
  have towerM : index_two_subgroup_tower G 1 M :=
    IndexTwoSubgroupTowerStep
      (IndexTwoSubgroupTowerZero G) sMG indexGM.
  exact: (IndexTwoSubgroupTowerStep towerM sPM indexMP).
Qed.

End FiniteGroupTower.

(** Transitivity supplies the factor five, while subgroup containment and
    [|F20| = 20] bound the remaining factor. *)
Lemma transitive_subgroup_conjugate_F20_twoExponent
    (G : {group S5}) (x : S5) :
  [transitive G, on [set: 'I_5] | 'P] ->
  G \subset (standard_F20 :^ x) ->
  exists e : nat, e <= 2 /\ #|G| = (5 * 2 ^ e)%N.
Proof.
move=> trG subGF20.
have fiveDcardG : (5 %| #|G|)%N.
  by move: (atrans_dvd trG); rewrite cardsT card_ord.
have cardG_dvd20 : (#|G| %| 20)%N.
  move: (cardSg subGF20).
  by rewrite cardJg card_standard_F20.
exact: five_dvd_divisor_twenty_twoExponent fiveDcardG cardG_dvd20.
Qed.

(** The complete group-theoretic output for a transitive subgroup contained
    in a conjugate of [F20]. *)
Theorem transitive_subgroup_conjugate_F20_tower
    (G : {group S5}) (x : S5) :
  [transitive G, on [set: 'I_5] | 'P] ->
  G \subset (standard_F20 :^ x) ->
  exists (e : nat) (P : {group S5}),
    e <= 2 /\ #|P| = 5%N /\ P <| G /\
    index_two_subgroup_tower G e P.
Proof.
move=> trG subGF20.
have [e [ele2 cardG]] :=
  transitive_subgroup_conjugate_F20_twoExponent trG subGF20.
have [P [cardP [nPG towerP]]] :=
  normal_sylowFive_and_index_two_tower ele2 cardG.
exists e; exists P.
by repeat split; assumption.
Qed.

(** Paper-shaped adapter for the faithful Galois action of an irreducible
    rational quintic.  It produces the index-two fixed-field tower and the
    final Galois degree-five layer. *)
Section IrreducibleQuintic.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_irr : irreducible_poly p.

Let L := numfield p.

Theorem quintic_fixedField_index_two_tower_of_F20 (x : S5) :
  @quintic_galois_image p p_size p_irr \subset
    (standard_F20 :^ x) ->
  exists (e : nat) (P : {group gal_of {:L}}),
    e <= 2 /\
    #|'Gal({:L} / 1%AS)| = (5 * 2 ^ e)%N /\
    #|P| = 5%N /\
    P <| 'Gal({:L} / 1%AS) /\
    D.index_two_galois_tower 1%AS e (fixedField P) /\
    galois (fixedField P) {:L} /\
    \dim_(fixedField P) {:L} = 5%N.
Proof.
move=> subImageF20.
have [e [ele2 cardImage]] :=
  transitive_subgroup_conjugate_F20_twoExponent
    (@quintic_galois_image_transitive p p_size p_irr)
    subImageF20.
have cardGal : #|'Gal({:L} / 1%AS)| = (5 * 2 ^ e)%N.
  rewrite -cardImage /quintic_galois_image.
  symmetry.
  exact: card_injm
    (@injm_quintic_gal_perm p p_size p_irr) (subxx _).
have [P [cardP [nPG towerP]]] :=
  normal_sylowFive_and_index_two_tower ele2 cardGal.
have galQL : galois 1%AS {:L} := galois_numfield p.
have fieldTower : D.index_two_galois_tower 1%AS e (fixedField P) :=
  full_galois_subgroup_tower_fixedField galQL towerP.
have galFinal : galois (fixedField P) {:L} := fixedField_galois {:L} P.
have dimFinal : \dim_(fixedField P) {:L} = 5%N.
  by rewrite -dim_fixedField cardP.
exists e; exists P.
by repeat split; assumption.
Qed.

(** Solvability first yields the exact [F20]-containment premise through the
    existing quintic criterion; no radical tower is assumed. *)
Theorem quintic_fixedField_index_two_tower_of_solvable :
  solvable 'Gal({:L} / 1%AS) ->
  exists (e : nat) (P : {group gal_of {:L}}),
    e <= 2 /\
    #|'Gal({:L} / 1%AS)| = (5 * 2 ^ e)%N /\
    #|P| = 5%N /\
    P <| 'Gal({:L} / 1%AS) /\
    D.index_two_galois_tower 1%AS e (fixedField P) /\
    galois (fixedField P) {:L} /\
    \dim_(fixedField P) {:L} = 5%N.
Proof.
move=> solGal.
have [x subImageF20] :=
  (proj1 (@quintic_galois_solvable_iff_conjugate_F20
    p p_size p_irr)) solGal.
exact: quintic_fixedField_index_two_tower_of_F20 subImageF20.
Qed.

(** The exact Kummer endpoint for the field tower just constructed.  This
    theorem does not turn the relative degree [5] into a presentation.  It
    invokes the Hilbert--90 generator theorem through [D] and therefore
    requires an actual primitive fifth root in the terminal fixed field.

    Keeping [w \in fixedField P] explicit is essential: [numfield p] need
    not contain a primitive fifth root of unity. *)
Lemma quintic_fixedField_terminal_fifth_kummer
    (e : nat) (P : {group gal_of {:L}})
    (hfieldTower :
      D.index_two_galois_tower 1%AS e (fixedField P))
    (hgalFinal : galois (fixedField P) {:L})
    (hdimFinal : \dim_(fixedField P) {:L} = 5%N)
    (w : L) :
  5.-primitive_root w ->
  w \in fixedField P ->
  D.square_roots_and_fifth_root_presentation 1%AS {:L} e.
Proof.
move=> wroot wfixed.
have twoN0 : (2%:R : L) != 0.
  by rewrite -[2%:R](rmorph_nat (in_alg L) 2) fmorph_eq0.
have hzero : D.index_two_galois_tower 1%AS 0 1%AS :=
  D.IndexTwoGaloisTowerZero.
have hpresentation :=
  @D.two_index_two_galois_towers_then_fifth_kummer
    rat L 1%AS 1%AS (fixedField P) {:L} 0 e w
    twoN0 hzero hfieldTower hgalFinal hdimFinal wroot wfixed.
by move: hpresentation; rewrite add0n.
Qed.

(** Enriched F20 output: in addition to the subgroup and field tower, the
    conclusion exposes the exact operation which turns any *supplied*
    primitive fifth root in the terminal fixed field into the promised one
    fifth-root adjunction. *)
Theorem quintic_fixedField_terminal_kummer_of_F20 (x : S5) :
  @quintic_galois_image p p_size p_irr \subset
    (standard_F20 :^ x) ->
  exists (e : nat) (P : {group gal_of {:L}}),
    e <= 2 /\
    #|'Gal({:L} / 1%AS)| = (5 * 2 ^ e)%N /\
    #|P| = 5%N /\
    P <| 'Gal({:L} / 1%AS) /\
    D.index_two_galois_tower 1%AS e (fixedField P) /\
    galois (fixedField P) {:L} /\
    \dim_(fixedField P) {:L} = 5%N /\
    (forall w : L,
      5.-primitive_root w ->
      w \in fixedField P ->
      D.square_roots_and_fifth_root_presentation 1%AS {:L} e).
Proof.
move=> hcontain.
have [e [P [hele2 [hcardGal [hcard [hnormal
    [htower [hgal hdim]]]]]]] :=
  quintic_fixedField_index_two_tower_of_F20 hcontain.
exists e; exists P.
repeat split.
- exact: hele2.
- exact: hcardGal.
- exact: hcard.
- exact: hnormal.
- exact: htower.
- exact: hgal.
- exact: hdim.
- move=> w wroot wfixed.
  exact: quintic_fixedField_terminal_fifth_kummer
    htower hgal hdim wroot wfixed.
Qed.

Theorem quintic_fixedField_terminal_kummer_of_solvable :
  solvable 'Gal({:L} / 1%AS) ->
  exists (e : nat) (P : {group gal_of {:L}}),
    e <= 2 /\
    #|'Gal({:L} / 1%AS)| = (5 * 2 ^ e)%N /\
    #|P| = 5%N /\
    P <| 'Gal({:L} / 1%AS) /\
    D.index_two_galois_tower 1%AS e (fixedField P) /\
    galois (fixedField P) {:L} /\
    \dim_(fixedField P) {:L} = 5%N /\
    (forall w : L,
      5.-primitive_root w ->
      w \in fixedField P ->
      D.square_roots_and_fifth_root_presentation 1%AS {:L} e).
Proof.
move=> hsolvable.
have [x hcontain] :=
  (proj1 (@quintic_galois_solvable_iff_conjugate_F20
    p p_size p_irr)) hsolvable.
exact: quintic_fixedField_terminal_kummer_of_F20 hcontain.
Qed.

End IrreducibleQuintic.

Print Assumptions index_two_subgroup_tower_terminal_sub.
Print Assumptions index_two_subgroup_tower_fixedField.
Print Assumptions full_galois_subgroup_tower_fixedField.
Print Assumptions normal_sylowFive_and_index_two_tower.
Print Assumptions transitive_subgroup_conjugate_F20_twoExponent.
Print Assumptions transitive_subgroup_conjugate_F20_tower.
Print Assumptions quintic_fixedField_index_two_tower_of_F20.
Print Assumptions quintic_fixedField_index_two_tower_of_solvable.
Print Assumptions quintic_fixedField_terminal_fifth_kummer.
Print Assumptions quintic_fixedField_terminal_kummer_of_F20.
Print Assumptions quintic_fixedField_terminal_kummer_of_solvable.

End PolynomialFormulasLazardOptimalityTheoremFourF20Tower.
