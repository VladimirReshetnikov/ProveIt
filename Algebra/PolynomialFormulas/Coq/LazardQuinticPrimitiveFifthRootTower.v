From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra falgebra fieldext.
From Abel Require Import various map_gal.
From PolynomialFormulas Require Import
  LazardQuinticPrimitiveFifthRoot
  LazardQuinticCertificateRadicalTower
  LazardOptimalityTheoremFourDegree
  LazardOptimalityTheoremFourF20Tower
  LazardOptimalityTheoremThreeCounterexample.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The exact radical tower supplied by the classical two-square expression
    for a primitive fifth root, its common-ambient Kummer composition with a
    base-changed F20 fixed-field tower, and its composition with Lazard's
    displayed two-square/one-fifth formula tower.  Every count below is
    witnessed by actual power membership at the corresponding intermediate
    field. *)
Module PolynomialFormulasLazardQuinticPrimitiveFifthRootTower.

Import GRing.Theory.
Local Open Scope ring_scope.

Module PF := PolynomialFormulasLazardQuinticPrimitiveFifthRoot.
Module CRT := PolynomialFormulasLazardQuinticCertificateRadicalTower.
Module T4 := PolynomialFormulasLazardOptimalityTheoremFourDegree.
Module F20T := PolynomialFormulasLazardOptimalityTheoremFourF20Tower.
Module KG := PolynomialFormulasLazardCyclicKummerGenerator.
Module C5 := PolynomialFormulasLazardOptimalityTheoremThreeCounterexample.
Module OC :=
  PolynomialFormulasLazardOptimalityCyclicQuinticCounterexample.

Section CyclotomicTower.

Variables (F0 : fieldType) (L : fieldExtType F0).
Implicit Types (B : {subfield L}) (s t : L).

(** The field obtained by the two classical square adjunctions. *)
Definition lazard_square_radical_fifth_root_field B s t : {subfield L} :=
  << <<B; s>>%AS; t>>%AS.

(** The two displayed square-power memberships give an exact length-two
    square tower. *)
Lemma lazard_square_radical_fifth_root_field_is_two_square_tower B s t :
  s ^+ 2 \in B ->
  t ^+ 2 \in <<B; s>>%AS ->
  @T4.square_radical_tower F0 L B 2
    (lazard_square_radical_fifth_root_field B s t).
Proof.
move=> hs ht.
have hs_tower : @T4.square_radical_tower F0 L B 1 <<B; s>>%AS.
  exact: (T4.SquareRadicalTowerStep (T4.SquareRadicalTowerZero B) hs).
have ht_tower : @T4.square_radical_tower F0 L <<B; s>>%AS 1
    (lazard_square_radical_fifth_root_field B s t).
  exact: (T4.SquareRadicalTowerStep
    (T4.SquareRadicalTowerZero <<B; s>>%AS) ht).
exact: (T4.square_radical_tower_trans hs_tower ht_tower).
Qed.

(** The classical equations themselves imply the two required membership
    statements. *)
Lemma lazard_square_radical_fifth_root_field_is_two_square_tower_of_eq B s t :
  s ^+ 2 = 5%:R ->
  t ^+ 2 = - 10%:R - 2%:R * s ->
  @T4.square_radical_tower F0 L B 2
    (lazard_square_radical_fifth_root_field B s t).
Proof.
move=> hs ht.
apply: lazard_square_radical_fifth_root_field_is_two_square_tower.
- by rewrite hs rpred_nat.
- rewrite ht.
  apply: rpredB.
  + exact: rpredN (rpred_nat _ _).
  + exact: rpredM (rpred_nat _ _) memv_adjoin.
Qed.

(** The explicit primitive fifth root is already contained in the second
    square field; adjoining it requires no additional radical step. *)
Lemma lazard_square_radical_fifth_root_mem B s t :
  PF.lazard_square_radical_fifth_root s t \in
    lazard_square_radical_fifth_root_field B s t.
Proof.
rewrite /PF.lazard_square_radical_fifth_root.
apply: rpred_div; last exact: rpred_nat _ _.
apply: rpredD; last exact: memv_adjoin.
apply: rpredD.
- exact: rpredN rpred1.
- exact: subvP_adjoin memv_adjoin.
Qed.

(** Base-field membership is preserved by the two cyclotomic adjunctions. *)
Lemma lazard_base_le_square_radical_fifth_root_field B s t :
  (B <= lazard_square_radical_fifth_root_field B s t)%VS.
Proof.
move=> x hx.
exact: subvP_adjoin (subvP_adjoin hx).
Qed.

End CyclotomicTower.

(* -------------------------------------------------------------------- *)
(** * The two-square fifth-root field has degree exactly four over Q *)

Section RationalCyclotomicDegree.

Variable L : splittingFieldType rat.

(** The standard minimal-polynomial uniqueness argument, stated for an
    arbitrary rational extension rather than the one concrete cyclotomic
    ambient in which it was first needed. *)
Lemma irreducible_monic_root_eq_minPoly_rat
    (p : {poly rat}) (x : L) :
  irreducible_poly p -> p \is monic ->
  root (map_poly (in_alg L) p) x ->
  map_poly (in_alg L) p = minPoly 1 x.
Proof.
move=> p_irred p_monic px0.
have p_over : map_poly (in_alg L) p \is a polyOver 1%AS.
  by apply/polyOver1P; exists p.
have min_dvd : minPoly 1 x %| map_poly (in_alg L) p :=
  minPoly_dvdp p_over px0.
have min_size1 : size (minPoly 1 x) != 1%N by rewrite size_minPoly.
have /polyOver1P[q hq] := minPolyOver 1 x.
have q_size1 : size q != 1%N.
  move: min_size1.
  by rewrite hq size_map_poly.
have q_dvd_p : q %| p.
  move: min_dvd.
  by rewrite hq dvdp_map.
have min_eqp : minPoly 1 x %= map_poly (in_alg L) p.
  rewrite hq eqp_map.
  exact: p_irred q q_size1 q_dvd_p.
have mapped_monic : map_poly (in_alg L) p \is monic.
  by rewrite map_monic.
apply/eqP.
rewrite -eqp_monic ?monic_minPoly //.
by rewrite (eqp_sym min_eqp).
Qed.

(** A primitive fifth root satisfies the irreducible rational fifth
    cyclotomic polynomial. *)
Lemma primitive_fifth_root_is_root_cyclotomic_rat (w : L) :
  5.-primitive_root w ->
  root (map_poly (in_alg L) C5.fifth_cyclotomic_Q) w.
Proof.
move=> wroot.
rewrite C5.fifth_cyclotomic_Q_eq_cyclotomic_rat
  /OC.cyclotomic_rat -map_poly_comp.
have hmap :
    (in_alg L) \o (intr : int -> rat) =1 (intr : int -> L).
  by move=> a /=; rewrite rmorph_int.
rewrite (eq_map_poly hmap) (Phi_cyclotomic wroot).
by rewrite root_cyclotomic.
Qed.

(** Hence adjoining a primitive fifth root to the rational prime field has
    degree four. *)
Lemma primitive_fifth_root_adjoin_dim (w : L) :
  5.-primitive_root w -> \dim <<1; w>>%AS = 4%N.
Proof.
move=> wroot.
have hmin :
    map_poly (in_alg L) C5.fifth_cyclotomic_Q = minPoly 1 w.
  exact: irreducible_monic_root_eq_minPoly_rat
    C5.fifth_cyclotomic_Q_irreducible
    C5.fifth_cyclotomic_Q_monic
    (primitive_fifth_root_is_root_cyclotomic_rat wroot).
rewrite dim_Fadjoin dimv1 muln1.
apply: succn_inj.
rewrite -size_minPoly -hmin.
by rewrite size_map_poly C5.fifth_cyclotomic_Q_size.
Qed.

(** A two-square presentation containing a primitive fifth root has both
    the square-tower upper bound and the cyclotomic lower bound, so its
    absolute degree is exactly four. *)
Lemma primitive_fifth_root_two_square_field_dim
    (W : {subfield L}) (w : L) :
  T4.square_radical_tower 1%AS 2 W ->
  5.-primitive_root w ->
  w \in W ->
  \dim W = 4%N.
Proof.
move=> htower wroot wW.
have hupper : \dim W <= 4%N.
  have := T4.square_radical_tower_dim_le htower.
  by rewrite expn2 dimv1 muln1.
have hadjoinW : (<<1; w>>%AS <= W)%VS.
  apply/FadjoinP; split; first exact: sub1v.
  exact: wW.
have hlower : 4%N <= \dim W.
  rewrite -(primitive_fifth_root_adjoin_dim wroot).
  exact: dimvS hadjoinW.
apply/eqP.
by rewrite eqn_leq hupper hlower.
Qed.

End RationalCyclotomicDegree.

(* -------------------------------------------------------------------- *)
(** * A degree-five layer survives the two-power base change *)

Section DegreeFiveBaseChange.

Variables (F0 : fieldType) (L : splittingFieldType F0).
Implicit Types (K S W : {subfield L}).

(** If [S/K] is Galois of prime degree five and [W] has absolute degree at
    most four, then adjoining [W] cannot collapse the degree-five layer.

    The proof is the actual intersection argument.  Put [M = K W] and
    [J = S :&: M].  Galois correspondence makes [[S:J]] divide five, so it
    is one or five.  The case one would put [S] inside [M], whereas
    [dim M <= dim K * dim W <= 4 * dim K] and
    [dim S = 5 * dim K].  Thus [J] is the bottom intermediate field and
    Abel's [galois_isog] gives the claimed base-changed degree. *)
Lemma galois_degree_five_prodvr_of_dim_le_four K S W :
  galois K S ->
  \dim_K S = 5%N ->
  \dim W <= 4%N ->
  galois (K * W)%AS (S * (K * W)%AS)%AS /\
    \dim_(K * W)%AS (S * (K * W)%AS)%AS = 5%N.
Proof.
move=> hgalKS hdimKS hdimW.
pose M := (K * W)%AS.
pose N := (S * M)%AS.
pose J := (S :&: M)%AS.
have hKS : (K <= S)%VS := galois_subW hgalKS.
have hKM : (K <= M)%VS.
  rewrite /M.
  exact: field_subvMr K W.
have hJS : (J <= S)%VS := capvSl S M.
have hJM : (J <= M)%VS := capvSr S M.
have hKJ : (K <= J)%VS.
  apply/subvP=> x hx.
  by rewrite memv_cap (subvP hKS hx) (subvP hKM hx).
have hgalJS : galois J S := capv_galois hKM hgalKS.
have hgalMN : galois M N.
  rewrite /N.
  exact: galois_prodvr hKM hgalKS.
have hdimS : \dim S = (5 * \dim K)%N.
  by rewrite (dim_sup_field hKS) hdimKS.
have hdimM_le : \dim M <= (\dim K * \dim W)%N.
  rewrite /M.
  exact: dim_prodv K W.
have hS_not_sub_M : ~ (S <= M)%VS.
  move=> hSM.
  have hSMdim : \dim S <= \dim M := dimvS hSM.
  have hMfour : \dim M <= (4 * \dim K)%N.
    apply: leq_trans hdimM_le.
    have := leq_mul (leqnn (\dim K)) hdimW.
    by rewrite [\dim K * 4]mulnC.
  have hbad : (5 * \dim K <= 4 * \dim K)%N.
    rewrite -hdimS.
    exact: leq_trans hSMdim hMfour.
  by move: hbad; rewrite leq_pmul2r.
have hdegree_dvd : (\dim_J S %| 5)%N.
  have hcard := cardSg (galS hKJ).
  move: hcard.
  by rewrite -(galois_dim hgalJS) -(galois_dim hgalKS) hdimKS.
have hdegree_ne_one : \dim_J S != 1%N.
  apply/negP=> /eqP hdegree_one.
  have hdimJS : \dim J = \dim S.
    have hsup := dim_sup_field hJS.
    move: hsup.
    by rewrite hdegree_one mul1n => ->.
  have hJS_eq : J = S.
    apply: val_inj; apply/eqP.
    by rewrite eqEdim hJS hdimJS leqnn.
  apply: hS_not_sub_M.
  rewrite -hJS_eq.
  exact: hJM.
have hdimJS : \dim_J S = 5%N :=
  elimT (prime_nt_dvdP (isT : prime 5) hdegree_ne_one) hdegree_dvd.
split; first exact: hgalMN.
rewrite (galois_dim hgalMN)
  (card_isog (galois_isog hgalKS hKM))
  -(galois_dim hgalJS).
exact: hdimJS.
Qed.

(** Composing a concrete two-square cyclotomic tower with a mapped F20
    square tower now needs no extra base-change premise.  The theorem above
    supplies the genuine degree-five Galois endpoint, and Hilbert--90
    supplies its fifth-root generator. *)
Theorem lazard_two_square_base_change_terminal_kummer
    K S W (e : nat) (w : L) :
  T4.square_radical_tower 1%AS 2 W ->
  T4.square_radical_tower 1%AS e K ->
  galois K S ->
  \dim_K S = 5%N ->
  5.-primitive_root w ->
  w \in W ->
  T4.square_roots_and_fifth_root_presentation
    1%AS (S * (K * W)%AS)%AS (2 + e).
Proof.
move=> hcyclotomic hformula hgalKS hdimKS wroot wW.
pose M := (K * W)%AS.
pose N := (S * M)%AS.
have hdimW : \dim W <= 4%N.
  have := T4.square_radical_tower_dim_le hcyclotomic.
  by rewrite expn2 dimv1 muln1.
have [hgalMN hdimMN] :=
  galois_degree_five_prodvr_of_dim_le_four hgalKS hdimKS hdimW.
have hformula_base_changed : T4.square_radical_tower W e M.
  have hbase := T4.square_radical_tower_prodvr hformula W.
  have h1W : ((1%AS : {subfield L}) * W)%AS = W.
    apply: val_inj.
    exact: prod1v W.
  move: hbase.
  by rewrite h1W.
have wM : w \in M.
  rewrite /M.
  exact: (subvP (field_subvMl K W) wW).
have hcyclic : cyclic 'Gal(N / M).
  apply/prime_cyclic.
  by rewrite galois_dim // hdimMN.
have wrootdim : (\dim_M N).-primitive_root w by rewrite hdimMN.
have [a [_ _ hapow hN]] :=
  KG.cyclic_kummer_generator wrootdim wM hgalMN hcyclic.
have hapow5 : a ^+ 5 \in M by rewrite -hdimMN.
rewrite /N hN.
exact: T4.two_square_towers_then_fifth
  hcyclotomic hformula_base_changed hapow5.
Qed.

(** Exact post-base-change form.  The exponent [e_Q] belongs to the
    pre-base-change F20 tower.  After adjoining the cyclotomic field, some
    quadratic steps may collapse; [square_radical_tower_compress] deletes
    exactly those steps and returns the distinct exponent [e_omega].

    The Galois hypothesis over the bottom field is used only for the stated
    cardinality of the full post-base-change Galois group.  The terminal
    relative degree five, the absolute degree, and the shorter radical
    presentation already follow from the compressed tower and tower law. *)
Theorem lazard_two_square_base_change_terminal_kummer_compressed
    K S W (e_Q : nat) (w : L) :
  T4.square_radical_tower 1%AS 2 W ->
  T4.square_radical_tower 1%AS e_Q K ->
  \dim W = 4%N ->
  galois 1%AS S ->
  galois K S ->
  \dim_K S = 5%N ->
  5.-primitive_root w ->
  w \in W ->
  exists e_omega,
    e_omega <= e_Q /\
    T4.square_radical_tower W e_omega (K * W)%AS /\
    \dim_W (K * W)%AS = 2 ^ e_omega /\
    galois W (S * (K * W)%AS)%AS /\
    #|'Gal((S * (K * W)%AS)%AS / W)| = 5 * 2 ^ e_omega /\
    \dim (S * (K * W)%AS)%AS = 5 * 2 ^ (2 + e_omega) /\
    T4.square_roots_and_fifth_root_presentation
      1%AS (S * (K * W)%AS)%AS (2 + e_omega).
Proof.
move=> hcyclotomic hformula hdimW hgal1S hgalKS hdimKS wroot wW.
pose M := (K * W)%AS.
pose N := (S * M)%AS.
have hdimW_le : \dim W <= 4%N by rewrite hdimW.
have [hgalMN hdimMN] :=
  galois_degree_five_prodvr_of_dim_le_four hgalKS hdimKS hdimW_le.
have hformula_base_changed : T4.square_radical_tower W e_Q M.
  have hbase := T4.square_radical_tower_prodvr hformula W.
  have h1W : ((1%AS : {subfield L}) * W)%AS = W.
    apply: val_inj.
    exact: prod1v W.
  move: hbase.
  by rewrite h1W.
have [e_omega [eomega_le [hformula_compressed
    [hdimM hdimWM]]]] :=
  T4.square_radical_tower_compress hformula_base_changed.
have hWM : (W <= M)%VS :=
  T4.square_radical_tower_terminal_sub hformula_compressed.
have hMN : (M <= N)%VS.
  rewrite /N.
  exact: field_subvMl S M.
have hWN : (W <= N)%VS := subv_trans hWM hMN.
have hdimNfactor :
    \dim N = ((5 * 2 ^ e_omega) * \dim W)%N.
  rewrite (dim_sup_field hMN) hdimMN hdimM.
  by rewrite !mulnA.
have hdimWN : \dim_W N = 5 * 2 ^ e_omega.
  by rewrite hdimNfactor mulnK ?adim_gt0.
have hdimWpow : \dim W = 2 ^ 2 by rewrite hdimW expn2.
have hdimN : \dim N = 5 * 2 ^ (2 + e_omega) :=
  T4.finrank_five_mul_two_power_add hWN hdimWpow hdimWN.
have hKS : (K <= S)%VS := galois_subW hgalKS.
have hSKprod_v : (S * K)%VS = S.
  rewrite prodvC.
  apply: field_module_eq.
  by rewrite sup_field_module.
have hNprod : N = (S * W)%AS.
  apply: val_inj.
  by rewrite /N /M -prodvA hSKprod_v.
have hgalWN : galois W N.
  rewrite hNprod.
  exact: galois_prodvr (sub1v W) hgal1S.
have hcardWN : #|'Gal(N / W)| = 5 * 2 ^ e_omega.
  by rewrite -(galois_dim hgalWN) hdimWN.
have wM : w \in M.
  rewrite /M.
  exact: (subvP (field_subvMl K W) wW).
have hcyclic : cyclic 'Gal(N / M).
  apply/prime_cyclic.
  by rewrite galois_dim // hdimMN.
have wrootdim : (\dim_M N).-primitive_root w by rewrite hdimMN.
have [a [_ _ hapow hNadjoin]] :=
  KG.cyclic_kummer_generator wrootdim wM hgalMN hcyclic.
have hapow5 : a ^+ 5 \in M by rewrite -hdimMN.
have hpresentation :
    T4.square_roots_and_fifth_root_presentation
      1%AS N (2 + e_omega).
  rewrite /N hNadjoin.
  exact: T4.two_square_towers_then_fifth
    hcyclotomic hformula_compressed hapow5.
exists e_omega; split; first exact: eomega_le.
split; first exact: hformula_compressed.
split; first exact: hdimWM.
split; first exact: hgalWN.
split; first exact: hcardWN.
split; first exact: hdimN.
exact: hpresentation.
Qed.

End DegreeFiveBaseChange.

(* -------------------------------------------------------------------- *)
(** * Mapping the actual rational F20 tower into a common ambient field *)

Section MappedF20CommonCompositum.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_irr : irreducible_poly p.
Let Canonical := numfield p.

Variable Ambient : splittingFieldType rat.
Variable h : 'AHom(Canonical, Ambient).

(** This theorem closes the formerly conditional F20-to-Kummer interface.
    Its only algebraic premise is solvability of the actual canonical
    quintic Galois group.  The F20 theorem constructs the original fixed
    field and exact index-two tower, including the exact rational Galois
    order and its normal order-five subgroup; [square_radical_tower_aimg]
    maps that generated tower along [h].  An arbitrary primitive fifth root
    [w] in the common ambient canonically produces the two displayed square
    radicals [s] and [t], so [w] belongs to their two-square field [W].
    Finally the proved degree-five base-change lemma constructs the terminal
    Kummer layer over the genuine compositum subfield. *)
Theorem lazard_mapped_solvable_F20_common_compositum
    (w : Ambient) :
  5.-primitive_root w ->
  solvable 'Gal({:Canonical} / 1%AS) ->
  exists (e : nat) (P : {group gal_of {:Canonical}})
      (W : {subfield Ambient}),
    e <= 2 /\
    #|'Gal({:Canonical} / 1%AS)| = (5 * 2 ^ e)%N /\
    #|P| = 5%N /\
    P <| 'Gal({:Canonical} / 1%AS) /\
    W = lazard_square_radical_fifth_root_field
      (1%AS : {subfield Ambient})
      (PF.lazard_primitive_fifth_root_square_s w)
      (PF.lazard_primitive_fifth_root_square_t w) /\
    T4.square_radical_tower (1%AS : {subfield Ambient}) 2 W /\
    T4.square_radical_tower (1%AS : {subfield Ambient}) e
      (h @: fixedField P) /\
    galois (h @: fixedField P) (h @: {:Canonical}) /\
    \dim_(h @: fixedField P) (h @: {:Canonical}) = 5%N /\
    w \in W /\
    T4.square_roots_and_fifth_root_presentation
      (1%AS : {subfield Ambient})
      ((h @: {:Canonical}) * ((h @: fixedField P) * W)%AS)%AS
      (2 + e).
Proof.
move=> wroot solGal.
have [e [P [ele2 [cardGal [cardP [normalP
    [hfieldTower [hgalFinal hdimFinal]]]]]]]] :=
  @F20T.quintic_fixedField_index_two_tower_of_solvable
    p p_size p_irr solGal.
have twoN0Canonical : (2%:R : Canonical) != 0.
  by rewrite -[2%:R](rmorph_nat (in_alg Canonical) 2) fmorph_eq0.
have twoN0Ambient : (2%:R : Ambient) != 0.
  by rewrite -[2%:R](rmorph_nat (in_alg Ambient) 2) fmorph_eq0.
have hformulaCanonical : T4.square_radical_tower
    (1%AS : {subfield Canonical}) e (fixedField P) :=
  T4.index_two_galois_tower_is_square
    twoN0Canonical hfieldTower.
have haimg1 :
    (h @: (1%AS : {subfield Canonical})) =
      (1%AS : {subfield Ambient}).
  apply: val_inj.
  exact: aimg1 h.
have hformulaMapped : T4.square_radical_tower
    (1%AS : {subfield Ambient}) e (h @: fixedField P).
  have hmapped := T4.square_radical_tower_aimg h hformulaCanonical.
  move: hmapped.
  by rewrite haimg1.
have hgalMapped : galois (h @: fixedField P) (h @: {:Canonical}).
  by rewrite galois_aimg.
have hdimMapped :
    \dim_(h @: fixedField P) (h @: {:Canonical}) = 5%N.
  move: hdimFinal.
  by rewrite !dim_aimg.
pose s := PF.lazard_primitive_fifth_root_square_s w.
pose t := PF.lazard_primitive_fifth_root_square_t w.
pose W := lazard_square_radical_fifth_root_field
  (1%AS : {subfield Ambient}) s t.
have hs : s ^+ 2 = 5%:R.
  exact: PF.lazard_primitive_fifth_root_square_sE wroot.
have ht : t ^+ 2 = - 10%:R - 2%:R * s.
  exact: PF.lazard_primitive_fifth_root_square_tE wroot.
have hcyclotomic : T4.square_radical_tower
    (1%AS : {subfield Ambient}) 2 W.
  exact: lazard_square_radical_fifth_root_field_is_two_square_tower_of_eq
    hs ht.
have wW : w \in W.
  rewrite -(PF.lazard_primitive_fifth_root_square_reconstruct
    twoN0Ambient w).
  exact: lazard_square_radical_fifth_root_mem
    (1%AS : {subfield Ambient}) s t.
have hpresentation :=
  lazard_two_square_base_change_terminal_kummer
    hcyclotomic hformulaMapped hgalMapped hdimMapped wroot wW.
exists e, P, W.
split; first exact: ele2.
split; first exact: cardGal.
split; first exact: cardP.
split; first exact: normalP.
split; first reflexivity.
split; first exact: hcyclotomic.
split; first exact: hformulaMapped.
split; first exact: hgalMapped.
split; first exact: hdimMapped.
split; first exact: wW.
exact: hpresentation.
Qed.

(** Refined mapped theorem with both exponents made explicit.  [e_Q] is
    extracted from the exact identity
    [#|Gal(Canonical/Q)| = 5 * 2^e_Q], returned together with the normal
    order-five subgroup [P]; [e_omega] is the exponent after base change to
    the field containing the primitive fifth root.  In particular, the
    absolute degree and the radical count use [e_omega], not the possibly
    redundant pre-base-change [e_Q]. *)
Theorem lazard_mapped_solvable_F20_common_compositum_compressed
    (w : Ambient) :
  5.-primitive_root w ->
  solvable 'Gal({:Canonical} / 1%AS) ->
  exists (e_Q e_omega : nat)
      (P : {group gal_of {:Canonical}})
      (W : {subfield Ambient}),
    e_Q <= 2 /\
    #|'Gal({:Canonical} / 1%AS)| = (5 * 2 ^ e_Q)%N /\
    #|P| = 5%N /\
    P <| 'Gal({:Canonical} / 1%AS) /\
    e_omega <= e_Q /\
    W = lazard_square_radical_fifth_root_field
      (1%AS : {subfield Ambient})
      (PF.lazard_primitive_fifth_root_square_s w)
      (PF.lazard_primitive_fifth_root_square_t w) /\
    \dim W = 4%N /\
    T4.square_radical_tower (1%AS : {subfield Ambient}) 2 W /\
    T4.square_radical_tower (1%AS : {subfield Ambient}) e_Q
      (h @: fixedField P) /\
    T4.square_radical_tower W e_omega
      ((h @: fixedField P) * W)%AS /\
    \dim_W ((h @: fixedField P) * W)%AS = 2 ^ e_omega /\
    galois (h @: fixedField P) (h @: {:Canonical}) /\
    \dim_(h @: fixedField P) (h @: {:Canonical}) = 5%N /\
    galois W
      ((h @: {:Canonical}) * ((h @: fixedField P) * W)%AS)%AS /\
    #|'Gal(
      ((h @: {:Canonical}) * ((h @: fixedField P) * W)%AS)%AS / W)| =
      5 * 2 ^ e_omega /\
    \dim
      ((h @: {:Canonical}) * ((h @: fixedField P) * W)%AS)%AS =
      5 * 2 ^ (2 + e_omega) /\
    w \in W /\
    T4.square_roots_and_fifth_root_presentation
      (1%AS : {subfield Ambient})
      ((h @: {:Canonical}) * ((h @: fixedField P) * W)%AS)%AS
      (2 + e_omega).
Proof.
move=> wroot solGal.
have [e_Q [P [W [eQle2 [cardGal [cardP [normalP
    [hW [hcyclotomic [hformula
      [hgalFinal [hdimFinal [wW hpresentation_Q]]]]]]]]]]]]] :=
  lazard_mapped_solvable_F20_common_compositum wroot solGal.
have hdimW : \dim W = 4%N :=
  primitive_fifth_root_two_square_field_dim hcyclotomic wroot wW.
have haimg1 :
    (h @: (1%AS : {subfield Canonical})) =
      (1%AS : {subfield Ambient}).
  apply: val_inj.
  exact: aimg1 h.
have hgalMappedBase :
    galois (1%AS : {subfield Ambient}) (h @: {:Canonical}).
  have hmapped :
      galois (h @: (1%AS : {subfield Canonical}))
        (h @: {:Canonical}).
    by rewrite galois_aimg; exact: galois_numfield p.
  move: hmapped.
  by rewrite haimg1.
have [e_omega [eomegale [hformula_omega [hdimFormulaOmega
    [hgalOmega [hcardOmega [hdimTop hpresentationOmega]]]]]]] :=
  lazard_two_square_base_change_terminal_kummer_compressed
    hcyclotomic hformula hdimW hgalMappedBase hgalFinal hdimFinal
    wroot wW.
exists e_Q, e_omega, P, W.
split; first exact: eQle2.
split; first exact: cardGal.
split; first exact: cardP.
split; first exact: normalP.
split; first exact: eomegale.
split; first exact: hW.
split; first exact: hdimW.
split; first exact: hcyclotomic.
split; first exact: hformula.
split; first exact: hformula_omega.
split; first exact: hdimFormulaOmega.
split; first exact: hgalFinal.
split; first exact: hdimFinal.
split; first exact: hgalOmega.
split; first exact: hcardOmega.
split; first exact: hdimTop.
split; first exact: wW.
exact: hpresentationOmega.
Qed.

End MappedF20CommonCompositum.

(* -------------------------------------------------------------------- *)
(** * The explicit primitive root at the F20 terminal layer *)

Section CommonAmbientTerminalKummer.

Variable L : fieldExtType rat.
Implicit Types (B M N : {subfield L}).

(** Correct common-ambient endpoint for the paper's [d+e] count.

    The explicit equations give the two cyclotomic square adjunctions from
    [B] to [W].  A caller supplies the *base-changed* F20 fixed-field tower
    from [W] to [M].  The final degree-five Galois layer is then cyclic, and
    the explicit primitive fifth root in [W <= M] lets Hilbert--90 construct
    a genuine fifth-root generator.  Thus no presentation is inferred from
    degree alone. *)
Theorem lazard_cyclotomic_F20_terminal_kummer_presentation
    (B M N : {subfield L}) (e : nat) (s t : L)
    (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s)
    (hfieldTower :
      T4.index_two_galois_tower
        (lazard_square_radical_fifth_root_field B s t) e M)
    (hgalFinal : galois M N)
    (hdimFinal : \dim_M N = 5%N) :
  T4.square_roots_and_fifth_root_presentation B N (2 + e).
Proof.
have twoN0 : (2%:R : L) != 0.
  by rewrite -[2%:R](rmorph_nat (in_alg L) 2) fmorph_eq0.
have fiveN0 : (5%:R : L) != 0.
  by rewrite -[5%:R](rmorph_nat (in_alg L) 5) fmorph_eq0.
have hcyclotomic : T4.square_radical_tower B 2
    (lazard_square_radical_fifth_root_field B s t).
  exact: lazard_square_radical_fifth_root_field_is_two_square_tower_of_eq
    hs ht.
have hformula : T4.square_radical_tower
    (lazard_square_radical_fifth_root_field B s t) e M.
  exact: T4.index_two_galois_tower_is_square twoN0 hfieldTower.
pose w := PF.lazard_square_radical_fifth_root s t.
have wroot : 5.-primitive_root w.
  exact: (PF.lazard_square_radical_fifth_root_primitive
    twoN0 fiveN0 hs ht).
have wcyclotomic :
    w \in lazard_square_radical_fifth_root_field B s t.
  exact: lazard_square_radical_fifth_root_mem B s t.
have hWM :
    (lazard_square_radical_fifth_root_field B s t <= M)%VS.
  exact: T4.index_two_galois_tower_terminal_sub hfieldTower.
have wM : w \in M := hWM wcyclotomic.
have hcyclic : cyclic 'Gal(N / M).
  apply/prime_cyclic.
  by rewrite galois_dim // hdimFinal.
have wrootdim : (\dim_M N).-primitive_root w.
  by rewrite hdimFinal.
have [a [_ _ hapow hN]] :=
  KG.cyclic_kummer_generator wrootdim wM hgalFinal hcyclic.
have hapow5 : a ^+ 5 \in M by rewrite -hdimFinal.
rewrite hN.
exact: T4.two_square_towers_then_fifth
  hcyclotomic hformula hapow5.
Qed.

End CommonAmbientTerminalKummer.

Section F20TerminalKummer.

Variable p : {poly rat}.
Let L := numfield p.

(** This is the narrow composition missing from the F20 fixed-field output.
    The subgroup tower supplies the exact square steps and the genuine
    degree-five Galois layer.  The two displayed square equations construct
    the primitive fifth root used by Kummer theory.

    The containment hypothesis is not cosmetic: a rational quintic
    splitting field need not contain a primitive fifth root.  It says
    precisely that the explicitly constructed cyclotomic two-square field
    lies in the terminal fixed field. *)
Theorem lazard_F20_terminal_kummer_of_explicit_primitive_root
    (e : nat) (P : {group gal_of {:L}})
    (hfieldTower :
      T4.index_two_galois_tower 1%AS e (fixedField P))
    (hgalFinal : galois (fixedField P) {:L})
    (hdimFinal : \dim_(fixedField P) {:L} = 5%N)
    (s t : L)
    (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s)
    (hcyclotomic :
      (lazard_square_radical_fifth_root_field 1%AS s t <=
        fixedField P)%VS) :
  T4.square_roots_and_fifth_root_presentation 1%AS {:L} e.
Proof.
have twoN0 : (2%:R : L) != 0.
  by rewrite -[2%:R](rmorph_nat (in_alg L) 2) fmorph_eq0.
have fiveN0 : (5%:R : L) != 0.
  by rewrite -[5%:R](rmorph_nat (in_alg L) 5) fmorph_eq0.
pose w := PF.lazard_square_radical_fifth_root s t.
have wroot : 5.-primitive_root w.
  exact: (PF.lazard_square_radical_fifth_root_primitive
    twoN0 fiveN0 hs ht).
have wcyclotomic :
    w \in lazard_square_radical_fifth_root_field 1%AS s t.
  exact: lazard_square_radical_fifth_root_mem 1%AS s t.
have wfixed : w \in fixedField P := hcyclotomic wcyclotomic.
exact: (F20T.quintic_fixedField_terminal_fifth_kummer
  (p := p) hfieldTower hgalFinal hdimFinal wroot wfixed).
Qed.

End F20TerminalKummer.

Section FormulaComposition.

Variables (F0 : fieldType) (L : fieldExtType F0).

(** All coefficient-side membership data can be transported from the bottom
    field to any larger field. *)
Lemma lazard_radical_invariant_data_in_mono
    (B C : {subfield L})
    (c : CRT.RP.LazardDepressedRootCoefficients L)
    (i : CRT.RP.LazardRootInvariants L)
    (D Finvariant G H I J K : L) :
  (B <= C)%VS ->
  CRT.lazard_radical_invariant_data_in B c i
    D Finvariant G H I J K ->
  CRT.lazard_radical_invariant_data_in C c i
    D Finvariant G H I J K.
Proof.
move=> hBC hdata; constructor.
- exact: hBC (CRT.lazard_D_in_base hdata).
- exact: hBC (CRT.lazard_E_in_base hdata).
- exact: hBC (CRT.lazard_F_in_base hdata).
- exact: hBC (CRT.lazard_G_in_base hdata).
- exact: hBC (CRT.lazard_H_in_base hdata).
- exact: hBC (CRT.lazard_I_in_base hdata).
- exact: hBC (CRT.lazard_J_in_base hdata).
- exact: hBC (CRT.lazard_K_in_base hdata).
Qed.

(** The displayed formula field, based after the two cyclotomic square
    adjunctions. *)
Definition lazard_combined_formula_field
    (B : {subfield L}) (s t : L)
    (c : CRT.RP.LazardDepressedRootCoefficients L)
    (i : CRT.RP.LazardRootInvariants L)
    (D Finvariant G H I J K : L)
    (d : CRT.lazard_radical_certificate c i
      D Finvariant G H I J K) : {subfield L} :=
  CRT.lazard_certificate_generated_field
    (lazard_square_radical_fifth_root_field B s t) d.

(** Two cyclotomic square adjunctions followed by the formula's two square
    adjunctions and its final fifth-root adjunction give the exact
    four-square/one-fifth presentation. *)
Theorem lazard_combined_formula_field_has_four_square_fifth_presentation
    (B : {subfield L}) (s t : L)
    (c : CRT.RP.LazardDepressedRootCoefficients L)
    (i : CRT.RP.LazardRootInvariants L)
    (D Finvariant G H I J K : L)
    (d : CRT.lazard_radical_certificate c i
      D Finvariant G H I J K)
    (hs : s ^+ 2 \in B)
    (ht : t ^+ 2 \in <<B; s>>%AS)
    (hdata : CRT.lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K) :
  @T4.square_roots_and_fifth_root_presentation F0 L B
    (lazard_combined_formula_field B s t d) 4.
Proof.
have hcyclotomic :=
  lazard_square_radical_fifth_root_field_is_two_square_tower hs ht.
have hbase := lazard_base_le_square_radical_fifth_root_field B s t.
have hdata' := lazard_radical_invariant_data_in_mono hbase hdata.
have hpresentation :=
  CRT.lazard_certificate_generated_field_has_two_square_fifth_presentation
    d hdata'.
case: hpresentation=> M hformula p hp hfield.
rewrite /lazard_combined_formula_field hfield.
exact: (T4.two_square_towers_then_fifth hcyclotomic hformula hp).
Qed.

(** Equation-shaped version used by the primitive-root construction. *)
Theorem lazard_combined_formula_field_has_four_square_fifth_presentation_of_eq
    (B : {subfield L}) (s t : L)
    (c : CRT.RP.LazardDepressedRootCoefficients L)
    (i : CRT.RP.LazardRootInvariants L)
    (D Finvariant G H I J K : L)
    (d : CRT.lazard_radical_certificate c i
      D Finvariant G H I J K)
    (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s)
    (hdata : CRT.lazard_radical_invariant_data_in B c i
      D Finvariant G H I J K) :
  @T4.square_roots_and_fifth_root_presentation F0 L B
    (lazard_combined_formula_field B s t d) 4.
Proof.
apply: lazard_combined_formula_field_has_four_square_fifth_presentation hdata.
- by rewrite hs rpred_nat.
- rewrite ht.
  apply: rpredB.
  + exact: rpredN (rpred_nat _ _).
  + exact: rpredM (rpred_nat _ _) memv_adjoin.
Qed.

End FormulaComposition.

Print Assumptions lazard_square_radical_fifth_root_field_is_two_square_tower.
Print Assumptions
  lazard_square_radical_fifth_root_field_is_two_square_tower_of_eq.
Print Assumptions lazard_square_radical_fifth_root_mem.
Print Assumptions irreducible_monic_root_eq_minPoly_rat.
Print Assumptions primitive_fifth_root_adjoin_dim.
Print Assumptions primitive_fifth_root_two_square_field_dim.
Print Assumptions galois_degree_five_prodvr_of_dim_le_four.
Print Assumptions lazard_two_square_base_change_terminal_kummer.
Print Assumptions
  lazard_two_square_base_change_terminal_kummer_compressed.
Print Assumptions lazard_mapped_solvable_F20_common_compositum.
Print Assumptions
  lazard_mapped_solvable_F20_common_compositum_compressed.
Print Assumptions
  lazard_F20_terminal_kummer_of_explicit_primitive_root.
Print Assumptions
  lazard_cyclotomic_F20_terminal_kummer_presentation.
Print Assumptions
  lazard_combined_formula_field_has_four_square_fifth_presentation.
Print Assumptions
  lazard_combined_formula_field_has_four_square_fifth_presentation_of_eq.

End PolynomialFormulasLazardQuinticPrimitiveFifthRootTower.
