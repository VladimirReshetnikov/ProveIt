From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import char0 abel.
From PolynomialFormulas Require Import
  QuinticF20Data QuinticThetaValues QuinticGaloisAction
  QuinticRecursiveFactor QuinticPaddedSymmetrization
  SexticRecursiveCore SexticNewtonPowerSums
  SexticComputedResolvents SexticVietaBridge
  QuinticCanonicalDecision
  LazardQuinticRootRadicals LazardQuinticRootProjections
  LazardQuinticRootFourierNumeratorRing
  LazardQuinticInvariantDescentF20.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Nonvanishing of Lazard's epsilon on the selected canonical ordering.

    The root-level epsilon theorem reduces a zero epsilon factor to the
    cubic equation

      [5 x^3 + 4 p x + 8 q = 0].

    For an irreducible rational quintic this equation is impossible for
    every selected root: its minimal polynomial has degree five, whereas
    the displayed obstruction has degree three.  Thus the cubic premise of
    the root-level theorem is derived here from irreducibility, rather than
    exposed as a certificate hypothesis. *)
Module PolynomialFormulasLazardQuinticCanonicalEpsilonNonzero.

Import GRing.Theory.
Import Num.Theory.
Import PolynomialFormulasQuinticF20Data.
Module TV := PolynomialFormulasQuinticThetaValues.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module QPS := PolynomialFormulasQuinticPaddedSymmetrization.
Module SNP := PolynomialFormulasSexticNewtonPowerSums.
Module SCV := PolynomialFormulasSexticComputedResolvents.
Module SVB := PolynomialFormulasSexticVietaBridge.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module NR := PolynomialFormulasLazardQuinticRootFourierNumeratorRing.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.

Local Open Scope group_scope.
Local Open Scope ring_scope.

Section GenericVieta.

Variable F : fieldType.

Add Ring lazard_canonical_epsilon_ring :
  (@NR.lazard_numerator_ring_theory F).
Opaque NR.lazard_numerator_ring_zero NR.lazard_numerator_ring_one
  NR.lazard_numerator_ring_add NR.lazard_numerator_ring_mul
  NR.lazard_numerator_ring_sub NR.lazard_numerator_ring_opp
  NR.lazard_numerator_ring_eq.

Ltac finish_lazard_canonical_epsilon_ring :=
  repeat first
    [ rewrite NR.lazard_numerator_ring_addE
    | rewrite NR.lazard_numerator_ring_mulE
    | rewrite NR.lazard_numerator_ring_subE
    | rewrite NR.lazard_numerator_ring_oppE
    | rewrite NR.lazard_numerator_ring_zeroE
    | rewrite NR.lazard_numerator_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (NR.lazard_numerator_ring_eq lhs rhs)
  end;
  ring.

(** Padding a five-tuple by zero contributes exactly the factor [X]. *)
Lemma lazard_prod_XsubC_pad_quintic (roots : 5.-tuple F) :
  \prod_(r <- QPS.pad_quintic_roots roots) ('X - r%:P : {poly F}) =
    ('X * \prod_(r <- roots) ('X - r%:P : {poly F}))%R.
Proof.
rewrite -(map_tnth_enum (QPS.pad_quintic_roots roots)) big_map big_enum.
rewrite -(map_tnth_enum roots) big_map big_enum.
rewrite !big_ord_recl !big_ord0.
rewrite /QPS.pad_quintic_roots !tnth_mktuple /=.
have h0 : (inord 0 : 'I_5) = ord0.
  apply: val_inj; exact: (@inordK 4 0 isT).
have h1 : (inord (bump 0 0) : 'I_5) = lift ord0 ord0.
  apply: val_inj; exact: (@inordK 4 1 isT).
have h2 : (inord (bump 0 (bump 0 0)) : 'I_5) =
    lift ord0 (lift ord0 ord0).
  apply: val_inj; exact: (@inordK 4 2 isT).
have h3 : (inord (bump 0 (bump 0 (bump 0 0))) : 'I_5) =
    lift ord0 (lift ord0 (lift ord0 ord0)).
  apply: val_inj; exact: (@inordK 4 3 isT).
have h4 : (inord (bump 0 (bump 0 (bump 0 (bump 0 0)))) : 'I_5) =
    lift ord0 (lift ord0 (lift ord0 (lift ord0 ord0))).
  apply: val_inj; exact: (@inordK 4 4 isT).
rewrite h0 h1 h2 h3 h4 subr0 !mulr1.
rewrite [(_ * 'X)]mulrC.
do 4! rewrite [(_ * ('X * _))]mulrCA.
reflexivity.
Qed.

(** A permutation changes neither the characteristic linear-factor
    product nor, consequently, the Vieta coordinates. *)
Lemma lazard_prod_XsubC_permute_quintic
    (roots : 5.-tuple F) (s : S5) :
  \prod_(r <- TV.permute_quintic_roots s roots)
      ('X - r%:P : {poly F}) =
    \prod_(r <- roots) ('X - r%:P : {poly F}).
Proof.
rewrite -(map_tnth_enum (TV.permute_quintic_roots s roots)) big_map big_enum.
rewrite -(map_tnth_enum roots) big_map big_enum.
under [LHS]eq_bigr=> k _ do rewrite TV.tnth_permute_quintic_roots.
rewrite (reindex_inj (@perm_inj _ (s^-1)%g)) /=.
under [LHS]eq_bigr=> k _ do rewrite permKV.
reflexivity.
Qed.

(** The second and third elementary coordinates of a zero-padded tuple are
    the explicit five-root expressions used by Lazard's formulas. *)
Lemma lazard_root_esymm_pad_quintic_ord1 (roots : 5.-tuple F) :
  SNP.root_esymm (QPS.pad_quintic_roots roots) (inord 1) =
    RP.lazard_root_esymm2 roots.
Proof.
rewrite /SNP.root_esymm SNP.six_indicesE /=.
have h0 : (inord 0 : 'I_6) = widen_ord (leqnSn 5) o0.
  apply: val_inj; exact: (@inordK 5 0 isT).
have h1 : (inord 1 : 'I_6) = widen_ord (leqnSn 5) o1.
  apply: val_inj; exact: (@inordK 5 1 isT).
have h2 : (inord 2 : 'I_6) = widen_ord (leqnSn 5) o2.
  apply: val_inj; exact: (@inordK 5 2 isT).
have h3 : (inord 3 : 'I_6) = widen_ord (leqnSn 5) o3.
  apply: val_inj; exact: (@inordK 5 3 isT).
have h4 : (inord 4 : 'I_6) = widen_ord (leqnSn 5) o4.
  apply: val_inj; exact: (@inordK 5 4 isT).
have h5 : (inord 5 : 'I_6) = ord_max.
  apply: val_inj; exact: (@inordK 5 5 isT).
rewrite h0 h1 h2 h3 h4 h5
  !QPS.tnth_pad_quintic_roots_in
  QPS.tnth_pad_quintic_roots_last
  /RP.lazard_root_esymm2.
have hinord1 : nat_of_ord (inord 1 : 'I_6) = 1%N.
  exact: (@inordK 5 1 isT).
rewrite -h1 hinord1 /=.
finish_lazard_canonical_epsilon_ring.
Qed.

Lemma lazard_root_esymm_pad_quintic_ord2 (roots : 5.-tuple F) :
  SNP.root_esymm (QPS.pad_quintic_roots roots) (inord 2) =
    RP.lazard_root_esymm3 roots.
Proof.
rewrite /SNP.root_esymm SNP.six_indicesE /=.
have h0 : (inord 0 : 'I_6) = widen_ord (leqnSn 5) o0.
  apply: val_inj; exact: (@inordK 5 0 isT).
have h1 : (inord 1 : 'I_6) = widen_ord (leqnSn 5) o1.
  apply: val_inj; exact: (@inordK 5 1 isT).
have h2 : (inord 2 : 'I_6) = widen_ord (leqnSn 5) o2.
  apply: val_inj; exact: (@inordK 5 2 isT).
have h3 : (inord 3 : 'I_6) = widen_ord (leqnSn 5) o3.
  apply: val_inj; exact: (@inordK 5 3 isT).
have h4 : (inord 4 : 'I_6) = widen_ord (leqnSn 5) o4.
  apply: val_inj; exact: (@inordK 5 4 isT).
have h5 : (inord 5 : 'I_6) = ord_max.
  apply: val_inj; exact: (@inordK 5 5 isT).
rewrite h0 h1 h2 h3 h4 h5
  !QPS.tnth_pad_quintic_roots_in
  QPS.tnth_pad_quintic_roots_last
  /RP.lazard_root_esymm3.
have hinord2 : nat_of_ord (inord 2 : 'I_6) = 2%N.
  exact: (@inordK 5 2 isT).
rewrite -h2 hinord2 /=.
finish_lazard_canonical_epsilon_ring.
Qed.

End GenericVieta.

Section CanonicalNonvanishing.

Variable f : QRF.monic_quintic.
Let p := CD.rational_monic_quintic f.
Let p_size : size p = 6%N := CD.size_rational_monic_quintic f.
Let L := numfield p.
Let roots : 5.-tuple L := @GA.quintic_root_tuple p p_size.

(** The canonical input is depressed precisely when its first elementary
    coordinate (equivalently, the negative [X^4] coefficient) is zero. *)
Definition lazard_canonical_quintic_depressed : Prop :=
  tnth (SCV.monic_elementary_values
    (QRF.quintic_sextic_embedding f)) ord0 = 0.

Definition lazard_canonical_depressed_p : rat :=
  ((tnth (SCV.monic_elementary_values
    (QRF.quintic_sextic_embedding f)) (inord 1))%:~R : rat).

Definition lazard_canonical_depressed_q : rat :=
  - ((tnth (SCV.monic_elementary_values
    (QRF.quintic_sextic_embedding f)) (inord 2))%:~R : rat).

Lemma lazard_selected_quintic_padded_factorization (i : 'I_6) :
  map_poly (intr : int -> L)
      (PolynomialFormulasSexticRecursiveCore.monic_polynomial
        (QRF.quintic_sextic_embedding f)) =
    \prod_(r <- QPS.pad_quintic_roots (ID.lazard_selected_roots f i))
      ('X - r%:P : {poly L}).
Proof.
rewrite lazard_prod_XsubC_pad_quintic.
rewrite /ID.lazard_selected_roots
  lazard_prod_XsubC_permute_quintic.
rewrite -CD.prod_XsubC_pad_quintic_roots.
exact: CD.canonical_quintic_padded_factorization.
Qed.

Lemma lazard_selected_quintic_padded_vieta (i : 'I_6) :
  @SCV.cast_int_values L
      (SCV.monic_elementary_values (QRF.quintic_sextic_embedding f)) =
    SNP.elementary_values
      (QPS.pad_quintic_roots (ID.lazard_selected_roots f i)).
Proof.
apply: SVB.monic_sextic_vieta.
exact: lazard_selected_quintic_padded_factorization.
Qed.

Lemma lazard_selected_root_esymm1E (i : 'I_6) :
  RP.lazard_root_esymm1 (ID.lazard_selected_roots f i) =
    (@ratr L)
      ((tnth (SCV.monic_elementary_values
        (QRF.quintic_sextic_embedding f)) ord0)%:~R : rat).
Proof.
have hv := congr1 (fun values : 6.-tuple L => tnth values ord0)
  (lazard_selected_quintic_padded_vieta i).
rewrite /SCV.cast_int_values tnth_mktuple
  SNP.tnth_elementary_values CD.root_esymm_pad_quintic_ord0
  /RP.lazard_root_esymm1 in hv.
rewrite ratr_int.
exact: esym hv.
Qed.

Lemma lazard_selected_root_esymm2E (i : 'I_6) :
  RP.lazard_root_esymm2 (ID.lazard_selected_roots f i) =
    (@ratr L) lazard_canonical_depressed_p.
Proof.
have hv := congr1 (fun values : 6.-tuple L => tnth values (inord 1))
  (lazard_selected_quintic_padded_vieta i).
rewrite /SCV.cast_int_values tnth_mktuple
  SNP.tnth_elementary_values lazard_root_esymm_pad_quintic_ord1 in hv.
rewrite /lazard_canonical_depressed_p ratr_int.
exact: esym hv.
Qed.

Lemma lazard_selected_root_esymm3E (i : 'I_6) :
  RP.lazard_root_esymm3 (ID.lazard_selected_roots f i) =
    (@ratr L)
      ((tnth (SCV.monic_elementary_values
        (QRF.quintic_sextic_embedding f)) (inord 2))%:~R : rat).
Proof.
have hv := congr1 (fun values : 6.-tuple L => tnth values (inord 2))
  (lazard_selected_quintic_padded_vieta i).
rewrite /SCV.cast_int_values tnth_mktuple
  SNP.tnth_elementary_values lazard_root_esymm_pad_quintic_ord2 in hv.
rewrite ratr_int.
exact: esym hv.
Qed.

Lemma lazard_selected_root_esymm1_zero
    (hdepressed : lazard_canonical_quintic_depressed) (i : 'I_6) :
  RP.lazard_root_esymm1 (ID.lazard_selected_roots f i) = 0.
Proof.
rewrite lazard_selected_root_esymm1E.
rewrite /lazard_canonical_quintic_depressed in hdepressed.
by rewrite hdepressed ratr_int.
Qed.

Lemma lazard_selected_root_pE (i : 'I_6) :
  RP.lazard_root_p
      (RP.lazard_depressed_of_roots (ID.lazard_selected_roots f i)) =
    (@ratr L) lazard_canonical_depressed_p.
Proof.
exact: lazard_selected_root_esymm2E.
Qed.

Lemma lazard_selected_root_qE (i : 'I_6) :
  RP.lazard_root_q
      (RP.lazard_depressed_of_roots (ID.lazard_selected_roots f i)) =
    (@ratr L) lazard_canonical_depressed_q.
Proof.
rewrite /RP.lazard_depressed_of_roots /=
  /lazard_canonical_depressed_q
  -(char0_ratrE (char_numfield p)) rmorphN
  lazard_selected_root_esymm3E.
reflexivity.
Qed.

(** The rational cubic forced by a zero epsilon factor. *)
Definition lazard_cubic_obstruction (p0 q0 : rat) : {poly rat} :=
  (5%:R : rat) *: 'X^3 +
    ((4%:R : rat) * p0) *: 'X +
    (((8%:R : rat) * q0)%:P).

Lemma lazard_size_poly_from_top_coefficient
    (g : {poly rat}) (n : nat)
    (hnz : g`_n != 0)
    (habove : forall j : nat, (n < j)%N -> g`_j = 0) :
  size g = n.+1.
Proof.
have hle : (size g <= n.+1)%N.
  apply/leq_sizeP=> j hj.
  exact: habove j hj.
have hnotle : ~~ (size g <= n)%N.
  apply/negP=> hlen.
  have hz : g`_n = 0 := (elimT (leq_sizeP g n) hlen n (leqnn n)).
  by move: hnz; rewrite hz eqxx.
have hlt : (n < size g)%N by rewrite ltnNge hnotle.
apply/eqP; rewrite eqn_leq.
exact/andP.
Qed.

Lemma lazard_cubic_obstruction_size p0 q0 :
  size (lazard_cubic_obstruction p0 q0) = 4%N.
Proof.
apply: (lazard_size_poly_from_top_coefficient (n := 3%N)).
- rewrite /lazard_cubic_obstruction.
  rewrite !coefD !coefZ !coefXn !coefX !coefC /=
    ?mulr0 ?addr0.
  by rewrite mulr1 pnatr_eq0.
- move=> j; case: j => [|[|[|[|j]]]] // _.
  rewrite /lazard_cubic_obstruction.
  by rewrite !coefD !coefZ !coefXn !coefX !coefC /=
    ?mulr0 ?addr0.
Qed.

Lemma lazard_cubic_obstruction_horner
    (p0 q0 : rat) (x : L) :
  (map_poly (@ratr L) (lazard_cubic_obstruction p0 q0)).[x] =
    5%:R * x ^+ 3 + 4%:R * (@ratr L) p0 * x +
      8%:R * (@ratr L) q0.
Proof.
rewrite -(char0_ratrE (char_numfield p)).
rewrite /lazard_cubic_obstruction.
rewrite !rmorphD /=.
rewrite !map_polyZ !map_polyXn !map_polyX !map_polyC.
rewrite !hornerD !hornerZ !hornerXn !hornerX !hornerC.
change
  ((char0_ratr (char_numfield p)) (5%:R : rat) * x ^+ 3 +
   (char0_ratr (char_numfield p)) ((4%:R : rat) * p0) * x +
   (char0_ratr (char_numfield p)) ((8%:R : rat) * q0) =
   (5%:R : L) * x ^+ 3 +
   (4%:R : L) * (char0_ratr (char_numfield p)) p0 * x +
   (8%:R : L) * (char0_ratr (char_numfield p)) q0).
by rewrite !rmorphM !rmorph_nat.
Qed.

(** Degree five cannot share a selected canonical root with Lazard's
    degree-three obstruction. *)
Theorem lazard_selected_cubic_obstruction_neq0
    (p_irr : irreducible_poly p) (i : 'I_6) (k : 'I_5) :
  5%:R * tnth (ID.lazard_selected_roots f i) k ^+ 3 +
      4%:R * (@ratr L) lazard_canonical_depressed_p *
        tnth (ID.lazard_selected_roots f i) k +
      8%:R * (@ratr L) lazard_canonical_depressed_q != 0.
Proof.
pose g := lazard_cubic_obstruction
  lazard_canonical_depressed_p lazard_canonical_depressed_q.
pose x := tnth (ID.lazard_selected_roots f i) k.
apply/eqP=> hzero.
have xmem : x \in @GA.quintic_root_seq p.
  rewrite /x /ID.lazard_selected_roots
    TV.tnth_permute_quintic_roots.
  exact: mem_tnth.
have hgroot : root
    (map_poly (char0_ratr (char_numfield p)) g) x.
  by rewrite rootE /g lazard_cubic_obstruction_horner hzero eqxx.
have hover : map_poly (char0_ratr (char_numfield p)) g
    \is a polyOver 1%AS.
  apply/polyOver1P; exists g; apply: eq_map_poly=> a.
  by rewrite in_algE alg_num_field.
have hdiv : minPoly 1%VS x %|
    map_poly (char0_ratr (char_numfield p)) g :=
  minPoly_dvdp hover hgroot.
have hg0 : map_poly (char0_ratr (char_numfield p)) g != 0.
  by rewrite -size_poly_eq0 size_map_poly /g
    lazard_cubic_obstruction_size.
have hle := dvdp_leq hg0 hdiv.
have hmin := @GA.quintic_minPoly_root p p_size p_irr x xmem.
move: hle.
rewrite (eqp_size hmin) -(char0_ratrE (char_numfield p)).
by rewrite !size_map_poly p_size /g
  lazard_cubic_obstruction_size.
Qed.

(** The same obstruction, with [p] and [q] read directly from the selected
    root tuple as required by the root-level epsilon theorem. *)
Theorem lazard_selected_root_cubic_obstruction_neq0
    (p_irr : irreducible_poly p) (i : 'I_6) (k : 'I_5) :
  5%:R * tnth (ID.lazard_selected_roots f i) k ^+ 3 +
      4%:R * RP.lazard_root_p
        (RP.lazard_depressed_of_roots (ID.lazard_selected_roots f i)) *
        tnth (ID.lazard_selected_roots f i) k +
      8%:R * RP.lazard_root_q
        (RP.lazard_depressed_of_roots (ID.lazard_selected_roots f i)) != 0.
Proof.
rewrite lazard_selected_root_pE lazard_selected_root_qE.
exact: lazard_selected_cubic_obstruction_neq0.
Qed.

(** No cubic-obstruction certificate is required: irreducibility and the
    canonical depressed coefficient relation discharge it. *)
Theorem lazard_selected_epsilon_product_neq0
    (p_irr : irreducible_poly p)
    (hdepressed : lazard_canonical_quintic_depressed) (i : 'I_6) :
  RR.lazard_epsilon_product (ID.lazard_selected_roots f i) != 0.
Proof.
pose c := RP.lazard_depressed_of_roots (ID.lazard_selected_roots f i).
apply: (@RR.lazard_epsilon_product_neq0 L
  (ID.lazard_selected_roots f i)
  (RP.lazard_root_p c) (RP.lazard_root_q c)).
- move: (lazard_selected_root_esymm1_zero hdepressed i).
  by rewrite /RP.lazard_root_esymm1.
- by rewrite /c /RP.lazard_depressed_of_roots /=.
- by rewrite /c /RP.lazard_depressed_of_roots /= opprK.
- exact: lazard_selected_root_cubic_obstruction_neq0 p_irr i.
Qed.

Lemma lazard_primitive_fifth_discriminant_factor_neq0
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  RR.lazard_fifth_root_discriminant_factor omega != 0.
Proof.
apply/eqP=> hzero.
have hcyclo := RR.lazard_primitive_fifth_root_cyclotomic omega_primitive.
have hsquare :=
  RR.lazard_fifth_root_discriminant_factor_sq_of_cyclotomic hcyclo.
rewrite hzero expr2 mul0r in hsquare.
have hfive : (5%:R : L) != 0.
  rewrite -[5%:R](rmorph_nat (char0_ratr (char_numfield p)) 5).
  by rewrite fmorph_eq0 pnatr_eq0.
by move: hfive; rewrite -hsquare eqxx.
Qed.

(** The complete selected-root epsilon, including its primitive-fifth-root
    coefficient, is nonzero without any supplied nonvanishing certificate. *)
Theorem lazard_selected_root_epsilon_neq0
    (p_irr : irreducible_poly p)
    (hdepressed : lazard_canonical_quintic_depressed)
    (i : 'I_6) (omega : L)
    (omega_primitive : 5.-primitive_root omega) :
  RP.lazard_root_epsilon omega (ID.lazard_selected_roots f i) != 0.
Proof.
rewrite /RP.lazard_root_epsilon.
apply: mulf_neq0.
- change (RR.lazard_fifth_root_discriminant_factor omega != 0).
  exact: lazard_primitive_fifth_discriminant_factor_neq0 omega_primitive.
- change (RR.lazard_epsilon_product (ID.lazard_selected_roots f i) != 0).
  exact: lazard_selected_epsilon_product_neq0 p_irr hdepressed i.
Qed.

End CanonicalNonvanishing.

End PolynomialFormulasLazardQuinticCanonicalEpsilonNonzero.
