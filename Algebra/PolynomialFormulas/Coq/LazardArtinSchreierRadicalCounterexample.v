From HB Require Import structures.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import abel.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** * An Artin--Schreier obstruction to ordinary radical towers

    Let [k] be an algebraic closure of [F_3], let [K = k(t)], and consider

                         [X^3 - X - t].

    The polynomial is separable and irreducible.  Its splitting extension is
    cyclic of degree three, but no root belongs to a tower obtained by
    adjoining elements whose ordinary prime powers lie in the preceding
    field.  In particular it is not solvable by [radical] in the literal
    sense used by MathComp--Abel and by Lazard's Definition 1.

    The final package below constructs the constant field, rational-function
    field, polynomial, splitting field, and root internally.  It accepts no
    irreducibility, Galois, or non-radicality certificate from its caller. *)
Module PolynomialFormulasLazardArtinSchreierRadicalCounterexample.

Import GRing.Theory.

Local Open Scope ring_scope.

(** Transport a reflected proposition across an explicit Boolean equality. *)
Lemma is_true_of_eq (a b : bool) : a = b -> b -> a.
Proof. by move=> ->. Qed.

(**************************************************************************)
(** * Algebraically closed constants and the rational function field *)

Definition artin_schreier_constant_package :=
  countable_algebraic_closure 'F_3.

Definition artin_schreier_constants : countClosedFieldType :=
  tag artin_schreier_constant_package.

Definition artin_schreier_F3_embedding :
    {rmorphism 'F_3 -> artin_schreier_constants} :=
  tag (tagged artin_schreier_constant_package).

Local Notation k := artin_schreier_constants.
Local Notation K := {fraction {poly k}}.
Local Notation "p %:K" :=
  (@FracField.tofrac {poly k} p)
  (at level 2, format "p %:K").

Definition artin_schreier_constant_to_function : {rmorphism k -> K} :=
  (@FracField.tofrac {poly k}) \o polyC.

Definition artin_schreier_parameter : K := ('X : {poly k})%:K.

Lemma artin_schreier_constants_pchar_three : 3 \in [pchar k].
Proof.
exact: (rmorph_pchar artin_schreier_F3_embedding (@pchar_Fp 3 isT)).
Qed.

Lemma artin_schreier_function_pchar_three : 3 \in [pchar K].
Proof.
exact: (rmorph_pchar artin_schreier_constant_to_function
  artin_schreier_constants_pchar_three).
Qed.

Lemma artin_schreier_parameter_neq0 : artin_schreier_parameter != 0.
Proof. by rewrite /artin_schreier_parameter tofrac_eq0 polyX_eq0. Qed.

(** Every quotient is exposed with a nonzero polynomial denominator. *)
Lemma artin_schreier_fraction_presentation (x : K) :
  exists p q : {poly k}, q != 0 /\ x = p%:K / q%:K.
Proof.
elim/quotW: x=> r.
exists \n_r, \d_r; split; first exact: denom_ratioP.
symmetry.
unlock FracField.tofrac.
rewrite !piE /FracField.invf /FracField.mulf
  !numden_Ratio ?(oner_neq0, mulf_neq0, denom_ratioP) //.
by rewrite !mulr1 !mul1r Ratio_numden.
Qed.

(** Cross multiplication for [y^3-y=t]. *)
Lemma artin_schreier_cross_multiply p q (q0 : q != 0) :
  (p%:K / q%:K) ^+ 3 - p%:K / q%:K = artin_schreier_parameter ->
  p ^+ 3 - p * q ^+ 2 = 'X * q ^+ 3.
Proof.
set P : K := p%:K.
set Q : K := q%:K.
set T : K := artin_schreier_parameter.
have Q0 : Q != 0 by rewrite /Q tofrac_eq0.
have Q30 : Q ^+ 3 != 0 := expf_neq0 3 Q0.
move=> h.
have hmul := congr1 (fun z : K => z * Q ^+ 3) h.
have hcube : (P / Q) ^+ 3 * Q ^+ 3 = P ^+ 3.
  by rewrite expr_div_n (divfK Q30).
have hlinear : (P / Q) * Q ^+ 3 = P * Q ^+ 2.
  rewrite [Q ^+ 3]exprS.
  rewrite -[(P / Q) * (Q * Q ^+ 2)]mulrA.
  rewrite (mulrA Q^-1 Q (Q ^+ 2)) (mulVf Q0) mul1r.
  by [].
rewrite mulrBl hcube hlinear in hmul.
apply/eqP.
rewrite -tofrac_eq.
apply/eqP.
move: hmul.
rewrite /P /Q /T /artin_schreier_parameter => hmul.
rewrite -!tofracXn -!tofracM -!tofracB in hmul.
exact: hmul.
Qed.

(** Polynomial degree at infinity rules out an Artin--Schreier value. *)
Lemma artin_schreier_polynomial_degree_contradiction
    (p q : {poly k}) (q0 : q != 0) :
  p ^+ 3 - p * q ^+ 2 = 'X * q ^+ 3 -> False.
Proof.
move=> hpq.
have x0 : ('X : {poly k}) != 0 by rewrite polyX_eq0.
have rhs0 : 'X * q ^+ 3 != 0.
  exact: mulf_neq0 x0 (expf_neq0 3 q0).
have p0 : p != 0.
  apply/negP=> /eqP pE.
  move: rhs0.
  by rewrite -hpq pE expr0n /= mul0r subrr eqxx.
pose dp := (size p).-1.
pose dq := (size q).-1.
have sp3 : size (p ^+ 3) = (dp * 3).+1.
  by rewrite polySpred ?expf_neq0 // size_exp.
have sq2 : size (q ^+ 2) = (dq * 2).+1.
  by rewrite polySpred ?expf_neq0 // size_exp.
have sq3 : size (q ^+ 3) = (dq * 3).+1.
  by rewrite polySpred ?expf_neq0 // size_exp.
have spq2 : size (p * q ^+ 2) = (dp + dq * 2).+1.
  rewrite size_mul ?expf_neq0 // (polySpred p0) sq2.
  change ((dp.+1 + (dq * 2).+1).-1 = (dp + dq * 2).+1).
  by rewrite addnS /= addSn.
have srhs : size ('X * q ^+ 3) = (dq * 3).+2.
  rewrite mulrC size_mulX ?expf_neq0 //.
  by rewrite sq3.
have [dq_lt_dp|dp_le_dq] := ltnP dq dp.
- have hdegree : ltn (size (p * q ^+ 2)) (size (p ^+ 3)).
    rewrite spq2 sp3.
    change (ltn (dp + dq * 2) (dp * 3)).
    have hmulE : ltn (dq * 2) (dp * 2) = ltn dq dp.
      exact: (@ltn_pmul2r 2 dq dp isT).
    have hmul : ltn (dq * 2) (dp * 2) :=
      is_true_of_eq hmulE dq_lt_dp.
    have haddE :
        ltn (dp + dq * 2) (dp + dp * 2) = ltn (dq * 2) (dp * 2).
      exact: ltn_add2l dp (dq * 2) (dp * 2).
    have hadd : ltn (dp + dq * 2) (dp + dp * 2) :=
      is_true_of_eq haddE hmul.
    have hrhs : dp * 3 = dp + dp * 2 := mulnS dp 2.
    have htargetE :
        ltn (dp + dq * 2) (dp * 3) =
        ltn (dp + dq * 2) (dp + dp * 2).
      exact: (@congr1 nat bool (fun n : nat => ltn (dp + dq * 2) n)
        (dp * 3) (dp + dp * 2) hrhs).
    exact: is_true_of_eq htargetE hadd.
  have slhs : size (p ^+ 3 - p * q ^+ 2) = (dp * 3).+1.
    rewrite (size_polyDl _); first exact: sp3.
    by rewrite size_polyN.
  have hsize := @congr1 {poly k} nat (fun f : {poly k} => size f)
    _ _ hpq.
  rewrite slhs srhs in hsize.
  have hpred := congr1 predn hsize.
  rewrite /= in hpred.
  have hmod := congr1 (fun n : nat => modn n 3) hpred.
  move: hmod.
  by rewrite modnMl -addn1 modnMDl modn_small.
- have hp3_le : leq (size (p ^+ 3)) (dq * 3).+1.
    rewrite sp3.
    change (leq (dp * 3) (dq * 3)).
    have hE : leq (dp * 3) (dq * 3) = leq dp dq.
      exact: (@leq_pmul2r 3 dp dq isT).
    exact: is_true_of_eq hE dp_le_dq.
  have hpq2_le : leq (size (p * q ^+ 2)) (dq * 3).+1.
    rewrite spq2.
    change (leq (dp + dq * 2) (dq * 3)).
    have haddE :
        leq (dp + dq * 2) (dq + dq * 2) = leq dp dq.
      exact: leq_add2r (dq * 2) dp dq.
    have hadd : leq (dp + dq * 2) (dq + dq * 2) :=
      is_true_of_eq haddE dp_le_dq.
    have hrhs : dq * 3 = dq + dq * 2 := mulnS dq 2.
    have htargetE :
        leq (dp + dq * 2) (dq * 3) =
        leq (dp + dq * 2) (dq + dq * 2).
      exact: (@congr1 nat bool (fun n : nat => leq (dp + dq * 2) n)
        (dq * 3) (dq + dq * 2) hrhs).
    exact: is_true_of_eq htargetE hadd.
  have hlhs_le : leq (size (p ^+ 3 - p * q ^+ 2)) (dq * 3).+1.
    apply: leq_trans (size_polyD _ _) _.
    by rewrite size_polyN geq_max hp3_le hpq2_le.
  move: hlhs_le.
  by rewrite hpq srhs ltnn.
Qed.

Theorem artin_schreier_parameter_not_value (x : K) :
  x ^+ 3 - x != artin_schreier_parameter.
Proof.
apply/negP=> /eqP hx.
have [p [q [q0 xE]]] := artin_schreier_fraction_presentation x.
rewrite xE in hx.
exact: (artin_schreier_polynomial_degree_contradiction q0
  (artin_schreier_cross_multiply q0 hx)).
Qed.

(**************************************************************************)
(** * The separable irreducible cubic *)

Definition artin_schreier_polynomial : {poly K} :=
  'X ^+ 3 - ('X + artin_schreier_parameter%:P).

Lemma artin_schreier_polynomial_size :
  size artin_schreier_polynomial = 4.
Proof.
have htail :
    ltn (size (- ('X + artin_schreier_parameter%:P : {poly K})))
      (size ('X ^+ 3 : {poly K})).
  rewrite size_polyN size_polyXn.
  apply: leq_ltn_trans (size_polyD _ _) _.
  rewrite size_polyX size_polyC.
  by case: (artin_schreier_parameter == 0).
change (size (('X ^+ 3 : {poly K}) +
  - ('X + artin_schreier_parameter%:P)) = 4).
by rewrite (size_polyDl htail) size_polyXn.
Qed.

Lemma artin_schreier_polynomial_monic :
  artin_schreier_polynomial \is monic.
Proof.
apply/monicP.
have htail :
    ltn (size (- ('X + artin_schreier_parameter%:P : {poly K})))
      (size ('X ^+ 3 : {poly K})).
  rewrite size_polyN size_polyXn.
  apply: leq_ltn_trans (size_polyD _ _) _.
  rewrite size_polyX size_polyC.
  by case: (artin_schreier_parameter == 0).
rewrite /artin_schreier_polynomial.
by rewrite (lead_coefDl htail) lead_coefXn.
Qed.

Lemma artin_schreier_polynomial_has_no_root (x : K) :
  ~~ root artin_schreier_polynomial x.
Proof.
apply/negP=> hx.
have hx' : x ^+ 3 = x + artin_schreier_parameter.
  move: hx.
  by rewrite /artin_schreier_polynomial rootE !hornerE subr_eq0 => /eqP.
have hvalue : x ^+ 3 - x = artin_schreier_parameter.
  by rewrite hx' [x + artin_schreier_parameter]addrC addrK.
move: (artin_schreier_parameter_not_value x).
by rewrite hvalue eqxx.
Qed.

Theorem artin_schreier_polynomial_irreducible :
  irreducible_poly artin_schreier_polynomial.
Proof.
apply: cubic_irreducible.
- by rewrite artin_schreier_polynomial_size.
- exact: artin_schreier_polynomial_has_no_root.
Qed.

Lemma artin_schreier_polynomial_derivative :
  artin_schreier_polynomial^`() = - (1 : {poly K}).
Proof.
rewrite /artin_schreier_polynomial derivB derivXn derivD derivX derivC
  addr0 -scaler_nat.
rewrite (GRing.pcharf0 artin_schreier_function_pchar_three) scale0r.
by rewrite sub0r.
Qed.

Theorem artin_schreier_polynomial_separable :
  separable_poly artin_schreier_polynomial.
Proof.
have minus_oneE :
    (-1 : {poly K}) = (-1 : K) *: (1 : {poly K}).
  by rewrite scaleN1r.
rewrite unlock /separable_poly artin_schreier_polynomial_derivative
  minus_oneE.
by rewrite coprimepZr ?oppr_eq0 ?oner_eq0 // coprimep1.
Qed.

(**************************************************************************)
(** * Roots of unity supplied by the closed constant field *)

Lemma closed_field_primitive_root_exists
    (F : closedFieldType) (n : nat) :
  n%:R != 0 :> F -> {z : F | n.-primitive_root z}.
Proof.
move=> n0.
have n_gt0 : (n > 0)%N.
  by case: n n0 => //=; rewrite eqxx.
pose p : {poly F} := 'X^n - 1.
have [r Dp] := closed_field_poly_normal p.
apply/sigW; rewrite (monicP _) ?monicXnsubC // scale1r in Dp.
have rn1 : all n.-unity_root r.
  by apply/allP=> z; rewrite -root_prod_XsubC -Dp.
have sz_r : (n < (size r).+1)%N.
  by rewrite -(size_prod_XsubC r id) -Dp size_XnsubC.
have [|z] := hasP (has_prim_root n_gt0 rn1 _ sz_r); last by exists z.
by rewrite -separable_prod_XsubC -Dp separable_Xn_sub_1.
Qed.

(**************************************************************************)
(** * The obstruction in an arbitrary ambient splitting field *)

Definition artin_schreier_polynomial_in (L : fieldExtType K) : {poly L} :=
  map_poly (in_alg L) artin_schreier_polynomial.

Definition artin_schreier_parameter_in (L : fieldExtType K) : L :=
  in_alg L artin_schreier_parameter.

Section Ambient.

Variable L : splittingFieldType K.

Local Notation pL := (artin_schreier_polynomial_in L).
Local Notation tL := (artin_schreier_parameter_in L).

Lemma artin_schreier_ambient_pchar_three : 3 \in [pchar L].
Proof. by rewrite pchar_lalg artin_schreier_function_pchar_three. Qed.

Lemma artin_schreier_polynomial_in_size : size pL = 4.
Proof.
by rewrite /artin_schreier_polynomial_in size_map_poly
  artin_schreier_polynomial_size.
Qed.

Lemma artin_schreier_polynomial_in_monic : pL \is monic.
Proof.
by rewrite /artin_schreier_polynomial_in map_monic
  artin_schreier_polynomial_monic.
Qed.

Lemma artin_schreier_polynomial_in_separable : separable_poly pL.
Proof.
by rewrite /artin_schreier_polynomial_in separable_map
  artin_schreier_polynomial_separable.
Qed.

Lemma artin_schreier_polynomial_in_over (E : {subfield L}) :
  pL \is a polyOver E.
Proof.
rewrite /artin_schreier_polynomial_in.
exact: alg_polyOver E artin_schreier_polynomial.
Qed.

Lemma artin_schreier_parameter_in_mem (E : {subfield L}) : tL \in E.
Proof.
by rewrite /artin_schreier_parameter_in memvZ ?mem1v.
Qed.

Lemma artin_schreier_root_equation (y : L) :
  root pL y -> y ^+ 3 - y = tL.
Proof.
move=> hy.
have hy' : y ^+ 3 = y + tL.
  move: hy.
  rewrite /artin_schreier_polynomial_in
    /artin_schreier_polynomial /artin_schreier_parameter_in.
  by rewrite rootE !rmorphB !rmorphD !rmorphXn /=
    !map_polyX !map_polyC !hornerE subr_eq0 => /eqP.
by rewrite hy' [y + tL]addrC addrK.
Qed.

(** [ArtinSchreierRootless E] says that the fixed cubic has no root in [E]. *)
Definition ArtinSchreierRootless (E : {subfield L}) : Prop :=
  forall y : L, y \in E -> ~~ root pL y.

Lemma artin_schreier_rootless_base : ArtinSchreierRootless 1.
Proof.
move=> y; case/vlineP=> c ->.
change (~~ root pL (in_alg L c)).
by rewrite /artin_schreier_polynomial_in mapf_root
  artin_schreier_polynomial_has_no_root.
Qed.

(** If the cubic stays rootless over [E], adjoining one of its roots has
    relative degree exactly three. *)
Lemma artin_schreier_root_adjoin_degree
    (E : {subfield L}) (y : L) :
  ArtinSchreierRootless E -> root pL y ->
  \dim_E <<E; y>> = 3.
Proof.
move=> rootlessE hy.
have pE := artin_schreier_polynomial_in_over E.
have /polyOver_subvs[q qE] := pE.
have qsize : size q = 4.
  rewrite -(size_map_poly vsval) -qE.
  exact: artin_schreier_polynomial_in_size.
have qrootless (z : subvs_of E) : ~~ root q z.
  apply/negP=> hz.
  have hpz : root pL (val z).
    by rewrite qE mapf_root.
  move: (rootlessE (val z) (valP z)).
  by rewrite hpz.
have qirr : irreducible_poly q.
  apply: cubic_irreducible.
  - by rewrite qsize.
  - exact: qrootless.
have qy : root (map_poly vsval q) y by rewrite -qE.
have q0 : q != 0 := irredp_neq0 qirr.
have qminimal := (subfx_irreducibleP qy q0).2 qirr.
have /polyOver_subvs[m mE] := minPolyOver E y.
have my : root (map_poly vsval m) y.
  by rewrite -mE root_minPoly.
have m0 : m != 0.
  apply/negP=> /eqP mZ.
  move: (monic_neq0 (monic_minPoly E y)).
  by rewrite mE mZ rmorph0 eqxx.
have lower : leq 4 (size (minPoly E y)).
  rewrite mE size_map_poly.
  move: (qminimal m my m0).
  by rewrite qsize.
have pL0 : pL != 0 := monic_neq0 artin_schreier_polynomial_in_monic.
have upper : leq (size (minPoly E y)) 4.
  move: (dvdp_leq pL0 (minPoly_dvdp pE hy)).
  by rewrite artin_schreier_polynomial_in_size.
have minsize : size (minPoly E y) = 4.
  apply: anti_leq.
  by apply/andP; split; [exact: upper | exact: lower].
rewrite -adjoin_degreeE.
have hpred := @congr1 nat nat predn _ _ (size_minPoly E y).
rewrite minsize /= in hpred.
exact: esym hpred.
Qed.

(** In characteristic three, adjoining an element whose cube lies in [E]
    is purely inseparable: cubes of all elements of the simple adjunction
    still lie in [E]. *)
Lemma artin_schreier_cube_mem_adjoin
    (E : {subfield L}) (x y : L) :
  x ^+ 3 \in E -> y \in <<E; x>>%VS -> y ^+ 3 \in E.
Proof.
move=> x3E /Fadjoin_polyP[q qE ->].
rewrite -(pFrobenius_autE artin_schreier_ambient_pchar_three q.[x])
  -horner_map.
apply: rpred_horner.
- apply/polyOverP=> i.
  rewrite coef_map.
  move/polyOverP: qE=> qEi.
  exact: rpredX (qEi i).
- exact: x3E.
Qed.

(** One ordinary prime-radical adjunction preserves rootlessness.  For
    prime three this is the purely inseparable argument above.  For every
    other prime, the closed constants provide the needed primitive root of
    unity, MathComp--Abel's Kummer lemma gives degree [p], and a cubic
    subfield would force [3 | p]. *)
Lemma artin_schreier_rootless_pradical_step
    (E : {subfield L}) (x : L) (p : nat) :
  ArtinSchreierRootless E ->
  prime p -> x ^+ p \in E ->
  ArtinSchreierRootless <<E; x>>%VS.
Proof.
move=> rootlessE pprime xpE y yEx.
apply/negP=> hy.
have yNE : y \notin E.
  apply/negP=> yE.
  move: (rootlessE y yE).
  by rewrite hy.
have ydegree : \dim_E <<E; y>> = 3 :=
  artin_schreier_root_adjoin_degree rootlessE hy.
have yeq := artin_schreier_root_equation hy.
have [p3|pN3] := eqVneq p 3.
- subst p.
  have y3E : y ^+ 3 \in E :=
    artin_schreier_cube_mem_adjoin xpE yEx.
  have yE : y \in E.
    have -> : y = y ^+ 3 - tL.
      by rewrite -yeq subKr.
    exact: rpredB y3E (artin_schreier_parameter_in_mem E).
  by move: yNE; rewrite yE.
- have xNE : x \notin E.
    apply/negP=> xE.
    have KxE : (<<E; x>>%AS <= E)%VS.
      apply/FadjoinP; split.
      - exact: subvv.
      - exact: xE.
    have yE : y \in E := (subvP KxE) y yEx.
    move: (rootlessE y yE).
    by rewrite hy.
  have p0k : p%:R != 0 :> k.
    have prime_three : prime 3 := isT.
    rewrite -(dvdn_pcharf artin_schreier_constants_pchar_three).
    by rewrite (dvdn_prime2 prime_three pprime) eq_sym pN3.
  have [w wprim] := closed_field_primitive_root_exists p0k.
  pose wK : K := artin_schreier_constant_to_function w.
  pose wL : L := in_alg L wK.
  have wKprim : p.-primitive_root wK.
    by rewrite /wK fmorph_primitive_root.
  have wLprim : p.-primitive_root wL.
    by rewrite /wL fmorph_primitive_root.
  have wE : wL \in E.
    have w1 : wL \in (1%VS : {vspace L}).
      apply/vlineP; exists wK.
      by rewrite /wL in_algE.
    exact: (subvP (sub1v E)) wL w1.
  have xminsize := @size_minPoly_pradical
    p K L wL x wLprim E pprime wE xNE xpE.
  have xdegree : \dim_E <<E; x>> = p.
    rewrite -adjoin_degreeE.
    have hsize := size_minPoly E x.
    by rewrite xminsize in hsize; case: hsize.
  have EyEx : (<<E; y>> <= <<E; x>>)%VS.
    apply/FadjoinP; split; first exact: subv_adjoin.
    exact: yEx.
  have degree_dvd := field_dimS EyEx.
  rewrite (dim_sup_field (subv_adjoin E y))
    (dim_sup_field (subv_adjoin E x)) ydegree xdegree in degree_dvd.
  have three_dvd_p : (3 %| p)%N.
    move: degree_dvd.
    by rewrite dvdn_pmul2r ?adim_gt0.
  have p_eq_three : p = 3.
    have prime_three : prime 3 := isT.
    apply/eqP.
    move: three_dvd_p.
    by rewrite (dvdn_prime2 prime_three pprime) eq_sym.
  by move: pN3; rewrite p_eq_three eqxx.
Qed.

(** Literal paper-facing endpoint: no field obtained by an ordinary radical
    tower from the base can contain a root of the cubic. *)
Theorem artin_schreier_root_not_solvable_by_radical
    (a : L) :
  root pL a ->
  ~ solvable_by radical 1 <<1; a>>.
Proof.
move=> ha hrad.
have hprad := solvable_by_pradical_radical hrad.
move: hprad=> [R [[/= n e pw] /towerP epwP hR] hcontain].
pose m := n.
have prefix_rootless : ArtinSchreierRootless <<1 & take m e>>%VS.
  elim: m => [|m IHm].
  - have hnil : (<<1 & [::]>>%AS : {subfield L}) =
        (1%AS : {subfield L}).
      apply: val_inj.
      by rewrite /= Fadjoin_nil.
    by rewrite take0 hnil; exact: artin_schreier_rootless_base.
  - have [mn|nm] := ltnP m n; last first.
      move: IHm.
      by rewrite !take_oversize ?size_tuple // leqW.
    have hstep := epwP (Ordinal mn).
    rewrite (tnth_nth 0) (tnth_nth 0%N) /= in hstep.
    move/pradicalP: hstep=> [pwprime epower].
    pose B : {subfield L} := <<1 & take m e>>%VS.
    pose C : {subfield L} := <<B; e`_m>>%VS.
    have IHmB : ArtinSchreierRootless B := IHm.
    have epowerB : e`_m ^+ nth 0%N pw m \in B := epower.
    have hnext : ArtinSchreierRootless C.
      exact: artin_schreier_rootless_pradical_step IHmB pwprime epowerB.
    have hsucc : (<<1 & take m.+1 e>>%AS : {subfield L}) = C.
      apply: val_inj.
      by rewrite /C /B /= (take_nth 0) ?size_tuple // adjoin_rcons.
    by rewrite hsucc.
have Rrootless : ArtinSchreierRootless R.
  have hReq : (<<1 & e>>%AS : {subfield L}) = R.
    apply: val_inj.
    by rewrite /= hR.
  rewrite -hReq.
  move: prefix_rootless.
  by rewrite /m take_oversize ?size_tuple.
have aR : a \in R.
  apply: (subvP hcontain).
  exact: memv_adjoin.
move: (Rrootless a aR).
by rewrite ha.
Qed.

End Ambient.

(**************************************************************************)
(** * The internally constructed cyclic splitting field *)

Section RootField.

Variable M : fieldExtType K.

Local Notation pM := (artin_schreier_polynomial_in M).
Local Notation tM := (artin_schreier_parameter_in M).

Lemma artin_schreier_fieldext_pchar_three : 3 \in [pchar M].
Proof. by rewrite pchar_lalg artin_schreier_function_pchar_three. Qed.

Lemma artin_schreier_fieldext_size : size pM = 4.
Proof.
by rewrite /artin_schreier_polynomial_in size_map_poly
  artin_schreier_polynomial_size.
Qed.

Lemma artin_schreier_fieldext_monic : pM \is monic.
Proof.
by rewrite /artin_schreier_polynomial_in map_monic
  artin_schreier_polynomial_monic.
Qed.

Lemma artin_schreier_fieldext_separable : separable_poly pM.
Proof.
by rewrite /artin_schreier_polynomial_in separable_map
  artin_schreier_polynomial_separable.
Qed.

Lemma artin_schreier_fieldext_root_equation (a : M) :
  root pM a -> a ^+ 3 = a + tM.
Proof.
rewrite /artin_schreier_polynomial_in /artin_schreier_polynomial
  /artin_schreier_parameter_in rootE.
by rewrite !rmorphB !rmorphD !rmorphXn /= !map_polyX !map_polyC
  !hornerE subr_eq0 => /eqP.
Qed.

Lemma artin_schreier_translate_root (a c : M) :
  c ^+ 3 = c -> root pM a -> root pM (a + c).
Proof.
move=> cfix ha.
have afix := artin_schreier_fieldext_root_equation ha.
have fresh : (a + c) ^+ 3 = a ^+ 3 + c ^+ 3.
  exact: (@pFrobenius_autD_comm M 3
    artin_schreier_fieldext_pchar_three a c (mulrC a c)).
rewrite /artin_schreier_polynomial_in /artin_schreier_polynomial
  /artin_schreier_parameter_in rootE.
rewrite !rmorphB !rmorphD !rmorphXn /= !map_polyX !map_polyC
  !hornerE subr_eq0.
apply/eqP.
rewrite fresh cfix afix.
exact: addrAC a tM c.
Qed.

Lemma artin_schreier_two_natrE : (2%:R : M) = 1 + 1.
Proof. exact: (@natrD M 1 1). Qed.

Lemma artin_schreier_two_fixed : (2%:R : M) ^+ 3 = 2%:R.
Proof.
rewrite artin_schreier_two_natrE.
have h := (@pFrobenius_autD_comm M 3
  artin_schreier_fieldext_pchar_three 1 1 (commr1 (1 : M))).
rewrite !pFrobenius_autE !expr1n in h.
exact: h.
Qed.

Lemma artin_schreier_neq_addr_nonzero (u c : M) :
  c != 0 -> u != u + c.
Proof.
move=> c0; apply/negP=> /eqP h.
have cE : c = 0.
  apply: (addrI u).
  rewrite addr0.
  exact: esym h.
by move: c0; rewrite cE eqxx.
Qed.

Definition artin_schreier_root_list (a : M) : seq M :=
  [:: a; a + 1; a + 2%:R].

Lemma artin_schreier_root_list_uniq (a : M) :
  uniq (artin_schreier_root_list a).
Proof.
have two0 : (2%:R : M) != 0.
  by rewrite -(dvdn_pcharf artin_schreier_fieldext_pchar_three).
have h01 : a != a + 1 :=
  @artin_schreier_neq_addr_nonzero a 1 (oner_neq0 M).
have h02 : a != a + 2%:R :=
  @artin_schreier_neq_addr_nonzero a 2%:R two0.
have h12 : a + 1 != a + 2%:R.
  rewrite artin_schreier_two_natrE addrA.
  exact: (@artin_schreier_neq_addr_nonzero (a + 1) 1 (oner_neq0 M)).
by rewrite /artin_schreier_root_list /= !inE
  (negPf h01) (negPf h02) (negPf h12).
Qed.

Lemma artin_schreier_root_list_all_roots (a : M) :
  root pM a -> all (root pM) (artin_schreier_root_list a).
Proof.
move=> ha.
have h1 : root pM (a + 1).
  apply: artin_schreier_translate_root ha.
  by rewrite expr1n.
have h2 : root pM (a + 2%:R).
  exact: artin_schreier_translate_root artin_schreier_two_fixed ha.
by rewrite /artin_schreier_root_list /= ha h1 h2.
Qed.

Lemma artin_schreier_root_factorization (a : M) :
  root pM a ->
  pM = \prod_(z <- artin_schreier_root_list a) ('X - z%:P).
Proof.
move=> ha.
rewrite [LHS](@all_roots_prod_XsubC _ _
  (artin_schreier_root_list a)).
- by rewrite (monicP artin_schreier_fieldext_monic) scale1r.
- by rewrite artin_schreier_fieldext_size
    /artin_schreier_root_list.
- exact: artin_schreier_root_list_all_roots ha.
- by rewrite uniq_rootsE artin_schreier_root_list_uniq.
Qed.

Lemma artin_schreier_root_list_adjoin (a : M) :
  <<1 & artin_schreier_root_list a>>%VS = <<1; a>>%VS.
Proof.
have one1 : (1 : M) \in (1%VS : {vspace M}).
  apply/vlineP; exists (1 : K).
  by rewrite scale1r.
have one_adjoin : (1 : M) \in <<1; a>>%VS :=
  (subvP (subv_adjoin 1 a)) 1 one1.
have two_adjoin : (2%:R : M) \in <<1; a>>%VS.
  rewrite artin_schreier_two_natrE.
  apply: memvD.
  - exact: one_adjoin.
  - exact: one_adjoin.
apply/eqP; rewrite eqEsubv; apply/andP; split.
- apply/Fadjoin_seqP; split; first exact: subv_adjoin.
  move=> z.
  rewrite /artin_schreier_root_list !inE.
  move=> /orP[/eqP -> | /orP[/eqP -> | /eqP ->]].
  + exact: memv_adjoin.
  + exact: memvD (memv_adjoin 1 a) one_adjoin.
  + exact: memvD (memv_adjoin 1 a) two_adjoin.
- apply/FadjoinP; split; first exact: subv_adjoin_seq.
  by rewrite seqv_sub_adjoin ?mem_head.
Qed.

End RootField.

Section RootGalois.

Variable M : splittingFieldType K.

Local Notation pM := (artin_schreier_polynomial_in M).

Theorem artin_schreier_root_field_galois (a : M) :
  root pM a -> galois 1 <<1; a>>.
Proof.
move=> ha.
apply/splitting_galoisField.
exists pM; split.
- exact: (@artin_schreier_polynomial_in_over M (1 : {subfield M})).
- exact: artin_schreier_fieldext_separable.
- exists (artin_schreier_root_list a).
  + by rewrite (@artin_schreier_root_factorization M a ha) eqpxx.
  + exact: artin_schreier_root_list_adjoin a.
Qed.

End RootGalois.

Local Open Scope group_scope.

(** A closed, nonvacuous counterexample.  The splitting field and root are
    constructed from irreducibility; the three translated roots establish
    splitting and Galoisness; the no-radical conclusion is the literal Abel
    predicate, not the separate polynomial-level convenience definition. *)
Theorem exists_artin_schreier_C3_not_solvable_by_radical :
  {L : splittingFieldType K & {a : L |
    root (artin_schreier_polynomial_in L) a /\
    <<1; a>>%VS = (fullv : {vspace L}) /\
    @galois K L (1 : {vspace L}) (fullv : {vspace L}) /\
    #|'Gal((fullv : {vspace L}) / (1 : {vspace L}))| = 3 /\
    cyclic 'Gal((fullv : {vspace L}) / (1 : {vspace L})) /\
    solvable 'Gal((fullv : {vspace L}) / (1 : {vspace L})) /\
    ~ @solvable_by K L radical (1 : {vspace L}) <<1; a>>%VS}}.
Proof.
have [L0 dimL0 [a ha agen]] :=
  irredp_FAdjoin artin_schreier_polynomial_irreducible.
have splitL0 : SplittingField.axiom L0.
  exists (artin_schreier_polynomial_in L0).
  - exact: (@alg_polyOver K L0 (1 : {subfield L0})
      artin_schreier_polynomial).
  - exists (artin_schreier_root_list a).
    + by rewrite (@artin_schreier_root_factorization L0 a ha) eqpxx.
    + by rewrite artin_schreier_root_list_adjoin agen.
pose splitMixin := FieldExt_isSplittingField.Build K L0 splitL0.
pose S : splittingFieldType K := HB.pack L0 splitMixin.
have dimL03 : \dim {:L0} = 3.
  by move: dimL0; rewrite artin_schreier_polynomial_size.
have galoisS : @galois K S (1 : {vspace S}) (fullv : {vspace S}).
  have ga := @artin_schreier_root_field_galois S a ha.
  by rewrite agen in ga.
have cardS : #|'Gal((fullv : {vspace S}) / (1 : {vspace S}))| = 3.
  rewrite -(galois_dim galoisS) dimv1 divn1.
  exact: dimL03.
have cyclicS : cyclic 'Gal((fullv : {vspace S}) / (1 : {vspace S})).
  apply/prime_cyclic.
  by rewrite cardS.
have solvableS : solvable 'Gal((fullv : {vspace S}) / (1 : {vspace S})).
  exact: abelian_sol (cyclic_abelian cyclicS).
exists S, a; repeat split.
- exact: ha.
- exact: agen.
- exact: galoisS.
- exact: cardS.
- exact: cyclicS.
- exact: solvableS.
- exact: (@artin_schreier_root_not_solvable_by_radical S a ha).
Qed.

Print Assumptions artin_schreier_parameter_not_value.
Print Assumptions artin_schreier_polynomial_irreducible.
Print Assumptions artin_schreier_polynomial_separable.
Print Assumptions artin_schreier_rootless_pradical_step.
Print Assumptions artin_schreier_root_not_solvable_by_radical.
Print Assumptions artin_schreier_root_field_galois.
Print Assumptions exists_artin_schreier_C3_not_solvable_by_radical.

End PolynomialFormulasLazardArtinSchreierRadicalCounterexample.
