From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field.
From mathcomp.algebra.num_theory Require Import numdomain.
From Abel Require Import char0 cyclotomic_ext abel.
From PolynomialFormulas Require Import
  QuinticCanonicalDecision QuinticThetaGaloisBridge
  LazardGeneralResolventCriterion LazardGeneralResolventExplicit
  LazardQuinticInvariantDescentF20
  LazardQuinticCanonicalEpsilonNonzero
  LazardQuinticRootCentering LazardQuinticRootMembershipDescent
  LazardQuinticRootExtensionTransport
  LazardQuinticCoherentAlternateCompositumTower
  LazardQuinticPrimitiveFifthRootTower.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A concrete common-compositum wrapper for the corrected Lazard formula.

    The generic compositum theorem deliberately accepts a finite Galois
    overfield, a complete ordered-root presentation, and a primitive fifth
    root.  None of those objects is an assumption here.  For a rational
    quintic [p] we take MathComp--Abel's concrete splitting field of

                         [p * Phi_5].

    Divisibility extracts a linear factorization of [p] from the product
    factorization.  [splitting_ahom] then embeds the canonical [numfield p]
    into the common field.  A primitive complex fifth root is pulled back
    through the same product factorization, exactly as in the concrete
    cyclotomic counterexample development.  The final theorem exposes both
    directions of root correctness for the actual alternate formula output.

    This file is intentionally separate from the generic descent and tower
    files: the lemmas below are the missing reusable MathComp adapter for a
    splitting field of a product.

    Coefficient scope is important.  The product-splitting-field adapters in
    the first half of the file apply to every nonzero [p : {poly rat}].  The
    final executable theorem, however, is specialized to
    [QRF.monic_quintic], whose five stored lower coefficients are integers;
    [QC.rational_monic_quintic] merely maps that integer polynomial to
    [rat].  Thus this file does not yet by itself give the same front end for
    an arbitrary rational-coefficient monic depressed quintic. *)
Module PolynomialFormulasLazardQuinticCoherentAlternateConcreteCompositum.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.

Local Open Scope ring_scope.
Local Open Scope group_scope.

Module TV := PolynomialFormulasQuinticThetaValues.
Module TGB := PolynomialFormulasQuinticThetaGaloisBridge.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module QPS := PolynomialFormulasQuinticPaddedSymmetrization.
Module RRS := PolynomialFormulasSexticRationalRootSearch.
Module QC := PolynomialFormulasQuinticCanonicalDecision.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.
Module CE := PolynomialFormulasLazardQuinticCanonicalEpsilonNonzero.
Module RC := PolynomialFormulasLazardQuinticRootCentering.
Module RM := PolynomialFormulasLazardQuinticRootMembershipDescent.
Module RT := PolynomialFormulasLazardQuinticRootExtensionTransport.
Module GC := PolynomialFormulasLazardGeneralResolventCriterion.
Module GE := PolynomialFormulasLazardGeneralResolventExplicit.
Module CT :=
  PolynomialFormulasLazardQuinticCoherentAlternateCompositumTower.
Module RCT := PolynomialFormulasLazardQuinticRootCompleteAlternateTower.
Module RRC := PolynomialFormulasLazardQuinticRootRadicalCertificate.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module O := PolynomialFormulasLazardOptimality.
Module PT := PolynomialFormulasLazardQuinticPrimitiveFifthRootTower.
Module T4 := PolynomialFormulasLazardOptimalityTheoremFourDegree.
Module PF := PolynomialFormulasLazardQuinticPrimitiveFifthRoot.

(* -------------------------------------------------------------------- *)
(** * The product splitting field and its two factors *)

Definition lazard_fifth_cyclotomic_Q : {poly rat} :=
  map_poly (intr : int -> rat) 'Phi_5.

Lemma lazard_fifth_cyclotomic_Q_monic :
  lazard_fifth_cyclotomic_Q \is monic.
Proof.
by rewrite /lazard_fifth_cyclotomic_Q map_monic Cyclotomic_monic.
Qed.

Lemma lazard_fifth_cyclotomic_Q_neq0 :
  lazard_fifth_cyclotomic_Q != 0.
Proof. exact: monic_neq0 lazard_fifth_cyclotomic_Q_monic. Qed.

Definition lazard_quintic_cyclotomic_product (p : {poly rat}) :
    {poly rat} :=
  p * lazard_fifth_cyclotomic_Q.

Lemma lazard_quintic_cyclotomic_product_neq0 p :
  p != 0 -> lazard_quintic_cyclotomic_product p != 0.
Proof.
move=> p_neq0.
by rewrite /lazard_quintic_cyclotomic_product
  mulf_neq0 p_neq0 lazard_fifth_cyclotomic_Q_neq0.
Qed.

Definition lazard_quintic_cyclotomic_ambient (p : {poly rat}) :
    splittingFieldType rat :=
  numfield (lazard_quintic_cyclotomic_product p).

Section ProductFactor.

Variable p : {poly rat}.
Hypothesis p_neq0 : p != 0.

Let product := lazard_quintic_cyclotomic_product p.
Let Ambient := lazard_quintic_cyclotomic_ambient p.

(** A divisor of a product of linear factors is itself a product of a
    sublist of those factors.  This is the precise adapter absent from the
    high-level [numfield] interface. *)
Lemma exists_lazard_quintic_factor_roots :
  {rs : seq Ambient |
    map_poly (in_alg Ambient) p %=
      \prod_(z <- rs) ('X - z%:P)}.
Proof.
have product_neq0 : product != 0 :=
  lazard_quintic_cyclotomic_product_neq0 p_neq0.
have hproduct := poly_numfield_eqp product_neq0.
have hpdivProduct :
    map_poly (in_alg Ambient) p %|
      map_poly (in_alg Ambient) product.
  rewrite /product /lazard_quintic_cyclotomic_product map_polyM.
  exact: dvdp_mulIl.
have hpdivLinear :
    map_poly (in_alg Ambient) p %|
      \prod_(z <- numfield_roots product) ('X - z%:P).
  rewrite -(eqp_dvdr _ hproduct).
  exact: hpdivProduct.
have [m hm] := dvdp_prod_XsubC hpdivLinear.
by exists (mask m (numfield_roots product)).
Qed.

Definition lazard_quintic_factor_roots : seq Ambient :=
  sval exists_lazard_quintic_factor_roots.

Lemma lazard_quintic_factorization_in_ambient :
  map_poly (in_alg Ambient) p %=
    \prod_(z <- lazard_quintic_factor_roots) ('X - z%:P).
Proof.
rewrite /lazard_quintic_factor_roots.
by case: exists_lazard_quintic_factor_roots.
Qed.

(** The extracted roots also define the factor splitting field directly in
    the product ambient.  The older [FullField] wrapper below remains useful
    to the generic formula API, while this direct form is the one needed by
    the Galois compositum/base-change theorem. *)
Definition lazard_quintic_factor_field_ambient : {subfield Ambient} :=
  <<1 & lazard_quintic_factor_roots>>%AS.

Lemma lazard_quintic_splitting_in_ambient :
  splittingFieldFor 1 (map_poly (in_alg Ambient) p)
    lazard_quintic_factor_field_ambient.
Proof.
exists lazard_quintic_factor_roots; last exact: erefl.
exact: lazard_quintic_factorization_in_ambient.
Qed.

(** Hence the canonical splitting field embeds directly into
    [numfield (p * Phi_5)], with image exactly the subfield generated by the
    extracted roots of [p]. *)
Lemma exists_lazard_quintic_embedding_in_ambient :
  {h : 'AHom(numfield p, Ambient) |
    limg h = lazard_quintic_factor_field_ambient}.
Proof.
exact: splitting_ahom (numfieldP p_neq0)
  lazard_quintic_splitting_in_ambient.
Qed.

Let E : {subfield Ambient} := {:Ambient}.
Let FullField := subvs_of E.
Let into_full : 'AHom(Ambient, FullField) :=
  linfun_ahom (vsproj {:Ambient}).

Definition lazard_quintic_factor_roots_full : seq FullField :=
  map into_full lazard_quintic_factor_roots.

Definition lazard_quintic_factor_field_full : {subfield FullField} :=
  <<1 & lazard_quintic_factor_roots_full>>%AS.

Lemma lazard_quintic_splitting_in_full :
  splittingFieldFor 1 (map_poly (in_alg FullField) p)
    lazard_quintic_factor_field_full.
Proof.
exists lazard_quintic_factor_roots_full; last exact: erefl.
rewrite /lazard_quintic_factor_roots_full.
move: lazard_quintic_factorization_in_ambient.
rewrite -(eqp_map into_full) map_prod_XsubC -map_poly_comp.
by rewrite (eq_map_poly (fmorph_eq_rat into_full)).
Qed.

(** The canonical splitting field of [p] embeds into the concrete common
    product field; the image is precisely the subfield generated by the
    extracted [p]-roots. *)
Lemma exists_lazard_quintic_embedding_in_full :
  {h : 'AHom(numfield p, FullField) |
    limg h = lazard_quintic_factor_field_full}.
Proof.
exact: splitting_ahom (numfieldP p_neq0)
  lazard_quintic_splitting_in_full.
Qed.

End ProductFactor.

(* -------------------------------------------------------------------- *)
(** * An internally constructed primitive fifth root *)

Section PrimitiveFifthRoot.

Variable p : {poly rat}.
Hypothesis p_neq0 : p != 0.

Let product := lazard_quintic_cyclotomic_product p.
Let Ambient := lazard_quintic_cyclotomic_ambient p.
Let ambient_inC : {rmorphism Ambient -> algC} := numfield_inC product.

Definition lazard_primitive_fifth_root_C : algC :=
  projT1 (C_prim_root_exists (n := 5) isT).

Lemma lazard_primitive_fifth_root_C_primitive :
  5.-primitive_root lazard_primitive_fifth_root_C.
Proof.
rewrite /lazard_primitive_fifth_root_C.
case: C_prim_root_exists=> z /= hz.
exact: hz.
Qed.

Lemma lazard_primitive_fifth_root_C_cyclotomic :
  root (map_poly (@ratr algC) lazard_fifth_cyclotomic_Q)
    lazard_primitive_fifth_root_C.
Proof.
rewrite /lazard_fifth_cyclotomic_Q -map_poly_comp.
have hmap :
    (@ratr algC) \o (intr : int -> rat) =1
      (intr : int -> algC).
  by move=> a /=; rewrite rmorph_int.
rewrite (eq_map_poly hmap)
  (Phi_cyclotomic lazard_primitive_fifth_root_C_primitive).
by rewrite root_cyclotomic.
Qed.

Lemma lazard_primitive_fifth_root_C_product :
  root (map_poly (@ratr algC) product)
    lazard_primitive_fifth_root_C.
Proof.
rewrite /product /lazard_quintic_cyclotomic_product
  map_polyM rootM lazard_primitive_fifth_root_C_cyclotomic orbT.
Qed.

(** Pull the chosen complex primitive root back through the proved product
    factorization.  Injectivity of [numfield_inC] then transports
    primitivity; no root-of-unity constant is postulated. *)
Lemma exists_lazard_primitive_fifth_root_in_ambient :
  {omega : Ambient |
    ambient_inC omega = lazard_primitive_fifth_root_C}.
Proof.
have product_neq0 : product != 0 :=
  lazard_quintic_cyclotomic_product_neq0 p_neq0.
have hfactor :
    map_poly (@ratr algC) product %=
      \prod_(z <- numfield_roots product)
        ('X - (ambient_inC z)%:P).
  move: (poly_numfield_eqp product_neq0).
  rewrite -(eqp_map ambient_inC) map_prod_XsubC -map_poly_comp.
  by rewrite (eq_map_poly (fmorph_eq_rat ambient_inC)).
have hzprod :
    root (\prod_(z <- numfield_roots product)
      ('X - (ambient_inC z)%:P))
      lazard_primitive_fifth_root_C.
  by rewrite -(eqp_root hfactor)
    lazard_primitive_fifth_root_C_product.
move: hzprod; rewrite root_prod_XsubC=> /mapP[z _ hz].
by exists z; exact: esym hz.
Qed.

Definition lazard_primitive_fifth_root_ambient : Ambient :=
  sval exists_lazard_primitive_fifth_root_in_ambient.

Lemma lazard_primitive_fifth_root_ambient_inC :
  ambient_inC lazard_primitive_fifth_root_ambient =
    lazard_primitive_fifth_root_C.
Proof.
rewrite /lazard_primitive_fifth_root_ambient.
by case: exists_lazard_primitive_fifth_root_in_ambient.
Qed.

Lemma lazard_primitive_fifth_root_ambient_primitive :
  5.-primitive_root lazard_primitive_fifth_root_ambient.
Proof.
move: lazard_primitive_fifth_root_C_primitive.
by rewrite -lazard_primitive_fifth_root_ambient_inC
  fmorph_primitive_root.
Qed.

End PrimitiveFifthRoot.

(* -------------------------------------------------------------------- *)
(** * The actual F20/Kummer tower in the product common compositum *)

Section ActualF20KummerCompositum.

Variable p : {poly rat}.
Hypothesis p_size : size p = 6%N.
Hypothesis p_irr : irreducible_poly p.

(** Nonzeroness is part of being a quintic, not an additional premise of
    the paper-facing endpoint. *)
Let p_neq0 : p != 0.
Proof. by rewrite -size_poly_eq0 p_size. Qed.

Let Canonical := numfield p.
Let Ambient := lazard_quintic_cyclotomic_ambient p.
Let omega : Ambient :=
  @lazard_primitive_fifth_root_ambient p p_neq0.

(** This is the unconditional common-compositum endpoint missing from the
    earlier Theorem-4 crosswalk.  The ambient field and primitive fifth root
    are the concrete objects constructed from [p * Phi_5], and the embedding
    of [numfield p] is obtained from the proved factor splitting field.
    Solvability alone then constructs:

    - the mapped F20 fixed-field square tower;
    - the explicit two-square cyclotomic field [W]; and
    - the noncollapsed cyclic degree-five Kummer endpoint.

    The top displayed below is the actual compositum subfield generated by
    the embedded quintic splitting field and [W].  No equality with every
    element of the larger implementation ambient is needed. *)
Theorem exists_lazard_actual_F20_kummer_common_compositum :
  solvable 'Gal({:Canonical} / 1%AS) ->
  exists (h : 'AHom(Canonical, Ambient))
      (e : nat) (P : {group gal_of {:Canonical}})
      (W : {subfield Ambient}),
    limg h =
      @lazard_quintic_factor_field_ambient p p_neq0 /\
    5.-primitive_root omega /\
    e <= 2 /\
    #|'Gal({:Canonical} / 1%AS)| = (5 * 2 ^ e)%N /\
    #|P| = 5%N /\
    P <| 'Gal({:Canonical} / 1%AS) /\
    W = PT.lazard_square_radical_fifth_root_field
      (1%AS : {subfield Ambient})
      (PF.lazard_primitive_fifth_root_square_s omega)
      (PF.lazard_primitive_fifth_root_square_t omega) /\
    T4.square_radical_tower (1%AS : {subfield Ambient}) 2 W /\
    T4.square_radical_tower (1%AS : {subfield Ambient}) e
      (h @: fixedField P) /\
    galois (h @: fixedField P) (h @: {:Canonical}) /\
    \dim_(h @: fixedField P) (h @: {:Canonical}) = 5%N /\
    omega \in W /\
    T4.square_roots_and_fifth_root_presentation
      (1%AS : {subfield Ambient})
      ((h @: {:Canonical}) * ((h @: fixedField P) * W)%AS)%AS
      (2 + e).
Proof.
move=> solGal.
have [h himage] :=
  @exists_lazard_quintic_embedding_in_ambient p p_neq0.
have omega_primitive : 5.-primitive_root omega :=
  @lazard_primitive_fifth_root_ambient_primitive p p_neq0.
have [e [P [W [ele2 [cardGal [cardP [normalP
    [hW [hcyclotomic [hformula
      [hgal [hdim [homega hpresentation]]]]]]]]]]]]] :=
  @PT.lazard_mapped_solvable_F20_common_compositum
    p p_size p_irr Ambient h omega omega_primitive solGal.
exists h, e, P, W.
split; first exact: himage.
split; first exact: omega_primitive.
split; first exact: ele2.
split; first exact: cardGal.
split; first exact: cardP.
split; first exact: normalP.
split; first exact: hW.
split; first exact: hcyclotomic.
split; first exact: hformula.
split; first exact: hgal.
split; first exact: hdim.
split; first exact: homega.
exact: hpresentation.
Qed.

(** Exact version of the actual common-compositum theorem.  The two
    exponents have different meanings:

    - [e_Q] measures the two-primary part of the original rational F20
      Galois group, whose exact order is returned together with its normal
      order-five subgroup;
    - [e_omega] measures the formula-side extension after cyclotomic base
      change.

    Collapsed base-change steps are removed, so the Galois cardinality,
    absolute degree, and radical count below all use [e_omega]. *)
Theorem exists_lazard_actual_F20_kummer_common_compositum_compressed :
  solvable 'Gal({:Canonical} / 1%AS) ->
  exists (h : 'AHom(Canonical, Ambient))
      (e_Q e_omega : nat)
      (P : {group gal_of {:Canonical}})
      (W : {subfield Ambient}),
    limg h =
      @lazard_quintic_factor_field_ambient p p_neq0 /\
    5.-primitive_root omega /\
    e_Q <= 2 /\
    #|'Gal({:Canonical} / 1%AS)| = (5 * 2 ^ e_Q)%N /\
    #|P| = 5%N /\
    P <| 'Gal({:Canonical} / 1%AS) /\
    e_omega <= e_Q /\
    W = PT.lazard_square_radical_fifth_root_field
      (1%AS : {subfield Ambient})
      (PF.lazard_primitive_fifth_root_square_s omega)
      (PF.lazard_primitive_fifth_root_square_t omega) /\
    \dim W = 4%N /\
    W = <<(1%AS : {subfield Ambient}); omega>>%AS /\
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
    omega \in W /\
    ((h @: {:Canonical}) * ((h @: fixedField P) * W)%AS)%AS =
      ((h @: {:Canonical}) * W)%AS /\
    ((h @: {:Canonical}) * ((h @: fixedField P) * W)%AS)%AS =
      ((h @: {:Canonical}) *
        <<(1%AS : {subfield Ambient}); omega>>%AS)%AS /\
    T4.square_roots_and_fifth_root_presentation
      (1%AS : {subfield Ambient})
      ((h @: {:Canonical}) * ((h @: fixedField P) * W)%AS)%AS
      (2 + e_omega) /\
    O.radical_extension
      (L := Ambient) (1%AS : {subfield Ambient})
      ((h @: {:Canonical}) * ((h @: fixedField P) * W)%AS)%AS.
Proof.
move=> solGal.
have [h himage] :=
  @exists_lazard_quintic_embedding_in_ambient p p_neq0.
have omega_primitive : 5.-primitive_root omega :=
  @lazard_primitive_fifth_root_ambient_primitive p p_neq0.
have hmapped :=
  @PT.lazard_mapped_solvable_F20_common_compositum_compressed
    p p_size p_irr Ambient h omega omega_primitive solGal.
case: hmapped=> e_Q [e_omega [P [W hdata]]].
case: hdata=> eQle2 hdata.
case: hdata=> cardGal hdata.
case: hdata=> cardP hdata.
case: hdata=> normalP hdata.
case: hdata=> eomegale hdata.
case: hdata=> hW hdata.
case: hdata=> hdimW hdata.
case: hdata=> hcyclotomic hdata.
case: hdata=> hformula_Q hdata.
case: hdata=> hformula_omega hdata.
case: hdata=> hdimFormulaOmega hdata.
case: hdata=> hgalFinal hdata.
case: hdata=> hdimFinal hdata.
case: hdata=> hgalOmega hdata.
case: hdata=> hcardOmega hdata.
case: hdata=> hdimTop hdata.
case: hdata=> homega hpresentation.
have hrootFieldLeW :
    (<<(1%AS : {subfield Ambient}); omega>>%AS <= W)%VS.
  apply/FadjoinP; split; first exact: sub1v.
  exact: homega.
have hrootFieldDim :
    \dim <<(1%AS : {subfield Ambient}); omega>>%AS = 4%N :=
  PT.primitive_fifth_root_adjoin_dim omega_primitive.
have hWgenerated :
    W = <<(1%AS : {subfield Ambient}); omega>>%AS.
  apply: val_inj; apply/eqP.
  by rewrite eq_sym eqEdim hrootFieldLeW /= hrootFieldDim hdimW eqxx.
have hKleS :
    (h @: fixedField P <= h @: {:Canonical})%VS.
  by rewrite limgS ?subvf.
have hSKprod_v :
    ((h @: {:Canonical}) * (h @: fixedField P))%VS =
      (h @: {:Canonical}).
  rewrite prodvC.
  apply: field_module_eq.
  by rewrite sup_field_module.
have htopW :
    ((h @: {:Canonical}) * ((h @: fixedField P) * W)%AS)%AS =
      ((h @: {:Canonical}) * W)%AS.
  apply: val_inj.
  by rewrite -prodvA hSKprod_v.
have htopGenerated :
    ((h @: {:Canonical}) * ((h @: fixedField P) * W)%AS)%AS =
      ((h @: {:Canonical}) *
        <<(1%AS : {subfield Ambient}); omega>>%AS)%AS.
  by rewrite htopW hWgenerated.
have hradical :
    O.radical_extension
      (L := Ambient) (1%AS : {subfield Ambient})
      ((h @: {:Canonical}) * ((h @: fixedField P) * W)%AS)%AS :=
  T4.square_roots_and_fifth_root_is_radical hpresentation.
exists h, e_Q, e_omega, P, W.
split; first exact: himage.
split; first exact: omega_primitive.
split; first exact: eQle2.
split; first exact: cardGal.
split; first exact: cardP.
split; first exact: normalP.
split; first exact: eomegale.
split; first exact: hW.
split; first exact: hdimW.
split; first exact: hWgenerated.
split; first exact: hcyclotomic.
split; first exact: hformula_Q.
split; first exact: hformula_omega.
split; first exact: hdimFormulaOmega.
split; first exact: hgalFinal.
split; first exact: hdimFinal.
split; first exact: hgalOmega.
split; first exact: hcardOmega.
split; first exact: hdimTop.
split; first exact: homega.
split; first exact: htopW.
split; first exact: htopGenerated.
split; first exact: hpresentation.
exact: hradical.
Qed.

End ActualF20KummerCompositum.

(* -------------------------------------------------------------------- *)
(** * Coefficient-to-common-compositum theorem *)

Section ConcreteQuintic.

(** The exact remaining adapter for arbitrary rational coefficients is a
    weighted change of variable, not merely a global clearing of
    denominators.  For

      [p(X) = X^5 + a4 X^4 + a3 X^3 + a2 X^2 + a1 X + a0]

    choose a positive nonzero integer [D] divisible by every [denq ai] and
    form

      [pD(Y) = D^5 * p(Y / D)]
              [= Y^5 + (a4 D) Y^4 + (a3 D^2) Y^3]
              [    + (a2 D^3) Y^2 + (a1 D^4) Y + a0 D^5].

    All five lower coefficients are then integers, so [pD] has a
    [QRF.monic_quintic] code.  MathComp already supplies [denq_gt0],
    [denq_neq0], [numqE], [divq_num_den], [Qint_dvdz], [intrP], and the
    polynomial-level [rat_poly_scale]; the polynomial substitution API is
    [comp_poly], [root_comp], [comp_polyZ], and [rootZ].  What remains to be
    packaged and proved is:

    - the displayed coefficient identity and the root bijection
      [x |-> D * x], with inverse [y |-> y / D];
    - preservation of irreducibility and of the zero [X^4] coefficient;
    - degree-four homogeneity
      [theta(D * roots) = D^4 * theta(roots)], which transports a rational
      scalar-resolvent root and hence the executable scaled-resolvent
      witness for [pD]; and
    - division of each returned value by [D], including root soundness,
      root completeness, and membership in the same radical field (because
      [D^-1] is in the rational bottom field).

    Until those lemmas are connected to the theorem below, its coefficient
    domain is exactly the integer-coded subclass, not all monic depressed
    polynomials over [rat]. *)

Variable f : QRF.monic_quintic.
Let p := QC.rational_monic_quintic f.
Let p_size : size p = 6%N := QC.size_rational_monic_quintic f.
Let Canonical := numfield p.
Let ratrCanonical : {rmorphism rat -> Canonical} :=
  char0_ratr (char_numfield p).
Let canonical_roots : 5.-tuple Canonical :=
  @GA.quintic_root_tuple p p_size.

Let product := lazard_quintic_cyclotomic_product p.
Let Ambient := lazard_quintic_cyclotomic_ambient p.
Let K : {subfield Ambient} := 1%AS.
Let E : {subfield Ambient} := {:Ambient}.
Let BottomField := subvs_of K.
Let FullField := subvs_of E.
Let common_galois : galois K E := galois_numfield product.

Local Notation base_embed :=
  (@GC.lazard_base_embedding rat Ambient K E common_galois).

Definition lazard_common_base_polynomial : {poly BottomField} :=
  map_poly (in_alg BottomField) p.

Definition lazard_common_roots
    (h : 'AHom(Canonical, FullField)) : 5.-tuple FullField :=
  map_tuple h canonical_roots.

Definition lazard_common_selected_roots
    (h : 'AHom(Canonical, FullField)) (i : 'I_6) :
    5.-tuple FullField :=
  TV.permute_quintic_roots ((representative i)^-1)
    (lazard_common_roots h).

Definition lazard_common_alternate_output
    (h : 'AHom(Canonical, FullField)) (omega : FullField)
    (i : 'I_6) (k : 'I_5) : FullField :=
  RCT.lazard_root_complete_alternate_output omega
    (lazard_common_selected_roots h i) k.

Definition lazard_common_alternate_field
    (h : 'AHom(Canonical, FullField)) (omega : FullField)
    (i : 'I_6) : {subfield FullField} :=
  RCT.lazard_root_complete_alternate_field
    (1%AS : {subfield FullField}) omega
    (lazard_common_selected_roots h i).

Lemma lazard_common_quintic_neq0 : p != 0.
Proof. by rewrite -size_poly_eq0 p_size. Qed.

Lemma lazard_common_embedding_rationalE
    (h : 'AHom(Canonical, FullField)) q :
  h (ratrCanonical q) = in_alg FullField q.
Proof.
by rewrite /ratrCanonical char0_ratrE (fmorph_eq_rat h)
  in_algE alg_num_field.
Qed.

Lemma lazard_common_base_embedding_rationalE q :
  base_embed (in_alg BottomField q) = in_alg FullField q.
Proof.
by rewrite !in_algE !alg_num_field (fmorph_eq_rat base_embed).
Qed.

Lemma lazard_common_base_polynomial_mapE :
  map_poly base_embed lazard_common_base_polynomial =
    map_poly (in_alg FullField) p.
Proof.
rewrite /lazard_common_base_polynomial -map_poly_comp.
apply: eq_map_poly=> q /=.
exact: lazard_common_base_embedding_rationalE.
Qed.

Lemma lazard_common_embedding_polynomialE
    (h : 'AHom(Canonical, FullField)) :
  map_poly h (map_poly ratrCanonical p) =
    map_poly (in_alg FullField) p.
Proof.
rewrite -map_poly_comp.
apply: eq_map_poly=> q /=.
exact: lazard_common_embedding_rationalE.
Qed.

Lemma lazard_common_root_factorization
    (h : 'AHom(Canonical, FullField)) :
  map_poly base_embed lazard_common_base_polynomial =
    \prod_(z <- lazard_common_roots h) ('X - z%:P).
Proof.
rewrite lazard_common_base_polynomial_mapE
  -(lazard_common_embedding_polynomialE h)
  QC.canonical_quintic_numfield_factorization map_prod_XsubC.
reflexivity.
Qed.

Lemma lazard_common_root_presentation
    (p_irr : irreducible_poly p)
    (h : 'AHom(Canonical, FullField)) :
  @GE.lazard_ordered_root_presentation
    rat Ambient K E common_galois 5 lazard_common_base_polynomial
    (lazard_common_roots h).
Proof.
split.
- apply/tuple_uniqP.
  exact: RT.lazard_extension_map_tuple_injective h
    (@GA.quintic_root_tuple_injective p p_size p_irr).
- rewrite lazard_common_root_factorization.
  exact: eqpxx.
Qed.

Lemma lazard_common_theta_injective
    (p_irr : irreducible_poly p)
    (h : 'AHom(Canonical, FullField)) :
  injective (TV.quintic_theta_value (lazard_common_roots h)).
Proof.
move=> i j hij.
apply: (QC.canonical_quintic_theta_value_injective p_irr).
apply: (fmorph_inj h).
by rewrite !TGB.quintic_theta_value_map.
Qed.

Lemma lazard_common_base_embedding_mem a :
  base_embed a \in (1%AS : {subfield FullField}).
Proof.
apply/vlineP.
have [q hq] := (elimT vlineP (valP a)).
exists q.
by apply: val_inj; rewrite GC.lazard_base_embeddingE hq /=.
Qed.

Lemma lazard_common_two_neq0 : (2%:R : FullField) != 0.
Proof.
by rewrite -[2%:R](rmorph_nat (in_alg FullField) 2) fmorph_eq0.
Qed.

Lemma lazard_common_five_neq0 : (5%:R : FullField) != 0.
Proof.
by rewrite -[5%:R](rmorph_nat (in_alg FullField) 5) fmorph_eq0.
Qed.

Lemma lazard_centered_selected_rootsE
    (hdepressed : CE.lazard_canonical_quintic_depressed f)
    (i : 'I_6) :
  RC.lazard_centered_roots (ID.lazard_selected_roots i) =
    ID.lazard_selected_roots i.
Proof.
apply: eq_from_tnth=> k.
rewrite RC.tnth_lazard_centered_roots /RC.lazard_root_center
  (CE.lazard_selected_root_esymm1_zero hdepressed i)
  div0r subr0.
Qed.

Lemma lazard_common_selected_roots_map
    (h : 'AHom(Canonical, FullField))
    (hdepressed : CE.lazard_canonical_quintic_depressed f)
    (i : 'I_6) :
  map_tuple h
      (RC.lazard_centered_roots (ID.lazard_selected_roots i)) =
    lazard_common_selected_roots h i.
Proof.
rewrite lazard_centered_selected_rootsE //.
apply: eq_from_tnth=> k.
by rewrite tnth_map /ID.lazard_selected_roots
  /lazard_common_selected_roots /lazard_common_roots
  !TV.tnth_permute_quintic_roots tnth_map.
Qed.

(** Everything quantified in the conclusion is constructed from the input
    coefficients.  Besides the radical field and reconstruction equality,
    the last two conjuncts say explicitly that every returned value is a
    root and every root in the common splitting field is returned. *)
Theorem
    exists_lazard_common_compositum_coherent_alternate_radical_tower
    (p_irr : irreducible_poly p)
    (hdepressed : CE.lazard_canonical_quintic_depressed f)
    (hq : RRS.has_rational_root (QPS.quintic_scaled_resolvent f)) :
  exists (h : 'AHom(Canonical, FullField))
      (omega : FullField) (q : rat) (i : 'I_6),
    5.-primitive_root omega /\
    TV.quintic_theta_value (lazard_common_roots h) i =
      in_alg FullField q /\
    injective (tnth (lazard_common_selected_roots h i)) /\
    @O.radical_extension rat FullField
      (1%AS : {subfield FullField})
      (lazard_common_alternate_field h omega i) /\
    (forall k : 'I_5,
      lazard_common_alternate_output h omega i k \in
        lazard_common_alternate_field h omega i) /\
    (forall k : 'I_5,
      lazard_common_alternate_output h omega i k =
        RFR.lazard_reversed_root_tuple
          (lazard_common_selected_roots h i) k) /\
    (forall k : 'I_5,
      root (map_poly (in_alg FullField) p)
        (lazard_common_alternate_output h omega i k)) /\
    (forall z : FullField,
      root (map_poly (in_alg FullField) p) z ->
      exists k : 'I_5,
        z = lazard_common_alternate_output h omega i k).
Proof.
have [h _] :=
  exists_lazard_quintic_embedding_in_full lazard_common_quintic_neq0.
pose omega : FullField := vsproj ({:Ambient})
  (@lazard_primitive_fifth_root_ambient p lazard_common_quintic_neq0).
have omega_primitive : 5.-primitive_root omega.
  rewrite /omega fmorph_primitive_root.
  exact: (@lazard_primitive_fifth_root_ambient_primitive
    p lazard_common_quintic_neq0).
have hsemantic :=
  (proj1 (@QC.quintic_scaled_resolvent_has_rational_root_correct
    Canonical ratrCanonical canonical_roots f
    QC.canonical_quintic_padded_vieta
    (QC.canonical_quintic_resolvent_scale_nonzero p_irr))) hq.
case: hsemantic=> q hqscalar.
have [i hi] :=
  (proj1 (TV.quintic_scalar_resolvent_root_iff
    canonical_roots (ratrCanonical q))) hqscalar.
pose qK : BottomField := in_alg BottomField q.
have htheta_base :
    TV.quintic_theta_value (lazard_common_roots h) i =
      base_embed qK.
  rewrite -TGB.quintic_theta_value_map hi
    lazard_common_embedding_rationalE
    /qK lazard_common_base_embedding_rationalE.
have htheta_full :
    TV.quintic_theta_value (lazard_common_roots h) i =
      in_alg FullField q.
  by rewrite htheta_base /qK lazard_common_base_embedding_rationalE.
have htheta_injective := lazard_common_theta_injective p_irr h.
have hpresentation := lazard_common_root_presentation p_irr h.
pose rootsL :=
  RC.lazard_centered_roots (ID.lazard_selected_roots i).
have hselected :
    map_tuple h rootsL = lazard_common_selected_roots h i.
  exact: lazard_common_selected_roots_map h hdepressed i.
have hrootsL : injective (tnth rootsL) :=
  RC.lazard_centered_selected_roots_injective p_irr i.
have hsumL : RP.lazard_root_esymm1 rootsL = 0 :=
  RC.lazard_centered_roots_sum_zero
    (ID.lazard_selected_roots i) (by rewrite pnatr_eq0).
have hepsilon_productL :
    RP.lazard_root_epsilon_product rootsL != 0.
  rewrite /rootsL RC.lazard_root_projection_epsilon_product_centered.
  change (RR.lazard_epsilon_product (ID.lazard_selected_roots i) != 0).
  exact: CE.lazard_selected_epsilon_product_neq0
    p_irr hdepressed i.
have hcL := RM.lazard_centered_selected_depressed_coefficients_in
  (1%AS : {subfield Canonical}) p_irr hi.
have hinvariantsL := RM.lazard_centered_selected_invariant_coordinates_in
  (1%AS : {subfield Canonical}) p_irr hi.
have [hdataL _] := RM.lazard_centered_selected_root_membership_data_bot
  p_irr hi.
(** The coherent-alternate tower needs distinctness, depression, and nonzero
    epsilon, but not [E != 0].  Transport those three facts separately so
    this denominator-safe path has no dependency on the standard quotient
    branch's [E]-nonvanishing theorem. *)
have hrootsMap := RT.lazard_extension_map_tuple_injective h hrootsL.
have hsumMap :
    RP.lazard_root_esymm1 (map_tuple h rootsL) = 0.
  by rewrite -RT.lazard_extension_root_esymm1_map hsumL rmorph0.
have hepsilonMap := RT.lazard_extension_mapped_root_epsilon_neq0 h
  lazard_common_five_neq0 hepsilon_productL omega_primitive.
have hroots : injective
    (tnth (lazard_common_selected_roots h i)).
  rewrite -hselected.
  exact: hrootsMap.
have hsum :
    RP.lazard_root_esymm1 (lazard_common_selected_roots h i) = 0.
  rewrite -hselected.
  exact: hsumMap.
have hepsilon :
    RP.lazard_root_epsilon omega
      (lazard_common_selected_roots h i) != 0.
  rewrite -hselected.
  exact: hepsilonMap.
have [hradical [hmem hreconstruct]] :=
  @CT.lazard_compositum_coherent_alternate_radical_tower_of_mapped_root_data
    rat Ambient K E common_galois
    lazard_common_base_polynomial (lazard_common_roots h) hpresentation
    i qK htheta_base htheta_injective omega omega_primitive
    Canonical h rootsL hselected hcL hinvariantsL hdataL
    lazard_common_base_embedding_mem
    lazard_common_two_neq0 lazard_common_five_neq0
    hroots hepsilon hsum.
have [hsound hcomplete] :=
  @CT.lazard_compositum_coherent_alternate_output_correct
    rat Ambient K E common_galois
    lazard_common_base_polynomial (lazard_common_roots h) hpresentation
    i qK htheta_base htheta_injective omega omega_primitive
    lazard_common_five_neq0 hsum.
have hsoundP : forall k : 'I_5,
    root (map_poly (in_alg FullField) p)
      (lazard_common_alternate_output h omega i k).
  move=> k.
  rewrite -lazard_common_base_polynomial_mapE.
  exact: hsound k.
have hcompleteP : forall z : FullField,
    root (map_poly (in_alg FullField) p) z ->
    exists k : 'I_5,
      z = lazard_common_alternate_output h omega i k.
  move=> z hz.
  apply: hcomplete.
  by rewrite lazard_common_base_polynomial_mapE.
exists h, omega, q, i.
repeat split.
- exact: omega_primitive.
- exact: htheta_full.
- exact: hroots.
- exact: hradical.
- exact: hmem.
- exact: hreconstruct.
- exact: hsoundP.
- exact: hcompleteP.
Qed.

End ConcreteQuintic.

Print Assumptions exists_lazard_quintic_embedding_in_ambient.
Print Assumptions exists_lazard_actual_F20_kummer_common_compositum.
Print Assumptions
  exists_lazard_actual_F20_kummer_common_compositum_compressed.
Print Assumptions
  exists_lazard_common_compositum_coherent_alternate_radical_tower.

End PolynomialFormulasLazardQuinticCoherentAlternateConcreteCompositum.
