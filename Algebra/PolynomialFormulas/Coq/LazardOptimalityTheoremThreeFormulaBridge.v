From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_solvable all_field.
From Abel Require Import char0 cyclotomic_ext abel.
From PolynomialFormulas Require Import
  QuinticRecursiveFactor QuinticCanonicalDecision QuinticGaloisAction
  QuinticThetaValues SexticRationalRootSearch SexticComputedResolvents
  LazardQuinticCanonicalEpsilonNonzero
  LazardQuinticRootCentering LazardQuinticRootMembershipDescent
  LazardQuinticRootInvariantENonzeroF20
  LazardQuinticRootRadicalCertificate
  LazardQuinticRootExtensionTransport
  LazardQuinticRootCertificateFieldContainment
  LazardOptimality
  LazardOptimalityCyclicQuinticCounterexample
  LazardOptimalityTheoremThreeCounterexample.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Unconditional root-origin realization of the formula field used in the
    concrete counterexample to Lazard's Theorem 3.

    The older theorem-three file deliberately accepted a formula-field
    profile as input.  Here the profile is built from the actual roots and
    radical choices selected by the proved Lazard formulas.  The concrete
    depressed polynomial is the affine transform [Y = 5 X + 1] of the
    cyclic quintic already used for Theorem 4. *)
Module PolynomialFormulasLazardOptimalityTheoremThreeFormulaBridge.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Local Open Scope ring_scope.
Local Open Scope group_scope.

Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module TV := PolynomialFormulasQuinticThetaValues.
Module RRS := PolynomialFormulasSexticRationalRootSearch.
Module QPS := PolynomialFormulasSexticComputedResolvents.
Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module ID := PolynomialFormulasLazardQuinticInvariantDescentF20.
Module CE := PolynomialFormulasLazardQuinticCanonicalEpsilonNonzero.
Module RC := PolynomialFormulasLazardQuinticRootCentering.
Module RM := PolynomialFormulasLazardQuinticRootMembershipDescent.
Module ENZ := PolynomialFormulasLazardQuinticRootInvariantENonzeroF20.
Module BE := PolynomialFormulasLazardQuinticRootBranchEquivariance.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module CRT := PolynomialFormulasLazardQuinticCertificateRadicalTower.
Module RRC := PolynomialFormulasLazardQuinticRootRadicalCertificate.
Module RT := PolynomialFormulasLazardQuinticRootExtensionTransport.
Module RFC :=
  PolynomialFormulasLazardQuinticRootCertificateFieldContainment.
Module T4 :=
  PolynomialFormulasLazardOptimalityCyclicQuinticCounterexample.
Module T3 :=
  PolynomialFormulasLazardOptimalityTheoremThreeCounterexample.

(* -------------------------------------------------------------------- *)
(** * The explicit depressed cyclic quintic *)

Definition cyclic_depressed_data : QRF.monic_quintic :=
  [tuple (979 : int); 2310; -55; -110; 0].

Definition cyclic_depressed_Z : {poly int} :=
  QRF.quintic_polynomial cyclic_depressed_data.

Definition cyclic_depressed_Q : {poly rat} :=
  CD.rational_monic_quintic cyclic_depressed_data.

Lemma cyclic_depressed_ZE :
  cyclic_depressed_Z =
    'X^5 - (110 : int) *: 'X^3 - (55 : int) *: 'X^2 +
      (2310 : int) *: 'X + 979%:P.
Proof. vm_compute; reflexivity. Qed.

Lemma cyclic_depressed_Z_size : size cyclic_depressed_Z = 6%N.
Proof. exact: QRF.size_quintic_polynomial. Qed.

Lemma cyclic_depressed_Q_size : size cyclic_depressed_Q = 6%N.
Proof. exact: CD.size_rational_monic_quintic. Qed.

Lemma cyclic_depressed_Q_monic : cyclic_depressed_Q \is monic.
Proof. exact: CD.rational_monic_quintic_monic. Qed.

(** Eisenstein at eleven: [979 = 11 * 89] but is not divisible by
    [11^2], and all four remaining non-leading coefficients are divisible
    by eleven. *)
Lemma cyclic_depressed_Z_irreducible :
  irreducible_poly cyclic_depressed_Z.
Proof.
apply: (eisenstein_crit (p := 11)).
- by vm_compute.
- by rewrite cyclic_depressed_Z_size.
- by vm_compute.
- by vm_compute.
- move=> [|[|[|[|[|i]]]]] //= _; vm_compute.
Qed.

Lemma cyclic_depressed_Q_irreducible :
  irreducible_poly cyclic_depressed_Q.
Proof.
rewrite /cyclic_depressed_Q /CD.rational_monic_quintic
  irreducible_rat_int.
change (irreducible_poly cyclic_depressed_Z).
exact: cyclic_depressed_Z_irreducible.
Qed.

Lemma cyclic_depressed_Q_neq0 : cyclic_depressed_Q != 0.
Proof. by rewrite -size_poly_eq0 cyclic_depressed_Q_size. Qed.

(** The coefficient of [X^4] is zero, exactly the hypothesis expected by
    the canonical epsilon nonvanishing theorem. *)
Lemma cyclic_depressed_is_depressed :
  CE.lazard_canonical_quintic_depressed cyclic_depressed_data.
Proof. vm_compute; reflexivity. Qed.

(** The scaled integer Dummit resolvent has the explicit rational root
    [-9955].  This is the root [-1991/125] for the unscaled original
    polynomial, multiplied by the fourth power of the affine scale five. *)
Lemma cyclic_depressed_resolvent_has_rational_root :
  RRS.has_rational_root
    (QPS.quintic_scaled_resolvent cyclic_depressed_data).
Proof.
exists (-9955 : rat).
vm_compute; reflexivity.
Qed.

(* -------------------------------------------------------------------- *)
(** * Identification of its splitting field inside the common ambient *)

Definition cyclic_depressed_affine : {poly rat} :=
  (5 : rat) *: 'X + 1%:P.

Lemma cyclic_depressed_affine_identity :
  cyclic_depressed_Q \Po cyclic_depressed_affine =
    (3125 : rat) *: T4.cyclic_quintic_Q.
Proof. vm_compute; reflexivity. Qed.

Definition cyclic_depressed_root : T4.Ambient :=
  5%:R * T4.cyclic_quintic_root + 1.

Lemma cyclic_depressed_root_is_root :
  root (map_poly (in_alg T4.Ambient) cyclic_depressed_Q)
    cyclic_depressed_root.
Proof.
have hscaled :
    root ((3125%:R : T4.Ambient) *:
      map_poly (in_alg T4.Ambient) T4.cyclic_quintic_Q)
      T4.cyclic_quintic_root.
  rewrite rootZ ?pnatr_eq0 //.
  exact: T4.cyclic_quintic_root_is_root.
have hmap :
    map_poly (in_alg T4.Ambient)
      (cyclic_depressed_Q \Po cyclic_depressed_affine) =
    (3125%:R : T4.Ambient) *:
      map_poly (in_alg T4.Ambient) T4.cyclic_quintic_Q.
  rewrite cyclic_depressed_affine_identity linearZ /= rmorph_nat.
  reflexivity.
move: hscaled; rewrite -hmap map_comp_poly root_comp
  /cyclic_depressed_affine !linearD !linearZ /=
  !map_polyX !map_polyC !hornerD !hornerZ !hornerX !hornerC
  !rmorph_nat /cyclic_depressed_root.
by [].
Qed.

Lemma cyclic_depressed_root_field :
  <<(1%AS : {subfield T4.Ambient}); cyclic_depressed_root>>%AS =
    T3.CyclicQuinticField.
Proof.
apply: val_inj; apply: subv_anti; apply/andP; split.
- apply/FadjoinP; split; first exact: sub1v.
  rewrite /cyclic_depressed_root /T3.CyclicQuinticField.
  apply: rpredD; last exact: rpred1.
  exact: rpredM (rpred_nat _ _) (memv_adjoin _ _).
- apply/FadjoinP; split; first exact: sub1v.
  have hy : cyclic_depressed_root \in
      <<(1%AS : {subfield T4.Ambient}); cyclic_depressed_root>>%AS :=
    memv_adjoin _ _.
  have hquot :
      (cyclic_depressed_root - 1) / 5%:R \in
      <<(1%AS : {subfield T4.Ambient}); cyclic_depressed_root>>%AS.
    exact: rpred_div (rpredB hy rpred1) (rpred_nat _ _).
  move: hquot.
  rewrite /cyclic_depressed_root addrK mulrK ?pnatr_eq0 //.
Qed.

Lemma cyclicQuinticField_le_elevenField :
  (T3.CyclicQuinticField <= T4.ElevenField)%VS.
Proof.
apply/FadjoinP; split; first exact: sub1v.
rewrite /T4.cyclic_quintic_root /T4.ElevenField.
apply: rpredD; first exact: memv_adjoin.
by rewrite memvV memv_adjoin.
Qed.

(** The degree-five subfield is normal because it is an intermediate
    subfield of the abelian eleventh cyclotomic extension. *)
Lemma cyclicQuinticField_galois : galois 1 T3.CyclicQuinticField.
Proof.
have hchain : (1 <= T3.CyclicQuinticField <= T4.ElevenField)%VS.
  by rewrite sub1v cyclicQuinticField_le_elevenField.
have hgal := galoisS hchain T4.ElevenField_galois.
have /galois_fixedField <- := hgal.
rewrite normal_fixedField_galois // -sub_abelian_normal ?galS //.
exact: abelian_cyclotomic T4.zeta11_primitive.
Qed.

Lemma cyclicQuinticField_normal :
  normalField 1 T3.CyclicQuinticField.
Proof.
move/and3P: cyclicQuinticField_galois=> [_ _ hnormal].
exact: hnormal.
Qed.

Lemma cyclic_depressed_eq_minPoly :
  map_poly (in_alg T4.Ambient) cyclic_depressed_Q =
    minPoly 1 cyclic_depressed_root.
Proof.
exact: T4.irreducible_monic_root_eq_minPoly
  cyclic_depressed_Q_irreducible cyclic_depressed_Q_monic
  cyclic_depressed_root_is_root.
Qed.

Lemma cyclic_depressed_splitting_in_cyclic_field :
  splittingFieldFor 1
    (map_poly (in_alg T4.Ambient) cyclic_depressed_Q)
    T3.CyclicQuinticField.
Proof.
have hy : cyclic_depressed_root \in T3.CyclicQuinticField.
  rewrite -cyclic_depressed_root_field.
  exact: memv_adjoin.
have [rs /= /allP hrs hfactor] :=
  normalFieldP cyclicQuinticField_normal cyclic_depressed_root hy.
exists rs.
- by rewrite cyclic_depressed_eq_minPoly hfactor eqpxx.
- apply/eqP; rewrite eqEsubv; apply/andP; split.
  + apply/Fadjoin_seqP; split; first exact: sub1v.
    exact: hrs.
  + rewrite -cyclic_depressed_root_field.
    apply/FadjoinP; split; first exact: subv_adjoin_seq.
    by rewrite seqv_sub_adjoin // -root_prod_XsubC -hfactor root_minPoly.
Qed.

Definition CyclicDepressedNumfield := numfield cyclic_depressed_Q.

Lemma exists_cyclic_depressed_embedding :
  {iota : 'AHom(CyclicDepressedNumfield, T4.Ambient) |
    limg iota = T3.CyclicQuinticField}.
Proof.
exact: splitting_ahom (numfieldP cyclic_depressed_Q_neq0)
  cyclic_depressed_splitting_in_cyclic_field.
Qed.

(* -------------------------------------------------------------------- *)
(** * The actual root-origin Lazard certificate in the ambient field *)

Let p := cyclic_depressed_Q.
Let L := CyclicDepressedNumfield.
Let ratrL : {rmorphism rat -> L} := char0_ratr (char_numfield p).
Let canonical_roots : 5.-tuple L :=
  @GA.quintic_root_tuple p cyclic_depressed_Q_size.

Lemma cyclic_selected_centeredE (i : 'I_6) :
  RC.lazard_centered_roots (ID.lazard_selected_roots i) =
    ID.lazard_selected_roots i.
Proof.
apply: eq_from_tnth=> k.
rewrite RC.tnth_lazard_centered_roots /RC.lazard_root_center
  (CE.lazard_selected_root_esymm1_zero
    cyclic_depressed_is_depressed i) div0r subr0.
Qed.

Lemma cyclic_centered_selected_is_root (i : 'I_6) (k : 'I_5) :
  root (map_poly ratrL p)
    (tnth (RC.lazard_centered_roots (ID.lazard_selected_roots i)) k).
Proof.
rewrite cyclic_selected_centeredE /ID.lazard_selected_roots
  TV.tnth_permute_quintic_roots.
exact: CD.canonical_quintic_all_roots.
Qed.

Lemma cyclic_depressed_map_embedding
    (iota : 'AHom(L, T4.Ambient)) :
  map_poly iota (map_poly ratrL p) =
    map_poly (in_alg T4.Ambient) p.
Proof.
rewrite -map_poly_comp.
apply: eq_map_poly=> a /=.
rewrite /ratrL char0_ratrE (fmorph_eq_rat iota)
  in_algE alg_num_field.
Qed.

Record cyclic_lazard_root_branch := CyclicLazardRootBranch {
  cyclic_lazard_roots : 5.-tuple T4.Ambient;
  cyclic_lazard_roots_in : forall k : 'I_5,
    tnth cyclic_lazard_roots k \in T3.CyclicQuinticField;
  cyclic_lazard_roots_are_roots : forall k : 'I_5,
    root (map_poly (in_alg T4.Ambient) p)
      (tnth cyclic_lazard_roots k);
  cyclic_lazard_first : Q.lazard_sign_branch;
  cyclic_lazard_second : Q.lazard_sign_branch;
  cyclic_lazard_certificate :
    RRC.lazard_root_radical_certificate cyclic_lazard_roots;
  cyclic_lazard_initialE :
    CRT.lazard_certificate_initial cyclic_lazard_certificate =
      Q.lazard_branch_triple
        (BE.lazard_root_quadratic_triple T4.zeta5 cyclic_lazard_roots)
        cyclic_lazard_first;
  cyclic_lazard_t_neq0 :
    Q.lazard_t (CRT.lazard_certificate_initial
      cyclic_lazard_certificate) != 0;
  cyclic_lazard_branchE :
    CRT.lazard_certificate_branch cyclic_lazard_certificate =
      cyclic_lazard_second;
  cyclic_lazard_p1E :
    CRT.lazard_certificate_p1 cyclic_lazard_certificate =
      BE.lazard_source_for_branch
        (BE.lazard_source_for_branch
          (BE.lazard_root_fourier_orbit T4.zeta5 cyclic_lazard_roots)
          cyclic_lazard_first) cyclic_lazard_second p0;
  cyclic_lazard_p1_neq0 :
    CRT.lazard_certificate_p1 cyclic_lazard_certificate != 0;
  cyclic_lazard_chosenE :
    CRT.lazard_certificate_chosen cyclic_lazard_certificate =
      Q.lazard_branch_triple
        (Q.lazard_branch_triple
          (BE.lazard_root_quadratic_triple T4.zeta5 cyclic_lazard_roots)
          cyclic_lazard_first) cyclic_lazard_second;
  cyclic_lazard_reconstruction : forall k : 'I_5,
    RRC.lazard_root_certificate_output T4.zeta5 cyclic_lazard_roots
      cyclic_lazard_certificate k =
      RFR.lazard_reversed_root_tuple
        (BE.lazard_roots_for_branch
          (BE.lazard_roots_for_branch cyclic_lazard_roots
            cyclic_lazard_first) cyclic_lazard_second) k;
  cyclic_lazard_radical_data :
    RRC.lazard_root_radical_invariant_data_in
      (1%AS : {subfield T4.Ambient}) cyclic_lazard_roots;
  cyclic_lazard_numerator_data :
    RRC.lazard_root_fourier_numerator_data_in
      (1%AS : {subfield T4.Ambient}) cyclic_lazard_roots
}.

Theorem exists_cyclic_lazard_root_branch : cyclic_lazard_root_branch.
Proof.
have [iota hiota] := exists_cyclic_depressed_embedding.
have hsemantic :=
  (proj1 (@CD.quintic_scaled_resolvent_has_rational_root_correct
    L ratrL canonical_roots cyclic_depressed_data
    CD.canonical_quintic_padded_vieta
    (CD.canonical_quintic_resolvent_scale_nonzero
      cyclic_depressed_Q_irreducible)))
    cyclic_depressed_resolvent_has_rational_root.
case: hsemantic=> q hq.
have [i hi] :=
  (proj1 (TV.quintic_scalar_resolvent_root_iff
    canonical_roots (ratrL q))) hq.
pose rootsL := RC.lazard_centered_roots (ID.lazard_selected_roots i).
pose rootsA := map_tuple iota rootsL.
have hrootsL : injective (tnth rootsL) :=
  RC.lazard_centered_selected_roots_injective
    cyclic_depressed_Q_irreducible i.
have hsumL : RP.lazard_root_esymm1 rootsL = 0 :=
  RC.lazard_centered_roots_sum_zero
    (ID.lazard_selected_roots i) (by rewrite pnatr_eq0).
have hepsilon_productL : RP.lazard_root_epsilon_product rootsL != 0.
  rewrite /rootsL RC.lazard_root_projection_epsilon_product_centered.
  change (RR.lazard_epsilon_product (ID.lazard_selected_roots i) != 0).
  exact: CE.lazard_selected_epsilon_product_neq0
    cyclic_depressed_Q_irreducible cyclic_depressed_is_depressed i.
have hrootEL : Q.lazard_root_E rootsL != 0.
  rewrite /rootsL RC.lazard_root_E_centered.
  exact: ENZ.lazard_selected_root_E_neq0
    cyclic_depressed_Q_irreducible hi.
have hcL := RM.lazard_centered_selected_depressed_coefficients_in
  (1%AS : {subfield L}) cyclic_depressed_Q_irreducible hi.
have hinvL := RM.lazard_centered_selected_invariant_coordinates_in
  (1%AS : {subfield L}) cyclic_depressed_Q_irreducible hi.
have [hdataL _] := RM.lazard_centered_selected_root_membership_data_bot
  cyclic_depressed_Q_irreducible hi.
have [hdataA hnumA] := RT.lazard_root_membership_data_map_bot
  iota hcL hinvL hdataL.
have [hrootsA hsumA hepsilonA hEA] :=
  RT.lazard_root_extension_hypotheses iota
    (by rewrite pnatr_eq0) hrootsL hsumL hepsilon_productL hrootEL
    T4.zeta5_primitive.
have [first [second [d
    [hinitial [ht [hbranch [hp1 [hp1_neq0
      [hchosen [hreconstruct _]]]]]]]]]]] :=
  RRC.lazard_exists_root_radical_certificate_complete
    (by rewrite pnatr_eq0) (by rewrite pnatr_eq0)
    T4.zeta5_primitive hrootsA hsumA hepsilonA hEA.
have hroots_in : forall k : 'I_5, tnth rootsA k \in
    T3.CyclicQuinticField.
  move=> k; rewrite /rootsA tnth_map -hiota memv_img ?memvf.
have hroots_root : forall k : 'I_5,
    root (map_poly (in_alg T4.Ambient) p) (tnth rootsA k).
  move=> k.
  have hsource := cyclic_centered_selected_is_root i k.
  have hmapped :
      root (map_poly iota (map_poly ratrL p)) (iota (tnth rootsL k)).
    by rewrite mapf_root.
  rewrite cyclic_depressed_map_embedding in hmapped.
  by move: hmapped; rewrite /rootsA tnth_map.
refine
  {| cyclic_lazard_roots := rootsA;
     cyclic_lazard_roots_in := hroots_in;
     cyclic_lazard_roots_are_roots := hroots_root;
     cyclic_lazard_first := first;
     cyclic_lazard_second := second;
     cyclic_lazard_certificate := d;
     cyclic_lazard_initialE := hinitial;
     cyclic_lazard_t_neq0 := ht;
     cyclic_lazard_branchE := hbranch;
     cyclic_lazard_p1E := hp1;
     cyclic_lazard_p1_neq0 := hp1_neq0;
     cyclic_lazard_chosenE := hchosen;
     cyclic_lazard_reconstruction := hreconstruct;
     cyclic_lazard_radical_data := hdataA;
     cyclic_lazard_numerator_data := hnumA |}.
Qed.

(* -------------------------------------------------------------------- *)
(** * The concrete formula and pre-fifth-root fields *)

Definition cyclic_lazard_base_field (b : cyclic_lazard_root_branch) :
    {subfield T4.Ambient} :=
  CRT.lazard_certificate_second_field
    (1%AS : {subfield T4.Ambient}) (cyclic_lazard_certificate b).

Definition cyclic_lazard_formula_field (b : cyclic_lazard_root_branch) :
    {subfield T4.Ambient} :=
  CRT.lazard_certificate_generated_field
    (1%AS : {subfield T4.Ambient}) (cyclic_lazard_certificate b).

Lemma cyclic_lazard_base_le_formula b :
  (cyclic_lazard_base_field b <= cyclic_lazard_formula_field b)%VS.
Proof. exact: subv_adjoin. Qed.

Lemma cyclic_lazard_p1_mem_formula b :
  CRT.lazard_certificate_p1 (cyclic_lazard_certificate b) \in
    cyclic_lazard_formula_field b.
Proof. exact: CRT.lazard_certificate_p1_mem_generated. Qed.

Lemma cyclic_lazard_p1_fifth_mem_base b :
  CRT.lazard_certificate_p1 (cyclic_lazard_certificate b) ^+ 5 \in
    cyclic_lazard_base_field b.
Proof.
exact: CRT.lazard_certificate_p1_fifth_mem_second
  (cyclic_lazard_certificate b) (cyclic_lazard_radical_data b).
Qed.

Lemma cyclic_lazard_formula_generated b :
  (cyclic_lazard_formula_field b : {vspace T4.Ambient}) =
    agenv (((cyclic_lazard_base_field b : {vspace T4.Ambient}) +
      <[CRT.lazard_certificate_p1 (cyclic_lazard_certificate b)]>)%VS).
Proof. reflexivity. Qed.

(** The actual root-origin formula field is the three-step radical tower
    certified in [LazardQuinticCertificateRadicalTower]: two square-root
    adjunctions followed by the fifth-root adjunction generated by [P1]. *)
Lemma cyclic_lazard_formula_is_radical b :
  PolynomialFormulasLazardOptimality.radical_extension
    (L := T4.Ambient) 1 (cyclic_lazard_formula_field b).
Proof.
exact: CRT.lazard_certificate_generated_field_is_radical
  (cyclic_lazard_certificate b) (cyclic_lazard_radical_data b).
Qed.

(** Every generator of the actual root-origin certificate is an expression
    in the cyclic quintic roots and [zeta5], so the complete formula field
    is contained in their compositum. *)
Lemma cyclic_lazard_formula_le_compositum b :
  (cyclic_lazard_formula_field b <= T3.CyclicQuinticCompositum)%VS.
Proof.
apply: (RFC.lazard_root_certificate_generated_field_le
  (B := (1%AS : {subfield T4.Ambient}))
  (omega := T4.zeta5)
  (roots := cyclic_lazard_roots b)
  (first := cyclic_lazard_first b)
  (second := cyclic_lazard_second b)
  (d := cyclic_lazard_certificate b)).
- exact: sub1v.
- exact: memv_adjoin.
- move=> k.
  exact: (subvP T3.cyclicQuinticField_le_compositum)
    (cyclic_lazard_roots_in b k).
- exact: cyclic_lazard_initialE b.
- exact: cyclic_lazard_p1E b.
Qed.

Lemma cyclic_lazard_root0_field b :
  <<(1%AS : {subfield T4.Ambient});
    tnth (cyclic_lazard_roots b) o0>>%AS = T3.CyclicQuinticField.
Proof.
have hsub :
    (<<(1%AS : {subfield T4.Ambient});
        tnth (cyclic_lazard_roots b) o0>>%AS <=
      T3.CyclicQuinticField)%VS.
  apply/FadjoinP; split; first exact: sub1v.
  exact: cyclic_lazard_roots_in b o0.
have hmin :
    map_poly (in_alg T4.Ambient) p =
      minPoly 1 (tnth (cyclic_lazard_roots b) o0).
  exact: T4.irreducible_monic_root_eq_minPoly
    cyclic_depressed_Q_irreducible cyclic_depressed_Q_monic
    (cyclic_lazard_roots_are_roots b o0).
have hdim :
    \dim <<(1%AS : {subfield T4.Ambient});
      tnth (cyclic_lazard_roots b) o0>>%AS = 5%N.
  rewrite dim_Fadjoin dimv1 muln1.
  apply: succn_inj.
  rewrite -size_minPoly -hmin size_map_poly cyclic_depressed_Q_size.
  reflexivity.
apply: val_inj; apply/eqP.
by rewrite eqEdim hsub /= hdim T3.cyclicQuinticField_dim eqxx.
Qed.

(** The zero-index inverse-Fourier output is the distinguished input root,
    already before adjoining [zeta5].  Since that root has degree five, it
    generates the concrete cyclic quintic field. *)
Lemma cyclicQuinticField_le_lazard_formula b :
  (T3.CyclicQuinticField <= cyclic_lazard_formula_field b)%VS.
Proof.
rewrite -cyclic_lazard_root0_field.
apply/FadjoinP; split; first exact: sub1v.
exact: RFC.lazard_root_o0_mem_generated
  (cyclic_lazard_certificate b)
  (cyclic_lazard_radical_data b)
  (cyclic_lazard_numerator_data b)
  (cyclic_lazard_reconstruction b).
Qed.

(** The formula field and the competing radical field contain the same
    explicit root of the original cyclic quintic.  This is the literal
    root-containment premise in Theorem 3, rather than only an implicit
    consequence of the degree-five field inclusion above. *)
Lemma cyclic_quintic_root_mem_lazard_formula b :
  T4.cyclic_quintic_root \in cyclic_lazard_formula_field b.
Proof.
apply: (subvP (cyclicQuinticField_le_lazard_formula b)).
by rewrite /T3.CyclicQuinticField; exact: memv_adjoin.
Qed.

(* -------------------------------------------------------------------- *)
(** * The two quadratic adjunctions have total degree at most four *)

Lemma adjoin_degree_le_two_of_square_mem
    (K : {subfield T4.Ambient}) (x : T4.Ambient) :
  x ^+ 2 \in K -> adjoin_degree K x <= 2%N.
Proof.
move=> hx2.
pose q : {poly T4.Ambient} := 'X^2 - (x ^+ 2)%:P.
have hqover : q \is a polyOver K.
  by rewrite /q polyOverXnsubC.
have hqroot : root q x.
  by rewrite /q rootE !hornerE subrr eqxx.
have hdiv : minPoly K x %| q := minPoly_dvdp hqover hqroot.
have hqmonic : q \is monic.
  exact: monicXnsubC (by []).
have hsize := dvdp_leq (monic_neq0 hqmonic) hdiv.
move: hsize.
by rewrite size_minPoly /q size_XnsubC // leqSS.
Qed.

Lemma cyclic_lazard_epsilon_square_mem_bottom b :
  Q.lazard_epsilon
      (CRT.lazard_certificate_initial (cyclic_lazard_certificate b)) ^+ 2
    \in (1%AS : {subfield T4.Ambient}).
Proof.
rewrite (CRT.lazard_certificate_epsilon_square
  (cyclic_lazard_certificate b)).
exact: rpredM (CRT.lazard_natr_mem _ 5)
  (CRT.lazard_D_in_base (cyclic_lazard_radical_data b)).
Qed.

Lemma cyclic_lazard_first_field_dim_le_two b :
  \dim (CRT.lazard_certificate_first_field
      (1%AS : {subfield T4.Ambient}) (cyclic_lazard_certificate b)) <= 2%N.
Proof.
rewrite dim_Fadjoin dimv1 muln1.
exact: adjoin_degree_le_two_of_square_mem
  (cyclic_lazard_epsilon_square_mem_bottom b).
Qed.

Lemma cyclic_lazard_t_square_mem_first b :
  Q.lazard_t
      (CRT.lazard_certificate_initial (cyclic_lazard_certificate b)) ^+ 2
    \in CRT.lazard_certificate_first_field
      (1%AS : {subfield T4.Ambient}) (cyclic_lazard_certificate b).
Proof.
rewrite (CRT.lazard_certificate_t_square (cyclic_lazard_certificate b)).
apply: rpredM.
- exact: rpred_div (CRT.lazard_natr_mem _ 5)
    (CRT.lazard_natr_mem _ 2).
- apply: rpredD.
  + exact: CRT.lazard_certificate_base_mem_first
      (cyclic_lazard_certificate b)
      (CRT.lazard_E_in_base (cyclic_lazard_radical_data b)).
  + apply: rpred_div.
    * exact: CRT.lazard_certificate_base_mem_first
        (cyclic_lazard_certificate b)
        (CRT.lazard_F_in_base (cyclic_lazard_radical_data b)).
    * exact: CRT.lazard_certificate_epsilon_mem_first
        (1%AS : {subfield T4.Ambient}) (cyclic_lazard_certificate b).
Qed.

Lemma cyclic_lazard_base_field_dim_le_four b :
  \dim (cyclic_lazard_base_field b) <= 4%N.
Proof.
have htdeg :
    adjoin_degree
      (CRT.lazard_certificate_first_field
        (1%AS : {subfield T4.Ambient}) (cyclic_lazard_certificate b))
      (Q.lazard_t
        (CRT.lazard_certificate_initial (cyclic_lazard_certificate b)))
      <= 2%N :=
  adjoin_degree_le_two_of_square_mem (cyclic_lazard_t_square_mem_first b).
rewrite /cyclic_lazard_base_field dim_Fadjoin.
apply: leq_trans (leq_mul htdeg (cyclic_lazard_first_field_dim_le_two b)).
by [].
Qed.

Lemma cyclic_lazard_formula_neq_base b :
  cyclic_lazard_formula_field b != cyclic_lazard_base_field b.
Proof.
apply/eqP=> hformula.
have hdim := dimvS (cyclicQuinticField_le_lazard_formula b).
rewrite hformula T3.cyclicQuinticField_dim in hdim.
have hbad := leq_trans hdim (cyclic_lazard_base_field_dim_le_four b).
by move: hbad.
Qed.

(* -------------------------------------------------------------------- *)
(** * A nontrivial relative Galois automorphism of the formula field *)

Definition FiftyFifthCyclotomicField : {subfield T4.Ambient} :=
  <<(1%AS : {subfield T4.Ambient}); T4.zeta55>>%AS.

Lemma elevenField_le_fiftyFifth :
  (T4.ElevenField <= FiftyFifthCyclotomicField)%VS.
Proof.
apply/FadjoinP; split; first exact: sub1v.
rewrite /T4.zeta11 /FiftyFifthCyclotomicField.
exact: rpredX memv_adjoin.
Qed.

Lemma cyclicCompositum_le_fiftyFifth :
  (T3.CyclicQuinticCompositum <= FiftyFifthCyclotomicField)%VS.
Proof.
apply/FadjoinP; split.
- exact: subv_trans cyclicQuinticField_le_elevenField
    elevenField_le_fiftyFifth.
- rewrite /T4.zeta5 /FiftyFifthCyclotomicField.
  exact: rpredX memv_adjoin.
Qed.

Lemma fiftyFifthField_galois : galois 1 FiftyFifthCyclotomicField.
Proof.
exact: (galois_Fadjoin_cyclotomic
  (E := (1%AS : {subfield T4.Ambient})) T4.zeta55_primitive).
Qed.

Lemma fiftyFifthField_abelian :
  abelian 'Gal(FiftyFifthCyclotomicField / 1).
Proof. exact: abelian_cyclotomic T4.zeta55_primitive. Qed.

Lemma cyclic_lazard_formula_le_fiftyFifth b :
  (cyclic_lazard_formula_field b <= FiftyFifthCyclotomicField)%VS.
Proof.
exact: subv_trans (cyclic_lazard_formula_le_compositum b)
  cyclicCompositum_le_fiftyFifth.
Qed.

Lemma cyclic_lazard_formula_galois b :
  galois 1 (cyclic_lazard_formula_field b).
Proof.
have hchain :
    (1 <= cyclic_lazard_formula_field b <= FiftyFifthCyclotomicField)%VS.
  by rewrite sub1v cyclic_lazard_formula_le_fiftyFifth.
have hgal := galoisS hchain fiftyFifthField_galois.
have /galois_fixedField <- := hgal.
rewrite normal_fixedField_galois // -sub_abelian_normal ?galS //.
exact: fiftyFifthField_abelian.
Qed.

Lemma cyclic_lazard_base_formula_galois b :
  galois (cyclic_lazard_base_field b) (cyclic_lazard_formula_field b).
Proof.
have hchain :
    (1 <= cyclic_lazard_base_field b <= cyclic_lazard_formula_field b)%VS.
  by rewrite sub1v cyclic_lazard_base_le_formula.
exact: galoisS hchain (cyclic_lazard_formula_galois b).
Qed.

Lemma cyclic_lazard_relative_dim_gt_one b :
  (1 < \dim_(cyclic_lazard_base_field b)
      (cyclic_lazard_formula_field b))%N.
Proof.
rewrite ltn_neqAle; apply/andP; split.
- apply/eqP=> hone.
  have hdim := dim_sup_field (cyclic_lazard_base_le_formula b).
  rewrite -hone mul1n in hdim.
  have heq : cyclic_lazard_formula_field b = cyclic_lazard_base_field b.
    apply: val_inj; apply/eqP.
    rewrite eq_sym eqEdim cyclic_lazard_base_le_formula /= hdim eqxx.
  move: (cyclic_lazard_formula_neq_base b).
  by rewrite heq eqxx.
- exact: adim_gt0.
Qed.

Lemma exists_cyclic_lazard_conjugation b :
  {sigma : gal_of (cyclic_lazard_formula_field b) |
    sigma \in 'Gal(cyclic_lazard_formula_field b /
      cyclic_lazard_base_field b) &
    sigma (CRT.lazard_certificate_p1 (cyclic_lazard_certificate b)) !=
      CRT.lazard_certificate_p1 (cyclic_lazard_certificate b)}.
Proof.
have hcard :
    #|'Gal(cyclic_lazard_formula_field b /
      cyclic_lazard_base_field b)| > 1.
  rewrite -(galois_dim (cyclic_lazard_base_formula_galois b)).
  exact: cyclic_lazard_relative_dim_gt_one.
have hnontrivial :
    'Gal(cyclic_lazard_formula_field b /
      cyclic_lazard_base_field b) :!=: 1.
  by rewrite -cardG_gt1.
have [sigma hsigma hsigma1] := (elimT trivgPn hnontrivial).
exists sigma; first exact: hsigma.
apply/negP=> /eqP hp1fix.
apply: (negP hsigma1).
have heq := gal_adjoin_eq hsigma group1.
move: heq.
rewrite /cyclic_lazard_formula_field
  /CRT.lazard_certificate_generated_field gal_id hp1fix !eqxx.
Qed.

(* -------------------------------------------------------------------- *)
(** * Unconditional profile and Theorem-3 counterexample *)

Definition cyclic_lazard_formula_profile (b : cyclic_lazard_root_branch) :
  T3.cyclic_lazard_formula_field_profile
    (cyclic_lazard_base_field b) (cyclic_lazard_formula_field b).
Proof.
have [sigma hsigma hmove] := exists_cyclic_lazard_conjugation b.
refine
  {| T3.profile_p1 :=
       CRT.lazard_certificate_p1 (cyclic_lazard_certificate b);
     T3.profile_base_le_formula := cyclic_lazard_base_le_formula b;
     T3.profile_cyclicQuintic_le_formula :=
       cyclicQuinticField_le_lazard_formula b;
     T3.profile_formula_le_compositum :=
       cyclic_lazard_formula_le_compositum b;
     T3.profile_p1_mem := cyclic_lazard_p1_mem_formula b;
     T3.profile_p1_nonzero := cyclic_lazard_p1_neq0 b;
     T3.profile_p1_fifth_mem := cyclic_lazard_p1_fifth_mem_base b;
     T3.profile_formula_generated := cyclic_lazard_formula_generated b;
     T3.profile_conjugation := gal_repr sigma;
     T3.profile_conjugation_stable := _;
     T3.profile_conjugation_fixes_base := _;
     T3.profile_conjugation_moves_p1 := hmove |}.
- move=> x hx.
  exact: memv_gal sigma hx.
- move=> x hx.
  exact: fixed_gal (cyclic_lazard_base_le_formula b) hsigma hx.
Defined.

(** The degree-[20] formula field cannot even admit a rational algebra
    embedding into the degree-[10] radical competitor [ElevenField].  In
    particular, [ElevenField] contains no subextension rationally
    isomorphic to the formula field, which is the literal containment-up-to-
    isomorphism conclusion asserted by the printed Theorem 3. *)
Theorem cyclic_lazard_formula_no_embedding_in_elevenField b :
  forall f : 'AHom(subvs_of (cyclic_lazard_formula_field b),
                    subvs_of T4.ElevenField), False.
Proof.
move=> f.
have hker :
    ({:subvs_of (cyclic_lazard_formula_field b)} :&: lker f = 0)%VS.
  by rewrite (eqP (AHom_lker0 f)) capv0.
have himg :
    \dim (f @: {:subvs_of (cyclic_lazard_formula_field b)}) =
      \dim {:subvs_of (cyclic_lazard_formula_field b)}.
  exact: limg_dim_eq hker.
have hdim := dimvS
  (subvf (f @: {:subvs_of (cyclic_lazard_formula_field b)})).
move: hdim.
rewrite himg !dimvf.
change (\dim (cyclic_lazard_formula_field b) <=
  \dim T4.ElevenField)%N -> False.
by rewrite (T3.profile_formula_dim (cyclic_lazard_formula_profile b))
  T3.elevenField_dim.
Qed.

(** The literal conclusion of Theorem 3, expressed without identifying
    isomorphic fields by equality inside the common ambient field.  An
    algebra homomorphism between fields is injective; the last two clauses
    say that its image is exactly the proposed intermediate field [M]. *)
Definition has_isomorphic_radical_subextension
    (b : cyclic_lazard_root_branch) : Prop :=
  exists M : {subfield T4.Ambient},
    (M <= T4.ElevenField)%VS /\
    PolynomialFormulasLazardOptimality.radical_extension
      (L := T4.Ambient) 1 M /\
    T4.cyclic_quintic_root \in M /\
    exists f : 'AHom(subvs_of (cyclic_lazard_formula_field b),
                     subvs_of T4.ElevenField),
      (forall x, val (f x) \in M) /\
      (forall y : T4.Ambient, y \in M ->
        exists x : subvs_of (cyclic_lazard_formula_field b),
          val (f x) = y).

(** The stronger no-embedding theorem discharges the paper's exact
    isomorphic-radical-subextension conclusion, with no profile or
    counterexample property left as a premise. *)
Theorem cyclic_lazard_no_isomorphic_radical_subextension b :
  ~ has_isomorphic_radical_subextension b.
Proof.
move=> [M [hME [hMradical [hroot [f [himage hsurjective]]]]]].
exact: (cyclic_lazard_formula_no_embedding_in_elevenField b f).
Qed.

(** Closed statement-level refutation of the printed Theorem 3 conclusion.
    The displayed quintic is irreducible, and its solvability premise is
    witnessed directly: the literal radical extension [ElevenField] contains
    every root.  The actual formula field is also radical, but has no rational
    algebra embedding into that competitor. *)
Theorem lazard_theorem3_no_isomorphic_subextension_counterexample :
  exists b : cyclic_lazard_root_branch,
    [/\
      size T4.cyclic_quintic_Q = 6%N,
      T4.cyclic_quintic_Q \is monic,
      irreducible_poly T4.cyclic_quintic_Q,
      root (map_poly (in_alg T4.Ambient) T4.cyclic_quintic_Q)
        T4.cyclic_quintic_root,
      (exists rs : seq T4.Ambient,
        all [in T4.ElevenField] rs /\
        map_poly (in_alg T4.Ambient) T4.cyclic_quintic_Q =
          \prod_(x <- rs) ('X - x%:P)),
      (forall x, T4.is_cyclic_quintic_root x -> x \in T4.ElevenField),
      PolynomialFormulasLazardOptimality.radical_extension
        (L := T4.Ambient) 1 T4.ElevenField,
      T4.cyclic_quintic_root \in T4.ElevenField,
      PolynomialFormulasLazardOptimality.radical_extension
        (L := T4.Ambient) 1 (cyclic_lazard_formula_field b),
      T4.cyclic_quintic_root \in cyclic_lazard_formula_field b,
      \dim (cyclic_lazard_formula_field b) = 20%N,
      ~ has_isomorphic_radical_subextension b
    & (forall f : 'AHom(subvs_of (cyclic_lazard_formula_field b),
                         subvs_of T4.ElevenField), False)].
Proof.
exists exists_cyclic_lazard_root_branch.
split.
- exact: T4.cyclic_quintic_Q_size.
- exact: T4.cyclic_quintic_Q_monic.
- exact: T4.cyclic_quintic_Q_irreducible.
- exact: T4.cyclic_quintic_root_is_root.
- exact: T4.cyclic_quintic_splits_in_ElevenFieldP.
- exact: T4.every_cyclic_quintic_root_in_ElevenField.
- exact: T4.ElevenField_radical_extension.
- exact: T3.cyclic_quintic_root_mem_elevenField.
- exact: cyclic_lazard_formula_is_radical.
- exact: cyclic_quintic_root_mem_lazard_formula.
- exact: T3.profile_formula_dim
    (cyclic_lazard_formula_profile exists_cyclic_lazard_root_branch).
- exact: cyclic_lazard_no_isomorphic_radical_subextension.
- exact: cyclic_lazard_formula_no_embedding_in_elevenField.
Qed.

Theorem lazard_theorem3_unconditional_counterexample :
  exists (b : cyclic_lazard_root_branch)
      (K0 E : {subfield T4.Ambient})
      (P : T3.cyclic_lazard_formula_field_profile K0 E),
    [/\
      size T4.cyclic_quintic_Q = 6%N,
      T4.cyclic_quintic_Q \is monic,
      irreducible_poly T4.cyclic_quintic_Q,
      root (map_poly (in_alg T4.Ambient) T4.cyclic_quintic_Q)
        T4.cyclic_quintic_root,
      T4.cyclic_quintic_root \in T4.ElevenField,
      PolynomialFormulasLazardOptimality.radical_extension
        (L := T4.Ambient) 1 T4.ElevenField,
      \dim T4.ElevenField = 10%N,
      E = T3.CyclicQuinticCompositum,
      \dim E = 20%N
    & ~ (E <= T4.ElevenField)%VS].
Proof.
exists exists_cyclic_lazard_root_branch.
exists (cyclic_lazard_base_field exists_cyclic_lazard_root_branch).
exists (cyclic_lazard_formula_field exists_cyclic_lazard_root_branch).
exists (cyclic_lazard_formula_profile exists_cyclic_lazard_root_branch).
exact: T3.lazard_theorem3_conditional_counterexample
  (cyclic_lazard_formula_profile exists_cyclic_lazard_root_branch).
Qed.

End PolynomialFormulasLazardOptimalityTheoremThreeFormulaBridge.
