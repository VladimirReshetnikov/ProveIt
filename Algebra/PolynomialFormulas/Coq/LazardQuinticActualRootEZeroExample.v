From Stdlib Require Import Ring.
From mathcomp Require Import
  all_ssreflect all_fingroup all_algebra all_field complex.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticRootRadicals
  LazardQuinticRootProjections LazardQuinticQuadratic
  LazardQuinticFourierNumerators LazardQuinticRootInvariantE
  LazardQuinticRootInvariantDFG LazardQuinticVieta
  LazardQuinticCoherentAlternateProjection
  LazardQuinticRootAlternateRecovery
  LazardQuinticRootFourierRelations
  LazardQuinticAlternateCertificateRadicalTower
  LazardQuinticRootCompleteAlternateTower
  LazardQuinticRootExtensionTransport.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** A concrete, reducible root-level example on Lazard's exceptional
    [E = 0] locus.

    The five roots are Gaussian integers and hence Gaussian rationals.  All
    numerical identities below are conversion proofs over the transparent
    definitions of [rat[i]]; [vm_compute] is used only for these finite exact
    calculations.  There is no irreducibility claim in this file.

    A primitive fifth root need not belong to [rat[i]].  The final section
    therefore transports the tuple through the canonical embedding into an
    arbitrary field extension which contains such a root.  It instantiates
    the already proved coherent-alternate recovery and Fourier-inversion
    theorems there. *)
Module PolynomialFormulasLazardQuinticActualRootEZeroExample.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Local Open Scope ring_scope.
Local Open Scope complex_scope.

Module RR := PolynomialFormulasLazardQuinticRootRadicals.
Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module Q := PolynomialFormulasLazardQuinticQuadratic.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.
Module RIE := PolynomialFormulasLazardQuinticRootInvariantE.
Module DFG := PolynomialFormulasLazardQuinticRootInvariantDFG.
Module V := PolynomialFormulasLazardQuinticVieta.
Module P := PolynomialFormulasLazardQuinticProjection.
Module C := PolynomialFormulasLazardQuinticCoherentAlternateProjection.
Module RA := PolynomialFormulasLazardQuinticRootAlternateRecovery.
Module RFR := PolynomialFormulasLazardQuinticRootFourierRelations.
Module ACT := PolynomialFormulasLazardQuinticAlternateCertificateRadicalTower.
Module RCT := PolynomialFormulasLazardQuinticRootCompleteAlternateTower.
Module RET := PolynomialFormulasLazardQuinticRootExtensionTransport.

Local Notation Gaussian := rat[i].

Definition lazard_ezero_gaussian_integer (a b : int) : Gaussian :=
  ((a%:~R : rat) +i* (b%:~R : rat))%C.

Definition lazard_ezero_roots : 5.-tuple Gaussian :=
  [tuple lazard_ezero_gaussian_integer (-1) 0;
         lazard_ezero_gaussian_integer 1 1;
         lazard_ezero_gaussian_integer (-2) (-3);
         lazard_ezero_gaussian_integer 5 (-2);
         lazard_ezero_gaussian_integer (-3) 4].

Definition lazard_ezero_quintic :
    RP.LazardDepressedRootCoefficients Gaussian :=
  {| RP.lazard_root_p := lazard_ezero_gaussian_integer (-5) 15;
     RP.lazard_root_q := lazard_ezero_gaussian_integer (-75) 35;
     RP.lazard_root_r := lazard_ezero_gaussian_integer 52 81;
     RP.lazard_root_s := lazard_ezero_gaussian_integer 123 61 |}.

Definition lazard_ezero_invariants : RP.LazardRootInvariants Gaussian :=
  {| RP.lazard_root_i4 := lazard_ezero_gaussian_integer 194 (-118);
     RP.lazard_root_i5 := lazard_ezero_gaussian_integer 1195 (-3135);
     RP.lazard_root_i6 := lazard_ezero_gaussian_integer 2500 (-15250);
     RP.lazard_root_i7 := lazard_ezero_gaussian_integer 30825 (-47405);
     RP.lazard_root_i8 := lazard_ezero_gaussian_integer 57768 (-259316) |}.

(** The roots are pairwise distinct. *)
Lemma lazard_ezero_roots_injective :
  injective (tnth lazard_ezero_roots).
Proof.
apply/tuple_uniqP.
vm_compute.
Qed.

(** Exact elementary symmetric coordinates. *)
Lemma lazard_ezero_root_esymm1 :
  RP.lazard_root_esymm1 lazard_ezero_roots = 0.
Proof. vm_compute. Qed.

Lemma lazard_ezero_root_esymm2 :
  RP.lazard_root_esymm2 lazard_ezero_roots =
    lazard_ezero_gaussian_integer (-5) 15.
Proof. vm_compute. Qed.

Lemma lazard_ezero_root_esymm3 :
  RP.lazard_root_esymm3 lazard_ezero_roots =
    lazard_ezero_gaussian_integer 75 (-35).
Proof. vm_compute. Qed.

Lemma lazard_ezero_root_esymm4 :
  RP.lazard_root_esymm4 lazard_ezero_roots =
    lazard_ezero_gaussian_integer 52 81.
Proof. vm_compute. Qed.

Lemma lazard_ezero_root_esymm5 :
  RP.lazard_root_esymm5 lazard_ezero_roots =
    lazard_ezero_gaussian_integer (-123) (-61).
Proof. vm_compute. Qed.

Theorem lazard_ezero_depressed_of_roots :
  RP.lazard_depressed_of_roots lazard_ezero_roots =
    lazard_ezero_quintic.
Proof. vm_compute. Qed.

(** Exact evaluation of Lazard's five root-orbit invariants. *)
Theorem lazard_ezero_root_invariants :
  RP.lazard_root_invariants lazard_ezero_roots =
    lazard_ezero_invariants.
Proof. vm_compute. Qed.

(** Exact cyclic products. *)
Theorem lazard_ezero_root_T_prime :
  RR.lazard_root_T_prime lazard_ezero_roots =
    lazard_ezero_gaussian_integer (-3452) 764.
Proof. vm_compute. Qed.

Theorem lazard_ezero_root_U_prime :
  RR.lazard_root_U_prime lazard_ezero_roots =
    lazard_ezero_gaussian_integer (-764) (-3452).
Proof. vm_compute. Qed.

Theorem lazard_ezero_root_U_prime_eq_i_mul_T_prime :
  RR.lazard_root_U_prime lazard_ezero_roots =
    'i%C * RR.lazard_root_T_prime lazard_ezero_roots.
Proof. vm_compute. Qed.

(** This is the exact relation forcing the root-side [E] to vanish. *)
Theorem lazard_ezero_root_TU_prime_square_sum :
  RR.lazard_root_T_prime lazard_ezero_roots ^+ 2 +
      RR.lazard_root_U_prime lazard_ezero_roots ^+ 2 = 0.
Proof. vm_compute. Qed.

Theorem lazard_ezero_epsilon_product :
  RR.lazard_epsilon_product lazard_ezero_roots =
    lazard_ezero_gaussian_integer (-15625) 15625.
Proof. vm_compute. Qed.

(** [RootExtensionTransport] uses the projection-module spelling of the
    same transparent root product. *)
Theorem lazard_ezero_projection_epsilon_product :
  RP.lazard_root_epsilon_product lazard_ezero_roots =
    lazard_ezero_gaussian_integer (-15625) 15625.
Proof. vm_compute. Qed.

Corollary lazard_ezero_epsilon_product_neq0 :
  RR.lazard_epsilon_product lazard_ezero_roots != 0.
Proof. vm_compute. Qed.

Corollary lazard_ezero_projection_epsilon_product_neq0 :
  RP.lazard_root_epsilon_product lazard_ezero_roots != 0.
Proof. vm_compute. Qed.

Theorem lazard_ezero_root_E :
  Q.lazard_root_E lazard_ezero_roots = 0.
Proof.
by rewrite /Q.lazard_root_E lazard_ezero_root_TU_prime_square_sum oppr0.
Qed.

(** The displayed coefficient invariant [E] is zero, not merely its shorter
    root expression. *)
Theorem lazard_ezero_invariant_E :
  FN.lazard_invariant_E
      (RP.lazard_depressed_of_roots lazard_ezero_roots)
      (RP.lazard_root_invariants lazard_ezero_roots) = 0.
Proof.
rewrite (@RIE.lazard_root_invariant_E_eq Gaussian lazard_ezero_roots
  lazard_ezero_root_esymm1).
exact: lazard_ezero_root_E.
Qed.

(** Exact values of the other three displayed quadratic-stage invariants. *)
Theorem lazard_ezero_invariant_D :
  DFG.lazard_invariant_D
      (RP.lazard_depressed_of_roots lazard_ezero_roots)
      (RP.lazard_root_invariants lazard_ezero_roots) =
    lazard_ezero_gaussian_integer 0 (-488281250).
Proof.
rewrite (@DFG.lazard_root_invariant_D_eq Gaussian lazard_ezero_roots
  lazard_ezero_root_esymm1) /Q.lazard_root_D
  lazard_ezero_epsilon_product.
vm_compute.
Qed.

Theorem lazard_ezero_invariant_F :
  DFG.lazard_invariant_F
      (RP.lazard_depressed_of_roots lazard_ezero_roots)
      (RP.lazard_root_invariants lazard_ezero_roots) =
    lazard_ezero_gaussian_integer 1227265000000 (-140355000000).
Proof.
rewrite (@DFG.lazard_root_invariant_F_eq Gaussian lazard_ezero_roots
  lazard_ezero_root_esymm1) /Q.lazard_root_F
  lazard_ezero_epsilon_product lazard_ezero_root_T_prime
  lazard_ezero_root_U_prime.
vm_compute.
Qed.

Theorem lazard_ezero_invariant_G :
  DFG.lazard_invariant_G
      (RP.lazard_depressed_of_roots lazard_ezero_roots)
      (RP.lazard_root_invariants lazard_ezero_roots) =
    lazard_ezero_gaussian_integer 70177500000 613632500000.
Proof.
rewrite (@DFG.lazard_root_invariant_G_eq Gaussian lazard_ezero_roots
  lazard_ezero_root_esymm1) /Q.lazard_root_G
  lazard_ezero_epsilon_product lazard_ezero_root_T_prime
  lazard_ezero_root_U_prime.
vm_compute.
Qed.

(** The tuple gives the exact multiplicity-sensitive factorization of the
    displayed depressed quintic. *)
Definition lazard_ezero_five_root_relations :
    V.lazard_depressed_five_root_relations
      (lazard_ezero_gaussian_integer (-5) 15)
      (lazard_ezero_gaussian_integer (-75) 35)
      (lazard_ezero_gaussian_integer 52 81)
      (lazard_ezero_gaussian_integer 123 61)
      (tnth lazard_ezero_roots).
Proof.
constructor <;> vm_compute.
Defined.

Theorem lazard_ezero_eval_factorization (z : Gaussian) :
  V.lazard_depressed_quintic_eval
      (lazard_ezero_gaussian_integer (-5) 15)
      (lazard_ezero_gaussian_integer (-75) 35)
      (lazard_ezero_gaussian_integer 52 81)
      (lazard_ezero_gaussian_integer 123 61) z =
    (z - tnth lazard_ezero_roots o0) *
    (z - tnth lazard_ezero_roots o1) *
    (z - tnth lazard_ezero_roots o2) *
    (z - tnth lazard_ezero_roots o3) *
    (z - tnth lazard_ezero_roots o4).
Proof.
exact: V.lazard_depressed_vieta_eval_factorization
  lazard_ezero_five_root_relations z.
Qed.

Lemma lazard_ezero_gaussian_two_neq0 : (2%:R : Gaussian) != 0.
Proof. vm_compute. Qed.

Lemma lazard_ezero_gaussian_five_neq0 : (5%:R : Gaussian) != 0.
Proof. vm_compute. Qed.

(* -------------------------------------------------------------------- *)
(** * Evaluation in a field containing a primitive fifth root *)

Section RadicalTarget.

Variable L : fieldExtType Gaussian.

Definition lazard_ezero_mapped_roots : 5.-tuple L :=
  map_tuple (in_alg L) lazard_ezero_roots.

Lemma lazard_ezero_mapped_roots_injective :
  injective (tnth lazard_ezero_mapped_roots).
Proof.
exact: (@RET.lazard_extension_map_tuple_injective
  Gaussian L (in_alg L) lazard_ezero_roots lazard_ezero_roots_injective).
Qed.

Lemma lazard_ezero_mapped_sum :
  RP.lazard_root_esymm1 lazard_ezero_mapped_roots = 0.
Proof.
rewrite /lazard_ezero_mapped_roots
  -(@RET.lazard_extension_root_esymm1_map
    Gaussian L (in_alg L) lazard_ezero_roots)
  lazard_ezero_root_esymm1 rmorph0.
Qed.

Lemma lazard_ezero_mapped_root_E :
  Q.lazard_root_E lazard_ezero_mapped_roots = 0.
Proof.
rewrite /lazard_ezero_mapped_roots
  -(@RET.lazard_extension_root_E_map
    Gaussian L (in_alg L) lazard_ezero_roots)
  lazard_ezero_root_E rmorph0.
Qed.

Lemma lazard_ezero_mapped_two_neq0 : (2%:R : L) != 0.
Proof.
rewrite -[2%:R](rmorph_nat (in_alg L) 2) fmorph_eq0.
exact: lazard_ezero_gaussian_two_neq0.
Qed.

Lemma lazard_ezero_mapped_five_neq0 : (5%:R : L) != 0.
Proof.
rewrite -[5%:R](rmorph_nat (in_alg L) 5) fmorph_eq0.
exact: lazard_ezero_gaussian_five_neq0.
Qed.

(** Every primitive fifth-root choice gives nonzero epsilon on the mapped
    tuple. *)
Theorem lazard_ezero_mapped_projection_root_epsilon_neq0
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  RP.lazard_root_epsilon omega lazard_ezero_mapped_roots != 0.
Proof.
rewrite /lazard_ezero_mapped_roots.
exact: (@RET.lazard_extension_mapped_root_epsilon_neq0
  Gaussian L (in_alg L) lazard_ezero_mapped_five_neq0
  lazard_ezero_roots lazard_ezero_projection_epsilon_product_neq0
  omega omega_primitive).
Qed.

Corollary lazard_ezero_mapped_root_epsilon_neq0
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  RR.lazard_root_epsilon omega lazard_ezero_mapped_roots != 0.
Proof.
change (RP.lazard_root_epsilon omega lazard_ezero_mapped_roots != 0).
exact: lazard_ezero_mapped_projection_root_epsilon_neq0 omega_primitive.
Qed.

(** The standard projection denominator really vanishes. *)
Theorem lazard_ezero_mapped_standard_denominator
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  RR.lazard_root_T omega lazard_ezero_mapped_roots ^+ 2 +
      RR.lazard_root_formula_U omega lazard_ezero_mapped_roots ^+ 2 = 0.
Proof.
have hcyclo := RR.lazard_primitive_fifth_root_cyclotomic omega_primitive.
rewrite (@Q.lazard_root_E_identity L omega lazard_ezero_mapped_roots
  hcyclo) lazard_ezero_mapped_root_E mulr0.
Qed.

(** Thus the printed projection matrix is singular on the mapped tuple. *)
Theorem lazard_ezero_mapped_standard_projection_matrix_det
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  \det (P.lazard_standard_projection_matrix
      (RR.lazard_root_epsilon omega lazard_ezero_mapped_roots)
      (RR.lazard_root_T omega lazard_ezero_mapped_roots)
      (RR.lazard_root_formula_U omega lazard_ezero_mapped_roots)) = 0.
Proof.
by rewrite P.lazard_standard_projection_matrix_det
  (lazard_ezero_mapped_standard_denominator omega_primitive) mulr0.
Qed.

(** The convention-safe alternate denominator is nevertheless nonzero. *)
Theorem lazard_ezero_mapped_coherent_alternate_denominator_neq0
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  C.lazard_coherent_alternate_denominator
      (RR.lazard_root_T omega lazard_ezero_mapped_roots)
      (RR.lazard_root_formula_U omega lazard_ezero_mapped_roots) != 0.
Proof.
have hcyclo := RR.lazard_primitive_fifth_root_cyclotomic omega_primitive.
exact: (@RA.lazard_root_coherent_alternate_denominator_neq0
  L omega lazard_ezero_mapped_roots hcyclo
  lazard_ezero_mapped_five_neq0 lazard_ezero_mapped_roots_injective).
Qed.

(** The corrected projection matrix is nonsingular on the same tuple. *)
Theorem lazard_ezero_mapped_coherent_alternate_projection_matrix_det_neq0
    (omega : L) (omega_primitive : 5.-primitive_root omega) :
  \det (C.lazard_coherent_alternate_projection_matrix
      (RR.lazard_root_epsilon omega lazard_ezero_mapped_roots)
      (RR.lazard_root_T omega lazard_ezero_mapped_roots)
      (RR.lazard_root_formula_U omega lazard_ezero_mapped_roots)) != 0.
Proof.
exact: C.lazard_coherent_alternate_projection_matrix_det_neq0
  lazard_ezero_mapped_two_neq0
  (lazard_ezero_mapped_root_epsilon_neq0 omega_primitive)
  (lazard_ezero_mapped_coherent_alternate_denominator_neq0 omega_primitive).
Qed.

(** The corrected projections genuinely recover each of the four actual
    Fourier fifth powers.  This is the coherent-alternate certificate step,
    and it uses no [E != 0] premise. *)
Theorem lazard_ezero_mapped_complete_alternate_component_fifth
    (omega : L) (omega_primitive : 5.-primitive_root omega)
    (j : 'I_4) :
  RCT.lazard_root_complete_alternate_source
      omega lazard_ezero_mapped_roots j ^+ 5 =
    C.lazard_coherent_alternate_recover
      (Q.lazard_epsilon
        (Q.lazard_branch_triple
          (RCT.lazard_root_complete_alternate_triple
            omega lazard_ezero_mapped_roots)
          (ACT.lazard_branch_for_orbit_index j)))
      (Q.lazard_t
        (Q.lazard_branch_triple
          (RCT.lazard_root_complete_alternate_triple
            omega lazard_ezero_mapped_roots)
          (ACT.lazard_branch_for_orbit_index j)))
      (Q.lazard_u
        (Q.lazard_branch_triple
          (RCT.lazard_root_complete_alternate_triple
            omega lazard_ezero_mapped_roots)
          (ACT.lazard_branch_for_orbit_index j)))
      (RCT.lazard_root_complete_alternate_projections
        omega lazard_ezero_mapped_roots).
Proof.
exact: (@RCT.lazard_root_complete_alternate_component_fifth
  Gaussian L omega lazard_ezero_mapped_roots
  lazard_ezero_mapped_two_neq0 lazard_ezero_mapped_five_neq0
  omega_primitive lazard_ezero_mapped_roots_injective
  (lazard_ezero_mapped_projection_root_epsilon_neq0 omega_primitive) j).
Qed.

(** Fourier inversion reconstructs the five mapped roots, up to the
    documented reversal permutation. *)
Theorem lazard_ezero_mapped_complete_alternate_outputE
    (omega : L) (omega_primitive : 5.-primitive_root omega)
    (k : 'I_5) :
  RCT.lazard_root_complete_alternate_output
      omega lazard_ezero_mapped_roots k =
    RFR.lazard_reversed_root_tuple lazard_ezero_mapped_roots k.
Proof.
exact: (@RCT.lazard_root_complete_alternate_outputE
  Gaussian L omega lazard_ezero_mapped_roots
  lazard_ezero_mapped_five_neq0 omega_primitive
  lazard_ezero_mapped_sum k).
Qed.

(** The mapped tuple still has the four explicit Gaussian-integer
    coefficients displayed above. *)
Lemma lazard_ezero_mapped_depressed_p :
  RP.lazard_root_p
      (RP.lazard_depressed_of_roots lazard_ezero_mapped_roots) =
    in_alg L (lazard_ezero_gaussian_integer (-5) 15).
Proof.
rewrite /lazard_ezero_mapped_roots
  -(@RET.lazard_depressed_p_map Gaussian Gaussian L (in_alg L)
    lazard_ezero_roots)
  lazard_ezero_depressed_of_roots.
reflexivity.
Qed.

Lemma lazard_ezero_mapped_depressed_q :
  RP.lazard_root_q
      (RP.lazard_depressed_of_roots lazard_ezero_mapped_roots) =
    in_alg L (lazard_ezero_gaussian_integer (-75) 35).
Proof.
rewrite /lazard_ezero_mapped_roots
  -(@RET.lazard_depressed_q_map Gaussian Gaussian L (in_alg L)
    lazard_ezero_roots)
  lazard_ezero_depressed_of_roots.
reflexivity.
Qed.

Lemma lazard_ezero_mapped_depressed_r :
  RP.lazard_root_r
      (RP.lazard_depressed_of_roots lazard_ezero_mapped_roots) =
    in_alg L (lazard_ezero_gaussian_integer 52 81).
Proof.
rewrite /lazard_ezero_mapped_roots
  -(@RET.lazard_depressed_r_map Gaussian Gaussian L (in_alg L)
    lazard_ezero_roots)
  lazard_ezero_depressed_of_roots.
reflexivity.
Qed.

Lemma lazard_ezero_mapped_depressed_s :
  RP.lazard_root_s
      (RP.lazard_depressed_of_roots lazard_ezero_mapped_roots) =
    in_alg L (lazard_ezero_gaussian_integer 123 61).
Proof.
rewrite /lazard_ezero_mapped_roots
  -(@RET.lazard_depressed_s_map Gaussian Gaussian L (in_alg L)
    lazard_ezero_roots)
  lazard_ezero_depressed_of_roots.
reflexivity.
Qed.

(** Exact factorization of the mapped explicit [E = 0] quintic by the five
    corrected alternate outputs. *)
Theorem lazard_ezero_mapped_complete_alternate_eval_factorization
    (omega : L) (omega_primitive : 5.-primitive_root omega) (z : L) :
  V.lazard_depressed_quintic_eval
      (in_alg L (lazard_ezero_gaussian_integer (-5) 15))
      (in_alg L (lazard_ezero_gaussian_integer (-75) 35))
      (in_alg L (lazard_ezero_gaussian_integer 52 81))
      (in_alg L (lazard_ezero_gaussian_integer 123 61)) z =
    (z - RCT.lazard_root_complete_alternate_output
      omega lazard_ezero_mapped_roots o0) *
    (z - RCT.lazard_root_complete_alternate_output
      omega lazard_ezero_mapped_roots o1) *
    (z - RCT.lazard_root_complete_alternate_output
      omega lazard_ezero_mapped_roots o2) *
    (z - RCT.lazard_root_complete_alternate_output
      omega lazard_ezero_mapped_roots o3) *
    (z - RCT.lazard_root_complete_alternate_output
      omega lazard_ezero_mapped_roots o4).
Proof.
rewrite -lazard_ezero_mapped_depressed_p
  -lazard_ezero_mapped_depressed_q
  -lazard_ezero_mapped_depressed_r
  -lazard_ezero_mapped_depressed_s.
exact: (@RCT.lazard_root_complete_alternate_eval_factorization
  Gaussian L omega lazard_ezero_mapped_roots
  lazard_ezero_mapped_five_neq0 omega_primitive
  lazard_ezero_mapped_sum z).
Qed.

(** Every corrected alternate output is a root of the mapped explicit
    quintic. *)
Theorem lazard_ezero_mapped_complete_alternate_output_root
    (omega : L) (omega_primitive : 5.-primitive_root omega) (k : 'I_5) :
  V.lazard_depressed_quintic_eval
      (in_alg L (lazard_ezero_gaussian_integer (-5) 15))
      (in_alg L (lazard_ezero_gaussian_integer (-75) 35))
      (in_alg L (lazard_ezero_gaussian_integer 52 81))
      (in_alg L (lazard_ezero_gaussian_integer 123 61))
      (RCT.lazard_root_complete_alternate_output
        omega lazard_ezero_mapped_roots k) = 0.
Proof.
rewrite -lazard_ezero_mapped_depressed_p
  -lazard_ezero_mapped_depressed_q
  -lazard_ezero_mapped_depressed_r
  -lazard_ezero_mapped_depressed_s.
exact: (@RCT.lazard_root_complete_alternate_output_root
  Gaussian L omega lazard_ezero_mapped_roots
  lazard_ezero_mapped_five_neq0 omega_primitive
  lazard_ezero_mapped_sum k).
Qed.

(** Every root of the mapped explicit quintic occurs among the five
    corrected alternate outputs. *)
Theorem lazard_ezero_mapped_complete_alternate_output_complete
    (omega : L) (omega_primitive : 5.-primitive_root omega) (z : L)
    (hz : V.lazard_depressed_quintic_eval
      (in_alg L (lazard_ezero_gaussian_integer (-5) 15))
      (in_alg L (lazard_ezero_gaussian_integer (-75) 35))
      (in_alg L (lazard_ezero_gaussian_integer 52 81))
      (in_alg L (lazard_ezero_gaussian_integer 123 61)) z = 0) :
  exists k : 'I_5,
    z = RCT.lazard_root_complete_alternate_output
      omega lazard_ezero_mapped_roots k.
Proof.
apply: (@RCT.lazard_root_complete_alternate_output_complete
  Gaussian L omega lazard_ezero_mapped_roots
  lazard_ezero_mapped_five_neq0 omega_primitive
  lazard_ezero_mapped_sum z).
move: hz.
by rewrite -lazard_ezero_mapped_depressed_p
  -lazard_ezero_mapped_depressed_q
  -lazard_ezero_mapped_depressed_r
  -lazard_ezero_mapped_depressed_s.
Qed.

End RadicalTarget.

End PolynomialFormulasLazardQuinticActualRootEZeroExample.
