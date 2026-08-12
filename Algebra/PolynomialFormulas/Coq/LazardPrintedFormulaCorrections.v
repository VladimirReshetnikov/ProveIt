From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra all_field.
From PolynomialFormulas Require Import LazardQuinticFourierNumerators.
From PolynomialFormulas Require Import
  QuinticGaloisAction QuinticRecursiveFactor QuinticCanonicalDecision.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The literal P22 display in Lazard's paper and its exact discrepancy from
    the corrected formula used by the formal reconstruction.

    The printed display contains [8 p^3] and [70 q^3 q].  The corrected
    formula contains [8 p^3 q] and [70 q^3].  The theorem below proves the
    resulting error term as an ordinary ring identity, and the rational
    specialization [p = 1], [q = r = s = 0] with all invariants zero shows
    that the two expressions are genuinely different. *)
Module PolynomialFormulasLazardPrintedFormulaCorrections.

Import GRing.Theory.
Local Open Scope ring_scope.

Module RP := PolynomialFormulasLazardQuinticRootProjections.
Module FN := PolynomialFormulasLazardQuinticFourierNumerators.

Section PrintedIdentity.

Variable F : fieldType.

(** Lazard's P22 exactly as printed, before the two corrections. *)
Definition lazard_printed_p22
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) : F :=
  25%:R *
    (- 10%:R * RP.lazard_root_q c * RP.lazard_root_i6 i +
      (8%:R * RP.lazard_root_p c ^+ 2 -
        50%:R * RP.lazard_root_r c) * RP.lazard_root_i5 i +
      (- 2%:R * RP.lazard_root_p c * RP.lazard_root_q c -
        25%:R * RP.lazard_root_s c) * RP.lazard_root_i4 i +
      8%:R * RP.lazard_root_p c ^+ 3 +
      70%:R * RP.lazard_root_q c ^+ 3 * RP.lazard_root_q c -
      20%:R * RP.lazard_root_p c ^+ 2 * RP.lazard_root_s c -
      26%:R * RP.lazard_root_p c * RP.lazard_root_q c *
        RP.lazard_root_r c +
      50%:R * RP.lazard_root_r c * RP.lazard_root_s c).

(** Local bridge from MathComp's packed field operations to Stdlib [ring]. *)
Let ring_carrier : Type := F.
Local Definition ring_zero : ring_carrier := @GRing.zero F.
Local Definition ring_one : ring_carrier := @GRing.one F.
Local Definition ring_add : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.add F.
Local Definition ring_mul : ring_carrier -> ring_carrier -> ring_carrier :=
  @GRing.mul F.
Local Definition ring_sub : ring_carrier -> ring_carrier -> ring_carrier :=
  fun x y => x - y.
Local Definition ring_opp : ring_carrier -> ring_carrier := @GRing.opp F.
Local Definition ring_eq : ring_carrier -> ring_carrier -> Prop :=
  @eq ring_carrier.

Lemma lazard_printed_p22_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma lazard_printed_p22_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma lazard_printed_p22_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma lazard_printed_p22_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma lazard_printed_p22_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma lazard_printed_p22_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma lazard_printed_p22_ring_theory :
  @ring_theory ring_carrier ring_zero ring_one ring_add ring_mul
    ring_sub ring_opp ring_eq.
Proof.
constructor; unfold ring_zero, ring_one, ring_add, ring_mul, ring_sub,
  ring_opp, ring_eq; intros.
- exact: add0r.
- exact: addrC.
- exact: addrA.
- exact: mul1r.
- exact: mulrC.
- exact: mulrA.
- exact: mulrDl.
- reflexivity.
- exact: addrN.
Qed.

Add Ring lazard_printed_p22_ring : lazard_printed_p22_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Ltac finish_lazard_printed_p22_ring :=
  repeat first
    [ rewrite lazard_printed_p22_ring_addE
    | rewrite lazard_printed_p22_ring_mulE
    | rewrite lazard_printed_p22_ring_subE
    | rewrite lazard_printed_p22_ring_oppE
    | rewrite lazard_printed_p22_ring_zeroE
    | rewrite lazard_printed_p22_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

(** The exact error term introduced by the two printed monomials. *)
Theorem lazard_p22_sub_printed_p22
    (c : RP.LazardDepressedRootCoefficients F)
    (i : RP.LazardRootInvariants F) :
  FN.lazard_p22 c i - lazard_printed_p22 c i =
    25%:R * (RP.lazard_root_q c - 1) *
      (8%:R * RP.lazard_root_p c ^+ 3 -
        70%:R * RP.lazard_root_q c ^+ 3).
Proof.
rewrite /FN.lazard_p22 /lazard_printed_p22.
finish_lazard_printed_p22_ring.
Qed.

End PrintedIdentity.

Section RationalCounterexample.

Definition lazard_printed_p22_counterexample_coefficients :
    RP.LazardDepressedRootCoefficients rat :=
  {| RP.lazard_root_p := 1;
     RP.lazard_root_q := 0;
     RP.lazard_root_r := 0;
     RP.lazard_root_s := 0 |}.

Definition lazard_printed_p22_counterexample_invariants :
    RP.LazardRootInvariants rat :=
  {| RP.lazard_root_i4 := 0;
     RP.lazard_root_i5 := 0;
     RP.lazard_root_i6 := 0;
     RP.lazard_root_i7 := 0;
     RP.lazard_root_i8 := 0 |}.

Theorem lazard_printed_p22_counterexample :
  lazard_printed_p22 lazard_printed_p22_counterexample_coefficients
      lazard_printed_p22_counterexample_invariants = (200%:R : rat) /\
  FN.lazard_p22 lazard_printed_p22_counterexample_coefficients
      lazard_printed_p22_counterexample_invariants = 0.
Proof. split; vm_compute; reflexivity. Qed.

Theorem lazard_printed_p22_ne_corrected_p22 :
  lazard_printed_p22 lazard_printed_p22_counterexample_coefficients
      lazard_printed_p22_counterexample_invariants <>
  FN.lazard_p22 lazard_printed_p22_counterexample_coefficients
      lazard_printed_p22_counterexample_invariants.
Proof.
move=> h.
have hne : (200%:R : rat) != 0 by vm_compute.
move: hne.
rewrite -lazard_printed_p22_counterexample.1
  -lazard_printed_p22_counterexample.2 h eqxx.
by [].
Qed.

(** ** A counterexample on genuine root-origin data

    The arbitrary invariant tuple above is enough to separate the two
    polynomial expressions.  The next specialization is stronger: both the
    depressed coefficients and the five Lazard invariants are constructed
    from one actual centered five-tuple of roots. *)

Definition lazard_printed_p22_root_counterexample : 5.-tuple rat :=
  [tuple 1; -1; 2; -2; 0].

Definition lazard_printed_p22_root_coefficients :
    RP.LazardDepressedRootCoefficients rat :=
  RP.lazard_depressed_of_roots lazard_printed_p22_root_counterexample.

Definition lazard_printed_p22_root_invariants :
    RP.LazardRootInvariants rat :=
  RP.lazard_root_invariants lazard_printed_p22_root_counterexample.

Lemma lazard_printed_p22_root_counterexample_centered :
  RP.lazard_root_esymm1 lazard_printed_p22_root_counterexample = 0.
Proof. vm_compute; reflexivity. Qed.

Lemma lazard_printed_p22_root_coefficientsE :
  lazard_printed_p22_root_coefficients =
    {| RP.lazard_root_p := -5;
       RP.lazard_root_q := 0;
       RP.lazard_root_r := 4;
       RP.lazard_root_s := 0 |}.
Proof. vm_compute; reflexivity. Qed.

(** The corrected value minus the literal printed value is nonzero even on
    this root-origin specialization. *)
Theorem lazard_corrected_p22_sub_printed_p22_root_origin :
  FN.lazard_p22 lazard_printed_p22_root_coefficients
      lazard_printed_p22_root_invariants -
    lazard_printed_p22 lazard_printed_p22_root_coefficients
      lazard_printed_p22_root_invariants = (25000%:R : rat).
Proof.
rewrite lazard_p22_sub_printed_p22
  lazard_printed_p22_root_coefficientsE.
by vm_compute.
Qed.

Theorem lazard_printed_p22_ne_corrected_p22_on_root_origin :
  lazard_printed_p22 lazard_printed_p22_root_coefficients
      lazard_printed_p22_root_invariants <>
    FN.lazard_p22 lazard_printed_p22_root_coefficients
      lazard_printed_p22_root_invariants.
Proof.
move=> h.
have hd := lazard_corrected_p22_sub_printed_p22_root_origin.
move: hd; rewrite h subrr.
by vm_compute.
Qed.

(** ** An irreducible counterexample in the paper's intended scope

    The preceding root-origin tuple gives a reducible polynomial.  The
    Eisenstein polynomial [X^5 + 2 X^3 + 2] closes that scope gap.  Its
    corrected-minus-printed discrepancy is [-1600] for every invariant
    tuple, so in particular it persists for invariants constructed from
    any ordered roots in a splitting field. *)

Definition lazard_printed_p22_irreducible_Z : {poly int} :=
  'X^5 + (2 : int) *: 'X^3 + (2 : int)%:P.

Definition lazard_printed_p22_irreducible_Q : {poly rat} :=
  map_poly (intr : int -> rat) lazard_printed_p22_irreducible_Z.

Lemma lazard_printed_p22_irreducible_Z_size :
  size lazard_printed_p22_irreducible_Z = 6%N.
Proof. vm_compute; reflexivity. Qed.

Lemma lazard_printed_p22_irreducible_Z_eisenstein :
  irreducible_poly lazard_printed_p22_irreducible_Z.
Proof.
apply: (eisenstein_crit (p := 2)).
- by vm_compute.
- by rewrite lazard_printed_p22_irreducible_Z_size.
- by vm_compute.
- by vm_compute.
- move=> [|[|[|[|[|i]]]]] //= _; vm_compute.
Qed.

Lemma lazard_printed_p22_irreducible_Q_irreducible :
  irreducible_poly lazard_printed_p22_irreducible_Q.
Proof.
rewrite /lazard_printed_p22_irreducible_Q irreducible_rat_int.
exact: lazard_printed_p22_irreducible_Z_eisenstein.
Qed.

Definition lazard_printed_p22_irreducible_coefficients
    (F : fieldType) : RP.LazardDepressedRootCoefficients F :=
  {| RP.lazard_root_p := 2%:R;
     RP.lazard_root_q := 0;
     RP.lazard_root_r := 0;
     RP.lazard_root_s := 2%:R |}.

Definition lazard_printed_p22_irreducible_coefficients_polynomial_Q :
    {poly rat} :=
  let c := lazard_printed_p22_irreducible_coefficients rat in
  'X^5 + RP.lazard_root_p c *: 'X^3 +
    RP.lazard_root_q c *: 'X^2 + RP.lazard_root_r c *: 'X +
    (RP.lazard_root_s c)%:P.

Lemma lazard_printed_p22_irreducible_coefficients_polynomial_QE :
  lazard_printed_p22_irreducible_coefficients_polynomial_Q =
    lazard_printed_p22_irreducible_Q.
Proof. vm_compute; reflexivity. Qed.

Lemma lazard_printed_p22_irreducible_coefficients_polynomial_Q_irreducible :
  irreducible_poly
    lazard_printed_p22_irreducible_coefficients_polynomial_Q.
Proof.
rewrite lazard_printed_p22_irreducible_coefficients_polynomial_QE.
exact: lazard_printed_p22_irreducible_Q_irreducible.
Qed.

Section IrreducibleScopeDiscrepancy.

Variable F : fieldType.

Theorem lazard_corrected_p22_sub_printed_p22_irreducible_scope
    (i : RP.LazardRootInvariants F) :
  FN.lazard_p22 (lazard_printed_p22_irreducible_coefficients F) i -
      lazard_printed_p22
        (lazard_printed_p22_irreducible_coefficients F) i =
    - (1600%:R : F).
Proof.
rewrite lazard_p22_sub_printed_p22
  /lazard_printed_p22_irreducible_coefficients.
finish_lazard_printed_p22_ring.
Qed.

End IrreducibleScopeDiscrepancy.

Theorem lazard_printed_p22_ne_corrected_p22_irreducible_scope
    (i : RP.LazardRootInvariants rat) :
  lazard_printed_p22
      (lazard_printed_p22_irreducible_coefficients rat) i <>
    FN.lazard_p22
      (lazard_printed_p22_irreducible_coefficients rat) i.
Proof.
move=> h.
have hd := lazard_corrected_p22_sub_printed_p22_irreducible_scope i.
move: hd; rewrite h subrr.
by vm_compute.
Qed.

(** ** Closed root-origin realization of the irreducible counterexample

    Here the invariant coordinates are no longer arbitrary: they are
    evaluated on the canonical complete root tuple of the same Eisenstein
    quintic in its [numfield]. *)

Definition lazard_printed_p22_irreducible_monic_quintic :
    PolynomialFormulasQuinticRecursiveFactor.monic_quintic :=
  [tuple 2; 0; 0; 2; 0].

Module QRF := PolynomialFormulasQuinticRecursiveFactor.
Module CD := PolynomialFormulasQuinticCanonicalDecision.
Module GA := PolynomialFormulasQuinticGaloisAction.
Module SCV := PolynomialFormulasSexticComputedResolvents.
Module SNP := PolynomialFormulasSexticNewtonPowerSums.
Module QPS := PolynomialFormulasQuinticPaddedSymmetrization.

Definition lazard_printed_p22_irreducible_canonical_Q : {poly rat} :=
  CD.rational_monic_quintic
    lazard_printed_p22_irreducible_monic_quintic.

Lemma lazard_printed_p22_irreducible_canonical_QE :
  lazard_printed_p22_irreducible_canonical_Q =
    lazard_printed_p22_irreducible_Q.
Proof. vm_compute; reflexivity. Qed.

Lemma lazard_printed_p22_irreducible_canonical_Q_size :
  size lazard_printed_p22_irreducible_canonical_Q = 6%N.
Proof.
rewrite /lazard_printed_p22_irreducible_canonical_Q.
exact: CD.size_rational_monic_quintic.
Qed.

Lemma lazard_printed_p22_irreducible_canonical_Q_irreducible :
  irreducible_poly lazard_printed_p22_irreducible_canonical_Q.
Proof.
rewrite lazard_printed_p22_irreducible_canonical_QE.
exact: lazard_printed_p22_irreducible_Q_irreducible.
Qed.

Let lazard_printed_p22_root_field :=
  numfield lazard_printed_p22_irreducible_canonical_Q.
Let lazard_printed_p22_root_embed :
    {rmorphism rat -> lazard_printed_p22_root_field} :=
  char0_ratr
    (char_numfield lazard_printed_p22_irreducible_canonical_Q).

Definition lazard_printed_p22_irreducible_roots :
    5.-tuple lazard_printed_p22_root_field :=
  @GA.quintic_root_tuple
    lazard_printed_p22_irreducible_canonical_Q
    lazard_printed_p22_irreducible_canonical_Q_size.

Lemma lazard_printed_p22_irreducible_roots_injective :
  injective (tnth lazard_printed_p22_irreducible_roots).
Proof.
exact: (@GA.quintic_root_tuple_injective
  lazard_printed_p22_irreducible_canonical_Q
  lazard_printed_p22_irreducible_canonical_Q_size
  lazard_printed_p22_irreducible_canonical_Q_irreducible).
Qed.

(** Exact monic factorization, so the displayed tuple is not merely a list
    of convenient elements: it contains all roots with multiplicity one. *)
Lemma lazard_printed_p22_irreducible_roots_factorization :
  map_poly lazard_printed_p22_root_embed
      lazard_printed_p22_irreducible_canonical_Q =
    \prod_(r <- lazard_printed_p22_irreducible_roots)
      ('X - r%:P : {poly lazard_printed_p22_root_field}).
Proof.
exact: (@CD.canonical_quintic_numfield_factorization
  lazard_printed_p22_irreducible_monic_quintic).
Qed.

(** Local zero-padding identities.  They are proved here to keep this
    correction module independent of the later Section-7 determinant and
    epsilon developments. *)
Lemma lazard_printed_p22_root_esymm_pad_ord1 :
  SNP.root_esymm
      (QPS.pad_quintic_roots lazard_printed_p22_irreducible_roots)
      (inord 1) =
    RP.lazard_root_esymm2 lazard_printed_p22_irreducible_roots.
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
finish_lazard_printed_p22_ring.
Qed.

Lemma lazard_printed_p22_root_esymm_pad_ord2 :
  SNP.root_esymm
      (QPS.pad_quintic_roots lazard_printed_p22_irreducible_roots)
      (inord 2) =
    RP.lazard_root_esymm3 lazard_printed_p22_irreducible_roots.
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
finish_lazard_printed_p22_ring.
Qed.

Lemma lazard_printed_p22_root_esymm_pad_ord3 :
  SNP.root_esymm
      (QPS.pad_quintic_roots lazard_printed_p22_irreducible_roots)
      (inord 3) =
    RP.lazard_root_esymm4 lazard_printed_p22_irreducible_roots.
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
  /RP.lazard_root_esymm4.
have hinord3 : nat_of_ord (inord 3 : 'I_6) = 3%N.
  exact: (@inordK 5 3 isT).
rewrite -h3 hinord3 /=.
finish_lazard_printed_p22_ring.
Qed.

Lemma lazard_printed_p22_root_esymm_pad_ord4 :
  SNP.root_esymm
      (QPS.pad_quintic_roots lazard_printed_p22_irreducible_roots)
      (inord 4) =
    RP.lazard_root_esymm5 lazard_printed_p22_irreducible_roots.
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
  /RP.lazard_root_esymm5.
have hinord4 : nat_of_ord (inord 4 : 'I_6) = 4%N.
  exact: (@inordK 5 4 isT).
rewrite -h4 hinord4 /=.
finish_lazard_printed_p22_ring.
Qed.

(** Canonical Vieta identifies the four coefficients reconstructed from the
    complete root tuple with the coefficients of the same Eisenstein
    quintic.  This is the missing composition needed to make the final P22
    counterexample literally root-origin rather than merely pairing roots
    and coefficients known to come from the same factorization. *)
Lemma lazard_printed_p22_irreducible_root_esymm2E :
  RP.lazard_root_esymm2 lazard_printed_p22_irreducible_roots =
    (2%:R : lazard_printed_p22_root_field).
Proof.
have hv := congr1
  (fun values : 6.-tuple lazard_printed_p22_root_field =>
    tnth values (inord 1))
  (@CD.canonical_quintic_padded_vieta
    lazard_printed_p22_irreducible_monic_quintic).
rewrite /SCV.cast_int_values tnth_mktuple
  SNP.tnth_elementary_values lazard_printed_p22_root_esymm_pad_ord1 in hv.
rewrite -hv /SCV.monic_elementary_values tnth_mktuple /=.
rewrite (QRF.quintic_sextic_embedding_nthE
  lazard_printed_p22_irreducible_monic_quintic
  (i := 4%N) isT) /=.
by rewrite /lazard_printed_p22_irreducible_monic_quintic.
Qed.

Lemma lazard_printed_p22_irreducible_root_neg_esymm3E :
  - RP.lazard_root_esymm3 lazard_printed_p22_irreducible_roots = 0.
Proof.
have hv := congr1
  (fun values : 6.-tuple lazard_printed_p22_root_field =>
    tnth values (inord 2))
  (@CD.canonical_quintic_padded_vieta
    lazard_printed_p22_irreducible_monic_quintic).
rewrite /SCV.cast_int_values tnth_mktuple
  SNP.tnth_elementary_values lazard_printed_p22_root_esymm_pad_ord2 in hv.
rewrite -hv /SCV.monic_elementary_values tnth_mktuple /=.
rewrite (QRF.quintic_sextic_embedding_nthE
  lazard_printed_p22_irreducible_monic_quintic
  (i := 3%N) isT) /= rmorphN opprK.
by rewrite /lazard_printed_p22_irreducible_monic_quintic.
Qed.

Lemma lazard_printed_p22_irreducible_root_esymm4E :
  RP.lazard_root_esymm4 lazard_printed_p22_irreducible_roots = 0.
Proof.
have hv := congr1
  (fun values : 6.-tuple lazard_printed_p22_root_field =>
    tnth values (inord 3))
  (@CD.canonical_quintic_padded_vieta
    lazard_printed_p22_irreducible_monic_quintic).
rewrite /SCV.cast_int_values tnth_mktuple
  SNP.tnth_elementary_values lazard_printed_p22_root_esymm_pad_ord3 in hv.
rewrite -hv /SCV.monic_elementary_values tnth_mktuple /=.
rewrite (QRF.quintic_sextic_embedding_nthE
  lazard_printed_p22_irreducible_monic_quintic
  (i := 2%N) isT) /=.
by rewrite /lazard_printed_p22_irreducible_monic_quintic.
Qed.

Lemma lazard_printed_p22_irreducible_root_neg_esymm5E :
  - RP.lazard_root_esymm5 lazard_printed_p22_irreducible_roots =
    (2%:R : lazard_printed_p22_root_field).
Proof.
have hv := congr1
  (fun values : 6.-tuple lazard_printed_p22_root_field =>
    tnth values (inord 4))
  (@CD.canonical_quintic_padded_vieta
    lazard_printed_p22_irreducible_monic_quintic).
rewrite /SCV.cast_int_values tnth_mktuple
  SNP.tnth_elementary_values lazard_printed_p22_root_esymm_pad_ord4 in hv.
rewrite -hv /SCV.monic_elementary_values tnth_mktuple /=.
rewrite (QRF.quintic_sextic_embedding_nthE
  lazard_printed_p22_irreducible_monic_quintic
  (i := 1%N) isT) /= rmorphN opprK.
by rewrite /lazard_printed_p22_irreducible_monic_quintic.
Qed.

Lemma lazard_printed_p22_irreducible_roots_depressed_of_roots :
  RP.lazard_depressed_of_roots lazard_printed_p22_irreducible_roots =
    lazard_printed_p22_irreducible_coefficients
      lazard_printed_p22_root_field.
Proof.
rewrite /RP.lazard_depressed_of_roots
  lazard_printed_p22_irreducible_root_esymm2E
  lazard_printed_p22_irreducible_root_neg_esymm3E
  lazard_printed_p22_irreducible_root_esymm4E
  lazard_printed_p22_irreducible_root_neg_esymm5E
  /lazard_printed_p22_irreducible_coefficients.
reflexivity.
Qed.

Theorem lazard_corrected_p22_sub_printed_p22_irreducible_root_origin :
  FN.lazard_p22
      (RP.lazard_depressed_of_roots
        lazard_printed_p22_irreducible_roots)
      (RP.lazard_root_invariants lazard_printed_p22_irreducible_roots) -
    lazard_printed_p22
      (RP.lazard_depressed_of_roots
        lazard_printed_p22_irreducible_roots)
      (RP.lazard_root_invariants lazard_printed_p22_irreducible_roots) =
    - (1600%:R : lazard_printed_p22_root_field).
Proof.
rewrite lazard_printed_p22_irreducible_roots_depressed_of_roots.
exact: lazard_corrected_p22_sub_printed_p22_irreducible_scope.
Qed.

Theorem lazard_printed_p22_ne_corrected_p22_irreducible_root_origin :
  lazard_printed_p22
      (RP.lazard_depressed_of_roots
        lazard_printed_p22_irreducible_roots)
      (RP.lazard_root_invariants lazard_printed_p22_irreducible_roots) <>
    FN.lazard_p22
      (RP.lazard_depressed_of_roots
        lazard_printed_p22_irreducible_roots)
      (RP.lazard_root_invariants lazard_printed_p22_irreducible_roots).
Proof.
move=> h.
have hd :=
  lazard_corrected_p22_sub_printed_p22_irreducible_root_origin.
move: hd; rewrite h subrr.
by rewrite oppr_eq0 pnatr_eq0.
Qed.

End RationalCounterexample.

End PolynomialFormulasLazardPrintedFormulaCorrections.
