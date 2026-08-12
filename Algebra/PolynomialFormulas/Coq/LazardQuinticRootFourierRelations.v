From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import
  QuinticF20Data LazardQuinticFourier LazardQuinticVieta
  LazardQuinticRootProjections.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The actual positive Fourier sums of a depressed ordered root tuple
    satisfy Lazard's four Fourier coefficient relations.  No relation is
    supplied as certificate data. *)
Module PolynomialFormulasLazardQuinticRootFourierRelations.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.
Import PolynomialFormulasLazardQuinticFourier.
Import PolynomialFormulasLazardQuinticVieta.
Import PolynomialFormulasLazardQuinticRootProjections.
Local Open Scope ring_scope.

Section RootFourierRelations.

Variable F : fieldType.
Variable omega : F.
Hypothesis omega_primitive : 5.-primitive_root omega.
Hypothesis five_neq0 : (5%:R : F) != 0.

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

Lemma lazard_root_fourier_ring_addE (x y : F) :
  x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma lazard_root_fourier_ring_mulE (x y : F) :
  x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma lazard_root_fourier_ring_subE (x y : F) :
  x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma lazard_root_fourier_ring_oppE (x : F) :
  - x = ring_opp x. Proof. reflexivity. Qed.
Lemma lazard_root_fourier_ring_zeroE :
  (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma lazard_root_fourier_ring_oneE :
  (1 : F) = ring_one. Proof. reflexivity. Qed.

Lemma lazard_root_fourier_ring_theory :
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

Add Ring lazard_root_fourier_ring : lazard_root_fourier_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Ltac finish_lazard_root_fourier_ring :=
  repeat first
    [ rewrite lazard_root_projection_five_natrE
    | rewrite lazard_root_projection_four_natrE
    | rewrite lazard_root_projection_three_natrE
    | rewrite lazard_root_projection_two_natrE
    | rewrite lazard_root_fourier_ring_addE
    | rewrite lazard_root_fourier_ring_mulE
    | rewrite lazard_root_fourier_ring_subE
    | rewrite lazard_root_fourier_ring_oppE
    | rewrite lazard_root_fourier_ring_zeroE
    | rewrite lazard_root_fourier_ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

(** Positive Fourier inversion reverses the four nonzero coordinates. *)
Definition lazard_reversed_root_tuple (roots : 5.-tuple F)
    (k : 'I_5) : F :=
  nth 0
    [:: tnth roots o0; tnth roots o4; tnth roots o3;
        tnth roots o2; tnth roots o1]
    (nat_of_ord k).

Lemma lazard_root_fourier_P0E roots :
  lazard_fourier_sum omega roots o0 = lazard_root_esymm1 roots.
Proof.
rewrite /lazard_fourier_sum lazard_sum_ord5
  /lazard_root_esymm1 /=.
by rewrite !muln0 !expr0 !mul1r.
Qed.

Lemma lazard_root_fourier_fifth_multiple n :
  omega ^+ (5 * n) = 1.
Proof.
by rewrite exprM (lazard_primitive_fifth_power5 omega_primitive) expr1n.
Qed.

Lemma lazard_inverse_fourier_root_fourier_coordinate roots k
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_inverse_fourier_output omega
      (lazard_root_fourier_P1 omega roots)
      (lazard_root_fourier_P2 omega roots)
      (lazard_root_fourier_P3 omega roots)
      (lazard_root_fourier_P4 omega roots) k =
    lazard_reversed_root_tuple roots k.
Proof.
have hp1 := @lazard_root_fourier_P1E F omega roots.
have hp2 := @lazard_root_fourier_P2E F omega roots omega_primitive.
have hp3 := @lazard_root_fourier_P3E F omega roots omega_primitive.
have hp4 := @lazard_root_fourier_P4E F omega roots omega_primitive.
case: k=> [[|[|[|[|[|k]]]]] hk].
- have -> : @Ordinal 5 0 hk = o0 by apply: val_inj.
  rewrite /lazard_reversed_root_tuple /=.
  rewrite -(@lazard_inverse_fourier_coordinateE F omega omega_primitive
    five_neq0 roots o0).
  rewrite /lazard_inverse_fourier_output
    /lazard_inverse_fourier_unscaled
    /lazard_inverse_fourier_coordinate
    /lazard_inverse_fourier_numerator lazard_sum_ord5
    lazard_root_fourier_P0E -hp1 -hp2 -hp3 -hp4 hsum /=.
  rewrite /= !lazard_root_fourier_fifth_multiple.
  finish_lazard_root_fourier_ring.
- have -> : @Ordinal 5 1 hk = o1 by apply: val_inj.
  rewrite /lazard_reversed_root_tuple /=.
  rewrite -(@lazard_inverse_fourier_coordinateE F omega omega_primitive
    five_neq0 roots o4).
  rewrite /lazard_inverse_fourier_output
    /lazard_inverse_fourier_unscaled
    /lazard_inverse_fourier_coordinate
    /lazard_inverse_fourier_numerator lazard_sum_ord5
    lazard_root_fourier_P0E -hp1 -hp2 -hp3 -hp4 hsum /=.
  rewrite /=.
  finish_lazard_root_fourier_ring.
- have -> : @Ordinal 5 2 hk = o2 by apply: val_inj.
  rewrite /lazard_reversed_root_tuple /=.
  rewrite -(@lazard_inverse_fourier_coordinateE F omega omega_primitive
    five_neq0 roots o3).
  rewrite /lazard_inverse_fourier_output
    /lazard_inverse_fourier_unscaled
    /lazard_inverse_fourier_coordinate
    /lazard_inverse_fourier_numerator lazard_sum_ord5
    lazard_root_fourier_P0E -hp1 -hp2 -hp3 -hp4 hsum /=.
  rewrite /=
    (lazard_primitive_fifth_power6 omega_primitive)
    (lazard_primitive_fifth_power8 omega_primitive).
  finish_lazard_root_fourier_ring.
- have -> : @Ordinal 5 3 hk = o3 by apply: val_inj.
  rewrite /lazard_reversed_root_tuple /=.
  rewrite -(@lazard_inverse_fourier_coordinateE F omega omega_primitive
    five_neq0 roots o2).
  rewrite /lazard_inverse_fourier_output
    /lazard_inverse_fourier_unscaled
    /lazard_inverse_fourier_coordinate
    /lazard_inverse_fourier_numerator lazard_sum_ord5
    lazard_root_fourier_P0E -hp1 -hp2 -hp3 -hp4 hsum /=.
  rewrite /=
    (lazard_primitive_fifth_power6 omega_primitive)
    (lazard_primitive_fifth_power9 omega_primitive)
    (lazard_primitive_fifth_power12 omega_primitive).
  finish_lazard_root_fourier_ring.
- have -> : @Ordinal 5 4 hk = o4 by apply: val_inj.
  rewrite /lazard_reversed_root_tuple /=.
  rewrite -(@lazard_inverse_fourier_coordinateE F omega omega_primitive
    five_neq0 roots o1).
  rewrite /lazard_inverse_fourier_output
    /lazard_inverse_fourier_unscaled
    /lazard_inverse_fourier_coordinate
    /lazard_inverse_fourier_numerator lazard_sum_ord5
    lazard_root_fourier_P0E -hp1 -hp2 -hp3 -hp4 hsum /=.
  rewrite /=
    (lazard_primitive_fifth_power8 omega_primitive)
    (lazard_primitive_fifth_power12 omega_primitive)
    (lazard_primitive_fifth_power16 omega_primitive).
  finish_lazard_root_fourier_ring.
- by move: hk.
Qed.

(** Reversal is a permutation, so it preserves all five elementary
    symmetric expressions and the depressed coefficient tuple. *)
Lemma lazard_reversed_root_relations roots
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_depressed_five_root_relations
    (lazard_root_p (@lazard_depressed_of_roots F roots))
    (lazard_root_q (@lazard_depressed_of_roots F roots))
    (lazard_root_r (@lazard_depressed_of_roots F roots))
    (lazard_root_s (@lazard_depressed_of_roots F roots))
    (lazard_reversed_root_tuple roots).
Proof.
constructor.
- rewrite /lazard_five_esymm1 /lazard_reversed_root_tuple /=.
  rewrite /lazard_root_esymm1 in hsum.
  transitivity
    (tnth roots o0 + tnth roots o1 + tnth roots o2 +
      tnth roots o3 + tnth roots o4).
  + finish_lazard_root_fourier_ring.
  + exact hsum.
- rewrite /lazard_five_esymm2 /lazard_reversed_root_tuple
    /lazard_depressed_of_roots /= /lazard_root_esymm2.
  finish_lazard_root_fourier_ring.
- rewrite /lazard_five_esymm3 /lazard_reversed_root_tuple
    /lazard_depressed_of_roots /= /lazard_root_esymm3.
  finish_lazard_root_fourier_ring.
- rewrite /lazard_five_esymm4 /lazard_reversed_root_tuple
    /lazard_depressed_of_roots /= /lazard_root_esymm4.
  finish_lazard_root_fourier_ring.
- rewrite /lazard_five_esymm5 /lazard_reversed_root_tuple
    /lazard_depressed_of_roots /= /lazard_root_esymm5.
  finish_lazard_root_fourier_ring.
Qed.

Lemma lazard_inverse_fourier_root_esymm2 roots
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_five_esymm2
      (lazard_inverse_fourier_output omega
        (lazard_root_fourier_P1 omega roots)
        (lazard_root_fourier_P2 omega roots)
        (lazard_root_fourier_P3 omega roots)
        (lazard_root_fourier_P4 omega roots)) =
    lazard_five_esymm2 (lazard_reversed_root_tuple roots).
Proof.
rewrite /lazard_five_esymm2.
by rewrite !lazard_inverse_fourier_root_fourier_coordinate.
Qed.

Lemma lazard_inverse_fourier_root_esymm3 roots
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_five_esymm3
      (lazard_inverse_fourier_output omega
        (lazard_root_fourier_P1 omega roots)
        (lazard_root_fourier_P2 omega roots)
        (lazard_root_fourier_P3 omega roots)
        (lazard_root_fourier_P4 omega roots)) =
    lazard_five_esymm3 (lazard_reversed_root_tuple roots).
Proof.
rewrite /lazard_five_esymm3.
by rewrite !lazard_inverse_fourier_root_fourier_coordinate.
Qed.

Lemma lazard_inverse_fourier_root_esymm4 roots
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_five_esymm4
      (lazard_inverse_fourier_output omega
        (lazard_root_fourier_P1 omega roots)
        (lazard_root_fourier_P2 omega roots)
        (lazard_root_fourier_P3 omega roots)
        (lazard_root_fourier_P4 omega roots)) =
    lazard_five_esymm4 (lazard_reversed_root_tuple roots).
Proof.
rewrite /lazard_five_esymm4.
by rewrite !lazard_inverse_fourier_root_fourier_coordinate.
Qed.

Lemma lazard_inverse_fourier_root_esymm5 roots
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_five_esymm5
      (lazard_inverse_fourier_output omega
        (lazard_root_fourier_P1 omega roots)
        (lazard_root_fourier_P2 omega roots)
        (lazard_root_fourier_P3 omega roots)
        (lazard_root_fourier_P4 omega roots)) =
    lazard_five_esymm5 (lazard_reversed_root_tuple roots).
Proof.
rewrite /lazard_five_esymm5.
by rewrite !lazard_inverse_fourier_root_fourier_coordinate.
Qed.

(** Clear a power of the Fourier normalization. *)
Lemma lazard_root_fourier_unscale n x y
    (h : ((5%:R : F)^-1) ^+ n * x = y) :
  x = (5%:R : F) ^+ n * y.
Proof.
rewrite -h mulrA [(5%:R : F) ^+ n * ((5%:R : F)^-1) ^+ n]mulrC.
by rewrite (@lazard_inv_five_power_cancel F five_neq0 n) mul1r.
Qed.

(** The actual P1,...,P4 Fourier sums satisfy the four relations used by
    the Vieta/root-soundness layer. *)
Theorem lazard_root_fourier_relations roots
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_fourier_relations
    (lazard_root_p (@lazard_depressed_of_roots F roots))
    (lazard_root_q (@lazard_depressed_of_roots F roots))
    (lazard_root_r (@lazard_depressed_of_roots F roots))
    (lazard_root_s (@lazard_depressed_of_roots F roots))
    (lazard_root_fourier_P1 omega roots)
    (lazard_root_fourier_P2 omega roots)
    (lazard_root_fourier_P3 omega roots)
    (lazard_root_fourier_P4 omega roots).
Proof.
have hvieta := lazard_reversed_root_relations hsum.
constructor.
- have hcyclic := @lazard_inverse_fourier_esymm2 F omega
    omega_primitive five_neq0
    (lazard_root_fourier_P1 omega roots)
    (lazard_root_fourier_P2 omega roots)
    (lazard_root_fourier_P3 omega roots)
    (lazard_root_fourier_P4 omega roots).
  rewrite (lazard_inverse_fourier_root_esymm2 hsum)
    (lazard_vieta_pairs hvieta) in hcyclic.
  have hscaled :
      - lazard_fourier_cyclic2
          (lazard_root_fourier_P1 omega roots)
          (lazard_root_fourier_P2 omega roots)
          (lazard_root_fourier_P3 omega roots)
          (lazard_root_fourier_P4 omega roots) =
        (5%:R : F) ^+ 1 *
          lazard_root_p (@lazard_depressed_of_roots F roots).
    apply: lazard_root_fourier_unscale.
    rewrite expr1 mulrN -mulNr.
    exact: (esym hcyclic).
  move: (congr1 (fun z : F => - z) hscaled).
  by rewrite opprK -mulNr.
- have hcyclic := @lazard_inverse_fourier_esymm3 F omega
    omega_primitive five_neq0
    (lazard_root_fourier_P1 omega roots)
    (lazard_root_fourier_P2 omega roots)
    (lazard_root_fourier_P3 omega roots)
    (lazard_root_fourier_P4 omega roots).
  rewrite (lazard_inverse_fourier_root_esymm3 hsum)
    (lazard_vieta_triples hvieta) in hcyclic.
  have hscaled := lazard_root_fourier_unscale (esym hcyclic).
  by rewrite mulrN in hscaled.
- have hcyclic := @lazard_inverse_fourier_esymm4 F omega
    omega_primitive five_neq0
    (lazard_root_fourier_P1 omega roots)
    (lazard_root_fourier_P2 omega roots)
    (lazard_root_fourier_P3 omega roots)
    (lazard_root_fourier_P4 omega roots).
  rewrite (lazard_inverse_fourier_root_esymm4 hsum)
    (lazard_vieta_quadruples hvieta) in hcyclic.
  exact: lazard_root_fourier_unscale (esym hcyclic).
- have hcyclic := @lazard_inverse_fourier_esymm5 F omega
    omega_primitive
    (lazard_root_fourier_P1 omega roots)
    (lazard_root_fourier_P2 omega roots)
    (lazard_root_fourier_P3 omega roots)
    (lazard_root_fourier_P4 omega roots).
  rewrite (lazard_inverse_fourier_root_esymm5 hsum)
    (lazard_vieta_product hvieta) in hcyclic.
  have hscaled := lazard_root_fourier_unscale (esym hcyclic).
  by rewrite mulrN in hscaled.
Qed.

(** The actual root Fourier coordinates satisfy the complete depressed Vieta
    package.  This is the direct certificate-free composition used by the
    Section 2/7 correctness endgame: the caller supplies the actual roots and
    their depressedness equation, not Fourier or Vieta identities. *)
Theorem lazard_root_fourier_vieta roots
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_depressed_five_root_relations
    (lazard_root_p (@lazard_depressed_of_roots F roots))
    (lazard_root_q (@lazard_depressed_of_roots F roots))
    (lazard_root_r (@lazard_depressed_of_roots F roots))
    (lazard_root_s (@lazard_depressed_of_roots F roots))
    (lazard_inverse_fourier_output omega
      (lazard_root_fourier_P1 omega roots)
      (lazard_root_fourier_P2 omega roots)
      (lazard_root_fourier_P3 omega roots)
      (lazard_root_fourier_P4 omega roots)).
Proof.
exact: (@lazard_fourier_relations_vieta F omega omega_primitive five_neq0
  (lazard_root_p (@lazard_depressed_of_roots F roots))
  (lazard_root_q (@lazard_depressed_of_roots F roots))
  (lazard_root_r (@lazard_depressed_of_roots F roots))
  (lazard_root_s (@lazard_depressed_of_roots F roots))
  (lazard_root_fourier_P1 omega roots)
  (lazard_root_fourier_P2 omega roots)
  (lazard_root_fourier_P3 omega roots)
  (lazard_root_fourier_P4 omega roots)
  (lazard_root_fourier_relations hsum)).
Qed.

(** Exact multiplicity-sensitive polynomial factorization obtained directly
    from an actual depressed root tuple. *)
Theorem lazard_root_fourier_polynomial_factorization roots
    (hsum : lazard_root_esymm1 roots = 0) :
  lazard_depressed_quintic_polynomial
      (lazard_root_p (@lazard_depressed_of_roots F roots))
      (lazard_root_q (@lazard_depressed_of_roots F roots))
      (lazard_root_r (@lazard_depressed_of_roots F roots))
      (lazard_root_s (@lazard_depressed_of_roots F roots)) =
    \prod_(k : 'I_5)
      ('X - (lazard_inverse_fourier_output omega
        (lazard_root_fourier_P1 omega roots)
        (lazard_root_fourier_P2 omega roots)
        (lazard_root_fourier_P3 omega roots)
        (lazard_root_fourier_P4 omega roots) k)%:P).
Proof.
exact: lazard_depressed_vieta_polynomial_factorization
  (lazard_root_fourier_vieta hsum).
Qed.

(** Multiplicity-sensitive five-factor evaluation identity obtained directly
    from an actual depressed root tuple. *)
Theorem lazard_root_fourier_eval_factorization roots
    (hsum : lazard_root_esymm1 roots = 0) (x : F) :
  lazard_depressed_quintic_eval
      (lazard_root_p (@lazard_depressed_of_roots F roots))
      (lazard_root_q (@lazard_depressed_of_roots F roots))
      (lazard_root_r (@lazard_depressed_of_roots F roots))
      (lazard_root_s (@lazard_depressed_of_roots F roots)) x =
    let output := lazard_inverse_fourier_output omega
      (lazard_root_fourier_P1 omega roots)
      (lazard_root_fourier_P2 omega roots)
      (lazard_root_fourier_P3 omega roots)
      (lazard_root_fourier_P4 omega roots) in
    (x - output o0) * (x - output o1) * (x - output o2) *
      (x - output o3) * (x - output o4).
Proof.
exact: lazard_depressed_vieta_eval_factorization
  (lazard_root_fourier_vieta hsum) x.
Qed.

(** Every reconstructed coordinate is a root, with no supplied correctness
    certificate. *)
Theorem lazard_root_fourier_output_root roots
    (hsum : lazard_root_esymm1 roots = 0) (k : 'I_5) :
  lazard_depressed_quintic_eval
      (lazard_root_p (@lazard_depressed_of_roots F roots))
      (lazard_root_q (@lazard_depressed_of_roots F roots))
      (lazard_root_r (@lazard_depressed_of_roots F roots))
      (lazard_root_s (@lazard_depressed_of_roots F roots))
      (lazard_inverse_fourier_output omega
        (lazard_root_fourier_P1 omega roots)
        (lazard_root_fourier_P2 omega roots)
        (lazard_root_fourier_P3 omega roots)
        (lazard_root_fourier_P4 omega roots) k) = 0.
Proof.
exact: lazard_depressed_vieta_root
  (lazard_root_fourier_vieta hsum) k.
Qed.

(** Every root of the depressed quintic occurs among the five reconstructed
    coordinates. *)
Theorem lazard_root_fourier_output_complete roots
    (hsum : lazard_root_esymm1 roots = 0) (x : F)
    (hx : lazard_depressed_quintic_eval
      (lazard_root_p (@lazard_depressed_of_roots F roots))
      (lazard_root_q (@lazard_depressed_of_roots F roots))
      (lazard_root_r (@lazard_depressed_of_roots F roots))
      (lazard_root_s (@lazard_depressed_of_roots F roots)) x = 0) :
  exists k : 'I_5, x = lazard_inverse_fourier_output omega
    (lazard_root_fourier_P1 omega roots)
    (lazard_root_fourier_P2 omega roots)
    (lazard_root_fourier_P3 omega roots)
    (lazard_root_fourier_P4 omega roots) k.
Proof.
exact: (lazard_depressed_vieta_complete (x := x)
  (lazard_root_fourier_vieta hsum) hx).
Qed.

(** Exact root-set characterization for the certificate-free root-origin
    reconstruction. *)
Theorem lazard_root_fourier_output_root_iff roots
    (hsum : lazard_root_esymm1 roots = 0) (x : F) :
  lazard_depressed_quintic_eval
      (lazard_root_p (@lazard_depressed_of_roots F roots))
      (lazard_root_q (@lazard_depressed_of_roots F roots))
      (lazard_root_r (@lazard_depressed_of_roots F roots))
      (lazard_root_s (@lazard_depressed_of_roots F roots)) x = 0 <->
  exists k : 'I_5, x = lazard_inverse_fourier_output omega
    (lazard_root_fourier_P1 omega roots)
    (lazard_root_fourier_P2 omega roots)
    (lazard_root_fourier_P3 omega roots)
    (lazard_root_fourier_P4 omega roots) k.
Proof.
exact: lazard_depressed_vieta_root_iff
  (lazard_root_fourier_vieta hsum) x.
Qed.

End RootFourierRelations.

End PolynomialFormulasLazardQuinticRootFourierRelations.
