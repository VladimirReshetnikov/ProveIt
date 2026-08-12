From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The formula-independent Fourier core in Section 2 of Lazard's paper.

    The degree is written [n.+1], so positivity is structural.  The forward
    transform uses Lazard's positive-exponent convention.  Its inverse uses
    inverse character values and therefore has the factor [(n.+1)%:R] in the
    denominator.  The reconstruction theorem states explicitly that this
    scalar is nonzero; this excludes exactly the characteristics dividing the
    degree.

    Finite functions are used instead of ordinary Coq functions.  Thus the
    final equality of transforms follows from the proved finite-function
    extensionality principle and introduces no functional-extensionality
    axiom. *)
Module PolynomialFormulasLazardGeneralFourier.

Import GRing.Theory.
Local Open Scope ring_scope.

Section LazardGeneralFourier.

Variable n : nat.
Local Notation d := n.+1.
Variable F : fieldType.
Variable omega : F.
Hypothesis omega_primitive : d.-primitive_root omega.

(** The multiplicative character represented by a primitive [d]th root. *)
Definition lazard_general_character (j k : 'I_d) : F :=
  omega ^+ (nat_of_ord j * nat_of_ord k).

(** Lazard's forward discrete Fourier transform, with positive exponent. *)
Definition lazard_general_dft_coordinate
    (x : {ffun 'I_d -> F}) (k : 'I_d) : F :=
  \sum_(j < d) lazard_general_character j k * x j.

Definition lazard_general_dft
    (x : {ffun 'I_d -> F}) : {ffun 'I_d -> F} :=
  [ffun k => lazard_general_dft_coordinate x k].

(** The normalized inverse transform for the positive-exponent convention. *)
Definition lazard_general_invDFT_coordinate
    (s : {ffun 'I_d -> F}) (i : 'I_d) : F :=
  (d%:R : F)^-1 *
    \sum_(k < d) (lazard_general_character i k)^-1 * s k.

Definition lazard_general_invDFT
    (s : {ffun 'I_d -> F}) : {ffun 'I_d -> F} :=
  [ffun i => lazard_general_invDFT_coordinate s i].

(** Cyclic relabelling [x_i |-> x_(i-a)] on the ordinal model of [Z/dZ]. *)
Definition lazard_general_shift (a : 'I_d)
    (x : {ffun 'I_d -> F}) : {ffun 'I_d -> F} :=
  [ffun i => x (i - a)].

Lemma lazard_general_omega_neq0 : omega != 0.
Proof.
by rewrite (prim_root_eq0 omega_primitive).
Qed.

(** Primitive-root powers indexed by [0,...,d-1] are pairwise distinct. *)
Lemma lazard_general_primitive_power_injective :
  injective (fun i : 'I_d => omega ^+ nat_of_ord i).
Proof.
move=> i j hij; apply: val_inj.
have hijmod : (nat_of_ord i == nat_of_ord j %[mod d]).
  have hpowers :
      omega ^+ nat_of_ord i == omega ^+ nat_of_ord j.
    exact/eqP.
  move: hpowers.
  by rewrite (eq_prim_root_expr omega_primitive).
move/eqP: hijmod => hijmod.
rewrite (modn_small (ltn_ord i)) (modn_small (ltn_ord j)) in hijmod.
exact: hijmod.
Qed.

(** A nontrivial [d]th root has zero finite geometric sum. *)
Lemma lazard_general_geometric_sum_zero (z : F)
    (hzd : z ^+ d = 1) (hz1 : z != 1) :
  \sum_(j < d) z ^+ nat_of_ord j = 0.
Proof.
have hgeom := subrX1 z d.
rewrite hzd subrr in hgeom.
have hzB1 : z - 1 != 0 by rewrite subr_eq0.
apply: (mulfI hzB1).
rewrite mulr0.
exact: esym hgeom.
Qed.

(** Character/geometric orthogonality for every positive degree. *)
Theorem lazard_general_character_orthogonality (b : 'I_d) :
  \sum_(j < d) lazard_general_character j b =
    if b == 0 then (d%:R : F) else 0.
Proof.
case: eqP => [-> | hb].
- rewrite /lazard_general_character /=.
  under eq_bigr do rewrite muln0 expr0.
  by rewrite sumr_const card_ord.
- transitivity (\sum_(j < d) (omega ^+ nat_of_ord b) ^+ nat_of_ord j).
  + apply: eq_bigr => j _.
    by rewrite /lazard_general_character mulnC exprM.
  + apply: lazard_general_geometric_sum_zero.
    * by rewrite exprAC (prim_expr_order omega_primitive) expr1n.
    * apply/negP => /eqP hb1.
      apply: hb.
      apply: lazard_general_primitive_power_injective.
      by rewrite hb1 expr0.
Qed.

(** The character is additive in its first coordinate. *)
Lemma lazard_general_character_add (a j k : 'I_d) :
  lazard_general_character (a + j) k =
    lazard_general_character a k * lazard_general_character j k.
Proof.
rewrite /lazard_general_character -exprD.
apply/eqP.
rewrite (eq_prim_root_expr omega_primitive).
by rewrite /= modnMml mulnDl.
Qed.

(** A cyclic relabelling multiplies Fourier mode [k] by the character at
    [(a,k)]. *)
Theorem lazard_general_dft_shift (a : 'I_d)
    (x : {ffun 'I_d -> F}) :
  lazard_general_dft (lazard_general_shift a x) =
    [ffun k => lazard_general_character a k *
      lazard_general_dft x k].
Proof.
apply/ffunP => k; rewrite !ffunE.
rewrite /lazard_general_dft_coordinate /lazard_general_shift.
rewrite (reindex_inj (addIr a)) /= mulr_sumr.
apply: eq_bigr => j _.
rewrite !ffunE addrK addrC lazard_general_character_add.
by rewrite mulrA.
Qed.

(** Orthogonality with the exact inverse/forward sign pattern. *)
Lemma lazard_general_inverse_kernel_sum (i j : 'I_d) :
  \sum_(k < d)
      (lazard_general_character i k)^-1 *
        lazard_general_character j k =
    if j == i then (d%:R : F) else 0.
Proof.
transitivity
  (\sum_(k < d)
    ((omega ^+ nat_of_ord i)^-1 * omega ^+ nat_of_ord j) ^+
      nat_of_ord k).
- apply: eq_bigr => k _.
  by rewrite /lazard_general_character exprMn exprVn -!exprM.
- case: eqP => [-> | hji].
  + have hwi : omega ^+ nat_of_ord i != 0 :=
      expf_neq0 _ lazard_general_omega_neq0.
    rewrite mulVf //.
    under eq_bigr do rewrite expr1n.
    by rewrite sumr_const card_ord.
  + apply: lazard_general_geometric_sum_zero.
    * rewrite exprMn exprVn
        (exprAC omega (nat_of_ord i) d)
        (exprAC omega (nat_of_ord j) d).
      by rewrite (prim_expr_order omega_primitive) !expr1n invr1 mul1r.
    * apply/negP => /eqP hratio.
      have hwi : omega ^+ nat_of_ord i != 0 :=
        expf_neq0 _ lazard_general_omega_neq0.
      have hpowers := congr1
        (fun z : F => omega ^+ nat_of_ord i * z) hratio.
      move: hpowers.
      rewrite mulrA mulfV // mul1r mulr1 => hpowers.
      apply: hji.
      exact: lazard_general_primitive_power_injective hpowers.
Qed.

(** Coordinate form of Fourier inversion.  The hypothesis is precisely the
    condition needed to cancel the normalization factor. *)
Theorem lazard_general_invDFT_dft_coordinate
    (degree_neq0 : (d%:R : F) != 0)
    (x : {ffun 'I_d -> F}) (i : 'I_d) :
  lazard_general_invDFT (lazard_general_dft x) i = x i.
Proof.
rewrite !ffunE /lazard_general_invDFT_coordinate
  /lazard_general_dft_coordinate.
transitivity
  ((d%:R : F)^-1 *
    \sum_(j < d)
      (\sum_(k < d)
        (lazard_general_character i k)^-1 *
          lazard_general_character j k) * x j).
- congr ((d%:R : F)^-1 * _).
  under eq_bigr do rewrite !ffunE mulr_sumr.
  rewrite exchange_big.
  apply: eq_bigr => j _.
  under eq_bigr do rewrite mulrA.
  by rewrite -mulr_suml.
- under eq_bigr do rewrite lazard_general_inverse_kernel_sum.
  rewrite (bigD1 i) //= eqxx.
  rewrite big1 ?addr0.
  + by rewrite mulrA mulVf // mul1r.
  + move=> j hji.
    by rewrite (negbTE hji) mul0r.
Qed.

(** Exact normalized inverse reconstruction over an arbitrary field. *)
Theorem lazard_general_invDFT_dft
    (degree_neq0 : (d%:R : F) != 0)
    (x : {ffun 'I_d -> F}) :
  lazard_general_invDFT (lazard_general_dft x) = x.
Proof.
apply/ffunP => i.
rewrite lazard_general_invDFT_dft_coordinate //.
Qed.

Check lazard_general_character_orthogonality.
Check lazard_general_dft_shift.
Check lazard_general_invDFT_dft_coordinate.
Check lazard_general_invDFT_dft.
Print Assumptions lazard_general_character_orthogonality.
Print Assumptions lazard_general_dft_shift.
Print Assumptions lazard_general_invDFT_dft_coordinate.
Print Assumptions lazard_general_invDFT_dft.

End LazardGeneralFourier.
End PolynomialFormulasLazardGeneralFourier.
