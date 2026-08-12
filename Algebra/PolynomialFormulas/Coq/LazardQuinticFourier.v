From mathcomp Require Import all_ssreflect all_fingroup all_algebra.
From PolynomialFormulas Require Import QuinticF20Data.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** Fourier foundations for Lazard's quintic formula.  The index order is
    the concrete order [o0,...,o4] from [QuinticF20Data]. *)
Module PolynomialFormulasLazardQuinticFourier.

Import GRing.Theory.
Import PolynomialFormulasQuinticF20Data.

Local Open Scope ring_scope.

Section Fourier.

Variable F : fieldType.
Variable omega : F.
Hypothesis omega_primitive : 5.-primitive_root omega.

(** Expand a sum over the five ordered indices. *)
Lemma lazard_sum_ord5 (f : 'I_5 -> F) :
  \sum_(i : 'I_5) f i = f o0 + f o1 + f o2 + f o3 + f o4.
Proof.
rewrite !big_ord_recl !big_ord0.
have h0 : (@ord0 4) = o0 by apply: val_inj.
have h1 : lift (@ord0 4) (@ord0 3) = o1 by apply: val_inj.
have h2 : lift (@ord0 4) (lift (@ord0 3) (@ord0 2)) = o2
  by apply: val_inj.
have h3 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2) (@ord0 1))) = o3
  by apply: val_inj.
have h4 : lift (@ord0 4)
    (lift (@ord0 3) (lift (@ord0 2) (lift (@ord0 1) (@ord0 0)))) = o4
  by apply: val_inj.
by rewrite h4 h3 h2 h1 h0 addr0 !addrA.
Qed.

(** The [k]-th Fourier sum [s_k = sum_j omega^(jk) x_j]. *)
Definition lazard_fourier_sum (roots : 5.-tuple F) (k : 'I_5) : F :=
  \sum_(j : 'I_5)
    omega ^+ (nat_of_ord j * nat_of_ord k) * tnth roots j.

(** The five Fourier sums, retained in their canonical order. *)
Definition lazard_fourier_sums (roots : 5.-tuple F) : 5.-tuple F :=
  [tuple lazard_fourier_sum roots k | k < 5].

Lemma tnth_lazard_fourier_sums roots k :
  tnth (lazard_fourier_sums roots) k = lazard_fourier_sum roots k.
Proof. by rewrite /lazard_fourier_sums tnth_mktuple. Qed.

(** The cyclic substitution [x_i -> x_(i-1)]. *)
Local Open Scope group_scope.
Definition lazard_cyclic_shift (roots : 5.-tuple F) : 5.-tuple F :=
  [tuple tnth roots (five_cycle i) | i < 5].

Lemma tnth_lazard_cyclic_shift roots i :
  tnth (lazard_cyclic_shift roots) i = tnth roots (five_cycle i).
Proof. by rewrite /lazard_cyclic_shift tnth_mktuple. Qed.

Lemma lazard_five_cycle_inv_val i :
  nat_of_ord (five_cycle^-1 i) = ((nat_of_ord i + 1) %% 5)%N.
Proof.
case: i=> [[|[|[|[|[|i]]]]] hi] //=.
- have -> : @Ordinal 5 0 hi = o0 by apply: val_inj.
  by rewrite five_cycle_inv_o0.
- have -> : @Ordinal 5 1 hi = o1 by apply: val_inj.
  by rewrite five_cycle_inv_o1.
- have -> : @Ordinal 5 2 hi = o2 by apply: val_inj.
  by rewrite five_cycle_inv_o2.
- have -> : @Ordinal 5 3 hi = o3 by apply: val_inj.
  by rewrite five_cycle_inv_o3.
- have -> : @Ordinal 5 4 hi = o4 by apply: val_inj.
  by rewrite five_cycle_inv_o4.
Qed.

Lemma lazard_cyclic_shift_weight (i k : 'I_5) :
  (omega ^+ (nat_of_ord ((five_cycle^-1)%g i) * nat_of_ord k))%R =
    ((omega ^+ nat_of_ord k) *
      (omega ^+ (nat_of_ord i * nat_of_ord k)))%R.
Proof.
rewrite lazard_five_cycle_inv_val -exprD.
apply/eqP.
rewrite (eq_prim_root_expr omega_primitive).
case: i=> [[|[|[|[|[|i]]]]] hi] /=;
  case: k=> [[|[|[|[|[|k]]]]] hk] //=.
Qed.

(** The cyclic substitution multiplies the [k]-th Fourier sum by
    [omega^k], exactly as in Lazard's paper. *)
Theorem lazard_fourier_sum_cyclic_shift roots k :
  lazard_fourier_sum (lazard_cyclic_shift roots) k =
    ((omega ^+ nat_of_ord k) * lazard_fourier_sum roots k)%R.
Proof.
rewrite /lazard_fourier_sum.
under [LHS]eq_bigr=> i _ do rewrite tnth_lazard_cyclic_shift.
rewrite (reindex_inj (@perm_inj _ five_cycle^-1)) /=.
under [LHS]eq_bigr=> i _ do
  rewrite permKV lazard_cyclic_shift_weight.
rewrite mulr_sumr.
apply: eq_bigr=> i _.
by rewrite mulrA.
Qed.
Local Close Scope group_scope.

(** A geometric sum of powers of a primitive fifth root. *)
Definition lazard_geometric_sum (d : nat) : F :=
  \sum_(k : 'I_5) omega ^+ (d * nat_of_ord k).

Lemma lazard_five_natrE : (5%:R : F) = 1 + 1 + 1 + 1 + 1.
Proof.
have h2 : (2%:R : F) = 1 + 1 := @natrD F 1 1.
have h3 : (3%:R : F) = 1 + 1 + 1.
  rewrite -h2; exact: (@natrD F 2 1).
have h4 : (4%:R : F) = 1 + 1 + 1 + 1.
  rewrite -h3; exact: (@natrD F 3 1).
rewrite -h4.
exact: (@natrD F 4 1).
Qed.

(** Orthogonality of the five characters, stated for an arbitrary natural
    exponent so it can be used directly after exchanging the two Fourier
    sums. *)
Lemma lazard_geometric_orthogonality_nat d :
  lazard_geometric_sum d = if (5 %| d)%N then 5%:R else 0.
Proof.
case hd: (5 %| d)%N.
- have hpow : omega ^+ d = 1.
    apply/eqP.
    by rewrite -(prim_order_dvd omega_primitive) hd.
  rewrite /lazard_geometric_sum lazard_sum_ord5.
  rewrite !exprM hpow !expr1n.
  by rewrite -lazard_five_natrE.
- have hpow_neq1 : omega ^+ d != 1.
    by rewrite -(prim_order_dvd omega_primitive) hd.
  have hproduct :
      (omega ^+ d - 1) * lazard_geometric_sum d = 0.
    rewrite /lazard_geometric_sum.
    under eq_bigr => k _ do rewrite exprM.
    rewrite -subrX1.
    have horder := prim_expr_order omega_primitive.
    by rewrite -exprM mulnC exprM horder expr1n subrr.
  have hfactor : omega ^+ d - 1 != 0 by rewrite subr_eq0.
  have hsum0 : lazard_geometric_sum d = 0.
    apply: (mulfI hfactor).
    by rewrite mulr0 hproduct.
  exact: hsum0.
Qed.

(** The finite arithmetic used by inverse Fourier: among [0,...,4], only
    [j=i] makes [5-i+j] divisible by five. *)
Lemma lazard_five_dvd_inverse_offset (i j : 'I_5) :
  (5 %| (5 - nat_of_ord i + nat_of_ord j))%N = (j == i).
Proof.
case: i=> [[|[|[|[|[|i]]]]] hi] /=;
  case: j=> [[|[|[|[|[|j]]]]] hj] //=.
Qed.

(** The unscaled inverse Fourier numerator.  The exponent [(5-i)k]
    represents [-ik] modulo five. *)
Definition lazard_inverse_fourier_numerator
    (roots : 5.-tuple F) (i : 'I_5) : F :=
  \sum_(k : 'I_5)
    omega ^+ ((5 - nat_of_ord i) * nat_of_ord k) *
      lazard_fourier_sum roots k.

Lemma lazard_inverse_fourier_numeratorE roots i :
  lazard_inverse_fourier_numerator roots i =
    5%:R * tnth roots i.
Proof.
rewrite /lazard_inverse_fourier_numerator /lazard_fourier_sum.
under [LHS]eq_bigr => k _ do rewrite mulr_sumr.
rewrite exchange_big.
under [LHS]eq_bigr => j _.
  under eq_bigr => k _ do rewrite mulrA -exprD -mulnDl.
  rewrite -big_distrl
    -/(lazard_geometric_sum (5 - nat_of_ord i + nat_of_ord j)).
  rewrite lazard_geometric_orthogonality_nat.
  rewrite lazard_five_dvd_inverse_offset.
over.
rewrite (bigD1 i) //= eqxx.
rewrite big1 ?addr0 // => j hji.
by rewrite (negbTE hji) mul0r.
Qed.

Definition lazard_inverse_fourier_coordinate
    (roots : 5.-tuple F) (i : 'I_5) : F :=
  (5%:R)^-1 * lazard_inverse_fourier_numerator roots i.

(** Full inverse Fourier identity: every coordinate of the ordered root
    tuple is recovered from all five Fourier sums. *)
Theorem lazard_inverse_fourier_coordinateE
    (five_neq0 : (5%:R : F) != 0) roots i :
  lazard_inverse_fourier_coordinate roots i = tnth roots i.
Proof.
rewrite /lazard_inverse_fourier_coordinate
  lazard_inverse_fourier_numeratorE.
by rewrite mulrA (mulVf five_neq0) mul1r.
Qed.

End Fourier.

End PolynomialFormulasLazardQuinticFourier.
