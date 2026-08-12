From Stdlib Require Import Ring.
From mathcomp Require Import all_ssreflect all_algebra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(** The classical nested-square constructions of the four primitive fifth
    roots of unity used in Lazard's quintic formula.  The second nested root
    is selected coherently from the first, so its sign is not an extra
    premise. *)
Module PolynomialFormulasLazardQuinticPrimitiveFifthRoot.

Import GRing.Theory.

Local Open Scope ring_scope.

Section PrimitiveFifthRoot.

Variable F : fieldType.

(** If [s^2 = 5] and [t^2 = -10 - 2s], this is either of the two
    conjugate primitive fifth roots obtained by choosing a sign for [t]. *)
Definition lazard_square_radical_fifth_root (s t : F) : F :=
  (- 1 + s + t) / 4%:R.

(** The compatible determination of the other nested square root in the
    four-value display.  Defining it from [s] and [t] prevents an independent
    and possibly incoherent sign choice. *)
Definition lazard_square_radical_fifth_root_other_square (s t : F) : F :=
  (s - 1) * t / 2%:R.

(** The remaining three literal values, in Lazard's printed order. *)
Definition lazard_square_radical_fifth_root_pow_four (s t : F) : F :=
  (- 1 + s - t) / 4%:R.

Definition lazard_square_radical_fifth_root_pow_two (s t : F) : F :=
  (- 1 - s + lazard_square_radical_fifth_root_other_square s t) / 4%:R.

Definition lazard_square_radical_fifth_root_pow_three (s t : F) : F :=
  (- 1 - s - lazard_square_radical_fifth_root_other_square s t) / 4%:R.

(** Evaluation of the fifth cyclotomic polynomial. *)
Definition lazard_fifth_cyclotomic_value (z : F) : F :=
  z ^+ 4 + z ^+ 3 + z ^+ 2 + z + 1.

(** A local bridge exposing MathComp's packed ring operations to the
    standard [ring] tactic. *)
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

Lemma ring_addE (x y : F) : x + y = ring_add x y. Proof. reflexivity. Qed.
Lemma ring_mulE (x y : F) : x * y = ring_mul x y. Proof. reflexivity. Qed.
Lemma ring_subE (x y : F) : x - y = ring_sub x y. Proof. reflexivity. Qed.
Lemma ring_oppE (x : F) : - x = ring_opp x. Proof. reflexivity. Qed.
Lemma ring_zeroE : (0 : F) = ring_zero. Proof. reflexivity. Qed.
Lemma ring_oneE : @GRing.one F = ring_one. Proof. reflexivity. Qed.

Lemma lazard_fifth_root_mathcomp_ring_theory :
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

Add Ring lazard_fifth_root_ring : lazard_fifth_root_mathcomp_ring_theory.
Opaque ring_zero ring_one ring_add ring_mul ring_sub ring_opp ring_eq.

Lemma lazard_natr_succE n : (n.+1%:R : F) = n%:R + 1.
Proof. by rewrite natr1. Qed.

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

Lemma lazard_expr3E (x : F) : x ^+ 3 = x * x * x.
Proof. by rewrite exprSr expr2. Qed.

Lemma lazard_expr4E (x : F) : x ^+ 4 = x * x * x * x.
Proof. by rewrite exprSr lazard_expr3E. Qed.

Lemma lazard_expr5E (x : F) : x ^+ 5 = x * x * x * x * x.
Proof. by rewrite exprSr lazard_expr4E. Qed.

Ltac finish_lazard_fifth_root_ring :=
  repeat first
    [ rewrite lazard_expr3E | rewrite lazard_expr4E
    | rewrite lazard_expr5E | rewrite expr2
    | rewrite lazard_natr_succE | rewrite mulr0n
    | rewrite ring_addE | rewrite ring_mulE | rewrite ring_subE
    | rewrite ring_oppE | rewrite ring_zeroE | rewrite ring_oneE ];
  match goal with
  | |- ?lhs = ?rhs => change (ring_eq lhs rhs)
  end;
  ring.

Lemma lazard_four_neq0 (two_neq0 : (2%:R : F) != 0) :
  (4%:R : F) != 0.
Proof.
have h4 : (4%:R : F) = 2%:R * 2%:R by rewrite -natrM.
rewrite h4.
apply: mulf_neq0; exact: two_neq0.
Qed.

Lemma lazard_eight_neq0 (two_neq0 : (2%:R : F) != 0) :
  (8%:R : F) != 0.
Proof.
have h8 : (8%:R : F) = 2%:R * 4%:R by rewrite -natrM.
rewrite h8.
exact: mulf_neq0 two_neq0 (lazard_four_neq0 two_neq0).
Qed.

Lemma lazard_sixteen_neq0 (two_neq0 : (2%:R : F) != 0) :
  (16%:R : F) != 0.
Proof.
have h16 : (16%:R : F) = 4%:R * 4%:R by rewrite -natrM.
rewrite h16.
exact: mulf_neq0 (lazard_four_neq0 two_neq0)
  (lazard_four_neq0 two_neq0).
Qed.

(** Clearing the denominator in the definition of [z]. *)
Lemma lazard_square_radical_fifth_root_clear_denominator
    (two_neq0 : (2%:R : F) != 0) (s t : F) :
  4%:R * lazard_square_radical_fifth_root s t = - 1 + s + t.
Proof.
have four_neq0 := lazard_four_neq0 two_neq0.
rewrite /lazard_square_radical_fifth_root.
by rewrite [4%:R * _]mulrC divfK.
Qed.

Lemma lazard_square_radical_fifth_root_other_square_clear_denominator
    (two_neq0 : (2%:R : F) != 0) (s t : F) :
  2%:R * lazard_square_radical_fifth_root_other_square s t =
    (s - 1) * t.
Proof.
rewrite /lazard_square_radical_fifth_root_other_square.
by rewrite [2%:R * _]mulrC divfK.
Qed.

Lemma lazard_square_radical_fifth_root_pow_four_clear_denominator
    (two_neq0 : (2%:R : F) != 0) (s t : F) :
  4%:R * lazard_square_radical_fifth_root_pow_four s t = - 1 + s - t.
Proof.
have four_neq0 := lazard_four_neq0 two_neq0.
rewrite /lazard_square_radical_fifth_root_pow_four.
by rewrite [4%:R * _]mulrC divfK.
Qed.

Lemma lazard_square_radical_fifth_root_pow_two_clear_denominator
    (two_neq0 : (2%:R : F) != 0) (s t : F) :
  4%:R * lazard_square_radical_fifth_root_pow_two s t =
    - 1 - s + lazard_square_radical_fifth_root_other_square s t.
Proof.
have four_neq0 := lazard_four_neq0 two_neq0.
rewrite /lazard_square_radical_fifth_root_pow_two.
by rewrite [4%:R * _]mulrC divfK.
Qed.

Lemma lazard_square_radical_fifth_root_pow_three_clear_denominator
    (two_neq0 : (2%:R : F) != 0) (s t : F) :
  4%:R * lazard_square_radical_fifth_root_pow_three s t =
    - 1 - s - lazard_square_radical_fifth_root_other_square s t.
Proof.
have four_neq0 := lazard_four_neq0 two_neq0.
rewrite /lazard_square_radical_fifth_root_pow_three.
by rewrite [4%:R * _]mulrC divfK.
Qed.

(** The coherent determination really is a square root of the other printed
    radicand [-10 + 2s]. *)
Theorem lazard_square_radical_fifth_root_other_square_sq
    (two_neq0 : (2%:R : F) != 0) (s t : F)
    (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s) :
  lazard_square_radical_fifth_root_other_square s t ^+ 2 =
    - 10%:R + 2%:R * s.
Proof.
pose u := lazard_square_radical_fifth_root_other_square s t.
have four_neq0 := lazard_four_neq0 two_neq0.
have hu : 2%:R * u = (s - 1) * t.
  exact: lazard_square_radical_fifth_root_other_square_clear_denominator
    two_neq0 s t.
have hcertificate :
    4%:R * (u ^+ 2 - (- 10%:R + 2%:R * s)) =
      (t ^+ 2 + 4%:R) * (s ^+ 2 - 5%:R) +
      (6%:R - 2%:R * s) *
        (t ^+ 2 - (- 10%:R - 2%:R * s)) +
      (s * t - t + 2%:R * u) *
        (2%:R * u - (s - 1) * t).
  finish_lazard_fifth_root_ring.
apply: subr0_eq.
apply: (mulfI four_neq0).
by rewrite mulr0 hcertificate hs ht hu !subrr !mulr0 !addr0.
Qed.

(** The square equations imply the fifth cyclotomic equation.  The proof
    is a polynomial certificate after clearing the denominator. *)
Theorem lazard_square_radical_fifth_root_cyclotomic
    (two_neq0 : (2%:R : F) != 0) (s t : F)
    (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s) :
  lazard_fifth_cyclotomic_value
      (lazard_square_radical_fifth_root s t) = 0.
Proof.
pose z := lazard_square_radical_fifth_root s t.
have four_neq0 := lazard_four_neq0 two_neq0.
have hz : 4%:R * z = - 1 + s + t.
  exact: lazard_square_radical_fifth_root_clear_denominator two_neq0 s t.
have hclear :
    (4%:R) ^+ 4 * lazard_fifth_cyclotomic_value z =
      (4%:R * z) ^+ 4 +
      4%:R * (4%:R * z) ^+ 3 +
      (4%:R) ^+ 2 * (4%:R * z) ^+ 2 +
      (4%:R) ^+ 3 * (4%:R * z) + (4%:R) ^+ 4.
  rewrite /lazard_fifth_cyclotomic_value.
  finish_lazard_fifth_root_ring.
rewrite hz in hclear.
have hcertificate :
    (- 1 + s + t) ^+ 4 +
      4%:R * (- 1 + s + t) ^+ 3 +
      (4%:R) ^+ 2 * (- 1 + s + t) ^+ 2 +
      (4%:R) ^+ 3 * (- 1 + s + t) + (4%:R) ^+ 4 =
    (s ^+ 2 + 4%:R * s * t - 12%:R * s - 8%:R * t - 41%:R) *
      (s ^+ 2 - 5%:R) +
    (t ^+ 2 + 4%:R * s * t + 6%:R * s ^+ 2 - 2%:R * s) *
      (t ^+ 2 - (- 10%:R - 2%:R * s)).
  finish_lazard_fifth_root_ring.
have hscaled : (4%:R) ^+ 4 * lazard_fifth_cyclotomic_value z = 0.
  by rewrite hclear hcertificate hs ht !subrr !mulr0 addr0.
have hpow4 : (4%:R : F) ^+ 4 != 0 := expf_neq0 4 four_neq0.
have hcancel := congr1 (fun x : F => ((4%:R) ^+ 4)^-1 * x) hscaled.
by move: hcancel; rewrite mulrA (mulVf hpow4) mul1r mulr0.
Qed.

(** The cyclotomic equation immediately gives [z^5 = 1]. *)
Theorem lazard_square_radical_fifth_root_pow_five
    (two_neq0 : (2%:R : F) != 0) (s t : F)
    (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s) :
  lazard_square_radical_fifth_root s t ^+ 5 = 1.
Proof.
pose z := lazard_square_radical_fifth_root s t.
have hphi : lazard_fifth_cyclotomic_value z = 0.
  exact: (lazard_square_radical_fifth_root_cyclotomic
    (s := s) (t := t) two_neq0 hs ht).
have hfactor :
    z ^+ 5 = (z - 1) * lazard_fifth_cyclotomic_value z + 1.
  rewrite /lazard_fifth_cyclotomic_value.
  finish_lazard_fifth_root_ring.
by rewrite hfactor hphi mulr0 add0r.
Qed.

(** No choice of sign for [t] is needed to prove nontriviality.  Once the
    cyclotomic equation is known, substituting [z = 1] would make [5 = 0].
    Thus the only excluded characteristics are two (for the denominator)
    and five. *)
Theorem lazard_square_radical_fifth_root_neq_one
    (two_neq0 : (2%:R : F) != 0) (five_neq0 : (5%:R : F) != 0)
    (s t : F) (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s) :
  lazard_square_radical_fifth_root s t != 1.
Proof.
apply/negP=> /eqP hz1.
have hphi := lazard_square_radical_fifth_root_cyclotomic
  (s := s) (t := t) two_neq0 hs ht.
rewrite hz1 /lazard_fifth_cyclotomic_value !expr1n
  -lazard_five_natrE in hphi.
by move: five_neq0; rewrite hphi eqxx.
Qed.

(** Consequently the classical radical is primitive of exact order five. *)
Theorem lazard_square_radical_fifth_root_primitive
    (two_neq0 : (2%:R : F) != 0) (five_neq0 : (5%:R : F) != 0)
    (s t : F) (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s) :
  5.-primitive_root (lazard_square_radical_fifth_root s t).
Proof.
pose z := lazard_square_radical_fifth_root s t.
have hpow : z ^+ 5 = 1.
  exact: (lazard_square_radical_fifth_root_pow_five
    (s := s) (t := t) two_neq0 hs ht).
have hneq : z != 1.
  exact: (lazard_square_radical_fifth_root_neq_one
    (s := s) (t := t) two_neq0 five_neq0 hs ht).
have five_pos : (5 > 0)%N by [].
have [m hm hdiv] := prim_order_exists (n := 5) (z := z) five_pos hpow.
have hm_ne1 : m != 1%N.
  apply/negP=> /eqP hm1.
  have horder := prim_expr_order hm.
  rewrite hm1 expr1 in horder.
  by move: hneq; rewrite horder eqxx.
have hm5 : m = 5%N :=
  elimT (prime_nt_dvdP (isT : prime 5) hm_ne1) hdiv.
by move: hm; rewrite hm5.
Qed.

(** The third value in the printed display is the second power of the first.
    The proof uses the coherent square [u], rather than accepting a separate
    compatibility certificate from the caller. *)
Theorem lazard_square_radical_fifth_root_pow_twoE
    (two_neq0 : (2%:R : F) != 0) (s t : F)
    (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s) :
  lazard_square_radical_fifth_root_pow_two s t =
    lazard_square_radical_fifth_root s t ^+ 2.
Proof.
pose z := lazard_square_radical_fifth_root s t.
pose u := lazard_square_radical_fifth_root_other_square s t.
pose z2 := lazard_square_radical_fifth_root_pow_two s t.
have four_neq0 := lazard_four_neq0 two_neq0.
have hz : 4%:R * z = - 1 + s + t.
  exact: lazard_square_radical_fifth_root_clear_denominator two_neq0 s t.
have hu : 2%:R * u = (s - 1) * t.
  exact: lazard_square_radical_fifth_root_other_square_clear_denominator
    two_neq0 s t.
have hz2clear : 4%:R * z2 = - 1 - s + u.
  exact: lazard_square_radical_fifth_root_pow_two_clear_denominator
    two_neq0 s t.
have hcertificate :
    (- 1 + s + t) ^+ 2 - 4%:R * (- 1 - s + u) =
      (s ^+ 2 - 5%:R) +
      (t ^+ 2 - (- 10%:R - 2%:R * s)) -
      2%:R * (2%:R * u - (s - 1) * t).
  finish_lazard_fifth_root_ring.
have hnumerator :
    (- 1 + s + t) ^+ 2 = 4%:R * (- 1 - s + u).
  apply: subr0_eq.
  by rewrite hcertificate hs ht hu !subrr !mulr0 addr0 subr0.
have hz2 : 4%:R * z ^+ 2 = - 1 - s + u.
  apply: (mulfI four_neq0).
  transitivity ((4%:R * z) ^+ 2).
  - finish_lazard_fifth_root_ring.
  - by rewrite hz hnumerator.
apply: (mulfI four_neq0).
by rewrite hz2clear hz2.
Qed.

(** Multiplying the first and third displayed values gives the fourth one;
    together with the preceding square identity this proves the printed
    fourth value is the third power of the first. *)
Theorem lazard_square_radical_fifth_root_pow_threeE
    (two_neq0 : (2%:R : F) != 0) (s t : F)
    (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s) :
  lazard_square_radical_fifth_root_pow_three s t =
    lazard_square_radical_fifth_root s t ^+ 3.
Proof.
pose z := lazard_square_radical_fifth_root s t.
pose u := lazard_square_radical_fifth_root_other_square s t.
pose z2 := lazard_square_radical_fifth_root_pow_two s t.
pose z3 := lazard_square_radical_fifth_root_pow_three s t.
have sixteen_neq0 := lazard_sixteen_neq0 two_neq0.
have hz : 4%:R * z = - 1 + s + t.
  exact: lazard_square_radical_fifth_root_clear_denominator two_neq0 s t.
have hu : 2%:R * u = (s - 1) * t.
  exact: lazard_square_radical_fifth_root_other_square_clear_denominator
    two_neq0 s t.
have hz2clear : 4%:R * z2 = - 1 - s + u.
  exact: lazard_square_radical_fifth_root_pow_two_clear_denominator
    two_neq0 s t.
have hz3clear : 4%:R * z3 = - 1 - s - u.
  exact: lazard_square_radical_fifth_root_pow_three_clear_denominator
    two_neq0 s t.
have hcertificate :
    2%:R *
      ((- 1 + s + t) * (- 1 - s + u) -
        4%:R * (- 1 - s - u)) =
      (t - 4%:R) * (s ^+ 2 - 5%:R) +
      (s - 1) * (t ^+ 2 - (- 10%:R - 2%:R * s)) +
      (s + t + 3%:R) * (2%:R * u - (s - 1) * t).
  finish_lazard_fifth_root_ring.
have hnumerator :
    (- 1 + s + t) * (- 1 - s + u) =
      4%:R * (- 1 - s - u).
  apply: subr0_eq.
  apply: (mulfI two_neq0).
  by rewrite mulr0 hcertificate hs ht hu !subrr !mulr0 !addr0.
have hmul : z * z2 = z3.
  apply: (mulfI sixteen_neq0).
  transitivity ((4%:R * z) * (4%:R * z2)).
  - rewrite (@natrM F 4 4).
    finish_lazard_fifth_root_ring.
  - rewrite hz hz2clear hnumerator.
    rewrite (@natrM F 4 4) -mulrA hz3clear.
    reflexivity.
rewrite -hmul (lazard_square_radical_fifth_root_pow_twoE
  two_neq0 hs ht).
finish_lazard_fifth_root_ring.
Qed.

(** The second value in the printed display is the fourth power of the first. *)
Theorem lazard_square_radical_fifth_root_pow_fourE
    (two_neq0 : (2%:R : F) != 0) (s t : F)
    (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s) :
  lazard_square_radical_fifth_root_pow_four s t =
    lazard_square_radical_fifth_root s t ^+ 4.
Proof.
pose z := lazard_square_radical_fifth_root s t.
pose z4 := lazard_square_radical_fifth_root_pow_four s t.
have sixteen_neq0 := lazard_sixteen_neq0 two_neq0.
have hz : 4%:R * z = - 1 + s + t.
  exact: lazard_square_radical_fifth_root_clear_denominator two_neq0 s t.
have hz4clear : 4%:R * z4 = - 1 + s - t.
  exact: lazard_square_radical_fifth_root_pow_four_clear_denominator
    two_neq0 s t.
have hcertificate :
    (- 1 + s + t) * (- 1 + s - t) - 16%:R =
      (s ^+ 2 - 5%:R) -
      (t ^+ 2 - (- 10%:R - 2%:R * s)).
  finish_lazard_fifth_root_ring.
have hnumerator : (- 1 + s + t) * (- 1 + s - t) = 16%:R.
  apply: subr0_eq.
  by rewrite hcertificate hs ht !subrr.
have hproduct : z * z4 = 1.
  apply: (mulfI sixteen_neq0).
  transitivity ((4%:R * z) * (4%:R * z4)).
  - rewrite (@natrM F 4 4).
    finish_lazard_fifth_root_ring.
  - by rewrite hz hz4clear hnumerator mulr1.
have hproduct_neq0 : z * z4 != 0 by rewrite hproduct oner_eq0.
rewrite mulf_eq0 negb_or in hproduct_neq0.
move/andP: hproduct_neq0=> [z_neq0 _].
have hpow := lazard_square_radical_fifth_root_pow_five
  (s := s) (t := t) two_neq0 hs ht.
apply: (mulfI z_neq0).
rewrite hproduct.
transitivity (z ^+ 5).
- exact: esym hpow.
- finish_lazard_fifth_root_ring.
Qed.

Theorem lazard_square_radical_fifth_root_pow_four_primitive
    (two_neq0 : (2%:R : F) != 0) (five_neq0 : (5%:R : F) != 0)
    (s t : F) (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s) :
  5.-primitive_root (lazard_square_radical_fifth_root_pow_four s t).
Proof.
rewrite (lazard_square_radical_fifth_root_pow_fourE two_neq0 hs ht).
by rewrite (prim_root_exp_coprime 4
  (lazard_square_radical_fifth_root_primitive
    two_neq0 five_neq0 hs ht)).
Qed.

Theorem lazard_square_radical_fifth_root_pow_two_primitive
    (two_neq0 : (2%:R : F) != 0) (five_neq0 : (5%:R : F) != 0)
    (s t : F) (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s) :
  5.-primitive_root (lazard_square_radical_fifth_root_pow_two s t).
Proof.
rewrite (lazard_square_radical_fifth_root_pow_twoE two_neq0 hs ht).
by rewrite (prim_root_exp_coprime 2
  (lazard_square_radical_fifth_root_primitive
    two_neq0 five_neq0 hs ht)).
Qed.

Theorem lazard_square_radical_fifth_root_pow_three_primitive
    (two_neq0 : (2%:R : F) != 0) (five_neq0 : (5%:R : F) != 0)
    (s t : F) (hs : s ^+ 2 = 5%:R)
    (ht : t ^+ 2 = - 10%:R - 2%:R * s) :
  5.-primitive_root (lazard_square_radical_fifth_root_pow_three s t).
Proof.
rewrite (lazard_square_radical_fifth_root_pow_threeE two_neq0 hs ht).
by rewrite (prim_root_exp_coprime 3
  (lazard_square_radical_fifth_root_primitive
    two_neq0 five_neq0 hs ht)).
Qed.

(* -------------------------------------------------------------------- *)
(** * Recovering the two displayed square radicals from a primitive root *)

(** For an already supplied primitive fifth root [w], these are the two
    classical quadratic quantities whose displayed radical expression
    reconstructs [w].  Powers are used instead of an inverse so that all
    certificates below are polynomial identities modulo [Phi_5]. *)
Definition lazard_primitive_fifth_root_square_s (w : F) : F :=
  1 + 2%:R * (w + w ^+ 4).

Definition lazard_primitive_fifth_root_square_t (w : F) : F :=
  4%:R * w + 1 - lazard_primitive_fifth_root_square_s w.

(** The reverse direction of the cyclotomic calculation used above: exact
    order five forces the explicit fourth-degree cyclotomic value to vanish. *)
Lemma lazard_primitive_fifth_root_cyclotomic_value (w : F) :
  5.-primitive_root w -> lazard_fifth_cyclotomic_value w = 0.
Proof.
move=> w_primitive.
have hw5 : w ^+ 5 = 1 := prim_expr_order w_primitive.
have hw_ne1 : w != 1.
  apply/eqP=> hw1.
  have hbad : (5 %| 1)%N.
    by rewrite (prim_order_dvd w_primitive) hw1 expr1.
  by move: hbad.
have hfactor :
    (w - 1) * lazard_fifth_cyclotomic_value w = w ^+ 5 - 1.
  rewrite /lazard_fifth_cyclotomic_value.
  finish_lazard_fifth_root_ring.
have hproduct :
    (w - 1) * lazard_fifth_cyclotomic_value w = 0.
  by rewrite hfactor hw5 subrr.
have hw_sub_one : w - 1 != 0 by rewrite subr_eq0.
apply: (mulfI hw_sub_one).
by rewrite mulr0 hproduct.
Qed.

(** The first recovered quantity is an actual square root of five. *)
Lemma lazard_primitive_fifth_root_square_sE (w : F) :
  5.-primitive_root w ->
  lazard_primitive_fifth_root_square_s w ^+ 2 = 5%:R.
Proof.
move=> w_primitive.
have hphi := lazard_primitive_fifth_root_cyclotomic_value w_primitive.
have hcertificate :
    lazard_primitive_fifth_root_square_s w ^+ 2 - 5%:R =
      (- 4%:R + 8%:R * w - 4%:R * w ^+ 3 + 4%:R * w ^+ 4) *
        lazard_fifth_cyclotomic_value w.
  rewrite /lazard_primitive_fifth_root_square_s
    /lazard_fifth_cyclotomic_value.
  finish_lazard_fifth_root_ring.
apply/eqP.
by rewrite -subr_eq0 hcertificate hphi mulr0 eqxx.
Qed.

(** The second recovered quantity satisfies Lazard's second quadratic
    equation over the first square field. *)
Lemma lazard_primitive_fifth_root_square_tE (w : F) :
  5.-primitive_root w ->
  lazard_primitive_fifth_root_square_t w ^+ 2 =
    - 10%:R - 2%:R * lazard_primitive_fifth_root_square_s w.
Proof.
move=> w_primitive.
have hphi := lazard_primitive_fifth_root_cyclotomic_value w_primitive.
have hcertificate :
    lazard_primitive_fifth_root_square_t w ^+ 2 -
        (- 10%:R - 2%:R * lazard_primitive_fifth_root_square_s w) =
      (12%:R - 8%:R * w - 4%:R * w ^+ 3 + 4%:R * w ^+ 4) *
        lazard_fifth_cyclotomic_value w.
  rewrite /lazard_primitive_fifth_root_square_t
    /lazard_primitive_fifth_root_square_s
    /lazard_fifth_cyclotomic_value.
  finish_lazard_fifth_root_ring.
apply/eqP.
by rewrite -subr_eq0 hcertificate hphi mulr0 eqxx.
Qed.

(** Substitution into the displayed two-square formula recovers the chosen
    primitive root itself; this is the membership bridge needed in a
    concrete common compositum. *)
Lemma lazard_primitive_fifth_root_square_reconstruct
    (two_neq0 : (2%:R : F) != 0) (w : F) :
  lazard_square_radical_fifth_root
      (lazard_primitive_fifth_root_square_s w)
      (lazard_primitive_fifth_root_square_t w) = w.
Proof.
have four_neq0 := lazard_four_neq0 two_neq0.
have hnumerator :
    - 1 + lazard_primitive_fifth_root_square_s w +
        lazard_primitive_fifth_root_square_t w = 4%:R * w.
  rewrite /lazard_primitive_fifth_root_square_t
    /lazard_primitive_fifth_root_square_s.
  finish_lazard_fifth_root_ring.
rewrite /lazard_square_radical_fifth_root hnumerator.
by rewrite mulrC divfK.
Qed.

End PrimitiveFifthRoot.

End PolynomialFormulasLazardQuinticPrimitiveFifthRoot.
