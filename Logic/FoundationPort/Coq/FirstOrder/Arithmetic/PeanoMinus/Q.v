(**
  The omega-plus-one countermodel separating Robinson Q from PA-minus.

  This ports the semantic content of
  [Foundation/FirstOrder/Arithmetic/PeanoMinus/Q.lean].  Naturals are finite
  points and [None] is the extra top point.  It is a model of the exact
  Robinson laws, but its top is a successor fixed point and is below itself,
  so the Peano-minus strict-order laws cannot hold.
*)

From Stdlib Require Import Arith.PeanoNat Lia.
From Foundation.FirstOrder.Arithmetic.Basic Require Import Misc.
From Foundation.FirstOrder.Arithmetic.R0 Require Import Basic.
From Foundation.FirstOrder.Arithmetic.Q Require Import Basic.
From Foundation.FirstOrder.Arithmetic.PeanoMinus Require Import Basic.

Set Implicit Arguments.
Unset Strict Implicit.
Set Universe Polymorphism.

Definition omega_add_one : Type := option nat.

Definition omega_add_one_add (x y : omega_add_one) : omega_add_one :=
  match x, y with
  | Some n, Some m => Some (n + m)
  | None, _ => None
  | _, None => None
  end.

Definition omega_add_one_mul (x y : omega_add_one) : omega_add_one :=
  match x, y with
  | Some n, Some m => Some (n * m)
  | Some 0, None => Some 0
  | None, Some 0 => Some 0
  | _, _ => None
  end.

Definition omega_add_one_lt (x y : omega_add_one) : Prop :=
  match x, y with
  | Some n, Some m => n < m
  | _, None => True
  | None, Some _ => False
  end.

Definition omega_add_one_oring : oring_carrier omega_add_one :=
  {| oring_zero := Some 0;
     oring_one := Some 1;
     oring_add := omega_add_one_add;
     oring_mul := omega_add_one_mul;
     oring_lt := omega_add_one_lt |}.

Lemma omega_add_one_numeral : forall n,
  oring_numeral omega_add_one_oring n = Some n.
Proof.
  induction n as [|n IH]; [reflexivity|].
  destruct n as [|n]; [reflexivity|].
  change (omega_add_one_add
    (oring_numeral omega_add_one_oring (S n)) (Some 1) = Some (S (S n))).
  rewrite IH. cbn [omega_add_one_add]. f_equal. lia.
Qed.

Definition omega_add_one_robinson_q_laws :
    robinson_q_laws omega_add_one_oring.
Proof.
  constructor.
  - intros [n|]; cbn [omega_add_one_oring omega_add_one_add].
    + intro Heq. injection Heq. lia.
    + discriminate.
  - intros [n|] [m|]; cbn [omega_add_one_oring omega_add_one_add]; intro Heq;
      try discriminate; try reflexivity.
    injection Heq. intro Hnm. f_equal. lia.
  - intros [n|].
    + destruct n as [|n].
      * left. reflexivity.
      * right. exists (Some n).
        change (Some (S n) = Some (n + 1)). f_equal. lia.
    + right. exists None. reflexivity.
  - intros [n|]; cbn [omega_add_one_oring omega_add_one_add].
    + change (Some (n + 0) = Some n). f_equal. lia.
    + reflexivity.
  - intros [n|] [m|].
    + change (Some (n + (m + 1)) = Some (n + m + 1)). f_equal. lia.
    + reflexivity.
    + reflexivity.
    + reflexivity.
  - intros [n|].
    + cbv [omega_add_one_oring omega_add_one_mul oring_zero oring_mul].
      destruct n as [|n]; [reflexivity|].
      f_equal. apply Nat.mul_0_r.
    + reflexivity.
  - intros [n|] [m|].
    + destruct n as [|n]; destruct m as [|m];
        cbv [omega_add_one_oring omega_add_one_add omega_add_one_mul
          oring_one oring_add oring_mul]; try reflexivity;
        f_equal; lia.
    + destruct n;
        cbv [omega_add_one_oring omega_add_one_add omega_add_one_mul
          oring_one oring_add oring_mul]; reflexivity.
    + destruct m;
        cbv [omega_add_one_oring omega_add_one_add omega_add_one_mul
          oring_one oring_add oring_mul]; reflexivity.
    + reflexivity.
  - intros [n|] [m|];
      cbv [omega_add_one_oring omega_add_one_lt omega_add_one_add
        oring_zero oring_one oring_add oring_lt].
    + split.
      * intro Hnm. exists (Some (m - n - 1)). f_equal. lia.
      * intros [[c|] Hc].
        -- injection Hc. lia.
        -- discriminate.
    + split.
      * intro Htop. exists None. reflexivity.
      * intros Hexists. exact I.
    + split.
      * contradiction.
      * intros [[c|] Hc]; discriminate.
    + split.
      * intro Htop. exists (Some 0). reflexivity.
      * intros Hexists. exact I.
Defined.

Definition omega_add_one_r0_laws : r0_laws omega_add_one_oring.
Proof.
  constructor.
  - intros n m. rewrite !omega_add_one_numeral.
    cbv [omega_add_one_oring omega_add_one_add oring_add].
    f_equal.
  - intros n m. rewrite !omega_add_one_numeral.
    cbv [omega_add_one_oring omega_add_one_mul oring_mul].
    destruct n as [|n]; [reflexivity|]. f_equal.
  - intros n m Hne. rewrite !omega_add_one_numeral.
    intro Heq. injection Heq. contradiction.
  - intros n [x|].
    + rewrite omega_add_one_numeral.
      cbv [omega_add_one_oring omega_add_one_lt oring_lt]. split.
      * intro Hx. exists x. split; [exact Hx|].
        symmetry. apply omega_add_one_numeral.
      * intros [i [Hin Hi]]. rewrite omega_add_one_numeral in Hi.
        injection Hi. intro Hxi. subst i. exact Hin.
    + rewrite omega_add_one_numeral.
      cbv [omega_add_one_oring omega_add_one_lt oring_lt]. split.
      * contradiction.
      * intros [i [Hin Hi]]. rewrite omega_add_one_numeral in Hi.
        discriminate.
Defined.

Lemma omega_add_one_successor_fixed_point :
  exists x : omega_add_one,
    omega_add_one_add x (oring_one omega_add_one_oring) = x.
Proof. exists None. reflexivity. Qed.

Lemma omega_add_one_top_lt_top :
  omega_add_one_lt None None.
Proof. exact I. Qed.

Theorem omega_add_one_not_peano_minus :
  ~ peano_minus_laws omega_add_one_oring.
Proof.
  intro H.
  exact (@peano_minus_lt_irrefl omega_add_one omega_add_one_oring H
    None omega_add_one_top_lt_top).
Qed.
