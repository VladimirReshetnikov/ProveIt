From Stdlib Require Import Reals Ring Field Psatz.

Open Scope R_scope.

(** Field identities certifying the complete linear and quadratic formulas.
    A square root is passed together with its defining square equation, so
    these theorems make no hidden choice of a square-root branch. *)

Module LeanProofs.
Module PolynomialFormulas.

Definition linear (a b x : R) : R := a * x + b.

Theorem linear_formula (a b : R) (ha : a <> 0) :
  linear a b (-b / a) = 0.
Proof.
  unfold linear.
  field; exact ha.
Qed.

Definition solve_linear (a b : R) : R := -b / a.

Theorem solve_linear_correct (a b : R) (ha : a <> 0) :
  linear a b (solve_linear a b) = 0.
Proof. apply linear_formula; exact ha. Qed.

Theorem linear_eq_zero_iff (a b x : R) (ha : a <> 0) :
  linear a b x = 0 <-> x = -b / a.
Proof.
  unfold linear.
  split.
  - intro h.
    assert (hax : a * x = -b) by nra.
    rewrite <- hax.
    field; exact ha.
  - intro h. rewrite h. field; exact ha.
Qed.

Definition quadratic (a b c x : R) : R := a * x ^ 2 + b * x + c.

Definition solve_quadratic (a b c s : R) : R * R :=
  ((-b + s) / (2 * a), (-b - s) / (2 * a)).

Theorem quadratic_formula_plus (a b c s : R) (ha : a <> 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
  quadratic a b c ((-b + s) / (2 * a)) = 0.
Proof.
  set (x := (-b + s) / (2 * a)).
  assert (hx : 2 * a * x = -b + s).
  { unfold x. field; exact ha. }
  assert (hxsq : (2 * a * x) ^ 2 = (-b + s) ^ 2) by now rewrite hx.
  unfold quadratic.
  destruct (Rdichotomy a 0 ha); nra.
Qed.

Theorem quadratic_formula_minus (a b c s : R) (ha : a <> 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
  quadratic a b c ((-b - s) / (2 * a)) = 0.
Proof.
  set (x := (-b - s) / (2 * a)).
  assert (hx : 2 * a * x = -b - s).
  { unfold x. field; exact ha. }
  assert (hxsq : (2 * a * x) ^ 2 = (-b - s) ^ 2) by now rewrite hx.
  unfold quadratic.
  destruct (Rdichotomy a 0 ha); nra.
Qed.

Theorem solve_quadratic_correct (a b c s : R) (ha : a <> 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
  quadratic a b c (fst (solve_quadratic a b c s)) = 0 /\
  quadratic a b c (snd (solve_quadratic a b c s)) = 0.
Proof.
  split; cbn [solve_quadratic].
  - apply quadratic_formula_plus; assumption.
  - apply quadratic_formula_minus; assumption.
Qed.

Theorem quadratic_formula_factorization (a b c s x : R) (ha : a <> 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
  quadratic a b c x =
    a * (x - (-b + s) / (2 * a)) *
      (x - (-b - s) / (2 * a)).
Proof.
  set (xp := (-b + s) / (2 * a)).
  set (xm := (-b - s) / (2 * a)).
  assert (hp : 2 * a * xp = -b + s).
  { unfold xp. field; exact ha. }
  assert (hm : 2 * a * xm = -b - s).
  { unfold xm. field; exact ha. }
  assert (hsum : a * (xp + xm) = -b) by nra.
  assert (hprod_raw :
      (2 * a * xp) * (2 * a * xm) = (-b + s) * (-b - s))
    by now rewrite hp, hm.
  assert (hprod : a * xp * xm = c).
  { apply (Rmult_eq_reg_l a); [nra | exact ha]. }
  unfold quadratic.
  change (a * x ^ 2 + b * x + c = a * (x - xp) * (x - xm)).
  assert (hexpand : a * (x - xp) * (x - xm) =
      a * x ^ 2 - a * (xp + xm) * x + a * xp * xm) by ring.
  rewrite hexpand.
  rewrite hsum, hprod.
  ring.
Qed.

Theorem quadratic_eq_zero_iff (a b c s x : R) (ha : a <> 0)
    (hs : s ^ 2 = b ^ 2 - 4 * a * c) :
  quadratic a b c x = 0 <->
    x = (-b + s) / (2 * a) \/ x = (-b - s) / (2 * a).
Proof.
  rewrite (quadratic_formula_factorization a b c s x ha hs).
  split.
  - intro h.
    apply Rmult_integral in h as [h | h].
    + apply Rmult_integral in h as [h | h].
      * contradiction.
      * left. lra.
    + right. lra.
  - intros [h | h]; rewrite h; ring.
Qed.

End PolynomialFormulas.
End LeanProofs.
