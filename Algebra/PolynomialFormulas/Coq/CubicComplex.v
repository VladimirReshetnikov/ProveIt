From Stdlib Require Import Reals Ring Field Psatz.
From Coquelicot Require Import Complex.

Open Scope C_scope.

(** Cardano's formula and its exhaustive complex-root theorem. *)

Module LeanProofs.
Module PolynomialFormulasCubicComplex.

Definition c0 : C := RtoC 0.
Definition c1 : C := RtoC 1.
Definition c2 : C := RtoC 2.
Definition c3 : C := RtoC 3.

Lemma c1_neq_0 : c1 <> c0.
Proof. unfold c1, c0, RtoC; intros h; injection h; lra. Qed.

Lemma c2_neq_0 : c2 <> c0.
Proof. unfold c2, c0, RtoC; intros h; injection h; lra. Qed.

Lemma c3_neq_0 : c3 <> c0.
Proof. unfold c3, c0, RtoC; intros h; injection h; lra. Qed.

Lemma Cmult_eq_zero (x y : C) : x * y = c0 -> x = c0 \/ y = c0.
Proof.
  intro h.
  destruct (Ceq_dec x c0) as [hx | hx]; [now left | right].
  destruct (Ceq_dec y c0) as [hy | hy]; [exact hy |].
  exfalso.
  apply (Cmult_neq_0 x y hx hy).
  exact h.
Qed.

Lemma Cmult3_eq_zero (x y z : C) :
    x * y * z = c0 -> x = c0 \/ y = c0 \/ z = c0.
Proof.
  intro h.
  apply Cmult_eq_zero in h as [hxy | hz]; [| now right; right].
  apply Cmult_eq_zero in hxy as [hx | hy]; [now left | now right; left].
Qed.

Lemma Cminus_eq_zero (x y : C) : x - y = c0 -> x = y.
Proof. apply (proj2 (Ceq_minus x y)). Qed.

Definition cubic (a b c d x : C) : C :=
  a * x ^ 3 + b * x ^ 2 + c * x + d.

Definition monic_cubic (A B D x : C) : C :=
  x ^ 3 + A * x ^ 2 + B * x + D.

Definition depressed_cubic (p q y : C) : C := y ^ 3 + p * y + q.

Definition cubic_p (A B : C) : C := B - c3 * (A / c3) ^ 2.

Definition cubic_q (A B D : C) : C :=
  D - B * (A / c3) + c2 * (A / c3) ^ 3.

Definition cubic_delta (p q : C) : C :=
  (q / c2) ^ 2 + (p / c3) ^ 3.

Definition solve_cubic (a b c d u v omega : C) : C * (C * C) :=
  (u + v - (b / a) / c3,
   (omega * u + omega ^ 2 * v - (b / a) / c3,
    omega ^ 2 * u + omega * v - (b / a) / c3)).

(** A concrete primitive cube root, proving that the branch condition below
    is inhabited in the complex numbers. *)
Definition primitive_omega : C := ((-1 / 2)%R, (sqrt 3 / 2)%R).

Theorem primitive_omega_spec :
  primitive_omega ^ 2 + primitive_omega + c1 = c0.
Proof.
  assert (hpos : (0 <= 3)%R) by lra.
  pose proof (Rsqr_sqrt 3 hpos) as hsqrt.
  unfold Rsqr in hsqrt.
  unfold primitive_omega, c1, c0, Cpow, Cplus, Cmult, RtoC.
  simpl.
  f_equal; nra.
Qed.

Theorem primitive_cube_root_cubed (omega : C)
    (homega : omega ^ 2 + omega + c1 = c0) : omega ^ 3 = c1.
Proof.
  unfold c1, c0 in *.
  apply (proj2 (Ceq_minus (omega ^ 3) (RtoC 1))).
  assert (hfactor : omega ^ 3 - RtoC 1 =
      (omega - RtoC 1) * (omega ^ 2 + omega + RtoC 1)) by ring.
  rewrite hfactor, homega, Cmult_0_r.
  ring.
Qed.

Theorem cubic_normalization (a b c d x : C) (ha : a <> c0) :
  cubic a b c d x = a * monic_cubic (b / a) (c / a) (d / a) x.
Proof.
  unfold cubic, monic_cubic.
  field; exact ha.
Qed.

Theorem depress_monic_cubic (A B D y : C) :
  monic_cubic A B D (y - A / c3) =
    depressed_cubic (cubic_p A B) (cubic_q A B D) y.
Proof.
  unfold monic_cubic, depressed_cubic, cubic_p, cubic_q, c2, c3.
  field; exact c3_neq_0.
Qed.

Lemma translate_monic_cubic (A B D x : C) :
  monic_cubic A B D x =
    depressed_cubic (cubic_p A B) (cubic_q A B D) (x + A / c3).
Proof.
  rewrite <- depress_monic_cubic.
  replace (x + A / c3 - A / c3) with x by ring.
  reflexivity.
Qed.

(** The three Cardano values give the complete linear factorization of a
    depressed cubic. *)
Theorem cardano_factorization (p q u v omega y : C)
    (hu : u ^ 3 + v ^ 3 = -q)
    (huv : c3 * u * v = -p)
    (homega : omega ^ 2 + omega + c1 = c0) :
  depressed_cubic p q y =
    (y - (u + v)) *
      (y - (omega * u + omega ^ 2 * v)) *
        (y - (omega ^ 2 * u + omega * v)).
Proof.
  set (r0 := u + v).
  set (r1 := omega * u + omega ^ 2 * v).
  set (r2 := omega ^ 2 * u + omega * v).
  assert (hsum : r0 + r1 + r2 = c0).
  { unfold r0, r1, r2.
    assert (hexpand :
        u + v + (omega * u + omega ^ 2 * v) +
          (omega ^ 2 * u + omega * v) =
        (u + v) * (omega ^ 2 + omega + c1)) by (unfold c1; ring).
    rewrite hexpand, homega, Cmult_0_r; reflexivity. }
  assert (hpairs : r0 * r1 + r0 * r2 + r1 * r2 = -(c3 * u * v)).
  { unfold r0, r1, r2.
    assert (hexpand :
        (u + v) * (omega * u + omega ^ 2 * v) +
          (u + v) * (omega ^ 2 * u + omega * v) +
          (omega * u + omega ^ 2 * v) * (omega ^ 2 * u + omega * v) =
        -(c3 * u * v) +
          (u * v * omega ^ 2 +
            (u ^ 2 - u * v + v ^ 2) * omega + c3 * u * v) *
              (omega ^ 2 + omega + c1)) by (unfold c1, c3; ring).
    rewrite hexpand, homega, Cmult_0_r.
    ring. }
  assert (hproduct : r0 * r1 * r2 = u ^ 3 + v ^ 3).
  { unfold r0, r1, r2.
    assert (hexpand :
        (u + v) * (omega * u + omega ^ 2 * v) *
          (omega ^ 2 * u + omega * v) =
        u ^ 3 + v ^ 3 +
          ((v * u ^ 2 + v ^ 2 * u) * omega ^ 2 +
            (u ^ 3 + v ^ 3) * omega - (u ^ 3 + v ^ 3)) *
              (omega ^ 2 + omega + c1)) by (unfold c1; ring).
    rewrite hexpand, homega, Cmult_0_r.
    ring. }
  assert (hpoly :
      (y - r0) * (y - r1) * (y - r2) =
      y ^ 3 - (r0 + r1 + r2) * y ^ 2 +
        (r0 * r1 + r0 * r2 + r1 * r2) * y - r0 * r1 * r2) by ring.
  rewrite hpoly, hsum, hpairs, hproduct.
  unfold depressed_cubic, c0 in *.
  rewrite huv, hu.
  ring.
Qed.

(** The arbitrary cubic factors into Cardano's three translated values. *)
Theorem cubic_factorization (a b c d s u v omega x : C) (ha : a <> c0)
    (hu : u ^ 3 = -cubic_q (b / a) (c / a) (d / a) / c2 + s)
    (hv : v ^ 3 = -cubic_q (b / a) (c / a) (d / a) / c2 - s)
    (huv : u * v = -cubic_p (b / a) (c / a) / c3)
    (homega : omega ^ 2 + omega + c1 = c0) :
  cubic a b c d x =
    a * ((x - (u + v - (b / a) / c3)) *
      (x - (omega * u + omega ^ 2 * v - (b / a) / c3)) *
      (x - (omega ^ 2 * u + omega * v - (b / a) / c3))).
Proof.
  rewrite (cubic_normalization a b c d x ha).
  rewrite translate_monic_cubic.
  assert (hsum : u ^ 3 + v ^ 3 = -cubic_q (b / a) (c / a) (d / a)).
  { rewrite hu, hv; unfold c2; field; exact c2_neq_0. }
  assert (hcompat : c3 * u * v = -cubic_p (b / a) (c / a)).
  { replace (c3 * u * v) with (c3 * (u * v)) by ring.
    rewrite huv; unfold c3; field; exact c3_neq_0. }
  rewrite (cardano_factorization _ _ u v omega _ hsum hcompat homega).
  ring.
Qed.

(** Every value returned by the complex Cardano solver is a root. *)
Theorem solve_cubic_correct (a b c d s u v omega : C) (ha : a <> c0)
    (hs : s ^ 2 = cubic_delta (cubic_p (b / a) (c / a))
      (cubic_q (b / a) (c / a) (d / a)))
    (hu : u ^ 3 = -cubic_q (b / a) (c / a) (d / a) / c2 + s)
    (hv : v ^ 3 = -cubic_q (b / a) (c / a) (d / a) / c2 - s)
    (huv : u * v = -cubic_p (b / a) (c / a) / c3)
    (homega : omega ^ 2 + omega + c1 = c0) :
  let roots := solve_cubic a b c d u v omega in
  cubic a b c d (fst roots) = c0 /\
  cubic a b c d (fst (snd roots)) = c0 /\
  cubic a b c d (snd (snd roots)) = c0.
Proof.
  clear hs.
  unfold solve_cubic; cbn.
  repeat split;
    rewrite (cubic_factorization a b c d s u v omega _ ha hu hv huv homega);
    unfold c0;
    ring.
Qed.

(** Every complex root occurs in the three-entry Cardano collection. *)
Theorem solve_cubic_exhaustive (a b c d s u v omega x : C) (ha : a <> c0)
    (hu : u ^ 3 = -cubic_q (b / a) (c / a) (d / a) / c2 + s)
    (hv : v ^ 3 = -cubic_q (b / a) (c / a) (d / a) / c2 - s)
    (huv : u * v = -cubic_p (b / a) (c / a) / c3)
    (homega : omega ^ 2 + omega + c1 = c0)
    (hx : cubic a b c d x = c0) :
  let roots := solve_cubic a b c d u v omega in
  x = fst roots \/ x = fst (snd roots) \/ x = snd (snd roots).
Proof.
  rewrite (cubic_factorization a b c d s u v omega x
    ha hu hv huv homega) in hx.
  apply Cmult_eq_zero in hx as [ha0 | hroots]; [contradiction |].
  apply Cmult3_eq_zero in hroots as [h0 | [h1 | h2]].
  - cbn [solve_cubic]; left; now apply Cminus_eq_zero.
  - cbn [solve_cubic]; right; left; now apply Cminus_eq_zero.
  - cbn [solve_cubic]; right; right; now apply Cminus_eq_zero.
Qed.

(** The complex Cardano collection contains exactly all cubic roots. *)
Theorem cubic_eq_zero_iff (a b c d s u v omega x : C) (ha : a <> c0)
    (hs : s ^ 2 = cubic_delta (cubic_p (b / a) (c / a))
      (cubic_q (b / a) (c / a) (d / a)))
    (hu : u ^ 3 = -cubic_q (b / a) (c / a) (d / a) / c2 + s)
    (hv : v ^ 3 = -cubic_q (b / a) (c / a) (d / a) / c2 - s)
    (huv : u * v = -cubic_p (b / a) (c / a) / c3)
    (homega : omega ^ 2 + omega + c1 = c0) :
  cubic a b c d x = c0 <->
  let roots := solve_cubic a b c d u v omega in
  x = fst roots \/ x = fst (snd roots) \/ x = snd (snd roots).
Proof.
  split.
  - intro hx.
    exact (solve_cubic_exhaustive a b c d s u v omega x
      ha hu hv huv homega hx).
  - unfold solve_cubic; cbn.
    intros [-> | [-> | ->]].
    all: apply (solve_cubic_correct a b c d s u v omega
      ha hs hu hv huv homega).
Qed.

End PolynomialFormulasCubicComplex.
End LeanProofs.
