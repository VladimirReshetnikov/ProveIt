From Stdlib Require Import Reals Ring Field Psatz.
From PolynomialFormulas Require Import Basic.

Open Scope R_scope.

(** Algebraic verification of Cardano's formula. *)

Module LeanProofs.
Module PolynomialFormulasCubic.

Definition cubic (a b c d x : R) : R :=
  a * x ^ 3 + b * x ^ 2 + c * x + d.

Definition monic_cubic (A B C x : R) : R :=
  x ^ 3 + A * x ^ 2 + B * x + C.

Definition depressed_cubic (p q y : R) : R := y ^ 3 + p * y + q.

Definition cubic_p (A B : R) : R := B - 3 * (A / 3) ^ 2.

Definition cubic_q (A B C : R) : R := C - B * (A / 3) + 2 * (A / 3) ^ 3.

Definition cubic_delta (p q : R) : R := (q / 2) ^ 2 + (p / 3) ^ 3.

Definition solve_cubic (a b c d u v omega : R) : R * (R * R) :=
  (u + v - (b / a) / 3,
   (omega * u + omega ^ 2 * v - (b / a) / 3,
    omega ^ 2 * u + omega * v - (b / a) / 3)).

Theorem depress_monic_cubic (A B C y : R) :
  monic_cubic A B C (y - A / 3) =
    depressed_cubic (cubic_p A B) (cubic_q A B C) y.
Proof.
  unfold monic_cubic, depressed_cubic, cubic_p, cubic_q.
  set (t := A / 3).
  assert (ht : A = 3 * t) by (unfold t; field).
  rewrite ht.
  ring.
Qed.

Theorem cardano_depressed (p q u v : R)
    (hu : u ^ 3 + v ^ 3 = -q) (huv : u * v = -p / 3) :
  depressed_cubic p q (u + v) = 0.
Proof.
  unfold depressed_cubic.
  assert (huv3 : 3 * u * v = -p) by nra.
  assert (hexpand : (u + v) ^ 3 + p * (u + v) + q =
      (u ^ 3 + v ^ 3) + (3 * u * v + p) * (u + v) + q) by ring.
  rewrite hexpand.
  rewrite hu, huv3.
  ring.
Qed.

Theorem cardano_radical_pair (p q s u v : R)
    (hu : u ^ 3 = -q / 2 + s) (hv : v ^ 3 = -q / 2 - s)
    (huv : u * v = -p / 3) :
  depressed_cubic p q (u + v) = 0.
Proof.
  apply cardano_depressed; [nra | exact huv].
Qed.

Theorem cardano_discriminant_equation (p q s : R)
    (hs : s ^ 2 = cubic_delta p q) :
  (-q / 2 + s) * (-q / 2 - s) = -(p / 3) ^ 3.
Proof.
  unfold cubic_delta in hs.
  nra.
Qed.

Theorem cubic_normalization (a b c d x : R) (ha : a <> 0) :
  cubic a b c d x = a * monic_cubic (b / a) (c / a) (d / a) x.
Proof.
  set (A := b / a).
  set (B := c / a).
  set (C := d / a).
  assert (hA : a * A = b) by (unfold A; field; exact ha).
  assert (hB : a * B = c) by (unfold B; field; exact ha).
  assert (hC : a * C = d) by (unfold C; field; exact ha).
  unfold cubic, monic_cubic.
  assert (hexpand : a * (x ^ 3 + A * x ^ 2 + B * x + C) =
      a * x ^ 3 + (a * A) * x ^ 2 + (a * B) * x + a * C) by ring.
  rewrite hexpand, hA, hB, hC.
  ring.
Qed.

Theorem cardano_formula (a b c d s u v : R) (ha : a <> 0)
    (hs : s ^ 2 = cubic_delta (cubic_p (b / a) (c / a))
      (cubic_q (b / a) (c / a) (d / a)))
    (hu : u ^ 3 = -cubic_q (b / a) (c / a) (d / a) / 2 + s)
    (hv : v ^ 3 = -cubic_q (b / a) (c / a) (d / a) / 2 - s)
    (huv : u * v = -cubic_p (b / a) (c / a) / 3) :
  cubic a b c d (u + v - (b / a) / 3) = 0.
Proof.
  rewrite (cubic_normalization a b c d _ ha).
  rewrite depress_monic_cubic.
  rewrite (cardano_radical_pair _ _ s u v hu hv huv).
  ring.
Qed.

Theorem solve_cubic_correct (a b c d s u v omega : R) (ha : a <> 0)
    (hs : s ^ 2 = cubic_delta (cubic_p (b / a) (c / a))
      (cubic_q (b / a) (c / a) (d / a)))
    (hu : u ^ 3 = -cubic_q (b / a) (c / a) (d / a) / 2 + s)
    (hv : v ^ 3 = -cubic_q (b / a) (c / a) (d / a) / 2 - s)
    (huv : u * v = -cubic_p (b / a) (c / a) / 3)
    (homega : omega ^ 3 = 1) :
  let roots := solve_cubic a b c d u v omega in
  cubic a b c d (fst roots) = 0 /\
  cubic a b c d (fst (snd roots)) = 0 /\
  cubic a b c d (snd (snd roots)) = 0.
Proof.
  cbn [solve_cubic].
  assert (homega2 : (omega ^ 2) ^ 3 = 1).
  { assert (h : (omega ^ 2) ^ 3 = (omega ^ 3) ^ 2) by ring.
    rewrite h, homega; ring. }
  assert (hu1 : (omega * u) ^ 3 =
      -cubic_q (b / a) (c / a) (d / a) / 2 + s).
  { assert (h : (omega * u) ^ 3 = omega ^ 3 * u ^ 3) by ring.
    rewrite h, homega, hu; ring. }
  assert (hv1 : (omega ^ 2 * v) ^ 3 =
      -cubic_q (b / a) (c / a) (d / a) / 2 - s).
  { assert (h : (omega ^ 2 * v) ^ 3 = (omega ^ 2) ^ 3 * v ^ 3) by ring.
    rewrite h, homega2, hv; ring. }
  assert (huv1 : (omega * u) * (omega ^ 2 * v) =
      -cubic_p (b / a) (c / a) / 3).
  { assert (h : (omega * u) * (omega ^ 2 * v) =
        omega ^ 3 * (u * v)) by ring.
    rewrite h, homega, huv; ring. }
  assert (hu2 : (omega ^ 2 * u) ^ 3 =
      -cubic_q (b / a) (c / a) (d / a) / 2 + s).
  { assert (h : (omega ^ 2 * u) ^ 3 = (omega ^ 2) ^ 3 * u ^ 3) by ring.
    rewrite h, homega2, hu; ring. }
  assert (hv2 : (omega * v) ^ 3 =
      -cubic_q (b / a) (c / a) (d / a) / 2 - s).
  { assert (h : (omega * v) ^ 3 = omega ^ 3 * v ^ 3) by ring.
    rewrite h, homega, hv; ring. }
  assert (huv2 : (omega ^ 2 * u) * (omega * v) =
      -cubic_p (b / a) (c / a) / 3).
  { assert (h : (omega ^ 2 * u) * (omega * v) =
        omega ^ 3 * (u * v)) by ring.
    rewrite h, homega, huv; ring. }
  repeat split.
  - exact (cardano_formula a b c d s u v ha hs hu hv huv).
  - exact (cardano_formula a b c d s (omega * u) (omega ^ 2 * v)
      ha hs hu1 hv1 huv1).
  - exact (cardano_formula a b c d s (omega ^ 2 * u) (omega * v)
      ha hs hu2 hv2 huv2).
Qed.

End PolynomialFormulasCubic.
End LeanProofs.
