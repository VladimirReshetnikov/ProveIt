From Stdlib Require Import Reals Ring Field Psatz.
From PolynomialFormulas Require Import Basic Cubic.

Open Scope R_scope.

(** Algebraic verification of Ferrari's quartic formula. *)

Module LeanProofs.
Module PolynomialFormulasQuartic.

Import LeanProofs.PolynomialFormulas.

Definition quartic (a b c d e x : R) : R :=
  a * x ^ 4 + b * x ^ 3 + c * x ^ 2 + d * x + e.

Definition monic_quartic (A B C D x : R) : R :=
  x ^ 4 + A * x ^ 3 + B * x ^ 2 + C * x + D.

Definition depressed_quartic (p q r y : R) : R := y ^ 4 + p * y ^ 2 + q * y + r.

Definition quartic_p (A B : R) : R := B - 6 * (A / 4) ^ 2.

Definition quartic_q (A B C : R) : R := C - 2 * B * (A / 4) + 8 * (A / 4) ^ 3.

Definition quartic_r (A B C D : R) : R :=
  D - C * (A / 4) + B * (A / 4) ^ 2 - 3 * (A / 4) ^ 4.

Definition ferrari_resolvent (p q r m : R) : R :=
  q ^ 2 - 4 * (2 * m - p) * (m ^ 2 - r).

Definition solve_depressed_quartic (m s t rho sigma : R) :
    R * (R * (R * R)) :=
  ((s + rho) / 2,
   ((s - rho) / 2,
    ((-s + sigma) / 2, (-s - sigma) / 2))).

Definition solve_quartic (a b c d e m s t rho sigma : R) :
    R * (R * (R * R)) :=
  ((s + rho) / 2 - (b / a) / 4,
   ((s - rho) / 2 - (b / a) / 4,
    ((-s + sigma) / 2 - (b / a) / 4,
     (-s - sigma) / 2 - (b / a) / 4))).

Theorem quartic_normalization (a b c d e x : R) (ha : a <> 0) :
  quartic a b c d e x =
    a * monic_quartic (b / a) (c / a) (d / a) (e / a) x.
Proof.
  set (A := b / a).
  set (B := c / a).
  set (C := d / a).
  set (D := e / a).
  assert (hA : a * A = b) by (unfold A; field; exact ha).
  assert (hB : a * B = c) by (unfold B; field; exact ha).
  assert (hC : a * C = d) by (unfold C; field; exact ha).
  assert (hD : a * D = e) by (unfold D; field; exact ha).
  unfold quartic, monic_quartic.
  assert (hexpand : a * (x ^ 4 + A * x ^ 3 + B * x ^ 2 + C * x + D) =
      a * x ^ 4 + (a * A) * x ^ 3 + (a * B) * x ^ 2 +
        (a * C) * x + a * D) by ring.
  rewrite hexpand, hA, hB, hC, hD.
  ring.
Qed.

Theorem depress_monic_quartic (A B C D y : R) :
  monic_quartic A B C D (y - A / 4) =
    depressed_quartic (quartic_p A B) (quartic_q A B C) (quartic_r A B C D) y.
Proof.
  unfold monic_quartic, depressed_quartic, quartic_p, quartic_q, quartic_r.
  set (h := A / 4).
  assert (hA : A = 4 * h) by (unfold h; field).
  rewrite hA.
  ring.
Qed.

Theorem ferrari_factorization (p q r m s t y : R)
    (hs : s ^ 2 = 2 * m - p) (hst : 2 * s * t = -q)
    (ht : t ^ 2 = m ^ 2 - r) :
  depressed_quartic p q r y =
    (y ^ 2 - s * y + (m - t)) * (y ^ 2 + s * y + (m + t)).
Proof.
  unfold depressed_quartic.
  assert (hexpand :
      (y ^ 2 - s * y + (m - t)) * (y ^ 2 + s * y + (m + t)) =
      y ^ 4 + (2 * m - s ^ 2) * y ^ 2 - (2 * s * t) * y +
        (m ^ 2 - t ^ 2)) by ring.
  rewrite hexpand, hs, hst, ht.
  ring.
Qed.

Theorem ferrari_parameters_of_resolvent (p q r m s : R)
    (hres : ferrari_resolvent p q r m = 0)
    (hs : s ^ 2 = 2 * m - p) (hs0 : s <> 0) :
  2 * s * (-q / (2 * s)) = -q /\
  (-q / (2 * s)) ^ 2 = m ^ 2 - r.
Proof.
  split.
  - field; exact hs0.
  - set (t := -q / (2 * s)).
    assert (hlin : 2 * s * t = -q) by (unfold t; field; exact hs0).
    assert (hlinsq : (2 * s * t) ^ 2 = (-q) ^ 2) by now rewrite hlin.
    assert (hq : q ^ 2 = 4 * s ^ 2 * (m ^ 2 - r)).
    { unfold ferrari_resolvent in hres.
      assert (hmul : 4 * (2 * m - p) * (m ^ 2 - r) =
          4 * s ^ 2 * (m ^ 2 - r)) by (rewrite hs; ring).
      nra. }
    assert (hs2 : s ^ 2 <> 0) by (apply pow_nonzero; exact hs0).
    apply (Rmult_eq_reg_l (4 * s ^ 2)); [nra | nra].
Qed.

Lemma ferrari_first_plus (m s t rho : R)
    (hrho : rho ^ 2 = s ^ 2 - 4 * (m - t)) :
  ((s + rho) / 2) ^ 2 - s * ((s + rho) / 2) + (m - t) = 0.
Proof.
  set (y := (s + rho) / 2).
  assert (hy : 2 * y = s + rho) by (unfold y; field).
  assert (hysq : (2 * y) ^ 2 = (s + rho) ^ 2) by now rewrite hy.
  nra.
Qed.

Lemma ferrari_first_minus (m s t rho : R)
    (hrho : rho ^ 2 = s ^ 2 - 4 * (m - t)) :
  ((s - rho) / 2) ^ 2 - s * ((s - rho) / 2) + (m - t) = 0.
Proof.
  set (y := (s - rho) / 2).
  assert (hy : 2 * y = s - rho) by (unfold y; field).
  assert (hysq : (2 * y) ^ 2 = (s - rho) ^ 2) by now rewrite hy.
  nra.
Qed.

Lemma ferrari_second_plus (m s t sigma : R)
    (hsigma : sigma ^ 2 = s ^ 2 - 4 * (m + t)) :
  ((-s + sigma) / 2) ^ 2 + s * ((-s + sigma) / 2) + (m + t) = 0.
Proof.
  set (y := (-s + sigma) / 2).
  assert (hy : 2 * y = -s + sigma) by (unfold y; field).
  assert (hysq : (2 * y) ^ 2 = (-s + sigma) ^ 2) by now rewrite hy.
  nra.
Qed.

Lemma ferrari_second_minus (m s t sigma : R)
    (hsigma : sigma ^ 2 = s ^ 2 - 4 * (m + t)) :
  ((-s - sigma) / 2) ^ 2 + s * ((-s - sigma) / 2) + (m + t) = 0.
Proof.
  set (y := (-s - sigma) / 2).
  assert (hy : 2 * y = -s - sigma) by (unfold y; field).
  assert (hysq : (2 * y) ^ 2 = (-s - sigma) ^ 2) by now rewrite hy.
  nra.
Qed.

Theorem solve_depressed_quartic_correct (p q r m s t rho sigma : R)
    (hs : s ^ 2 = 2 * m - p) (hst : 2 * s * t = -q)
    (ht : t ^ 2 = m ^ 2 - r)
    (hrho : rho ^ 2 = s ^ 2 - 4 * (m - t))
    (hsigma : sigma ^ 2 = s ^ 2 - 4 * (m + t)) :
  let roots := solve_depressed_quartic m s t rho sigma in
  depressed_quartic p q r (fst roots) = 0 /\
  depressed_quartic p q r (fst (snd roots)) = 0 /\
  depressed_quartic p q r (fst (snd (snd roots))) = 0 /\
  depressed_quartic p q r (snd (snd (snd roots))) = 0.
Proof.
  cbn [solve_depressed_quartic].
  repeat split.
  - change (depressed_quartic p q r ((s + rho) / 2) = 0).
    rewrite (ferrari_factorization p q r m s t _ hs hst ht).
    rewrite (ferrari_first_plus m s t rho hrho); ring.
  - change (depressed_quartic p q r ((s - rho) / 2) = 0).
    rewrite (ferrari_factorization p q r m s t _ hs hst ht).
    rewrite (ferrari_first_minus m s t rho hrho); ring.
  - change (depressed_quartic p q r ((-s + sigma) / 2) = 0).
    rewrite (ferrari_factorization p q r m s t _ hs hst ht).
    rewrite (ferrari_second_plus m s t sigma hsigma); ring.
  - change (depressed_quartic p q r ((-s - sigma) / 2) = 0).
    rewrite (ferrari_factorization p q r m s t _ hs hst ht).
    rewrite (ferrari_second_minus m s t sigma hsigma); ring.
Qed.

Theorem solve_quartic_correct (a b c d e m s t rho sigma : R) (ha : a <> 0)
    (hs : s ^ 2 = 2 * m - quartic_p (b / a) (c / a))
    (hst : 2 * s * t = -quartic_q (b / a) (c / a) (d / a))
    (ht : t ^ 2 = m ^ 2 - quartic_r (b / a) (c / a) (d / a) (e / a))
    (hrho : rho ^ 2 = s ^ 2 - 4 * (m - t))
    (hsigma : sigma ^ 2 = s ^ 2 - 4 * (m + t)) :
  let roots := solve_quartic a b c d e m s t rho sigma in
  quartic a b c d e (fst roots) = 0 /\
  quartic a b c d e (fst (snd roots)) = 0 /\
  quartic a b c d e (fst (snd (snd roots))) = 0 /\
  quartic a b c d e (snd (snd (snd roots))) = 0.
Proof.
  unfold solve_quartic.
  cbn.
  pose proof (solve_depressed_quartic_correct
    (quartic_p (b / a) (c / a))
    (quartic_q (b / a) (c / a) (d / a))
    (quartic_r (b / a) (c / a) (d / a) (e / a))
    m s t rho sigma hs hst ht hrho hsigma) as hroots.
  unfold solve_depressed_quartic in hroots.
  cbn in hroots.
  destruct hroots as [h0 [h1 [h2 h3]]].
  unfold solve_depressed_quartic in h0, h1, h2, h3.
  cbn in h0, h1, h2, h3.
  repeat split.
  - change (quartic a b c d e ((s + rho) / 2 - (b / a) / 4) = 0).
    rewrite (quartic_normalization a b c d e _ ha), depress_monic_quartic, h0; ring.
  - change (quartic a b c d e ((s - rho) / 2 - (b / a) / 4) = 0).
    rewrite (quartic_normalization a b c d e _ ha), depress_monic_quartic, h1; ring.
  - change (quartic a b c d e ((-s + sigma) / 2 - (b / a) / 4) = 0).
    rewrite (quartic_normalization a b c d e _ ha), depress_monic_quartic, h2; ring.
  - change (quartic a b c d e ((-s - sigma) / 2 - (b / a) / 4) = 0).
    rewrite (quartic_normalization a b c d e _ ha), depress_monic_quartic, h3; ring.
Qed.

(** Every root of the depressed quartic occurs in the four-entry Ferrari
    collection. *)
Theorem solve_depressed_quartic_exhaustive
    (p q r m s t rho sigma y : R)
    (hs : s ^ 2 = 2 * m - p) (hst : 2 * s * t = -q)
    (ht : t ^ 2 = m ^ 2 - r)
    (hrho : rho ^ 2 = s ^ 2 - 4 * (m - t))
    (hsigma : sigma ^ 2 = s ^ 2 - 4 * (m + t))
    (hy : depressed_quartic p q r y = 0) :
  let roots := solve_depressed_quartic m s t rho sigma in
  y = fst roots \/ y = fst (snd roots) \/
  y = fst (snd (snd roots)) \/ y = snd (snd (snd roots)).
Proof.
  rewrite (ferrari_factorization p q r m s t y hs hst ht) in hy.
  apply Rmult_integral in hy as [hfirst | hsecond].
  - assert (hquadratic : quadratic 1 (-s) (m - t) y = 0).
    { unfold quadratic; nra. }
    assert (hdisc : rho ^ 2 = (-s) ^ 2 - 4 * 1 * (m - t)) by nra.
    apply (proj1 (quadratic_eq_zero_iff 1 (-s) (m - t) rho y
      R1_neq_R0 hdisc)) in hquadratic.
    cbn [solve_depressed_quartic].
    destruct hquadratic as [h | h].
    + left; change (y = (s + rho) / 2); nra.
    + right; left; change (y = (s - rho) / 2); nra.
  - assert (hquadratic : quadratic 1 s (m + t) y = 0).
    { unfold quadratic; nra. }
    assert (hdisc : sigma ^ 2 = s ^ 2 - 4 * 1 * (m + t)) by nra.
    apply (proj1 (quadratic_eq_zero_iff 1 s (m + t) sigma y
      R1_neq_R0 hdisc)) in hquadratic.
    cbn [solve_depressed_quartic].
    destruct hquadratic as [h | h].
    + right; right; left; change (y = (-s + sigma) / 2); nra.
    + right; right; right; change (y = (-s - sigma) / 2); nra.
Qed.

(** Every real root of the input quartic occurs in [solve_quartic]. *)
Theorem solve_quartic_exhaustive
    (a b c d e m s t rho sigma x : R) (ha : a <> 0)
    (hs : s ^ 2 = 2 * m - quartic_p (b / a) (c / a))
    (hst : 2 * s * t = -quartic_q (b / a) (c / a) (d / a))
    (ht : t ^ 2 = m ^ 2 - quartic_r (b / a) (c / a) (d / a) (e / a))
    (hrho : rho ^ 2 = s ^ 2 - 4 * (m - t))
    (hsigma : sigma ^ 2 = s ^ 2 - 4 * (m + t))
    (hx : quartic a b c d e x = 0) :
  let roots := solve_quartic a b c d e m s t rho sigma in
  x = fst roots \/ x = fst (snd roots) \/
  x = fst (snd (snd roots)) \/ x = snd (snd (snd roots)).
Proof.
  assert (hmonic : monic_quartic (b / a) (c / a) (d / a) (e / a) x = 0).
  { rewrite (quartic_normalization a b c d e x ha) in hx.
    apply Rmult_integral in hx as [ha0 | hmonic]; [contradiction | exact hmonic]. }
  set (y := x + (b / a) / 4).
  assert (hdepressed :
      depressed_quartic (quartic_p (b / a) (c / a))
        (quartic_q (b / a) (c / a) (d / a))
        (quartic_r (b / a) (c / a) (d / a) (e / a)) y = 0).
  { rewrite <- depress_monic_quartic.
    replace (y - b / a / 4) with x by (unfold y; field; exact ha).
    exact hmonic. }
  pose proof (solve_depressed_quartic_exhaustive
    (quartic_p (b / a) (c / a))
    (quartic_q (b / a) (c / a) (d / a))
    (quartic_r (b / a) (c / a) (d / a) (e / a))
    m s t rho sigma y hs hst ht hrho hsigma hdepressed) as hroots.
  unfold solve_depressed_quartic in hroots.
  cbn in hroots.
  unfold solve_quartic.
  cbn.
  destruct hroots as [h | [h | [h | h]]].
  - left; rewrite <- h; unfold y; ring.
  - right; left; rewrite <- h; unfold y; ring.
  - right; right; left; rewrite <- h; unfold y; ring.
  - right; right; right; rewrite <- h; unfold y; ring.
Qed.

(** The Ferrari collection contains exactly all real roots of the quartic. *)
Theorem quartic_eq_zero_iff (a b c d e m s t rho sigma x : R) (ha : a <> 0)
    (hs : s ^ 2 = 2 * m - quartic_p (b / a) (c / a))
    (hst : 2 * s * t = -quartic_q (b / a) (c / a) (d / a))
    (ht : t ^ 2 = m ^ 2 - quartic_r (b / a) (c / a) (d / a) (e / a))
    (hrho : rho ^ 2 = s ^ 2 - 4 * (m - t))
    (hsigma : sigma ^ 2 = s ^ 2 - 4 * (m + t)) :
  quartic a b c d e x = 0 <->
  let roots := solve_quartic a b c d e m s t rho sigma in
  x = fst roots \/ x = fst (snd roots) \/
  x = fst (snd (snd roots)) \/ x = snd (snd (snd roots)).
Proof.
  split.
  - apply solve_quartic_exhaustive; assumption.
  - cbn [solve_quartic].
    intros [-> | [-> | [-> | ->]]].
    all: apply (solve_quartic_correct a b c d e m s t rho sigma
      ha hs hst ht hrho hsigma).
Qed.

End PolynomialFormulasQuartic.
End LeanProofs.
