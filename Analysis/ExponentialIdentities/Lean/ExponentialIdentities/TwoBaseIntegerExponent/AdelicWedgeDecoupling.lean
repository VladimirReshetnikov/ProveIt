import ExponentialIdentities.TwoBaseIntegerExponent.FermatQuotientDeterminant

/-!
# Control-direction invariance of the Fermat-quotient wedge

The mod-`p` shadow of the finite-place wedge attached to a pair `(M, A)` is the
Fermat-quotient determinant `Δ_p(M,A) = q_p(M) q_p(3) - q_p(A) q_p(2)`.  The
companion module proves that it vanishes on the integer controls `(2^n, 3^n)`.

This module proves the *decoupling* identity behind the adelic no-go: the wedge is
invariant under multiplying `(M, A)` by an arbitrary control `(2^a, 3^a)`, hence
`Δ_p(2^a b, 3^a c) = Δ_p(b, c)` for every `a` and every pair `(b, c)` prime to `p`.

Consequences recorded here:

* `fermatQuotientResidue_mul` — the Fermat quotient is additive mod `p`;
* `fermatQuotientDeterminant_control_shift` — the wedge only sees the pair modulo the
  control direction, so *any* prescribed value of the wedge at `p` is realised inside
  every residue class `(2^a b, 3^a c)`;
* `fermatQuotientDeterminant_eq_zero_iff_line` — rank drop at `p` says exactly that
  `(q_p M, q_p A)` lies on the line spanned by `(q_p 2, q_p 3)`, i.e. that the pair is a
  control up to a Fermat-quotient-trivial twist.
-/

namespace LeanProofs.TwoBaseIntegerExponent

/-- Exact multiplicativity of the natural Fermat quotient over `ℕ`. -/
theorem fermatQuotientNat_mul {p u v : ℕ}
    (hp : p.Prime) (hpu : ¬p ∣ u) (hpv : ¬p ∣ v) :
    fermatQuotientNat p (u * v) =
      fermatQuotientNat p u + fermatQuotientNat p v +
        p * (fermatQuotientNat p u * fermatQuotientNat p v) := by
  have hpuv : ¬p ∣ u * v := by
    intro h
    rcases (Nat.Prime.dvd_mul hp).1 h with h' | h'
    · exact hpu h'
    · exact hpv h'
  have hu := pow_eq_one_add_mul_fermatQuotientNat hp hpu
  have hv := pow_eq_one_add_mul_fermatQuotientNat hp hpv
  have huv := pow_eq_one_add_mul_fermatQuotientNat hp hpuv
  set qu := fermatQuotientNat p u
  set qv := fermatQuotientNat p v
  set quv := fermatQuotientNat p (u * v)
  have hsplit : (u * v) ^ (p - 1) = u ^ (p - 1) * v ^ (p - 1) := mul_pow u v (p - 1)
  have key : 1 + p * quv = 1 + p * (qu + qv + p * (qu * qv)) := by
    calc 1 + p * quv = (u * v) ^ (p - 1) := huv.symm
      _ = u ^ (p - 1) * v ^ (p - 1) := hsplit
      _ = (1 + p * qu) * (1 + p * qv) := by rw [hu, hv]
      _ = 1 + p * (qu + qv + p * (qu * qv)) := by ring
  have := Nat.add_left_cancel key
  exact Nat.eq_of_mul_eq_mul_left hp.pos this

/-- The Fermat quotient is a homomorphism to `ZMod p`. -/
theorem fermatQuotientResidue_mul {p u v : ℕ}
    (hp : p.Prime) (hpu : ¬p ∣ u) (hpv : ¬p ∣ v) :
    fermatQuotientResidue p (u * v) =
      fermatQuotientResidue p u + fermatQuotientResidue p v := by
  have h := fermatQuotientNat_mul hp hpu hpv
  have hcast : ((fermatQuotientNat p (u * v) : ℕ) : ZMod p) =
      ((fermatQuotientNat p u + fermatQuotientNat p v +
        p * (fermatQuotientNat p u * fermatQuotientNat p v) : ℕ) : ZMod p) := by
    exact_mod_cast congrArg (fun n : ℕ => (n : ZMod p)) h
  simp only [fermatQuotientResidue]
  rw [hcast]
  push_cast
  simp

private theorem not_dvd_two {p : ℕ} (hp5 : 5 ≤ p) : ¬p ∣ 2 := by
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  omega

private theorem not_dvd_three {p : ℕ} (hp5 : 5 ≤ p) : ¬p ∣ 3 := by
  intro h
  have := Nat.le_of_dvd (by norm_num) h
  omega

/-- **Control-direction invariance.**  Multiplying `(M, A)` by the control `(2^a, 3^a)`
does not change the Fermat-quotient wedge.  Consequently the wedge at `p` carries no
information about the archimedean alignment of the pair: every value in `ZMod p` is
attained on the control orbit of a suitable `(b, c)`. -/
theorem fermatQuotientDeterminant_control_shift {p a b c : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpb : ¬p ∣ b) (hpc : ¬p ∣ c) :
    fermatQuotientDeterminant p (2 ^ a * b) (3 ^ a * c) =
      fermatQuotientDeterminant p b c := by
  have h2 : ¬p ∣ 2 := not_dvd_two hp5
  have h3 : ¬p ∣ 3 := not_dvd_three hp5
  have h2a : ¬p ∣ 2 ^ a := fun h => h2 (hp.dvd_of_dvd_pow h)
  have h3a : ¬p ∣ 3 ^ a := fun h => h3 (hp.dvd_of_dvd_pow h)
  simp only [fermatQuotientDeterminant]
  rw [fermatQuotientResidue_mul hp h2a hpb, fermatQuotientResidue_mul hp h3a hpc,
    fermatQuotientResidue_pow hp h2, fermatQuotientResidue_pow hp h3]
  ring

/-- Rank drop at `p` is exactly the statement that `(q_p M, q_p A)` is proportional to the
control direction `(q_p 2, q_p 3)`, in the concrete form used by the wedge analysis. -/
theorem fermatQuotientDeterminant_eq_zero_iff_line {p M A : ℕ} :
    fermatQuotientDeterminant p M A = 0 ↔
      fermatQuotientResidue p M * fermatQuotientResidue p 3 =
        fermatQuotientResidue p A * fermatQuotientResidue p 2 := by
  simp [fermatQuotientDeterminant, sub_eq_zero]

/-- Explicit witness for total rank collapse away from the controls: the pair
`(2 ^ a * b, 3 ^ a * c)` has vanishing wedge at `p` as soon as `(b, c)` does, for every
`a` — in particular for `b = c = 1`, where the wedge vanishes for all `p`, while the
integers `2 ^ a * b`, `3 ^ a * c` may be adjusted freely inside their residue classes. -/
theorem fermatQuotientDeterminant_control_shift_zero {p a b c : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpb : ¬p ∣ b) (hpc : ¬p ∣ c)
    (h : fermatQuotientDeterminant p b c = 0) :
    fermatQuotientDeterminant p (2 ^ a * b) (3 ^ a * c) = 0 := by
  rw [fermatQuotientDeterminant_control_shift hp hp5 hpb hpc]
  exact h

end LeanProofs.TwoBaseIntegerExponent
