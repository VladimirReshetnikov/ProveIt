import IPRADerivations.DiophantineNumberTheory.ConicIdentities
import IPRADerivations.Analysis.Polynomials.Taylor.PolynomialRemainder
import IPRADerivations.Core.Header

/-!
# The upper height bound of the conic parametrization

Packet: `diophantine-number-theory/diophantine_geometry_ipra`, Theorem `thm:conic-height`, the upper inequality
`Ht(Φ(T)) ≤ A Ht(T)²` with `A = 3CP`: "Take a primitive integer pair `(s, t)` representing `T`, and put
`S = max(|s|, |t|)` ... `|R(s, t)| ≤ C S²`, `|ℓ| + |m| ≤ 2CP`, `|L(s, t)| ≤ 2CPS`. The coordinates of `MF` are
`−p_0 R`, `−p_1 R + s L`, `−p_2 R + t L`. Their absolute values are at most `3CPS² = AS²`. Primitive normalization
cannot increase that maximum."

With `|a_{ij}| ≤ c_{ij}`, `C = ∑ c_{ij}`, `|p_i| ≤ P`, `|s|, |t| ≤ S` (`Analysis/PolynomialRemainder.AbsLe`):

* `abs_nat`, `abs_neg`: `|b| ≤ b` and `|−u| = |u|`;
* `R_bound`, `ell_bound`, `emm_bound`, `L_bound`: the bounds of the forms;
* `height_upper`: every coordinate of `M F(s, t)` has absolute value at most `3 C P S²`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.ConicHeight

open_ipra
open LeanProofs.IPRA.DiophantineNumberTheory.ConicIdentities (Form)
open LeanProofs.IPRA.Analysis.PolynomialRemainder (AbsLe abs_hi abs_lo abs_of abs_mono abs_add abs_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem abs_nat (b : PTm n) : Γ ⊢[PRAAx] AbsLe (ZT.ofNat b) b :=
  abs_of (by show Γ ⊢[PRAAx] le (b + zero) (b + zero); ipra_le 0)
    (by show Γ ⊢[PRAAx] le (zero + zero) (b + b); ipra_le 𝔞 b + 𝔞 b)

theorem abs_neg {u : ZT n} {b : PTm n} (h : Γ ⊢[PRAAx] AbsLe u b) : Γ ⊢[PRAAx] AbsLe (-u) b := by
  have h₁ := abs_hi h; have h₂ := abs_lo h
  exact abs_of (by show Γ ⊢[PRAAx] le (u.neg + zero) (b + u.pos); ipra_le sl h₂)
    (by show Γ ⊢[PRAAx] le (zero + u.pos) (u.neg + b); ipra_le sl h₁)

section Bounds

variable (Q : Form n) {c00 c01 c02 c11 c12 c22 P S : PTm n}
  (h00 : Γ ⊢[PRAAx] AbsLe Q.a00 c00) (h01 : Γ ⊢[PRAAx] AbsLe Q.a01 c01) (h02 : Γ ⊢[PRAAx] AbsLe Q.a02 c02)
  (h11 : Γ ⊢[PRAAx] AbsLe Q.a11 c11) (h12 : Γ ⊢[PRAAx] AbsLe Q.a12 c12) (h22 : Γ ⊢[PRAAx] AbsLe Q.a22 c22)

include h11 h12 h22 in
theorem R_bound {s t : ZT n} (hs : Γ ⊢[PRAAx] AbsLe s S) (ht : Γ ⊢[PRAAx] AbsLe t S) :
    Γ ⊢[PRAAx] AbsLe (Q.R s t) (c11 * S * S + c12 * S * S + c22 * S * S) :=
  show Γ ⊢[PRAAx] AbsLe (Q.a11 * s * s + Q.a12 * s * t + Q.a22 * t * t) _ from
    abs_add (abs_add (abs_mul (abs_mul h11 hs) hs) (abs_mul (abs_mul h12 hs) ht)) (abs_mul (abs_mul h22 ht) ht)

include h01 h11 h12 in
theorem ell_bound {p0 p1 p2 : ZT n} (hp0 : Γ ⊢[PRAAx] AbsLe p0 P) (hp1 : Γ ⊢[PRAAx] AbsLe p1 P)
    (hp2 : Γ ⊢[PRAAx] AbsLe p2 P) :
    Γ ⊢[PRAAx] AbsLe (Q.ell p0 p1 p2) (c01 * P + num 2 * c11 * P + c12 * P) :=
  show Γ ⊢[PRAAx] AbsLe (Q.a01 * p0 + ZT.ofNat (num 2) * Q.a11 * p1 + Q.a12 * p2) _ from
    abs_add (abs_add (abs_mul h01 hp0) (abs_mul (abs_mul (abs_nat (num 2)) h11) hp1)) (abs_mul h12 hp2)

include h02 h12 h22 in
theorem emm_bound {p0 p1 p2 : ZT n} (hp0 : Γ ⊢[PRAAx] AbsLe p0 P) (hp1 : Γ ⊢[PRAAx] AbsLe p1 P)
    (hp2 : Γ ⊢[PRAAx] AbsLe p2 P) :
    Γ ⊢[PRAAx] AbsLe (Q.emm p0 p1 p2) (c02 * P + c12 * P + num 2 * c22 * P) :=
  show Γ ⊢[PRAAx] AbsLe (Q.a02 * p0 + Q.a12 * p1 + ZT.ofNat (num 2) * Q.a22 * p2) _ from
    abs_add (abs_add (abs_mul h02 hp0) (abs_mul h12 hp1)) (abs_mul (abs_mul (abs_nat (num 2)) h22) hp2)

include h01 h02 h11 h12 h22 in
theorem L_bound {p0 p1 p2 s t : ZT n} (hp0 : Γ ⊢[PRAAx] AbsLe p0 P) (hp1 : Γ ⊢[PRAAx] AbsLe p1 P)
    (hp2 : Γ ⊢[PRAAx] AbsLe p2 P) (hs : Γ ⊢[PRAAx] AbsLe s S) (ht : Γ ⊢[PRAAx] AbsLe t S) :
    Γ ⊢[PRAAx] AbsLe (Q.L p0 p1 p2 s t)
      ((c01 * P + num 2 * c11 * P + c12 * P) * S + (c02 * P + c12 * P + num 2 * c22 * P) * S) :=
  show Γ ⊢[PRAAx] AbsLe (Q.ell p0 p1 p2 * s + Q.emm p0 p1 p2 * t) _ from
    abs_add (abs_mul (ell_bound Q h01 h11 h12 hp0 hp1 hp2) hs) (abs_mul (emm_bound Q h02 h12 h22 hp0 hp1 hp2) ht)

include h00 h01 h02 h11 h12 h22 in
/-- `thm:conic-height`, upper inequality: every coordinate of `M F(s, t)` is at most `3 C P S²` in absolute value. -/
theorem height_upper {p0 p1 p2 s t : ZT n} (hp0 : Γ ⊢[PRAAx] AbsLe p0 P) (hp1 : Γ ⊢[PRAAx] AbsLe p1 P)
    (hp2 : Γ ⊢[PRAAx] AbsLe p2 P) (hs : Γ ⊢[PRAAx] AbsLe s S) (ht : Γ ⊢[PRAAx] AbsLe t S) :
    (Γ ⊢[PRAAx] AbsLe (p0 * -Q.R s t) (num 3 * (c00 + c01 + c02 + c11 + c12 + c22) * P * (S * S))) ∧
    (Γ ⊢[PRAAx] AbsLe (p1 * -Q.R s t + s * Q.L p0 p1 p2 s t)
      (num 3 * (c00 + c01 + c02 + c11 + c12 + c22) * P * (S * S))) ∧
    (Γ ⊢[PRAAx] AbsLe (p2 * -Q.R s t + t * Q.L p0 p1 p2 s t)
      (num 3 * (c00 + c01 + c02 + c11 + c12 + c22) * P * (S * S))) := by
  have hR := abs_neg (R_bound Q h11 h12 h22 hs ht)
  have hL := L_bound Q h01 h02 h11 h12 h22 hp0 hp1 hp2 hs ht
  refine ⟨abs_mono ?_ (abs_mul hp0 hR), abs_mono ?_ (abs_add (abs_mul hp1 hR) (abs_mul hs hL)),
    abs_mono ?_ (abs_add (abs_mul hp2 hR) (abs_mul ht hL))⟩
  · ipra_le 𝔞 P * 𝔞 S * 𝔞 S * (3 * 𝔞 c00 + 3 * 𝔞 c01 + 3 * 𝔞 c02 + 2 * 𝔞 c11 + 2 * 𝔞 c12 + 2 * 𝔞 c22)
  · ipra_le 𝔞 P * 𝔞 S * 𝔞 S * (3 * 𝔞 c00 + 2 * 𝔞 c01 + 2 * 𝔞 c02)
  · ipra_le 𝔞 P * 𝔞 S * 𝔞 S * (3 * 𝔞 c00 + 2 * 𝔞 c01 + 2 * 𝔞 c02)

end Bounds

end LeanProofs.IPRA.DiophantineNumberTheory.ConicHeight
