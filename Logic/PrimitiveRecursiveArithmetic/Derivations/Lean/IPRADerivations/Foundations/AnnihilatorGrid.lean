import IPRADerivations.Core.LinearAlgebra
import IPRADerivations.Foundations.EigenvalueBound
import IPRADerivations.Foundations.RationalRootScan

/-!
# Separated annihilators: the boundary column and the grid radius (`ipra_presentations_to_witnesses`, `thm:annihilator-to-module`)

Packet: `foundations/ipra_presentations_to_witnesses`, theorem `thm:annihilator-to-module`: from
monic `q_k(T) = T^{d_k} + Σ_{i<d_k} a_{ki} T^i` with `q_k(X_k) = Σ_ℓ h_{kℓ} F_ℓ`, "if
`e_k = d_k − 1`, put `b̂_e = ∏_{j≠k} X_j^{e_j}`. Then
`X_k b_e − (−Σ_{i<d_k} a_{ki} b_{e[k←i]}) = b̂_e q_k(X_k) = Σ_ℓ (b̂_e h_{kℓ}) F_ℓ`. Thus the column of
`M_k` has entry `−a_{ki}` at the distinct rows `e[k←i]` ... the displayed products `b̂_e h_{kℓ}`
are its explicit residual witnesses", and "if `Δ_k` clears the denominators of
`a_{k0}, …, a_{k,d_k−1}`, a valid coordinate grid uses
`R_k = max(Δ_k, Σ_{i<d_k} |Δ_k a_{ki}|)`."

Integer terms, every degree `d` and every number `s` of equations (parameters of the Lean
statements); `x` is the value of `X_k`, `xp_i` of `X_k^i`, `xl` of `X_k^{d−1}`, `bh` of `b̂_e`:

* `boundary_ring`, `residual_ring`: the identities over a commutative ring;
* `annihilator_boundary`: `x (bh xl) + Σ_i a_i (bh xp_i) = bh (x xl + Σ_i a_i xp_i)`;
* `annihilator_residual`: with the membership identity `x xl + Σ_i a_i xp_i = Σ_ℓ h_ℓ F_ℓ`,
  the action residual `x (bh xl) + Σ_i a_i (bh xp_i) = Σ_ℓ (bh h_ℓ) F_ℓ`;
* `annihilator_zero`: at a common zero (`F_ℓ = 0` for every `ℓ`) the annihilator vanishes,
  `x xl + Σ_i a_i xp_i = 0`.

The grid, in the natural-number form of `Foundations/RationalRootDegree` (the coordinate is the
reduced fraction `p/q`, the integer coefficient list of `Δ q_k` is split by sign into `a`, `b`,
its leading coefficient is `Δ`):

* `annihilator_grid`: if the constant coefficient is nonzero, then `q ∣ Δ`, and both
  `q ≤ R` and `p ≤ R` for `R = max(Δ, Σ_{i<d} |c_i|)`: the packet's radius.

Here `p ∣ c_0` gives `p ≤ |c_0| ≤ Σ_{i<d} |c_i|` directly; the packet reaches the same radius
through the column sums of the companion matrices. Not derived: a zero constant coefficient
(removal of the factor `T^e`), the assembly of the `D = ∏ d_k` columns into one certificate
object, and the mixed-radix indexing of the exponent box (the digits are
`Foundations/MixedRadixGrid`).
-/

namespace LeanProofs.IPRA.Foundations.AnnihilatorGrid

open_ipra exports
open LeanProofs.IPRA.Foundations.RationalRootDegree (Bez P leading_dvd)
open LeanProofs.IPRA.Foundations.RationalRootConstant (num_bound)
open LeanProofs.IPRA.Foundations.RationalRootScan (bez_swap absd mx le_mx_left le_mx_right)
open LeanProofs.IPRA.Foundations.EigenvalueBound (adB inst2_adB)

section Ring

variable {R : Type*} [CommRing R] {d s : ℕ}

/-- The boundary column: `x (bh xl) + Σ a_i (bh xp_i) = bh (x xl + Σ a_i xp_i)`. -/
theorem boundary_ring (a xp : Fin d → R) (x bh xl : R) :
    x * (bh * xl) + ∑ i, a i * (bh * xp i) = bh * (x * xl + ∑ i, a i * xp i) := by
  have e : bh * ∑ i, a i * xp i = ∑ i, a i * (bh * xp i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  linear_combination (-1 : R) * e

/-- The residual of the boundary column, with explicit witnesses `bh h_ℓ`. -/
theorem residual_ring (a xp : Fin d → R) (h F : Fin s → R) (x bh xl : R)
    (hq : x * xl + ∑ i, a i * xp i = ∑ ℓ, h ℓ * F ℓ) :
    x * (bh * xl) + ∑ i, a i * (bh * xp i) = ∑ ℓ, bh * h ℓ * F ℓ := by
  rw [boundary_ring, hq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun ℓ _ => by ring

end Ring

variable {n : ℕ} {Γ : List (Fm PTm n)} {d s : ℕ}

/-- `thm:annihilator-to-module`, the boundary column. -/
theorem annihilator_boundary (a xp : Fin d → ZT n) (x bh xl : ZT n) :
    Γ ⊢[PRAAx] ZT.eq (x * (bh * xl) + ZT.sumFin fun i => a i * (bh * xp i))
      (bh * (x * xl + ZT.sumFin fun i => a i * xp i)) :=
  ZT.derive (by
    simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sumFin]
    exact boundary_ring _ _ _ _ _)

/-- `thm:annihilator-to-module`, the residual witnesses of the boundary column. -/
theorem annihilator_residual {a xp : Fin d → ZT n} {h F : Fin s → ZT n} {x xl : ZT n}
    (bh : ZT n)
    (hq : Γ ⊢[PRAAx] ZT.eq (x * xl + ZT.sumFin fun i => a i * xp i)
      (ZT.sumFin fun ℓ => h ℓ * F ℓ)) :
    Γ ⊢[PRAAx] ZT.eq (x * (bh * xl) + ZT.sumFin fun i => a i * (bh * xp i))
      (ZT.sumFin fun ℓ => bh * h ℓ * F ℓ) := by
  have e := ZT.toZ_eq hq
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sumFin] at e
  refine ZT.derive ?_
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_sumFin]
  exact residual_ring _ _ _ _ _ _ _ e

/-- At a common zero the separated annihilator vanishes at the coordinate. -/
theorem annihilator_zero {a xp : Fin d → ZT n} {h F : Fin s → ZT n} {x xl : ZT n}
    (hq : Γ ⊢[PRAAx] ZT.eq (x * xl + ZT.sumFin fun i => a i * xp i)
      (ZT.sumFin fun ℓ => h ℓ * F ℓ))
    (hF : ∀ ℓ, Γ ⊢[PRAAx] ZT.eq (F ℓ) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] ZT.eq (x * xl + ZT.sumFin fun i => a i * xp i) (ZT.natLit 0) := by
  have e := ZT.toZ_eq hq
  refine ZT.derive ?_
  rw [e, ZT.toZ_sumFin, ZT.toZ_natLit, Nat.cast_zero]
  refine Finset.sum_eq_zero fun ℓ _ => ?_
  have eF := ZT.toZ_eq (hF ℓ)
  rw [ZT.toZ_natLit, Nat.cast_zero] at eF
  rw [ZT.toZ_mul, eF]
  exact MulZeroClass.mul_zero _

/-! ## The grid radius -/

/-- `thm:annihilator-to-module`, the coordinate grid: a reduced root `p/q` of the cleared
annihilator with leading coefficient `Δ` and nonzero constant coefficient has `q ∣ Δ`, and
`q ≤ R`, `p ≤ R` for `R = max(Δ, Σ_{i<d} |c_i|)`. -/
theorem annihilator_grid (a b : PTm 2) {p' q' u v d x Δ' : PTm n}
    (hB : Γ ⊢[PRAAx] Bez p' (succ q') u v)
    (hE : Γ ⊢[PRAAx] P a (succ d) (succ p') (succ q') d x ≐ P b (succ d) (succ p') (succ q') d x)
    (hlead : Γ ⊢[PRAAx] absd a b d x ≐ succ Δ')
    (h0 : Γ ⊢[PRAAx] absd a b zero x ≐ succ (pred (absd a b zero x)))
    (hd : Γ ⊢[PRAAx] lt zero d) :
    Γ ⊢[PRAAx] dvd (succ q') (succ Δ') ⋏
      (le (succ q') (mx (succ Δ') (ap2 (sumF (adB a b)) d x)) ⋏
        le (succ p') (mx (succ Δ') (ap2 (sumF (adB a b)) d x))) := by
  have hdv : Γ ⊢[PRAAx] dvd (succ q') (succ Δ') :=
    dvd_congr hlead (leading_dvd a b (bez_swap hB) hE)
  have hq : Γ ⊢[PRAAx] le (succ q') (succ Δ') :=
    Foundations.RationalRootConstant.dvd_le hdv (pos_of_eq_succ (.eqRefl _))
  have ht := term_le_sum (Γ := Γ) (adB a b) (x := x) hd
  rw [inst2_adB] at ht
  have hp : Γ ⊢[PRAAx] le (succ p') (ap2 (sumF (adB a b)) d x) :=
    le_trans (num_bound a b hB hE h0) ht
  exact .andI hdv (.andI (le_trans hq (le_mx_left _ _)) (le_trans hp (le_mx_right _ _)))

end LeanProofs.IPRA.Foundations.AnnihilatorGrid
