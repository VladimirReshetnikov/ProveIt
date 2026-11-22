import IPRADerivations.Algebra.AdjugateInverse
import Mathlib.Data.Rat.Defs
import Mathlib.LinearAlgebra.Matrix.DotProduct

/-!
# Fan-disk certificates and the halting reduction

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/08_limits.tex`:

* L03 (convex polygonal loops), its interior step: "each side functional is nonnegative on every vertex and
  strictly positive on at least one, hence positive on their average" (`center_interior`, for the side
  functional's values at the `m` vertices, whose average is its value at the centre);
* L04 (`prop:disk-certificate`), the intersection certificate: for the barycentric variables `z ≥ 0` with
  `E z = b`, a rational vector `y` with `Eᵀ y ≥ c` (`c ≥ 0`) and `bᵀ y ≤ 0` gives
  "`cᵀ z ≤ yᵀ E z = yᵀ b ≤ 0`. The selected nonnegative entries must all vanish" (`dual_bound`,
  `selected_vanish`), over the rationals;
* L06 ("an exact arbitrary-union extractor would decide halting"): an extractor returning the bit of
  `⋃_t A_{e,t}` with `A_{e,t} ≠ ∅` iff program `e` halts within `t` steps is a halting decider
  (`extractor_decides`), and no halting decider exists against a diagonal program ("Either value of `h(d)`
  contradicts its specification", `no_decider`, `no_extractor`).
-/

namespace LeanProofs.IPRA.Topology.LimitCertificates

/-! ## L03 -/

/-- Nonnegative values at the vertices, one of them positive, have a positive sum (so the side functional is
positive at the average of the vertices). -/
theorem center_interior {m : ℕ} (f : Fin m → ℚ) (hnn : ∀ i, 0 ≤ f i) (hpos : ∃ i, 0 < f i) : 0 < ∑ i, f i := by
  obtain ⟨i, hi⟩ := hpos
  exact lt_of_lt_of_le hi (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i))

/-! ## L04 -/

variable {r s : ℕ}

/-- `cᵀ z ≤ yᵀ E z = yᵀ b ≤ 0`. -/
theorem dual_bound (E : Matrix (Fin r) (Fin s) ℚ) (b : Fin r → ℚ) (y : Fin r → ℚ) (c z : Fin s → ℚ)
    (hz : ∀ j, 0 ≤ z j) (hEz : E.mulVec z = b) (hdual : ∀ j, c j ≤ (E.transpose.mulVec y) j)
    (hb : b ⬝ᵥ y ≤ 0) : c ⬝ᵥ z ≤ 0 := by
  have h1 : c ⬝ᵥ z ≤ (E.transpose.mulVec y) ⬝ᵥ z := by
    unfold dotProduct
    exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_right (hdual j) (hz j)
  have h2 : (E.transpose.mulVec y) ⬝ᵥ z = b ⬝ᵥ y := by
    rw [← hEz, Matrix.mulVec_transpose, ← Matrix.dotProduct_mulVec, dotProduct_comm]
  linarith

/-- The selected entries vanish: `c_j > 0` forces `z_j = 0`. -/
theorem selected_vanish (E : Matrix (Fin r) (Fin s) ℚ) (b : Fin r → ℚ) (y : Fin r → ℚ) (c z : Fin s → ℚ)
    (hc : ∀ j, 0 ≤ c j) (hz : ∀ j, 0 ≤ z j) (hEz : E.mulVec z = b)
    (hdual : ∀ j, c j ≤ (E.transpose.mulVec y) j) (hb : b ⬝ᵥ y ≤ 0) {j : Fin s} (hj : 0 < c j) : z j = 0 := by
  have hle := dual_bound E b y c z hz hEz hdual hb
  have hnn : ∀ k ∈ Finset.univ, 0 ≤ c k * z k := fun k _ => mul_nonneg (hc k) (hz k)
  have hzero : ∑ k, c k * z k = 0 := le_antisymm hle (Finset.sum_nonneg hnn)
  have hcz := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hzero j (Finset.mem_univ j)
  rcases mul_eq_zero.mp hcz with h | h
  · exact absurd h (ne_of_gt hj)
  · exact h

/-! ## L06 -/

/-- An exact union extractor for `A_{e,t}` = "program `e` halts on `e` within `t` steps" decides halting. -/
theorem extractor_decides {Halts : ℕ → Prop} {A : ℕ → ℕ → Prop} (hA : ∀ e, Halts e ↔ ∃ t, A e t)
    {U : ℕ → Bool} (hU : ∀ e, U e = true ↔ ∃ t, A e t) : ∀ e, U e = true ↔ Halts e :=
  fun e => (hU e).trans (hA e).symm

/-- No halting decider exists when every total `h` has a diagonal program `d` with
`Halts d ↔ h d = false`. -/
theorem no_decider {Halts : ℕ → Prop} (hdiag : ∀ h : ℕ → Bool, ∃ d, Halts d ↔ h d = false) :
    ¬ ∃ h : ℕ → Bool, ∀ e, h e = true ↔ Halts e := by
  rintro ⟨h, hh⟩
  obtain ⟨d, hd⟩ := hdiag h
  cases hv : h d with
  | false =>
    have := (hh d).mpr (hd.mpr hv)
    rw [hv] at this
    exact absurd this (by decide)
  | true =>
    have hHalts := (hh d).mp hv
    have := hd.mp hHalts
    rw [hv] at this
    exact absurd this (by decide)

/-- L06: no exact arbitrary-union extractor exists for the halting family. -/
theorem no_extractor {Halts : ℕ → Prop} {A : ℕ → ℕ → Prop} (hA : ∀ e, Halts e ↔ ∃ t, A e t)
    (hdiag : ∀ h : ℕ → Bool, ∃ d, Halts d ↔ h d = false) :
    ¬ ∃ U : ℕ → Bool, ∀ e, U e = true ↔ ∃ t, A e t := by
  rintro ⟨U, hU⟩
  exact no_decider hdiag ⟨U, extractor_decides hA hU⟩

end LeanProofs.IPRA.Topology.LimitCertificates
