import IPRADerivations.Algebra.AdjugateInverse
import IPRADerivations.Core.IntCertificates
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

L03 and L04 are also derived in iPRA for integer terms (`ZT`, the rationals cleared of a common
denominator), with the certificates of `Core/IntCertificates`: `center_interior_ipra`,
`dual_bound_ipra` and `selected_vanish_ipra` (which gives the iPRA equation `z_j = 0`).
-/

namespace LeanProofs.IPRA.Topology.LimitCertificates

/-! ## L03 -/

/-- Nonnegative values at the vertices, one of them positive, have a positive sum (so the side functional is
positive at the average of the vertices). -/
theorem center_interior {m : ℕ} (f : Fin m → ℚ) (hnn : ∀ i, 0 ≤ f i) (hpos : ∃ i, 0 < f i) : 0 < ∑ i, f i := by
  obtain ⟨i, hi⟩ := hpos
  exact _root_.lt_of_lt_of_le hi (Finset.single_le_sum (fun j _ => hnn j) (Finset.mem_univ i))

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
  have hzero : ∑ k, c k * z k = 0 := _root_.le_antisymm hle (Finset.sum_nonneg hnn)
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

/-! ## L03 and L04 in iPRA -/

section IPRA

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- L03 in iPRA: nonnegative integer values, one at least `1`, have sum at least `1`. -/
theorem center_interior_ipra {m : ℕ} (f : Fin m → ZT n) (hnn : ∀ i, Γ ⊢[PRAAx] zle (ZT.natLit 0) (f i))
    {j : Fin m} (hj : Γ ⊢[PRAAx] zle (ZT.natLit 1) (f j)) : Γ ⊢[PRAAx] zle (ZT.natLit 1) (ZT.sumFin f) := by
  refine zle_of_comb (zsl hj + ∑ i ∈ Finset.univ.erase j, ZT.toZ Γ (f i)) ?_
    (nn_add (nn_zsl hj) (nn_sum _ _ fun i _ => nn_zle0 (hnn i)))
  rw [zsl_def, ZT.toZ_sumFin, ← Finset.add_sum_erase Finset.univ (fun i => ZT.toZ Γ (f i)) (Finset.mem_univ j)]
  ring

/-- L04 in iPRA: `z ≥ 0`, `E z = b`, `c ≤ Eᵀ y` and `bᵀ y ≤ 0` give `cᵀ z ≤ 0`. -/
theorem dual_bound_ipra (E : Fin r → Fin s → ZT n) (b y : Fin r → ZT n) (c z : Fin s → ZT n)
    (hz : ∀ j, Γ ⊢[PRAAx] zle (ZT.natLit 0) (z j))
    (hEz : ∀ i, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => E i j * z j) (b i))
    (hdual : ∀ j, Γ ⊢[PRAAx] zle (c j) (ZT.sumFin fun i => E i j * y i))
    (hb : Γ ⊢[PRAAx] zle (ZT.sumFin fun i => b i * y i) (ZT.natLit 0)) :
    Γ ⊢[PRAAx] zle (ZT.sumFin fun j => c j * z j) (ZT.natLit 0) := by
  refine zle_of_comb (zsl hb + ∑ j, zsl (hdual j) * ZT.toZ Γ (z j)) ?_
    (nn_add (nn_zsl hb) (nn_sum _ _ fun j _ => nn_mul (nn_zsl _) (nn_zle0 (hz j))))
  have hE : ∀ i, ZT.toZ Γ (b i) = ∑ j, ZT.toZ Γ (E i j) * ZT.toZ Γ (z j) := fun i => by
    have := ZT.toZ_eq (hEz i)
    simp only [ZT.toZ_sumFin, ZT.toZ_mul] at this
    exact this.symm
  have key : ∑ i, (∑ j, ZT.toZ Γ (E i j) * ZT.toZ Γ (z j)) * ZT.toZ Γ (y i) =
      ∑ j, (∑ i, ZT.toZ Γ (E i j) * ZT.toZ Γ (y i)) * ZT.toZ Γ (z j) := by
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
  simp only [zsl_def, ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero, hE]
  rw [key]
  simp only [sub_mul, Finset.sum_sub_distrib]
  ring

/-- L04 in iPRA: an entry `j` with `c_j ≥ 1` has `z_j = 0`. -/
theorem selected_vanish_ipra (E : Fin r → Fin s → ZT n) (b y : Fin r → ZT n) (c z : Fin s → ZT n)
    (hc : ∀ j, Γ ⊢[PRAAx] zle (ZT.natLit 0) (c j)) (hz : ∀ j, Γ ⊢[PRAAx] zle (ZT.natLit 0) (z j))
    (hEz : ∀ i, Γ ⊢[PRAAx] ZT.eq (ZT.sumFin fun j => E i j * z j) (b i))
    (hdual : ∀ j, Γ ⊢[PRAAx] zle (c j) (ZT.sumFin fun i => E i j * y i))
    (hb : Γ ⊢[PRAAx] zle (ZT.sumFin fun i => b i * y i) (ZT.natLit 0)) {j : Fin s}
    (hj : Γ ⊢[PRAAx] zle (ZT.natLit 1) (c j)) : Γ ⊢[PRAAx] ZT.eq (z j) (ZT.natLit 0) := by
  have H := dual_bound_ipra E b y c z hz hEz hdual hb
  have hle : Γ ⊢[PRAAx] zle (z j) (ZT.natLit 0) := by
    refine zle_of_comb (zsl H + ∑ k ∈ Finset.univ.erase j, ZT.toZ Γ (c k) * ZT.toZ Γ (z k) +
      zsl hj * ZT.toZ Γ (z j)) ?_
      (nn_add (nn_add (nn_zsl H) (nn_sum _ _ fun k _ => nn_mul (nn_zle0 (hc k)) (nn_zle0 (hz k))))
        (nn_mul (nn_zsl hj) (nn_zle0 (hz j))))
    simp only [zsl_def, ZT.toZ_sumFin, ZT.toZ_mul, ZT.toZ_natLit, Nat.cast_zero, Nat.cast_one]
    rw [← Finset.add_sum_erase Finset.univ (fun k => ZT.toZ Γ (c k) * ZT.toZ Γ (z k)) (Finset.mem_univ j)]
    ring
  exact le_antisymm hle (hz j)

end IPRA

end LeanProofs.IPRA.Topology.LimitCertificates
