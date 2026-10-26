import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Linarith

/-! A rank congruence determines an actual positive whole-cell stride.
Divisibility, the quotient equation, and the cyclic residue are derived,
not supplied. No polynomial, packing, or controller constants occur here. -/
namespace DiophantineConsistency.ControllerRankStride

set_option Elab.async false
set_option maxRecDepth 10000

def stride (d N R : ℕ) : ℕ := R/d-N

theorem rank_dvd {d N R s : ℕ} (hmod : R ≡ d*s [MOD d*N]) : d ∣ R :=
  (hmod.dvd_iff (dvd_mul_right d N)).mpr (dvd_mul_right d s)

theorem quotient_mul {d N R s : ℕ} (hmod : R ≡ d*s [MOD d*N]) : d*(R/d) = R :=
  Nat.mul_div_cancel' (rank_dvd hmod)

theorem quotient_mod {d N R s : ℕ} (hd : 0 < d)
    (hmod : R ≡ d*s [MOD d*N]) : R/d ≡ s [MOD N] := by
  apply Nat.ModEq.mul_left_cancel' (Nat.ne_of_gt hd)
  rwa [quotient_mul hmod]

theorem quotient_gt {d N R s : ℕ} (_hd : 0 < d)
    (hlarge : 2*(d*N) < R) (hmod : R ≡ d*s [MOD d*N]) : 2*N < R/d := by
  have he := quotient_mul hmod
  nlinarith

theorem stride_gt_cells {d N R s : ℕ} (hd : 0 < d)
    (hlarge : 2*(d*N) < R) (hmod : R ≡ d*s [MOD d*N]) : N < stride d N R := by
  have h := quotient_gt hd hlarge hmod
  unfold stride
  omega

theorem stride_mul {d N R s : ℕ} (hmod : R ≡ d*s [MOD d*N]) :
    d*stride d N R = R-d*N := by
  unfold stride
  rw [Nat.mul_sub_left_distrib,quotient_mul hmod]

/-- This is the actual quotient of the printed exponent, with no remainder. -/
theorem stride_quotient {d N R s : ℕ} (hd : 0 < d)
    (hmod : R ≡ d*s [MOD d*N]) : stride d N R = (R-d*N)/d := by
  rw [← stride_mul hmod,Nat.mul_div_cancel_left _ hd]

theorem stride_mod {d N R s : ℕ} (hd : 0 < d)
    (hlarge : 2*(d*N) < R) (hmod : R ≡ d*s [MOD d*N]) :
    stride d N R ≡ s [MOD N] := by
  have h := quotient_gt hd hlarge hmod
  exact (Nat.sub_modulus_modEq_iff (by omega : N ≤ R/d)).mpr (quotient_mod hd hmod)

/-- The supplied number R determines the positive stride. The original
stride need not be a canonical representative to obtain cyclic equality. -/
theorem stride_spec {d N R s : ℕ} (hd : 0 < d) (hN : 0 < N)
    (hlarge : 2*(d*N) < R) (hmod : R ≡ d*s [MOD d*N]) :
    0 < stride d N R ∧ d*stride d N R = R-d*N ∧
      (stride d N R : ZMod N) = (s : ZMod N) := by
  refine ⟨lt_trans hN (stride_gt_cells hd hlarge hmod),stride_mul hmod,?_⟩
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mpr (stride_mod hd hlarge hmod)

theorem stride_value {d N R s : ℕ} (hd : 0 < d) (hN : 0 < N) (hs : s < N)
    (hlarge : 2*(d*N) < R) (hmod : R ≡ d*s [MOD d*N]) :
    (stride d N R : ZMod N).val = s := by
  rw [(stride_spec hd hN hlarge hmod).2.2,ZMod.val_natCast_of_lt hs]

theorem exists_stride {d N R s : ℕ} (hd : 0 < d) (hN : 0 < N)
    (hlarge : 2*(d*N) < R) (hmod : R ≡ d*s [MOD d*N]) :
    ∃ t : ℕ, 0 < t ∧ d*t = R-d*N ∧ (t : ZMod N) = (s : ZMod N) :=
  ⟨stride d N R,stride_spec hd hN hlarge hmod⟩

end DiophantineConsistency.ControllerRankStride
