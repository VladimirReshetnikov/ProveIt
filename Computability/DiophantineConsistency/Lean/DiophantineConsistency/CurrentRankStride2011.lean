import DiophantineConsistency.ControllerRankStride
import DiophantineConsistency.CurrentControllerData2011
import DiophantineConsistency.CurrentWordRephase2011

/-! The derived whole-cell stride has the exact current binary displacement.
The packing adapter preserves its particular source, carries, and digits.
Its number R is explicitly supplied with growth and congruence; binding R
to that packing's actual rank is a separate obligation, not claimed here. -/
namespace DiophantineConsistency.CurrentRankStride2011

open CurrentControllerData2011 CurrentWordClause2011 CurrentWordCopies2011
  WangTiles942Periodic
set_option Elab.async false
set_option maxRecDepth 10000

def derivedStride (N R : ℕ) : ℕ := ControllerRankStride.stride d N R

theorem displacement_mul (t : ℕ) : displacement t = d*t := by
  rw [d_factors]
  unfold displacement
  exact (Nat.mul_assoc _ _ _).symm

theorem derived_spec {N R s : ℕ} (hN : 0 < N)
    (hlarge : 2*(d*N) < R) (hmod : R ≡ d*s [MOD d*N]) :
    0 < derivedStride N R ∧ d*derivedStride N R = R-d*N ∧
      (derivedStride N R : ZMod N) = (s : ZMod N) :=
  ControllerRankStride.stride_spec (by decide) hN hlarge hmod

theorem derived_quotient {N R s : ℕ} (hmod : R ≡ d*s [MOD d*N]) :
    derivedStride N R = (R-d*N)/d :=
  ControllerRankStride.stride_quotient (by decide) hmod

theorem displacement_derived {N R s : ℕ} (hmod : R ≡ d*s [MOD d*N]) :
    displacement (derivedStride N R) = R-d*N := by
  rw [displacement_mul]
  exact ControllerRankStride.stride_mul hmod

theorem power_displacement_derived {N R s : ℕ} (hmod : R ≡ d*s [MOD d*N]) :
    2^(displacement (derivedStride N R)) = 2^(R-d*N) := by
  rw [displacement_derived hmod]

variable {N : ℕ} [NeZero N]

/-- Rephase a particular packing at the derived positive quotient stride.
R is a supplied natural number with the displayed arithmetic facts, not
an implicitly asserted rank. No fresh choice of normalized digits occurs. -/
theorem packing_at_derived_stride (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s R : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (carry digits : ZMod (N*2011) → ℕ)
    (hf : CurrentNativePacking2011.Facts a dummy s carry digits)
    (hlarge : 2*(d*N) < R) (hmod : R ≡ d*s [MOD d*N]) :
    0 < derivedStride N R ∧
      constructedWord a dummy (derivedStride N R) = constructedWord a dummy s ∧
      CurrentNativePacking2011.Facts a dummy (derivedStride N R) carry digits ∧
      displacement (derivedStride N R) = R-d*N ∧
      2^(displacement (derivedStride N R)) = 2^(R-d*N) := by
  obtain ⟨hpos,hprod,hcast⟩ := derived_spec (NeZero.pos N) hlarge hmod
  refine ⟨hpos,?_,?_,displacement_derived hmod,power_displacement_derived hmod⟩
  · exact CurrentWordRephase2011.constructedWord_eq a dummy (derivedStride N R) s hcast
  · exact CurrentWordRephase2011.packing_rephase a dummy hd s (derivedStride N R)
      hcast.symm ha carry digits hf

end DiophantineConsistency.CurrentRankStride2011
