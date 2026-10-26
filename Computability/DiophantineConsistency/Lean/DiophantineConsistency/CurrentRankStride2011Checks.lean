import DiophantineConsistency.CurrentRankStride2011

namespace DiophantineConsistency.CurrentRankStride2011Checks
open CurrentControllerData2011 CurrentRankStride2011 CurrentWordClause2011
  CurrentWordCopies2011 WangTiles942Periodic
set_option Elab.async false

example (t : ℕ) : displacement t = 94517*t := displacement_mul t
example {N R s : ℕ} (hmod : R ≡ d*s [MOD d*N]) :
    2^(displacement (derivedStride N R)) = 2^(R-d*N) :=
  power_displacement_derived hmod

-- Full periods are retained in the natural quotient; powers are symbolic.
example : derivedStride 3 (d*10) = 7 := by decide
example : displacement (derivedStride 3 (d*10)) = d*10-d*3 :=
  displacement_derived (by decide : d*10 ≡ d*1 [MOD d*3])

example {N : ℕ} [NeZero N] (a : ZMod N → Fin 942) (dummy : ZMod N → ℕ)
    (hd : ∀ j, dummy j ≤ 1) (s R : ℕ) (ha : MarkedWord N (s : ℤ) a)
    (carry digits : ZMod (N*2011) → ℕ)
    (hf : CurrentNativePacking2011.Facts a dummy s carry digits)
    (hlarge : 2*(d*N) < R) (hmod : R ≡ d*s [MOD d*N]) :
    0 < derivedStride N R ∧
      constructedWord a dummy (derivedStride N R) = constructedWord a dummy s ∧
      CurrentNativePacking2011.Facts a dummy (derivedStride N R) carry digits ∧
      displacement (derivedStride N R) = R-d*N ∧
      2^(displacement (derivedStride N R)) = 2^(R-d*N) :=
  packing_at_derived_stride a dummy hd s R ha carry digits hf hlarge hmod

#print axioms displacement_mul
#print axioms derived_spec
#print axioms derived_quotient
#print axioms displacement_derived
#print axioms power_displacement_derived
#print axioms packing_at_derived_stride

end DiophantineConsistency.CurrentRankStride2011Checks
