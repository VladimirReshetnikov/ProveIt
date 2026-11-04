import Trace74AbstractCover
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace74GenericPowerCover

/-- Generic power sandwich keeps radix, exponents, and all values symbolic. -/
theorem cover (B short long full beta low defect high : ℕ)
    (hB : 0 < B) (hlen : short ≤ long)
    (hbeta : beta+1 = B^full) (hlow : low+defect+1 = B^full)
    (hdefect : defect < B^short) (hhigh : B^long ≤ high) :
    beta+1 ≤ low+high := by
  have hpow : B^short ≤ B^long := Nat.pow_le_pow_right hB hlen
  have hd : defect < high := lt_of_lt_of_le hdefect (le_trans hpow hhigh)
  exact Trace74AbstractCover.of_identity beta low defect high (B^full) hbeta hlow hd

#print axioms Trace74GenericPowerCover.cover
end Trace74GenericPowerCover
