import GowersSzemeredi.Proofs18ColorClass
import GowersSzemeredi.Proofs18SharpInterfaces
import GowersSzemeredi.Proofs03FourFactorSymmetry
import GowersSzemeredi.Proofs05Corollary58
import GowersSzemeredi.Proofs05HighCorrelationAssembly
import GowersSzemeredi.Proofs05HighCorrelationScale
import GowersSzemeredi.Proofs05ThresholdFreeScale

/-! **Van der Waerden numbers with `r` colours** (Notes L.15g).

Corollary 18.7 is Theorem 18.2 at density one half, for two colours. With
`r ≥ 2` colours one class has density at least `1/r`, so Theorem 18.2 at
`δ = 1/r` gives a monochromatic `k`-term progression in every `r`-colouring
of `[1, N]` once `N ≥ szemerediThresholdAt c (1/r) k = 2^(2^(r^(2^(2^(k+c)))))`.
This is Gowers's van der Waerden bound `W(k, r) ≤ 2^2^r^2^2^(k+9)` at
`c = 9`; with Theorem 18.2 at `L + 5` it holds with `k + 5`
(`van_der_waerden_L5`, in `Proofs18CoverSharperAllDegrees`).
* `exists_color_class_ge`: some colour class of `[1, N]` has at least
  `N/r` elements;
* `Theorem182AtSharp.van_der_waerden`. -/
set_option autoImplicit false
noncomputable section
open Finset
namespace LeanProofs.GowersSzemeredi

/-- **Theorem 18.2 gives van der Waerden numbers for `r` colours.** -/
theorem Theorem182AtSharp.van_der_waerden {c k : Nat} (h : Theorem182AtSharp c k) {r : Nat}
    (hr : 2 ≤ r) (N : Nat) (hN : szemerediThresholdAt c (1 / (r : Real)) k ≤ N)
    (color : Nat → Fin r) : HasMonochromaticAP N r color k := by
  have hrR : (2 : Real) ≤ r := by exact_mod_cast hr
  exact hasMonochromaticAP_of_density (by omega)
    (h (1 / (r : Real)) N (by positivity)
      (one_div_le_one_div_of_le (by norm_num) hrR) hN) color

end LeanProofs.GowersSzemeredi
