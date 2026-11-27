import IPRADerivations.Analysis.Stirling.Binet.Bose.LiteralTails.GaussianBinetBoseLiteralLate
import IPRADerivations.Analysis.Stirling.Binet.Bose.PrefixQuadrature.GaussianBinetBosePrefixRefinement

/-!
# Refine the original compact Bose panel with an independently late prefix

The finite geometric cutoff pays the compact comparison precision.
The literal and ordinary quadratures both read the original cells at
a later, independent clock. Weighting by the physical interval keeps
its exact width in the comparison with the literal prefix.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBosePrefixRefinementLate

open_ipra
open GaussianBinetArctangentQuadrature (fixedData)
open GaussianBinetBosePrefixQuadrature (cost point evaluatorF point_error_late quadrature_error_late)
open GaussianBinetBoseCompact (source)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianCompactRiemannName (quadrature precision mesh mesh_positive)
open GaussianRationalDistanceOrder (distance_radius_mono distance_congr distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "Actual" => GaussianBinetBoseIntegrandBound.nameF
local notation "actualData" => GaussianBinetBoseIntegrandBound.data

theorem point_error (s p N X Y D sign A B T E : PTm n)
    (hz : Γ ⊢[PRAAx] GaussianRightHalfPlaneLogarithm.source X D sign)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hE : Γ ⊢[PRAAx] le one E)
    (lower : Γ ⊢[PRAAx] le B (E*A)) (upper : Γ ⊢[PRAAx] le A (T*B))
    (hs : Γ ⊢[PRAAx] le s p) (hN : Γ ⊢[PRAAx] le (E*E*unit s) N) :
    Γ ⊢[PRAAx] distanceBounded (ap2 Actual p (actualData X Y D sign A B)) (point p N X Y D sign A B)
      (cost D T E) (unit s) :=
  point_error_late s p N X Y D sign A B T E hz hA hB hE lower upper hs hN

theorem quadrature_error (s p M N X Y D sign T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E) (hM : Γ ⊢[PRAAx] le one M)
    (hs : Γ ⊢[PRAAx] le s p) (hN : Γ ⊢[PRAAx] le (E*E*unit s) N) :
    Γ ⊢[PRAAx] distanceBounded
      (quadrature GaussianBinetBoseCompact.evaluatorF p M (E+A) C E (fixedData X Y D sign))
      (quadrature evaluatorF p M (E+A) C E (pairT N (fixedData X Y D sign)))
      (C*cost D T E) (E*unit s) :=
  quadrature_error_late s p M N X Y D sign T A C E h hM hs hN

theorem refined_prefix_error (p q R N X Y D sign T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E)
    (hR : Γ ⊢[PRAAx] le one R) (hq : Γ ⊢[PRAAx] le (precision p T) q)
    (hN : Γ ⊢[PRAAx] le (E*E*unit p) N) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianBinetBoseCompact.nameF p (GaussianBinetBoseCompact.data X Y D sign T A C E))
      (quadrature evaluatorF q (R*mesh p (GaussianBinetBoseCompact.gain D E T) T) (E+A) C E (pairT N (fixedData X Y D sign)))
      (num 3*E+C*cost D T E) (E*unit p) := by
  let x := fixedData X Y D sign
  let L := GaussianBinetBoseCompact.gain D E T
  let M := R*mesh p L T
  let f := GaussianBinetBoseCompact.evaluatorF
  let old := ap2 GaussianBinetBoseCompact.nameF p (GaussianBinetBoseCompact.data X Y D sign T A C E)
  let plain := quadrature f q M (E+A) C E x
  let W := unit (p+num 6)
  let U := unit p
  have hM := positive_product _ _ hR (mesh_positive p L T)
  have hE := h.andE₂.andE₂.andE₁
  have hp := unit_positive (Γ := Γ) p
  have he := positive_product _ _ hE hp
  have hs : Γ ⊢[PRAAx] le U W := GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have pq : Γ ⊢[PRAAx] le p q := le_trans (le_trans (le_add_right p T) (le_add_right (p+T) (num 6))) hq
  have width := GaussianBinetBoseCompact.compact_input X Y D sign T A C E h
  have refineDistance := GaussianCompactMeshIndependence.arbitrary_refinement f p q R (E+A) C E L T x width hR hq
  have read := GaussianCompactRiemannName.name_at (Γ := Γ) f p (E+A) C E L T x
  have raw := distance_congr (.eqRefl plain) read.eqSymm (.eqRefl _) (.eqRefl _) refineDistance
  have first : Γ ⊢[PRAAx] distanceBounded old plain (num 3*E) (E*U) :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive _) he
      (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right (num 3*E) hs))
      (distance_symmetric plain old (num 3) W (unit_positive _) raw)
  exact distance_triangle_same _ _ _ _ _ _ he first (quadrature_error p q M N X Y D sign T A C E h hM pq hN)

end LeanProofs.IPRA.Analysis.GaussianBinetBosePrefixRefinementLate
