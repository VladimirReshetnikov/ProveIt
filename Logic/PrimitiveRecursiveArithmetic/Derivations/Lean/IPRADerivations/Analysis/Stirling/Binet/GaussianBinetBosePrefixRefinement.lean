import IPRADerivations.Analysis.Stirling.Binet.GaussianBinetBosePrefixQuadrature
import IPRADerivations.Analysis.Integration.GaussianCompactMeshIndependence

/-!
# Read a literal Bose prefix on any certified refinement

The quadrature precision can be fixed before choosing the geometric
cutoff. The mesh refinement can be chosen later, independently of
both clocks and of the Pi sample used for the frozen rows.
-/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBinetBosePrefixRefinement

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentQuadrature (fixedData)
open GaussianBinetBoseCompact (source gain)
open GaussianBinetBosePrefixQuadrature (cost evaluatorF quadrature_error)
open GaussianCompactRiemannName (quadrature mesh mesh_positive precision)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)

theorem refined_prefix_error (p q R N X Y D sign T A C E : PTm n)
    (h : Γ ⊢[PRAAx] source X D sign T A C E)
    (hR : Γ ⊢[PRAAx] le one R) (hq : Γ ⊢[PRAAx] le (precision p T) q)
    (hN : Γ ⊢[PRAAx] le (E*E*unit q) N) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianBinetBoseCompact.nameF p (GaussianBinetBoseCompact.data X Y D sign T A C E))
      (quadrature evaluatorF q (R*mesh p (gain D E T) T) (E+A) C E (pairT N (fixedData X Y D sign)))
      (num 3+T*cost D T E) (unit p) := by
  let x := fixedData X Y D sign
  let L := gain D E T
  let M := R*mesh p L T
  let f := GaussianBinetBoseCompact.evaluatorF
  let old := ap2 GaussianBinetBoseCompact.nameF p (GaussianBinetBoseCompact.data X Y D sign T A C E)
  let plain := quadrature f q M (E+A) C E x
  let literal := quadrature evaluatorF q M (E+A) C E (pairT N x)
  let W := unit (p+num 6)
  have hM := positive_product _ _ hR (mesh_positive p L T)
  have hE := h.andE₂.andE₂.andE₁
  have hp := unit_positive (Γ := Γ) p
  have hs : Γ ⊢[PRAAx] le (unit p) W :=
    GaussianExponentialReference.unit_monotone (le_add_right _ _)
  have pq : Γ ⊢[PRAAx] le p q := le_trans (le_trans (le_add_right p T) (le_add_right (p+T) (num 6))) hq
  have upward := GaussianExponentialReference.unit_monotone (Γ := Γ) pq
  have width := GaussianBinetBoseCompact.compact_input X Y D sign T A C E h
  have refineDistance := GaussianCompactMeshIndependence.arbitrary_refinement f p q R (E+A) C E L T x width hR hq
  have read := GaussianCompactRiemannName.name_at (Γ := Γ) f p (E+A) C E L T x
  have raw := distance_congr (.eqRefl plain) read.eqSymm (.eqRefl _) (.eqRefl _) refineDistance
  have first : Γ ⊢[PRAAx] distanceBounded old plain (num 3) (unit p) :=
    distance_radius_mono _ _ _ _ _ _ (unit_positive _) hp (le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right (num 3) hs))
      (distance_symmetric plain old (num 3) W (unit_positive _) raw)
  have hWidth := width.andE₂.andE₂.andE₁
  have den := positive_product _ _ hE (unit_positive q)
  have rawPrefix := quadrature_error q M N X Y D sign T A C E h hM hN
  have next : Γ ⊢[PRAAx] distanceBounded plain literal (T*cost D T E) (unit p) := by
    apply distance_radius_mono _ _ _ _ _ _ den hp ?_ rawPrefix
    ipra_le 𝔞(cost D T E*unit p)*sl hWidth+𝔞(T*cost D T E*E)*sl upward
  exact distance_triangle_same old plain literal (num 3) (T*cost D T E) (unit p) hp first next

theorem actual_second_Binet_refined_Bose_prefix_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 12
    (((source (var 4) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11) ⋏ le one (var 2)) ⋏
      (le (precision (var 0) (var 8)) (var 1) ⋏ le (var 11*var 11*unit (var 1)) (var 3))) ⟶
    distanceBounded
      (ap2 GaussianBinetBoseCompact.nameF (var 0)
        (GaussianBinetBoseCompact.data (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) (var 10) (var 11)))
      (quadrature evaluatorF (var 1) (var 2*mesh (var 0) (gain (var 6) (var 11) (var 8)) (var 8))
        (var 11+var 9) (var 10) (var 11) (pairT (var 3) (fixedData (var 4) (var 5) (var 6) (var 7))))
      (num 3+var 8*cost (var 6) (var 8) (var 11)) (unit (var 0))) :=
  closeUniv 12 (.impI (refined_prefix_error _ _ _ _ _ _ _ _ _ _ _ _
    Prf.hyp0.andE₁.andE₁ Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetBosePrefixRefinement
