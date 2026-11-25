import IPRADerivations.Analysis.GaussianStirlingFiniteTelescopeBounds
import IPRADerivations.Analysis.GaussianNamedRealOrderEnvelope

/-!
# Named order for the original Stirling endpoint difference

The finite observation order is preserved by the original sum clock
and then by exact equivalence with the two named A endpoints.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingNamedTelescopeBounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianGammaCanonicalExponent (constantF constant_at constant_regular)
open GaussianNamedPositiveExponentialOrder (realOrder)
open GaussianNamedRealOrderEnvelope (envelope order_from_envelope)
open GaussianNameEquivalence (cross_refl cross_symm)
open GaussianRationalHorner (qzero)
open GaussianStirlingFiniteTelescopeBounds (rows sum_bounds)
open GaussianStirlingNames (source)
open GaussianStirlingRationalTelescopers (upperDifference)
open GaussianStirlingTelescopeName
  (nameF data endpointData name_at name_regular telescope_cross)
open RationalValueBounds (upper upper_congr upper_mono)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "G" => GaussianNamedDifference.nameF GaussianStirlingNames.nameF GaussianStirlingNames.nameF

def allRows (a b : PTm n) : Fm PTm n := .all (rows (var 0) (Syn.shift a) (Syn.shift b))
def endpointBounds (N a b : PTm n) : Fm PTm n :=
  realOrder constantF G qzero (endpointData N a b) ⋏
    realOrder G constantF (endpointData N a b) (upperDifference a b N)

@[simp] theorem subst_allRows {l : ℕ} (σ : Fin n → PTm l) (a b : PTm n) :
    (allRows a b).subst σ = allRows (Syn.subst σ a) (Syn.subst σ b) := by simp [allRows,Syn.subst_shift,Syn.shift_subst]
@[simp] theorem subst_endpointBounds {l : ℕ} (σ : Fin n → PTm l) (N a b : PTm n) :
    (endpointBounds N a b).subst σ = endpointBounds (Syn.subst σ N) (Syn.subst σ a) (Syn.subst σ b) := by
  simp [endpointBounds]

theorem rows_at (p a b : PTm n) (h : Γ ⊢[PRAAx] allRows a b) : Γ ⊢[PRAAx] rows p a b := by
  simpa only [allRows,GaussianStirlingFiniteTelescopeBounds.subst_rows,Syn.subst_var,
    Syn.inst_zero,Syn.subst_inst_shift] using h.allE p

theorem name_bounds_at (p N a b : PTm n) (ha : Γ ⊢[PRAAx] le one a) (h : Γ ⊢[PRAAx] allRows a b) :
    Γ ⊢[PRAAx] upper (fstT (ap2 constantF p qzero)) (fstT (ap2 nameF p (data N a b))) N (unit p) ⋏
      upper (fstT (ap2 nameF p (data N a b))) (fstT (ap2 constantF p (upperDifference a b N))) N (unit p) := by
  let q := GaussianFastValueCut.exponent N p
  have m := GaussianExponentialReference.unit_monotone (Γ := Γ) (le_add_right p (GaussianFastValueCut.normalizer N))
  have d := mul_le_mul_right N m
  have c := le_congr (mul_comm _ _) (mul_comm _ _) d
  have sum := sum_bounds q N a b ha (rows_at q a b h)
  have e := congrFst (name_at (Γ := Γ) p N a b).eqSymm
  exact .andI
    (upper_congr (congrFst (constant_at (Γ := Γ) p qzero).eqSymm) e (.eqRefl _) (.eqRefl _)
      (upper_mono _ _ _ _ _ _ (unit_positive q) sum.andE₁ c))
    (upper_congr e (congrFst (constant_at (Γ := Γ) p (upperDifference a b N)).eqSymm) (.eqRefl _) (.eqRefl _)
      (upper_mono _ _ _ _ _ _ (unit_positive q) sum.andE₂ c))

theorem named_telescope_bounds (N a b : PTm n) (hs : Γ ⊢[PRAAx] source a b) (h : Γ ⊢[PRAAx] allRows a b) :
    Γ ⊢[PRAAx] endpointBounds N a b := by
  let sh (u : PTm n) := Syn.shift u
  let Δ := Γ.map Fm.shift
  have h' : Δ ⊢[PRAAx] allRows (sh a) (sh b) := by simpa [Fm.shift,Syn.shift,sh,Δ] using h.shift
  have ha' : Δ ⊢[PRAAx] le one (sh a) := by simpa [Fm.shift,Syn.shift,sh,Δ,one] using hs.andE₁.shift
  have lower : Γ ⊢[PRAAx] envelope constantF nameF qzero (data N a b) N := by
    refine .allI ?_
    simpa [envelope,Syn.shift,sh,Δ] using (name_bounds_at (var 0) (sh N) (sh a) (sh b) ha' h').andE₁
  have upper : Γ ⊢[PRAAx] envelope nameF constantF (data N a b) (upperDifference a b N) N := by
    refine .allI ?_
    simpa [envelope,Syn.shift,sh,Δ] using (name_bounds_at (var 0) (sh N) (sh a) (sh b) ha' h').andE₂
  have C₀ := constant_regular (Γ := Γ) qzero
  have C₁ := constant_regular (Γ := Γ) (upperDifference a b N)
  have H := name_regular N a b hs
  have E := telescope_cross N a b hs
  exact .andI
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_refl _ _ C₀) E
      (order_from_envelope _ _ _ _ N C₀ H lower))
    (GaussianNamedRealOrderTransport.transport _ _ _ _ _ _ _ _ (cross_symm _ _ _ _ E) (cross_refl _ _ C₁)
      (order_from_envelope _ _ _ _ N H C₁ upper))

theorem actual_Stirling_endpoint_bounds_from_observations_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
    (source (var 0) (var 1) ⟶ allRows (var 0) (var 1) ⟶ endpointBounds (var 2) (var 0) (var 1)) :=
  closeUniv 3 (.impI (.impI (named_telescope_bounds _ _ _ Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianStirlingNamedTelescopeBounds
