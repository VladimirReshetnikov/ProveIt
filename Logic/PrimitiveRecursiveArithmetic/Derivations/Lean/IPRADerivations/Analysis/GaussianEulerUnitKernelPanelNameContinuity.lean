import IPRADerivations.Analysis.GaussianEulerUnitKernelPanelContinuity
import IPRADerivations.Analysis.GaussianNamedLipschitzRate

/-!
# Endpoint continuity of the actual original ordinary compact names

Both panels use their own original names and packed interval data. Their
same-query schedules coincide because the common native compact and
Lipschitz constant coincide. Actual finite quadrature continuity and the
two genuine regular names remove only auxiliary observation error.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelPanelNameContinuity

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerUnitKernelPanelContinuity (source leading)
open GaussianEulerUnitKernelCompactName (nameF data)
open GaussianCompactRiemannName (mesh precision)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianNamedInverseRate (independentRate rateNumerator rateDenominator)
open GaussianNamedLipschitzRate (diagonalNumerator diagonalDenominator)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

private theorem diagonal_budget (A M U V : PTm n) (h : Γ ⊢[PRAAx] le U V) : Γ ⊢[PRAAx]
    le ((A*V*V+M*(V+V))*(M*U)) ((A*U+two*M)*(M*V*V)) := by
  ipra_le (2*𝔞 M^2*𝔞 V)*sl h

theorem original_diagonal (t z R B a C b D M G A : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C b D M G A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF t (data z R B a C M G)) (ap2 nameF t (data z R B b D M G))
      (diagonalNumerator (leading R G A) M two t) (diagonalDenominator M t) := by
  let L := GaussianEulerUnitKernelCompactName.lipschitz R G
  let H := mesh t L one
  let q := precision t one
  have hM := hs.andE₁.andE₂.andE₁
  have hQ := positive_product _ _ (positive_product _ _ hM (unit_positive (Γ := Γ) q)) (unit_positive q)
  have hD := positive_product _ _ hM (unit_positive (Γ := Γ) t)
  have grow : Γ ⊢[PRAAx] le (unit t) (unit q) :=
    GaussianExponentialReference.unit_monotone (le_of_eq_add (d := one+num 6) (by dsimp only [q,precision]; ipra_ring))
  have raw := GaussianEulerUnitKernelPanelContinuity.original_same_count_bound q q H z R B a C b D M G A hs
    (GaussianCompactRiemannName.mesh_positive t L one)
  have actual := distance_congr (GaussianEulerUnitKernelCompactName.name_at t z R B a C M G).eqSymm
    (GaussianEulerUnitKernelCompactName.name_at t z R B b D M G).eqSymm (.eqRefl _) (.eqRefl _) raw
  exact distance_radius_mono _ _ _ _ _ _ hQ hD (diagonal_budget (leading R G A) M (unit t) (unit q) grow) actual

theorem original_rate (z R B a C b D M G A : PTm n) (hs : Γ ⊢[PRAAx] source z R B a C b D M G A) : Γ ⊢[PRAAx]
    independentRate nameF nameF (data z R B a C M G) (data z R B b D M G) (leading R G A) M := by
  refine GaussianNamedLipschitzRate.independent_rate nameF nameF (data z R B a C M G) (data z R B b D M G)
    (leading R G A) M two hs.andE₁.andE₂.andE₁
    (GaussianEulerUnitKernelCompactName.name_regular z R B a C M G hs.andE₁)
    (GaussianEulerUnitKernelCompactName.name_regular z R B b D M G hs.andE₂.andE₁) (.allI ?_)
  let s (u : PTm n) := Syn.shift u
  have hss : Γ.map Fm.shift ⊢[PRAAx] source (s z) (s R) (s B) (s a) (s C) (s b) (s D) (s M) (s G) (s A) := by
    simpa [Fm.shift,Syn.shift,s] using hs.shift
  simpa only [GaussianNamedLipschitzRate.diagonalEnvelope,GaussianEulerUnitKernelCompactName.subst_data,
    GaussianEulerUnitKernelPanelContinuity.subst_leading,ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,Syn.shift,s] using
    original_diagonal (var 0) (s z) (s R) (s B) (s a) (s C) (s b) (s D) (s M) (s G) (s A) hss

theorem original_observations (p q z R B a C b D M G A : PTm n)
    (hs : Γ ⊢[PRAAx] source z R B a C b D M G A) : Γ ⊢[PRAAx]
    distanceBounded (ap2 nameF p (data z R B a C M G)) (ap2 nameF q (data z R B b D M G))
      (rateNumerator (leading R G A) M p q) (rateDenominator M p q) :=
  GaussianNamedInverseRate.rate_at _ _ _ _ _ _ p q (original_rate z R B a C b D M G A hs)

theorem actual_original_unit_kernel_panel_name_continuity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 10
    (source (var 0) (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) (var 8) (var 9) ⟶
      independentRate nameF nameF (data (var 0) (var 1) (var 2) (var 3) (var 4) (var 7) (var 8))
        (data (var 0) (var 1) (var 2) (var 5) (var 6) (var 7) (var 8))
        (leading (var 1) (var 8) (var 9)) (var 7)) :=
  closeUniv 10 (.impI (original_rate _ _ _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerUnitKernelPanelNameContinuity
