import IPRADerivations.Analysis.GaussianBinetSecondWeightedSinePrefix

/-!
# Retiming the original frozen decay quadrature

The frozen Pi value and all physical time tags remain fixed. This
comparison allows the angular precision to precede the later clock
required by the mesh and geometric tail estimates.
-/

set_option autoImplicit false
set_option maxHeartbeats 850000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayRetiming

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetSecondDecayPointwise (angle fullDecay row frozenPiNumerator)
open GaussianBinetSecondDecayGrid (rowBody rowData row_at subst_rowData)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianEulerIntegrandName (decayF decayData decayPoint)
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalRiemannRefinement (termsDistance sum_distance)
open GaussianStirlingConstant (piDenominator)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero succ)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "Angle" => GaussianBinetArctangentQuadrature.nameF
local notation "atanData" => GaussianBinetArctangentQuadrature.data
local notation "DecayGrid" => GaussianBinetSecondDecayGrid.value
local notation "Frozen" => GaussianBinetBoseFrozenMatrix.value
local notation "frozenData" => GaussianBinetSecondDecaySharedTail.data
local notation "Sine" => GaussianBinetSecondWeightedSinePrefix.value

def cost (K T : PTm n) : PTm n := num 4+two*(K*T)

@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (K T : PTm n) :
    Syn.subst σ (cost K T) = cost (Syn.subst σ K) (Syn.subst σ T) := by simp [cost,two]

theorem row_distance (p q X Y D sign R a b T H J K : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hb : Γ ⊢[PRAAx] le one b)
    (ha : Γ ⊢[PRAAx] le a (b*T)) (hJ : Γ ⊢[PRAAx] le one J)
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (row q X Y D sign a b H J) (row p X Y D sign a b H J)
      (cost K T) (unit p) := by
  let c := two*(a*H)
  let e := b*J
  let d := decayData c e
  let z := decayPoint c e
  let x := atanData X Y D sign a b
  let f := angle q X Y D sign a b
  let g := angle p X Y D sign a b
  let u := fullDecay q a b H J
  let v := fullDecay p a b H J
  have hp := unit_positive (Γ := Γ) p
  have hq := unit_positive (Γ := Γ) q
  have he := positive_product _ _ hb hJ
  have regular := GaussianBinetArctangentQuadrature.regular X Y D sign a b hz.andE₁ hb
  have arctan : Γ ⊢[PRAAx] distanceBounded f g two (unit p) :=
    GaussianNamedProductObservationBound.late_observation Angle x p q regular hpq
  have decayRegular : Γ ⊢[PRAAx] GaussianEuclideanDistanceName.pointCN decayF d :=
    GaussianRadiusExponentialName.name_regular constantF (GaussianNameBounds.U constantF z) z
      (GaussianGammaFiniteApproximantName.exponential_input _ _ (constant_regular z))
  have decay : Γ ⊢[PRAAx] distanceBounded u v two (unit p) :=
    GaussianNamedProductObservationBound.late_observation decayF d p q decayRegular hpq
  have boundG : Γ ⊢[PRAAx] bounded g (K*T) one := by
    apply bounded_radius_mono _ _ _ _ _ (positive_product _ _ hb hz.andE₁.andE₁.andE₁) (le_refl one) ?_
      (GaussianBinetArctangentQuadratureBound.name_bound p X Y D sign a b hz.andE₁ hb)
    ipra_le 𝔞(D)*sl ha+𝔞(T)*𝔞(b)*sl hK
  have boundU : Γ ⊢[PRAAx] bounded u two one :=
    bounded_radius_mono _ _ _ _ _ hq (le_refl one) (by ipra_le sl hq)
      (GaussianBinetLaplaceScalarMajorant.original_decay_unit_bound q c e he)
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold cost; ipra_ring) (.eqRefl _)
    (GaussianNameArithmetic.product_distance f g u v two two (unit p) two (K*T) hp arctan decay boundU boundG)

private theorem grid_cell (j p q M T H J X Y D sign R K : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hM : Γ ⊢[PRAAx] le one M)
    (hj : Γ ⊢[PRAAx] le j M) (hJ : Γ ⊢[PRAAx] le one J)
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (inst2 rowBody j (rowData q M T H J X Y D sign))
      (inst2 rowBody j (rowData p M T H J X Y D sign)) (cost K T) (unit p) := by
  have tag : Γ ⊢[PRAAx] le (T*j) (M*T) := le_congr (mul_comm j T) (.eqRefl _) (mul_le_mul_right T hj)
  exact distance_congr (row_at j q M T H J X Y D sign).eqSymm (row_at j p M T H J X Y D sign).eqSymm
    (.eqRefl _) (.eqRefl _) (row_distance p q X Y D sign R (T*j) M T H J K hz hM tag hJ hK hpq)

theorem grid_distance (p q M T H J X Y D sign R K : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hM : Γ ⊢[PRAAx] le one M)
    (hJ : Γ ⊢[PRAAx] le one J) (hK : Γ ⊢[PRAAx] le D (K*X)) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (DecayGrid q M T H J X Y D sign) (DecayGrid p M T H J X Y D sign)
      (T*cost K T) (unit p) := by
  let x := rowData q M T H J X Y D sign
  let y := rowData p M T H J X Y D sign
  have rows : Γ ⊢[PRAAx] termsDistance rowBody rowBody M x y (cost K T) (unit p) := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let Δ := lt (var 0) (s M) :: Γ.map Fm.shift
    have zs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) := by simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift.wk
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift] using hM.shift.wk
    have js : Δ ⊢[PRAAx] le one (s J) := by simpa [Δ,s,Fm.shift,Syn.shift] using hJ.shift.wk
    have ks : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift.wk
    have cs : Δ ⊢[PRAAx] le (s p) (s q) := by simpa [Δ,s,Fm.shift,Syn.shift] using hpq.shift.wk
    simpa only [Δ,s,x,y,Syn.shift,subst_rowData,subst_cost,GaussianCoefficientNameBounds.subst_unit] using
      grid_cell (var 0) (s p) (s q) (s M) (s T) (s H) (s J) (s X) (s Y) (s D) (s sign) (s R) (s K)
        zs ms (le_of_lt Prf.hyp0) js ks cs
  exact distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (one_mul _)
    (GaussianCompactScalarMajorant.common_mesh_distance rowBody rowBody M x y T one _ _ hM (le_refl one)
      (unit_positive p) rows)

theorem prefix_distance (p q k I M T X Y D sign R K : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hM : Γ ⊢[PRAAx] le one M)
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (Frozen q k I M X Y D sign zero T one) (Frozen p k I M X Y D sign zero T one)
      (I*(T*cost K T)) (unit p) := by
  let f := GaussianBinetSecondDecayFrozenTail.body
  let x := frozenData q M T k zero X Y D sign
  let y := frozenData p M T k zero X Y D sign
  have rows : Γ ⊢[PRAAx] termsDistance f f I x y (T*cost K T) (unit p) := by
    refine .allI (.impI ?_)
    let s (z : PTm n) := Syn.shift z
    let j : PTm (n+1) := var 0
    let Δ := lt j (s I) :: Γ.map Fm.shift
    let H := frozenPiNumerator (succ (zero+j)) (s k)
    let J := piDenominator (s k)
    have zs : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) := by simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift.wk
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift] using hM.shift.wk
    have ks : Δ ⊢[PRAAx] le (s D) (s K*s X) := by simpa [Δ,s,Fm.shift,Syn.shift] using hK.shift.wk
    have cs : Δ ⊢[PRAAx] le (s p) (s q) := by simpa [Δ,s,Fm.shift,Syn.shift] using hpq.shift.wk
    have rowRate := grid_distance (s p) (s q) (s M) (s T) H J (s X) (s Y) (s D) (s sign) (s R) (s K)
      zs ms (GaussianBinetKernelPi.denominator_positive (s k)) ks cs
    simpa only [Δ,s,j,f,x,y,Syn.shift,GaussianBinetSecondDecaySharedTail.subst_data,subst_cost,
      PTm.subst_mul,GaussianCoefficientNameBounds.subst_unit,ConciseIPRA.PTm.subst_zero] using
      distance_congr (GaussianBinetSecondDecaySharedTail.row_at (Γ := Δ) j (s q) (s M) (s T) (s k) zero (s X) (s Y) (s D) (s sign)).eqSymm
        (GaussianBinetSecondDecaySharedTail.row_at (Γ := Δ) j (s p) (s M) (s T) (s k) zero (s X) (s Y) (s D) (s sign)).eqSymm
        (.eqRefl _) (.eqRefl _) rowRate
  exact distance_congr (GaussianBinetBoseFrozenOrigin.zero_origin q k I M X Y D sign T).eqSymm
    (GaussianBinetBoseFrozenOrigin.zero_origin p k I M X Y D sign T).eqSymm
    (.eqRefl _) (.eqRefl _) (sum_distance f f I x y _ _ (unit_positive p) rows)

theorem scheduled_prefix_distance (p q k I M T X Y D sign R K : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hM : Γ ⊢[PRAAx] le one M)
    (hK : Γ ⊢[PRAAx] le D (K*X)) (hpq : Γ ⊢[PRAAx] le p q) :
    Γ ⊢[PRAAx] distanceBounded (Frozen q k I M X Y D sign zero T one) (Sine p k I M T X Y D sign R K)
      (I*(T*(num 24+num 4*K*T))) (unit p) := by
  have before := prefix_distance p q k I M T X Y D sign R K hz hM hK hpq
  have after := GaussianBinetSecondWeightedSinePrefix.prefix_error p k I M T X Y D sign R K hz hM hK
  exact distance_congr (.eqRefl _) (.eqRefl _) (by unfold cost GaussianBinetSecondWeightedSinePoint.cost; ipra_ring)
    (.eqRefl _) (distance_triangle_same _ _ _ _ _ _ (unit_positive p) before after)

end LeanProofs.IPRA.Analysis.GaussianBinetSecondDecayRetiming
