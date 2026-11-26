import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.GaussianBinetSecondWeightedSineTranspose

/-!
# Discarding the initial frequency strip of the weighted sine grid

The original row estimate includes the removable time-zero value.
Multiplication by the actual frozen exponential and integration on
the original time mesh preserve a uniform width bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSineSuffix

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianBinetArctangentSineUniform (clock cutoff count cutoff_positive count_dominates)
open GaussianBinetSecondWeightedSineTranspose
  (suffixBody suffixData suffixValue transposedValue suffix_at scaled_transpose)
open GaussianBinetSecondDecayPointwise (fullDecay)
open GaussianCoefficientNameBounds (unit unit_positive bounded_radius_mono)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (bounded distanceBounded)
open GaussianRationalPowerAlgebra (qmul_commutative)
open GaussianRationalRiemannRefinement (termsDistance)
open LeanProofs.IPRA.PTm (num)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "SineGrid" => GaussianBinetSecondWeightedSineGrid.value
local notation "Sine" => GaussianBinetOscillatorySineRectangle.value
local notation "Suffix" => GaussianBinetOscillatorySineSmallStrip.suffixValue

def cost (T : PTm n) : PTm n := num 16*(T+one)

@[simp] theorem subst_cost {m : ℕ} (σ : Fin n → PTm m) (T : PTm n) :
    Syn.subst σ (cost T) = cost (Syn.subst σ T) := by simp [cost,one]

def window (q D R T K cut E : PTm n) : Fm PTm n :=
  le cut (count q D R T K) ⋏ (le one E ⋏ le (((D*cutoff q T K)*cut)*E) (count q D R T K))

@[simp] theorem subst_window {m : ℕ} (σ : Fin n → PTm m) (q D R T K cut E : PTm n) :
    (window q D R T K cut E).subst σ =
      window (Syn.subst σ q) (Syn.subst σ D) (Syn.subst σ R) (Syn.subst σ T)
        (Syn.subst σ K) (Syn.subst σ cut) (Syn.subst σ E) := by simp [window,one]

private theorem cell_error (j q M T H J X Y D sign R K cut E : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hM : Γ ⊢[PRAAx] le one M) (hJ : Γ ⊢[PRAAx] le one J)
    (hw : Γ ⊢[PRAAx] window q D R T K cut E) (hj : Γ ⊢[PRAAx] lt j M) :
    let p := clock q D R T K
    let L := cutoff q T K
    let N := count q D R T K
    Γ ⊢[PRAAx] distanceBounded
      (inst2 GaussianBinetSecondWeightedSineGrid.body j (GaussianBinetSecondWeightedSineGrid.data q M T H J X Y D sign R K))
      (inst2 suffixBody j (suffixData p M T H J X Y D sign R L N cut)) (cost T) E := by
  let p := clock q D R T K
  let L := cutoff q T K
  let N := count q D R T K
  let a := T*j
  let x := Sine p X Y D sign a M R T L N
  let y := Suffix p X Y D sign a M R T L N cut
  let e := fullDecay (p+N) a M H J
  let U := unit p
  let E' := E*(M*U)
  let A' := GaussianBinetOscillatorySineSmallStrip.numerator p a M
  have hE := hw.andE₂.andE₁
  have hU := unit_positive (Γ := Γ) p
  have hpN := unit_positive (Γ := Γ) (p+N)
  have den : Γ ⊢[PRAAx] le one E' := positive_product _ _ hE (positive_product _ _ hM hU)
  have ha : Γ ⊢[PRAAx] le a (M*T) :=
    le_congr (mul_comm j T) (.eqRefl _) (le_mul_mono (le_of_lt hj) (le_refl T))
  have hN : Γ ⊢[PRAAx] le one N := le_trans hU (count_dominates q D R T K).andE₂
  have cut_err := GaussianBinetOscillatorySineSmallStrip.discard_prefix_error p X Y D sign a M R T L N cut E
    hz hM hN (cutoff_positive q T K) ha hw.andE₁ hE hw.andE₂.andE₂
  have decay : Γ ⊢[PRAAx] bounded e two one :=
    bounded_radius_mono _ _ _ _ _ hpN (le_refl one) (by ipra_le sl hpN)
      (GaussianBinetLaplaceScalarMajorant.original_decay_unit_bound (p+N) (two*(a*H)) (M*J)
        (positive_product _ _ hM hJ))
  have raw : Γ ⊢[PRAAx] distanceBounded (qmul x e) (qmul y e) (two*A') E' :=
    distance_congr (qmul_commutative e x) (qmul_commutative e y) (.eqRefl _) (.eqRefl _)
      (GaussianApproximateInverseDistance.multiply_distance e x y two A' E' den decay cut_err)
  have budget : Γ ⊢[PRAAx] le ((two*A')*E) (cost T*E') := by
    dsimp only [cost,A',E',GaussianBinetOscillatorySineSmallStrip.numerator]
    ipra_le 16*𝔞(E)*𝔞(U)*sl ha+16*𝔞(E)*𝔞(M)*sl hU
  exact distance_congr (GaussianBinetSecondWeightedSineGrid.row_at j q M T H J X Y D sign R K).eqSymm
    (suffix_at j p M T H J X Y D sign R L N cut).eqSymm (.eqRefl _) (.eqRefl _)
    (distance_radius_mono _ _ _ _ _ _ den hE budget raw)

theorem grid_error (q M T H J X Y D sign R K cut E : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hM : Γ ⊢[PRAAx] le one M) (hJ : Γ ⊢[PRAAx] le one J)
    (hw : Γ ⊢[PRAAx] window q D R T K cut E) :
    let p := clock q D R T K
    let L := cutoff q T K
    let N := count q D R T K
    Γ ⊢[PRAAx] distanceBounded (SineGrid q M T H J X Y D sign R K)
      (suffixValue p M T H J X Y D sign R L N cut) (T*cost T) E := by
  let p := clock q D R T K
  let L := cutoff q T K
  let N := count q D R T K
  let f := GaussianBinetSecondWeightedSineGrid.body
  let x := GaussianBinetSecondWeightedSineGrid.data q M T H J X Y D sign R K
  let y := suffixData p M T H J X Y D sign R L N cut
  have rows : Γ ⊢[PRAAx] termsDistance f suffixBody M x y (cost T) E := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let Δ := lt (var 0) (s M)::Γ.map Fm.shift
    have z : Δ ⊢[PRAAx] source (s X) (s Y) (s D) (s sign) (s R) :=
      by simpa [Δ,s,Fm.shift,Syn.shift] using hz.shift.wk
    have ms : Δ ⊢[PRAAx] le one (s M) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hM.shift.wk
    have js : Δ ⊢[PRAAx] le one (s J) := by simpa [Δ,s,Fm.shift,Syn.shift,one] using hJ.shift.wk
    have ws : Δ ⊢[PRAAx] window (s q) (s D) (s R) (s T) (s K) (s cut) (s E) :=
      by simpa only [Δ,s,Fm.shift,Syn.shift,subst_window] using hw.shift.wk
    simpa only [s,Δ,x,y,p,L,N,f,Syn.shift,GaussianBinetSecondWeightedSineGrid.subst_data,
      GaussianBinetSecondWeightedSineTranspose.subst_suffixData,GaussianBinetArctangentSineUniform.subst_clock,
      GaussianBinetArctangentSineUniform.subst_cutoff,GaussianBinetArctangentSineUniform.subst_count,subst_cost] using
      cell_error (var 0) (s q) (s M) (s T) (s H) (s J) (s X) (s Y) (s D) (s sign) (s R) (s K) (s cut) (s E)
        z ms js ws Prf.hyp0
  exact distance_congr (.eqRefl _) (.eqRefl _) (.eqRefl _) (one_mul E)
    (GaussianCompactScalarMajorant.common_mesh_distance f suffixBody M x y T one (cost T) E
      hM (le_refl one) hw.andE₂.andE₁ rows)

theorem scaled_grid_error (q M T H J X Y D sign R K cut E : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R) (hM : Γ ⊢[PRAAx] le one M) (hJ : Γ ⊢[PRAAx] le one J)
    (hw : Γ ⊢[PRAAx] window q D R T K cut E) :
    let p := clock q D R T K
    let L := cutoff q T K
    let N := count q D R T K
    Γ ⊢[PRAAx] distanceBounded (qmul (fraction two one) (SineGrid q M T H J X Y D sign R K))
      (transposedValue p M T H J X Y D sign R L N cut) (two*(T*cost T)) E := by
  have scale := GaussianEulerExponentCompactBounds.fraction_bound (Γ := Γ) two one two (le_refl one)
    (le_congr (.eqRefl _) (by ipra_ring) (le_refl two))
  exact distance_congr (.eqRefl _) (scaled_transpose (clock q D R T K) M T H J X Y D sign R (cutoff q T K) (count q D R T K) cut)
    (.eqRefl _) (.eqRefl _) (GaussianApproximateInverseDistance.multiply_distance _ _ _ _ _ _
      hw.andE₂.andE₁ scale (grid_error q M T H J X Y D sign R K cut E hz hM hJ hw))

theorem actual_second_Binet_positive_suffix_strip_error_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 13
      (let q := var 0
       let M := var 1
       let T := var 2
       let H := var 3
       let J := var 4
       let X := var 5
       let Y := var 6
       let D := var 7
       let sign := var 8
       let R := var 9
       let K := var 10
       let cut := var 11
       let E := var 12
       (source X Y D sign R ⋏ le one M) ⋏ (le one J ⋏ window q D R T K cut E) ⟶
         distanceBounded (qmul (fraction two one) (SineGrid q M T H J X Y D sign R K))
           (transposedValue (clock q D R T K) M T H J X Y D sign R (cutoff q T K) (count q D R T K) cut)
           (two*(T*cost T)) E) :=
  closeUniv 13 (.impI (scaled_grid_error _ _ _ _ _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁.andE₁
    Prf.hyp0.andE₁.andE₂ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianBinetSecondWeightedSineSuffix
