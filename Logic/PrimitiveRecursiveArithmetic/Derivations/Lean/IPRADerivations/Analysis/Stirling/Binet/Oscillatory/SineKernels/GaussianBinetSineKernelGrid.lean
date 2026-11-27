import IPRADerivations.Analysis.Stirling.Binet.Oscillatory.SineKernels.GaussianBinetSineKernelFrequency
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.FrozenKernels.GaussianBinetFrozenKernelRectangle
import IPRADerivations.Analysis.Stirling.Binet.SecondFormula.WeightedSine.Grid.GaussianBinetSecondWeightedSineTranspose

/-!
# Compare the exact transposed column sum with the weighted kernel rows

The positive suffix retains the original mesh weight. The uniform
column comparison is summed on that suffix using the full mesh size
as a bound on the number of retained frequencies.
-/

set_option autoImplicit false
set_option maxHeartbeats 780000

namespace LeanProofs.IPRA.Analysis.GaussianBinetSineKernelGrid

open_ipra
open GaussianBinetSineKernelFrequency (angularCost scheduled_frequency_error subst_angularCost)
open GaussianBinetSineStripCut (cutoff prefix_admission)
open GaussianBinetBoseFrozenMatrix (subst_frozenPiNumerator subst_piDenominator)
open GaussianBinetSecondDecayPointwise (frozenPiNumerator)
open GaussianBinetSecondWeightedSineTranspose
  (transposedBody transposedData transposedValue transposed_at)
open GaussianBinetFrozenKernelRectangle (matrix cell_at)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianLogGammaEulerResidualDomain (source)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono)
open GaussianRationalFiniteSum (sum)
open GaussianRationalFubini (row rowBody row_entry)
open GaussianRationalHorner (positive_product qmul)
open GaussianRationalMetric (distanceBounded)
open GaussianRationalReciprocal (bounded_product bound_congr)
open GaussianRationalRiemannRefinement (termsDistance sum_distance weight weight_bound)
open GaussianStirlingConstant (piDenominator)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk _ t)
local notation "kernelData" => GaussianBinetFrozenKernelRectangle.data

def errorNumerator (s I E S T : PTm n) : PTm n :=
  angularCost I E S T*unit T+num 160*E*unit s

ipra_subst errorNumerator

def kernelRow (i s k N S cut X Y D sign R : PTm n) : PTm n :=
  qmul (weight S one N) (row matrix i (monus N cut) (kernelData s k N S cut X Y D sign R))

ipra_subst kernelRow [one]

private theorem step_error (j i s k I N E L M T X Y D sign R : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (hI : Γ ⊢[PRAAx] le (succ i) I)
    (hS : Γ ⊢[PRAAx] le one (D*L)) (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hmin : Γ ⊢[PRAAx] le (two*((D*L)*E)) N) (hc : Γ ⊢[PRAAx] le one (cutoff N (D*L) E))
    (hj : Γ ⊢[PRAAx] lt j (monus N (cutoff N (D*L) E)))
    (hT : Γ ⊢[PRAAx] le T (s+N)) (hM : Γ ⊢[PRAAx] le ((num 10*I+D*L)*T) M)
    (hP : Γ ⊢[PRAAx] le (unit (s+N)) M) :
    let S := D*L
    let c := cutoff N S E
    Γ ⊢[PRAAx] distanceBounded
      (inst2 transposedBody j (transposedData s M T (frozenPiNumerator (succ i) k) (piDenominator k) X Y D sign R L N c))
      (inst2 (rowBody matrix) j (pairT i (kernelData s k N S c X Y D sign R)))
      (errorNumerator s I E S T) (unit s*unit T) := by
  let S := D*L
  let c := cutoff N S E
  have cut := prefix_admission N S E hS hE
  have last : Γ ⊢[PRAAx] le (c+j) N :=
    le_congr (.eqRefl _) (eq_add_of_le cut.andE₁).eqSymm (add_le_add₂ (le_refl c) (le_of_lt hj))
  have raw := scheduled_frequency_error (c+j) s k (succ i) I X Y D sign R S N T M E
    hz (zero_lt_succ i) hI hS hN hE hmin (le_add_right c j) last hT hM hP
  have left := transposed_at (Γ := Γ) j s k (succ i) M T X Y D sign R L N c hc
  have right := (row_entry (Γ := Γ) matrix i j (kernelData s k N S c X Y D sign R)).eqTrans
    (cell_at i j s k N S c X Y D sign R)
  exact distance_congr left.eqSymm right.eqSymm (.eqRefl _) (.eqRefl _) raw

theorem row_error (i s k I N E L M T X Y D sign R : PTm n)
    (hz : Γ ⊢[PRAAx] source X Y D sign R)
    (hI : Γ ⊢[PRAAx] le (succ i) I)
    (hS : Γ ⊢[PRAAx] le one (D*L)) (hN : Γ ⊢[PRAAx] le one N) (hE : Γ ⊢[PRAAx] le one E)
    (hmin : Γ ⊢[PRAAx] le (two*((D*L)*E)) N) (hc : Γ ⊢[PRAAx] le one (cutoff N (D*L) E))
    (hT : Γ ⊢[PRAAx] le T (s+N)) (hM : Γ ⊢[PRAAx] le ((num 10*I+D*L)*T) M)
    (hP : Γ ⊢[PRAAx] le (unit (s+N)) M) :
    let S := D*L
    let c := cutoff N S E
    Γ ⊢[PRAAx] distanceBounded (transposedValue s M T (frozenPiNumerator (succ i) k) (piDenominator k)
      X Y D sign R L N c) (kernelRow i s k N S c X Y D sign R)
      (S*errorNumerator s I E S T) (unit s*unit T) := by
  let S := D*L
  let c := cutoff N S E
  let m := monus N c
  let H := unit s*unit T
  let F := errorNumerator s I E S T
  let x := transposedData s M T (frozenPiNumerator (succ i) k) (piDenominator k) X Y D sign R L N c
  let y := pairT i (kernelData s k N S c X Y D sign R)
  have rows : Γ ⊢[PRAAx] termsDistance transposedBody (rowBody matrix) m x y F H := by
    refine .allI (.impI ?_)
    let t (z : PTm n) := Syn.shift z
    let Δ := lt (var 0) (t m)::Γ.map Fm.shift
    have zs : Δ ⊢[PRAAx] source (t X) (t Y) (t D) (t sign) (t R) := by simpa [Δ,t,Fm.shift,Syn.shift] using hz.shift.wk
    have is : Δ ⊢[PRAAx] le (succ (t i)) (t I) := by simpa [Δ,t,Fm.shift,Syn.shift] using hI.shift.wk
    have ss : Δ ⊢[PRAAx] le one (t D*t L) := by simpa [Δ,t,S,Fm.shift,Syn.shift,one] using hS.shift.wk
    have ns : Δ ⊢[PRAAx] le one (t N) := by simpa [Δ,t,Fm.shift,Syn.shift,one] using hN.shift.wk
    have es : Δ ⊢[PRAAx] le one (t E) := by simpa [Δ,t,Fm.shift,Syn.shift,one] using hE.shift.wk
    have ls : Δ ⊢[PRAAx] le (two*((t D*t L)*t E)) (t N) := by simpa [Δ,t,Fm.shift,Syn.shift,two] using hmin.shift.wk
    have cs : Δ ⊢[PRAAx] le one (cutoff (t N) (t D*t L) (t E)) := by
      simpa [Δ,t,Fm.shift,Syn.shift,one] using hc.shift.wk
    have js : Δ ⊢[PRAAx] lt (var 0) (monus (t N) (cutoff (t N) (t D*t L) (t E))) := by
      simpa [Δ,t,m,c,S,Syn.shift] using (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (t m))
    have ts : Δ ⊢[PRAAx] le (t T) (t s+t N) := by simpa [Δ,t,Fm.shift,Syn.shift] using hT.shift.wk
    have ms : Δ ⊢[PRAAx] le ((num 10*t I+t D*t L)*t T) (t M) := by
      simpa [Δ,t,Fm.shift,Syn.shift] using hM.shift.wk
    have ps : Δ ⊢[PRAAx] le (unit (t s+t N)) (t M) := by simpa [Δ,t,Fm.shift,Syn.shift] using hP.shift.wk
    simpa only [Δ,t,x,y,F,H,S,c,Syn.shift,GaussianBinetSecondWeightedSineTranspose.subst_transposedData,
      GaussianBinetFrozenKernelRectangle.subst_data,GaussianBinetSineStripCut.subst_cutoff,
      subst_pairT,subst_frozenPiNumerator,subst_piDenominator,ConciseIPRA.PTm.subst_succ,
      PTm.subst_mul,subst_errorNumerator,GaussianCoefficientNameBounds.subst_unit] using
      step_error (var 0) (t i) (t s) (t k) (t I) (t N) (t E) (t L) (t M) (t T) (t X) (t Y)
        (t D) (t sign) (t R) zs is ss ns es ls cs js ts ms ps
  let f := sum transposedBody m x
  let g := sum (rowBody matrix) m y
  let w := weight S one N
  have hH := positive_product (Γ := Γ) _ _ (unit_positive s) (unit_positive T)
  have hDen := positive_product _ _ (le_refl one) hN
  have diff := sum_distance _ _ _ _ _ _ _ hH rows
  have bound := bounded_product w _ S (one*N) (m*F) H hDen hH (weight_bound S one N (le_refl one) hN) diff
  have raw := bound_congr (GaussianRationalRoundedPower.multiplication_difference w f g).eqSymm (.eqRefl _) (.eqRefl _) bound
  have leN : Γ ⊢[PRAAx] le m N :=
    le_congr (.eqRefl _) (eq_add_of_le (prefix_admission N S E hS hE).andE₁).eqSymm (le_add_left m c)
  apply distance_radius_mono _ _ _ _ _ _ (positive_product _ _ hDen hH) hH ?_ raw
  change Γ ⊢[PRAAx] le ((S*(m*F))*H) ((S*F)*((one*N)*H))
  ipra_le 𝔞(S*F*H)*sl leN

end LeanProofs.IPRA.Analysis.GaussianBinetSineKernelGrid
