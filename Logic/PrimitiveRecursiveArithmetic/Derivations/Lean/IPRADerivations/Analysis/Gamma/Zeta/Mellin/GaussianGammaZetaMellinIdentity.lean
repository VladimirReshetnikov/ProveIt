import IPRADerivations.Analysis.Gamma.Zeta.Dirichlet.GaussianGammaZetaDirichletProduct
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinFiniteDampedComparison
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinFiniteWindowTail
import IPRADerivations.Analysis.Gamma.Zeta.Mellin.Damped.GaussianGammaZetaMellinPoweredCompactProduct

/-!
# The original Gamma–zeta Mellin identity in iPRA

Choose a core window before the finite Dirichlet count. Enlarge it
only after choosing that count. Compare the finite damped integrals
on the two windows using their count-independent exterior bounds.
This separates the compact geometric cutoff from the Euler cutoff
required by each scaled improper row.
-/

set_option autoImplicit false
set_option maxHeartbeats 1400000

namespace LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinIdentity

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianFastValueCut (exponent query_budget)
open GaussianGammaCompactQuadratureBoundary (width)
open GaussianGammaEulerHeadShift (shifted)
open GaussianGammaIntegralCutoffs (etaDen top)
open GaussianGammaZetaDirichletRowDecay (block)
open GaussianGammaZetaMellinFiniteDampedComparison (threshold)
open GaussianGammaZetaMellinFiniteDampedEvaluator (budget evaluatorF)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open GaussianNameEquivalence (crossEquivalent)
open GaussianRationalDistanceOrder (distance_congr distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (distanceBounded)
open RationalValueBounds (positive_cancel)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)
local notation "Source" => GaussianEulerIntegralGammaIdentification.source
local notation "I" => GaussianGammaZetaMellinImproper.nameF
local notation "idat" => GaussianGammaZetaMellinImproper.data
local notation "P" => GaussianGammaZetaDirichletProduct.nameF
local notation "pdat" => GaussianGammaZetaDirichletProduct.data
local notation "F" => GaussianCompactRiemannName.nameF evaluatorF
local notation "Bprod" => GaussianGammaZetaMellinDampedImproper.gammaProductF

theorem independent_observations (p s z R B j : PTm n) (hz : Γ ⊢[PRAAx] Source z R B (succ j)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 I p (idat z R B j)) (ap2 P s (pdat z R B (succ j)))
      (unit p+unit s) (unit p*unit s) := by
  let A := succ j
  let h := p+num 4
  let k := p+num 8
  let c := GaussianGammaZetaMellinImproper.cutoff h R
  let E₀ := etaDen c A R
  let T₀ := top c A R
  let Z := shifted z B
  let R' := R+one
  let C := GaussianGammaZetaDirichletProduct.rateBudget z R B A
  let d := exponent C k
  let N := threshold k R' E₀ T₀+block A d
  let q := GaussianGammaZetaMellinPoweredCompactProduct.panelCutoff k c N Z R' B A A R
  let E := etaDen q A R
  let T := top q A R
  let Q := budget R' E T N
  let W := unit h
  let U := unit k
  let V := unit s
  let J := unit d
  let D := W*U*V
  let L := unit p
  let x := GaussianGammaZetaMellinImproper.value p z R B j
  let a := ap2 F k (GaussianGammaZetaMellinFiniteNested.datum z R B N Q A c)
  let b := ap2 F k (GaussianGammaZetaMellinFiniteNested.datum z R B N Q A q)
  let f := ap2 Bprod k (GaussianGammaZetaDirichletProduct.finiteData N z R B A)
  let y := ap2 P s (pdat z R B A)
  have hA := zero_lt_succ (Γ := Γ) j
  have hQ : Γ ⊢[PRAAx] le N Q :=
    le_of_eq_add (d := N*GaussianGammaZetaMellinDampedPoint.cost R' E T) (by dsimp only [Q,budget]; ipra_ring)
  have later : Γ ⊢[PRAAx] lt c q :=
    GaussianGammaZetaMellinPoweredWindow.later_cutoff c N _ A R' A R
  have hW := unit_positive (Γ := Γ) h
  have hU := unit_positive (Γ := Γ) k
  have hV := unit_positive (Γ := Γ) s
  have hJ := unit_positive (Γ := Γ) d
  have hD := positive_product _ _ (positive_product _ _ hW hU) hV
  have h0 := GaussianGammaZetaMellinCutoffWindows.cutoff_source z R B A c hz.andE₁
  have hfinite := GaussianGammaZetaMellinFiniteDampedComparison.finite_input
    Z R' B N Q one (width c A R) E₀ E₀ T₀ h0 hQ
  have near : Γ ⊢[PRAAx] distanceBounded a x (rateNumerator one U k h) (rateDenominator U k h) :=
    GaussianGammaZetaMellinFiniteDampedComparison.scheduled_observations
      k h k Z R' B N Q one (width c A R) E₀ E₀ T₀ h0 hfinite hQ (le_add_right _ _)
  have nearDen := denominator_positive U k h hU
  have first : Γ ⊢[PRAAx] distanceBounded x a ((U+two*W)*V) D :=
    distance_radius_mono _ _ _ _ _ _ nearDen hD
      (le_of_eq_add (d := zero) (by dsimp only [D,rateNumerator,rateDenominator,U,W]; ipra_ring))
      (distance_symmetric _ _ _ _ nearDen near)
  have tail : Γ ⊢[PRAAx] distanceBounded b a (num 5*U+num 7*W) (W*U) :=
    GaussianGammaZetaMellinFiniteWindowTail.observation_error k h z R B j N c q hz.andE₁ later (le_refl c)
  have tailDen := positive_product W U hW hU
  have second : Γ ⊢[PRAAx] distanceBounded a b ((num 5*U+num 7*W)*V) D :=
    distance_radius_mono _ _ _ _ _ _ tailDen hD
      (le_of_eq_add (d := zero) (by dsimp only [D]; ipra_ring))
      (distance_symmetric _ _ _ _ tailDen tail)
  have wide : Γ ⊢[PRAAx] distanceBounded b f (rateNumerator (num 10) U k k) (rateDenominator U k k) :=
    GaussianGammaZetaMellinPoweredCompactProduct.original_compact_product_observations
      k k k c N Z R' B A A R
      (GaussianGammaZetaDirichletPowerOrder.shifted_source z R B A hz) hA
  have third : Γ ⊢[PRAAx] distanceBounded b f (num 12*W*V) D :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive U k k hU) hD
      (le_of_eq_add (d := zero) (by dsimp only [D,rateNumerator,rateDenominator,U]; ipra_ring)) wide
  have product : Γ ⊢[PRAAx] distanceBounded f y (rateNumerator C J k s) (rateDenominator J k s) :=
    GaussianGammaZetaDirichletProduct.product_observations k s N z R B A d hz (le_add_left _ _)
  have pay : Γ ⊢[PRAAx] le (C*U) J := query_budget C k
  have fourth : Γ ⊢[PRAAx] distanceBounded f y ((two*V+U)*W) D :=
    distance_radius_mono _ _ _ _ _ _ (denominator_positive J k s hJ) hD
      (by
        change Γ ⊢[PRAAx] le ((C*U*V+J*(U+V))*(W*U*V)) (((two*V+U)*W)*(J*U*V))
        ipra_le 𝔞(W*U*V*V)*sl pay)
      product
  have joined : Γ ⊢[PRAAx] distanceBounded x y (num 6*U*V+num 23*W*V+W*U) D :=
    distance_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _)
      (distance_triangle_same _ _ _ _ _ _ hD (distance_triangle_same _ _ _ _ _ _ hD first second)
        (distance_triangle_same _ _ _ _ _ _ hD third fourth))
  have pad (m v : ℕ) (e : Γ ⊢[PRAAx] unit (num m : PTm n) ≐ num v) :
      Γ ⊢[PRAAx] unit (p+num m) ≐ num v*L :=
    ((pw_add two p (num m)).eqTrans (congrMul (.eqRefl _) e)).eqTrans (mul_comm _ _)
  have eW : Γ ⊢[PRAAx] W ≐ num 16*L :=
    pad 4 16 (LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound.pw_num 2 4)
  have eU : Γ ⊢[PRAAx] U ≐ num 256*L :=
    pad 8 256 (LeanProofs.IPRA.DiophantineNumberTheory.AperyMultibound.pw_num 2 8)
  have wRoom : Γ ⊢[PRAAx] le (num 12*L) W :=
    le_congr (.eqRefl _) eW.eqSymm (by ipra_le 4*𝔞(L))
  have uRoom : Γ ⊢[PRAAx] le (num 46*L) U :=
    le_congr (.eqRefl _) eU.eqSymm (by ipra_le 210*𝔞(L))
  have rad : Γ ⊢[PRAAx] le ((num 6*U*V+num 23*W*V+W*U)*(L*V)) ((L+V)*D) := by
    apply positive_cancel (c := two) (le_succ_self one)
    dsimp only [D]
    ipra_le 𝔞(U*V*V)*sl wRoom+𝔞(W*V*V)*sl uRoom
  have close := distance_radius_mono _ _ _ _ _ _ hD (positive_product _ _ (unit_positive p) hV) rad joined
  exact distance_congr (GaussianGammaZetaMellinImproper.sample_at p z R B j).eqSymm
    (.eqRefl _) (.eqRefl _) (.eqRefl _) close

theorem equivalent (z R B j : PTm n) (hz : Γ ⊢[PRAAx] Source z R B (succ j)) :
    Γ ⊢[PRAAx] crossEquivalent I P (idat z R B j) (pdat z R B (succ j)) := by
  let sh (t : PTm n) := Syn.shift (Syn.shift t)
  let Δ := (Γ.map Fm.shift).map Fm.shift
  have guard : Δ ⊢[PRAAx] Source (sh z) (sh R) (sh B) (succ (sh j)) := by
    simpa [Δ,sh,Fm.shift,Syn.shift] using hz.shift.shift
  refine .allI (.allI ?_)
  simpa only [crossEquivalent,GaussianGammaZetaMellinImproper.subst_data,GaussianGammaZetaDirichletProduct.subst_data,
    ConciseIPRA.PTm.subst_succ,Syn.shift,sh,Δ] using
      independent_observations (var 1) (var 0) (sh z) (sh R) (sh B) (sh j) guard

theorem actual_original_Gamma_zeta_Mellin_identity_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (Source (var 0) (var 1) (var 2) (succ (var 3)) ⟶
      crossEquivalent I P (idat (var 0) (var 1) (var 2) (var 3)) (pdat (var 0) (var 1) (var 2) (succ (var 3)))) :=
  closeUniv 4 (.impI (equivalent _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianGammaZetaMellinIdentity
