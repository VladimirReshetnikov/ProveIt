import IPRADerivations.Analysis.Euler.GaussianEulerRealIntegrandLowerEnvelope
import IPRADerivations.Analysis.Euler.PositiveAxis.GaussianEulerUnitPanelGeometry
import IPRADerivations.Analysis.Integration.GaussianCompactRiemannLower
import IPRADerivations.Analysis.RationalArithmetic.RationalUpperAddition
import IPRADerivations.Analysis.Gamma.GaussianEulerIntegralGammaIdentification
import IPRADerivations.Core.CertificateTactics

/-!
# The one-eighteenth lower bound on the original Euler integral

The middle panel is the entire interval from one to two. Its actual
integrand values have lower bound one eighteenth, while both exterior
panels have lower bound zero. The same mesh is compared to the actual
improper observation. Finite signed slack removal leaves just the
requested output tolerance.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIntegralPositiveLower

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEulerIntegralGammaIdentification (original_Euler_integral_is_Gamma)
open GaussianGammaReciprocalInverse (gammaF gammaData)
open GaussianEulerLowerPowerCoefficients
open GaussianEulerIntegrandName (evaluatorF fixedData sample timeData)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianCompactRiemannName (grid quadrature sampleBody sampleData sample_body_at)
open GaussianEulerUnitPanelGeometry (leftWidth rightWidth leftPanel unitPanel rightPanel pieces)
open GaussianGammaIntegralCutoffs (etaDen eta_den_positive top)
open GaussianGammaCompactQuadratureBoundary (width width_bound)
open GaussianBetaSharpFiniteBinding (fullEuler multiplier multiplier_positive)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (qadd positive_product)
open RationalGaussianRealPart (realBody real_add)
open RationalValueBounds (upper upper_congr upper_mono upper_triangle)
open RationalUpperAddition (add_upper)
open GaussianRationalSyntheticBounds (natCode)
open ComplexLogarithmRemainder (im)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def realSource (z R B A : PTm n) : Fm PTm n :=
  GaussianEulerLowerPowerCoefficients.source z R B A ⋏ ZT.eq (im z) (ZT.ofNat zero)

@[simp] theorem subst_realSource {l : ℕ} (σ : Fin n → PTm l) (z R B A : PTm n) :
    (realSource z R B A).subst σ = realSource (Syn.subst σ z) (Syn.subst σ R)
      (Syn.subst σ B) (Syn.subst σ A) := by
  simp [realSource,ZT.eq,ZT.ofNat,im]

private theorem zero_fraction (C D : PTm n) (hD : Γ ⊢[PRAAx] le one D) :
    Γ ⊢[PRAAx] fraction (C*zero) D ≐ natCode zero := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hD)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (fraction_represents (C*zero) D hD) (GaussianRationalSyntheticBounds.natCode_represents zero)
    hD (le_refl one)
  ipra_lc

private theorem fraction_cancel (E A B : PTm n) (hE : Γ ⊢[PRAAx] le one E)
    (hB : Γ ⊢[PRAAx] le one B) : Γ ⊢[PRAAx] fraction (E*A) (E*B) ≐ fraction A B := by
  have den := positive_product E B hE hB
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ den)
    (RationalNormalForm.normalize_well_formed _ _ hB) (fraction_represents _ _ den)
    (fraction_represents _ _ hB) den hB
  ipra_lc

private theorem scalar_entry (p N a C E z B i : PTm n) : Γ ⊢[PRAAx]
    RationalFiniteSum.term (realBody (sampleBody evaluatorF)) i (sampleData p N a C E (fixedData z B)) ≐
      fstT (sample p z B (a*N+C*i) (E*N)) := by
  simpa only [RationalFiniteSum.term,realBody,inst2,subst_fstT,sample,timeData,grid] using
    congrFst (sample_body_at (Γ := Γ) evaluatorF i p N a C E (fixedData z B))

private theorem exterior_rows (p N a C E z R B A : PTm n)
    (h : Γ ⊢[PRAAx] realSource z R B A) (ha : Γ ⊢[PRAAx] le one a)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianCompactRiemannLower.rows (realBody (sampleBody evaluatorF)) N
      (sampleData p N a C E (fixedData z B)) zero one one (unit p) := by
  let sh := fun q : PTm n => Syn.shift q
  let Δ := (lt (var 0 : PTm (n+1)) (sh N)) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] realSource (sh z) (sh R) (sh B) (sh A) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] realSource (sh z) (sh R) (sh B) (sh A) := by
      simpa [Fm.shift,Syn.shift,sh] using h.shift
    exact e.wk
  have npos : Δ ⊢[PRAAx] le one (sh N) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh,one] using hN.shift
    exact e.wk
  have apos : Δ ⊢[PRAAx] le one (sh a) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] le one (sh a) := by simpa [Fm.shift,Syn.shift,sh,one] using ha.shift
    exact e.wk
  have epos : Δ ⊢[PRAAx] le one (sh E) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] le one (sh E) := by simpa [Fm.shift,Syn.shift,sh,one] using hE.shift
    exact e.wk
  have bound := GaussianEulerRealIntegrandNonnegative.original_integrand_nonnegative (sh p) (sh z) (sh B)
    (sh a*sh N+sh C*var 0) (sh E*sh N)
    (.andI hs.andE₁.andE₂.andE₁.andE₁ (.andI hs.andE₂
      (.andI (le_trans (positive_product _ _ apos npos) (le_add_right _ _)) (positive_product _ _ epos npos))))
  have lo : Δ ⊢[PRAAx] fraction zero one ≐ RationalGaussianEmbedding.scalarZero := .eqRefl _
  have out := upper_congr lo.eqSymm
    (scalar_entry (sh p) (sh N) (sh a) (sh C) (sh E) (sh z) (sh B) (var 0)).eqSymm
    (.eqRefl _) (.eqRefl _) bound
  refine .allI (.impI ?_)
  simpa only [GaussianCompactRiemannName.subst_sampleData,GaussianEulerIntegrandName.subst_fixedData,
    GaussianCoefficientNameBounds.subst_unit,Syn.shift,sh,Δ,one,
    ConciseIPRA.PTm.subst_zero,ConciseIPRA.PTm.subst_succ] using out

private theorem middle_rows (p N E z R B A : PTm n)
    (h : Γ ⊢[PRAAx] realSource z R B A) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianCompactRiemannLower.rows (realBody (sampleBody evaluatorF)) N
      (sampleData p N E E E (fixedData z B)) one (num 18) one (unit p) := by
  let sh := fun q : PTm n => Syn.shift q
  let Δ := (lt (var 0 : PTm (n+1)) (sh N)) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] realSource (sh z) (sh R) (sh B) (sh A) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] realSource (sh z) (sh R) (sh B) (sh A) := by
      simpa [Fm.shift,Syn.shift,sh] using h.shift
    exact e.wk
  have npos : Δ ⊢[PRAAx] le one (sh N) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] le one (sh N) := by simpa [Fm.shift,Syn.shift,sh,one] using hN.shift
    exact e.wk
  have epos : Δ ⊢[PRAAx] le one (sh E) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] le one (sh E) := by simpa [Fm.shift,Syn.shift,sh,one] using hE.shift
    exact e.wk
  let b := sh E*sh N
  let a := b+sh E*var 0
  have hlow : Δ ⊢[PRAAx] le b a := le_add_right _ _
  have den : Δ ⊢[PRAAx] le one b := positive_product _ _ epos npos
  have grow := mul_le_mul_right (sh E) (le_of_lt (Prf.hyp0 : Δ ⊢[PRAAx] lt (var 0) (sh N)))
  have high : Δ ⊢[PRAAx] le a (two*b) :=
    le_congr (by dsimp only [a,b]; ipra_ring) (by dsimp only [b]; ipra_ring) (add_le_add_right b grow)
  have lower := GaussianEulerRealIntegrandLowerEnvelope.original_integrand_lower (sh p) (sh z) (sh R) (sh B)
    (sh A) a b hs.andE₁ hs.andE₂ (.andI (.andI (le_trans den hlow) den) hlow) high
  have out := upper_congr (.eqRefl _) (scalar_entry (sh p) (sh N) (sh E) (sh E) (sh E)
    (sh z) (sh B) (var 0)).eqSymm (.eqRefl _) (.eqRefl _) lower
  refine .allI (.impI ?_)
  simpa only [GaussianCompactRiemannName.subst_sampleData,GaussianEulerIntegrandName.subst_fixedData,
    GaussianCoefficientNameBounds.subst_unit,Syn.shift,sh,Δ,LeanProofs.IPRA.PTm.subst_num,
    GaussianEulerRealIntegrandLowerEnvelope.lower,one,ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] using out

private theorem add_upper_same (a b c d A C D : PTm n) (hD : Γ ⊢[PRAAx] le one D)
    (h : Γ ⊢[PRAAx] upper a b A D) (k : Γ ⊢[PRAAx] upper c d C D) :
    Γ ⊢[PRAAx] upper (RationalArithmetic.add a c) (RationalArithmetic.add b d) (A+C) D := by
  apply upper_mono _ _ _ _ _ _ (positive_product _ _ hD hD) (add_upper _ _ _ _ _ _ _ _ h k)
  exact le_congr (by ipra_ring) (.eqRefl _) (le_refl _)

private theorem exterior_panel (p N a C E z R B A : PTm n)
    (h : Γ ⊢[PRAAx] realSource z R B A) (ha : Γ ⊢[PRAAx] le one a)
    (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    upper (natCode zero) (fstT (quadrature evaluatorF p N a C E (fixedData z B))) C (E*unit p) := by
  have raw := GaussianCompactRiemannLower.left_sum_lower (sampleBody evaluatorF) N
    (sampleData p N a C E (fixedData z B)) C E zero one one (unit p) hE hN (le_refl _)
    (exterior_rows p N a C E z R B A h ha hE hN)
  have he : Γ ⊢[PRAAx] le one (E*one) := positive_product _ _ hE (le_refl _)
  exact upper_congr (zero_fraction C _ he) (.eqRefl _) (by ipra_ring) (.eqRefl _) raw

private theorem central_panel (p N E z R B A : PTm n)
    (h : Γ ⊢[PRAAx] realSource z R B A) (hE : Γ ⊢[PRAAx] le one E)
    (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    upper (fraction one (num 18)) (fstT (quadrature evaluatorF p N E E E (fixedData z B))) E (E*unit p) := by
  have d : Γ ⊢[PRAAx] le one (num 18 : PTm n) := le_of_eq_add (d := num 17) (by ipra_ring)
  have raw := GaussianCompactRiemannLower.left_sum_lower (sampleBody evaluatorF) N
    (sampleData p N E E E (fixedData z B)) E E one (num 18) one (unit p) hE hN d
    (middle_rows p N E z R B A h hE hN)
  exact upper_congr (fraction_cancel E one (num 18) hE d) (.eqRefl _) (by ipra_ring) (.eqRefl _) raw

private theorem combined_panels (p k K z R B A : PTm n)
    (h : Γ ⊢[PRAAx] realSource z R B A) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    upper (fraction one (num 18)) (fstT (pieces p k A R K z B)) (width k A R) (etaDen k A R*unit p) := by
  let E := etaDen k A R
  let L := leftWidth k A R
  let U := rightWidth k A R
  let c := fraction (one : PTm n) (num 18)
  have pos := GaussianEulerUnitPanelGeometry.widths_positive k A R h.andE₁.andE₁
  have hE := pos.andE₂.andE₁
  have left := exterior_panel p (L*K) one L E z R B A h (le_refl _) hE (positive_product _ _ pos.andE₁ hK)
  have middle := central_panel p (E*K) E z R B A h hE (positive_product _ _ hE hK)
  have right := exterior_panel p (U*K) (two*E) U E z R B A h
    (positive_product _ _ (le_succ_self one) hE) hE (positive_product _ _ pos.andE₂.andE₂ hK)
  have den := positive_product _ _ hE (unit_positive p)
  have h18 : Γ ⊢[PRAAx] le one (num 18 : PTm n) := le_of_eq_add (d := num 17) (by ipra_ring)
  have hc : Γ ⊢[PRAAx] RationalNormalForm.wellFormed c := RationalNormalForm.normalize_well_formed _ _ h18
  have first := add_upper_same _ _ _ _ _ _ _ den left middle
  have first' := upper_congr (GaussianRationalLinearProduct.scalar_zero_add c hc) (real_add _ _).eqSymm
    (.eqRefl _) (.eqRefl _) first
  have all := add_upper_same _ _ _ _ _ _ _ den first' right
  exact upper_congr (GaussianRationalLinearProduct.scalar_add_zero c hc) (real_add _ _).eqSymm
    (GaussianEulerUnitPanelGeometry.total_width k A R) (.eqRefl _) all

theorem actual_full_grid_lower (p k K z R B A : PTm n)
    (h : Γ ⊢[PRAAx] realSource z R B A) (hK : Γ ⊢[PRAAx] le one K) : Γ ⊢[PRAAx]
    upper (fraction one (num 18)) (fstT (fullEuler p k A R K z B)) (num 5*width k A R) (etaDen k A R*unit p) := by
  let E := etaDen k A R
  let W := width k A R
  let U := E*unit p
  have den := positive_product _ _ (eta_den_positive (Γ := Γ) k A R) (unit_positive p)
  have raw := GaussianEulerUnitPanelGeometry.actual_euler_unit_panel_split p k A R K z B
    h.andE₁.andE₂.andE₁ hK
  have split := GaussianRationalDistanceOrder.distance_symmetric _ _ _ _ den raw
  have right := RationalValueBounds.upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ den split)
  have joined := upper_triangle _ _ _ _ _ _ _ (combined_panels p k K z R B A h hK) right
  exact upper_mono _ _ _ _ _ _ (positive_product U U den den) joined
    (le_congr (by dsimp only [U,E]; ipra_ring) (.eqRefl _) (le_refl _))

theorem original_improper_positive_lower (p z R B A : PTm n)
    (h : Γ ⊢[PRAAx] realSource z R B A) : Γ ⊢[PRAAx]
    upper (fraction one (num 18)) (fstT (ap2 GaussianEulerImproperName.nameF p (GaussianEulerImproperName.data z R B A)))
      one (unit p) := by
  let c := fraction (one : PTm n) (num 18)
  let value := fstT (ap2 GaussianEulerImproperName.nameF p (GaussianEulerImproperName.data z R B A))
  let t := GaussianNamedRealOrderTransport.precision c value (unit p) (num 5)
  let E := etaDen t A R
  let T := top t A R
  let clock := GaussianBetaRefinedFixedCompactComparison.referencePrecision (t+num 4) t A R
  let demand := GaussianFastValueCut.exponent (num 5*T) t
  let s := clock+demand
  have hU := unit_positive (Γ := Γ) t
  have clockProof : Γ ⊢[PRAAx] le clock s := le_add_right _ _
  have prec : Γ ⊢[PRAAx] le (num 5*T*unit t) (unit s) :=
    le_trans (GaussianFastValueCut.query_budget (num 5*T) t)
      (GaussianExponentialReference.unit_monotone (le_add_left demand clock))
  have den := positive_product _ _ (eta_den_positive (Γ := Γ) t A R) (unit_positive s)
  have geom := mul_le_mul_right (num 5*unit t) (width_bound (Γ := Γ) t A R)
  have hd : Γ ⊢[PRAAx] le (num 5*width t A R*unit t) (one*(E*unit s)) := by
    have first : Γ ⊢[PRAAx] le (num 5*width t A R*unit t) (num 5*T*unit t*E) :=
      le_congr (by ipra_ring) (by ipra_ring) geom
    exact le_trans first (le_congr (.eqRefl _) (by ipra_ring) (mul_le_mul_right E prec))
  have mesh := multiplier_positive one t A R (le_refl (Γ := Γ) one)
  have left := upper_mono _ _ _ _ _ _ den (actual_full_grid_lower s t (multiplier one t A R) z R B A h mesh) hd
  have raw := GaussianBetaSharpFiniteBinding.original_improper_euler t s p t z R B A one
    (.andI h.andE₁.andE₂.andE₁ h.andE₁) (le_refl one) (le_refl t) clockProof
  have hp := unit_positive (Γ := Γ) p
  have right := RationalValueBounds.upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _
      (positive_product _ _ hU hp) raw)
  have together := upper_triangle _ _ _ _ _ _ _ left right
  have clean : Γ ⊢[PRAAx] upper c value (one*unit t+num 5*unit p) (unit p*unit t) :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ hU (positive_product _ _ hU hp)) together
      (le_congr (by ipra_ring) (.eqRefl _) (le_refl _))
  exact GaussianNamedRealOrderTransport.remove_upper_slack c value one (unit p) (num 5) clean

theorem original_Euler_integral_one_eighteenth_lower_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (realSource (var 1) (var 2) (var 3) (var 4) ⟶
        upper (fraction one (num 18))
          (fstT (ap2 GaussianEulerImproperName.nameF (var 0)
            (GaussianEulerImproperName.data (var 1) (var 2) (var 3) (var 4)))) one (unit (var 0))) :=
  closeUniv 5 (.impI (original_improper_positive_lower _ _ _ _ _ Prf.hyp0))

/-- The transfer to the actual Gamma query spends only that query's own
observation tolerance. -/
theorem original_gamma_positive_lower (p z R B A : PTm n)
    (h : Γ ⊢[PRAAx] realSource z R B A) (hR : Γ ⊢[PRAAx] le one R) : Γ ⊢[PRAAx]
    upper (fraction one (num 18)) (fstT (ap2 gammaF p (gammaData z R B A))) one (unit p) := by
  let c := fraction (one : PTm n) (num 18)
  let value := fstT (ap2 gammaF p (gammaData z R B A))
  let t := GaussianNamedRealOrderTransport.precision c value (unit p) two
  have cross := original_Euler_integral_is_Gamma z R B A (.andI h.andE₁ hR)
  have distance := GaussianNameEquivalence.cross_at _ _ _ _ t p cross
  have ht := unit_positive (Γ := Γ) t
  have denom := positive_product _ _ ht (unit_positive p)
  have right := RationalValueBounds.upper_of_radius _ _ _ _
    (GaussianNamedPositiveExponentialOrder.scalar_coordinate_distance _ _ _ _ denom distance)
  have combined := upper_triangle _ _ _ _ _ _ _ (original_improper_positive_lower t z R B A h) right
  have reduced : Γ ⊢[PRAAx] upper c value (unit t+two*unit p) (unit p*unit t) :=
    upper_mono _ _ _ _ _ _ (positive_product _ _ ht denom) combined
      (le_congr (by ipra_ring) (.eqRefl _) (le_refl _))
  exact GaussianNamedRealOrderTransport.remove_upper_slack c value one (unit p) two
    (upper_congr (.eqRefl _) (.eqRefl _) (by ipra_ring) (.eqRefl _) reduced)

theorem original_Gamma_one_eighteenth_lower_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      ((realSource (var 1) (var 2) (var 3) (var 4) ⋏ le one (var 2)) ⟶
        upper (fraction one (num 18))
          (fstT (ap2 gammaF (var 0) (gammaData (var 1) (var 2) (var 3) (var 4)))) one (unit (var 0))) :=
  closeUniv 5 (.impI (original_gamma_positive_lower _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂))

end LeanProofs.IPRA.Analysis.GaussianEulerIntegralPositiveLower
