import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.Integrands.GaussianEulerRealIntegrandNonnegative
import IPRADerivations.Analysis.Integration.CompactGrids.Comparisons.GaussianCompactRiemannLower
import IPRADerivations.Analysis.Euler.CompactExhaustion.Grids.GaussianEulerCompactAdditivity

/-!
# Nonnegativity of the actual real Euler compact observations

Every unchanged original real integrand observation has real part at
least minus its own dyadic error. The genuine weighted finite sum
therefore has lower error C/(E*2^s). At the original compact program's
actual precision s=p+T+6, its unchanged interval guard C<=E*T pays that
error inside 2^-p. Both zero and positive widths are covered; no margin,
integral value, or output nonnegativity is assumed.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerIncompleteRealCompactNonnegative

open_ipra
open GaussianEulerIntegrandName (evaluatorF fixedData sample timeData)
open GaussianCompactRiemannName (quadrature sampleBody sampleData sample_body_at precision mesh)
open GaussianEulerCompactAdditivity (intervalSource nameF data)
open GaussianEulerCompactModulus (lipschitz)
open GaussianCoefficientNameBounds (unit unit_positive)
open GaussianRationalHorner (positive_product)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open RationalGaussianRealPart (realBody)
open RationalGaussianEmbedding (scalarZero)
open RationalValueBounds (upper upper_congr upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def realSource (z B : PTm n) : Fm PTm n := le one B ⋏ ZT.eq (ComplexLogarithmRemainder.im z) (ZT.ofNat zero)
def source (z R B a C E T : PTm n) : Fm PTm n :=
  intervalSource z R B a C E T ⋏ ZT.eq (ComplexLogarithmRemainder.im z) (ZT.ofNat zero)

ipra_subst realSource [ZT.eq, ZT.ofNat, ComplexLogarithmRemainder.im]
ipra_subst source [ZT.eq, ZT.ofNat, ComplexLogarithmRemainder.im]

private theorem zero_fraction (C D : PTm n) (hD : Γ ⊢[PRAAx] le one D) : Γ ⊢[PRAAx]
    fraction (C*zero) D ≐ scalarZero := by
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _
    (RationalNormalForm.normalize_well_formed _ _ hD)
    (RationalNormalForm.normalize_well_formed _ _ (le_refl one))
    (fraction_represents (C*zero) D hD) (GaussianRationalSyntheticBounds.natCode_represents zero)
    hD (le_refl one)
  ipra_lc

private theorem scalar_entry (p N a C E z B i : PTm n) : Γ ⊢[PRAAx]
    RationalFiniteSum.term (realBody (sampleBody evaluatorF)) i (sampleData p N a C E (fixedData z B)) ≐
      fstT (sample p z B (a*N+C*i) (E*N)) := by
  simpa only [RationalFiniteSum.term,realBody,inst2,subst_fstT,sample,timeData,GaussianCompactRiemannName.grid] using
    congrFst (sample_body_at (Γ := Γ) evaluatorF i p N a C E (fixedData z B))

theorem original_rows_nonnegative (p N a C E z B : PTm n) (h : Γ ⊢[PRAAx] realSource z B)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    GaussianCompactRiemannLower.rows (realBody (sampleBody evaluatorF)) N
      (sampleData p N a C E (fixedData z B)) zero one one (unit p) := by
  let sh := fun q : PTm n => Syn.shift q
  let Δ := (lt (var 0 : PTm (n+1)) (sh N)) :: Γ.map Fm.shift
  have hs : Δ ⊢[PRAAx] realSource (sh z) (sh B) := by
    have e : Γ.map Fm.shift ⊢[PRAAx] realSource (sh z) (sh B) := by
      simpa only [Fm.shift,Syn.shift,sh,subst_realSource] using h.shift
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
  have raw := GaussianEulerRealIntegrandNonnegative.original_integrand_nonnegative (sh p) (sh z) (sh B)
    (sh a*sh N+sh C*var 0) (sh E*sh N)
    (.andI hs.andE₁ (.andI hs.andE₂
      (.andI (le_trans (positive_product _ _ apos npos) (le_add_right _ _)) (positive_product _ _ epos npos))))
  have zeroEq : Δ ⊢[PRAAx] fraction zero one ≐ scalarZero := .eqRefl _
  have out := upper_congr zeroEq.eqSymm
    (scalar_entry (sh p) (sh N) (sh a) (sh C) (sh E) (sh z) (sh B) (var 0)).eqSymm
    (.eqRefl _) (.eqRefl _) raw
  refine .allI (.impI ?_)
  simpa only [GaussianCompactRiemannName.subst_sampleData,GaussianEulerIntegrandName.subst_fixedData,
    GaussianCoefficientNameBounds.subst_unit,Syn.shift,sh,Δ,one,PTm.subst_zero,PTm.subst_succ] using out

theorem original_grid_nonnegative (p N a C E z B : PTm n) (h : Γ ⊢[PRAAx] realSource z B)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) (hN : Γ ⊢[PRAAx] le one N) : Γ ⊢[PRAAx]
    upper scalarZero (fstT (quadrature evaluatorF p N a C E (fixedData z B))) C (E*unit p) := by
  have raw := GaussianCompactRiemannLower.left_sum_lower (sampleBody evaluatorF) N
    (sampleData p N a C E (fixedData z B)) C E zero one one (unit p) hE hN (le_refl one)
    (original_rows_nonnegative p N a C E z B h ha hE hN)
  exact upper_congr (zero_fraction C _ (positive_product _ _ hE (le_refl one))) (.eqRefl _)
    (by ipra_ring) (.eqRefl _) raw

theorem original_sampler_nonnegative (p a C E L T z B : PTm n) (h : Γ ⊢[PRAAx] realSource z B)
    (ha : Γ ⊢[PRAAx] le one a) (hE : Γ ⊢[PRAAx] le one E) : Γ ⊢[PRAAx]
    upper scalarZero
      (fstT (ap2 (GaussianCompactRiemannName.nameF evaluatorF) p
        (GaussianCompactRiemannName.data a C E L T (fixedData z B)))) C (E*unit (precision p T)) :=
  upper_congr (.eqRefl _) (congrFst (GaussianCompactRiemannName.name_at evaluatorF p a C E L T (fixedData z B))).eqSymm
    (.eqRefl _) (.eqRefl _) (original_grid_nonnegative (precision p T) (mesh p L T) a C E z B h ha hE
      (GaussianCompactRiemannName.mesh_positive p L T))

theorem clock_budget (p C E T : PTm n) (hWidth : Γ ⊢[PRAAx] le C (E*T)) : Γ ⊢[PRAAx]
    le (C*unit p) (E*unit (precision p T)) := by
  have later := GaussianCompactRiemannName.dyadic_monotone (Γ := Γ) p (p+num 6) (le_add_right _ _)
  have clock := le_trans (mul_le_mul_right T later) (GaussianCompactRiemannName.precision_lower p T)
  exact le_trans (mul_le_mul_right (unit p) hWidth)
    (le_congr (by ipra_ring) (by ipra_ring) (mul_le_mul_right E clock))

theorem original_compact_nonnegative (p z R B a C E T : PTm n) (h : Γ ⊢[PRAAx] source z R B a C E T) : Γ ⊢[PRAAx]
    upper scalarZero (fstT (ap2 nameF p (data z R B a C E T))) one (unit p) := by
  have hE := h.andE₁.andE₁.andE₂.andE₁
  have width := le_trans (le_add_left C a) h.andE₁.andE₂.andE₂
  have native := original_sampler_nonnegative p a C E (lipschitz R E T) T z B
    (.andI h.andE₁.andE₁.andE₁ h.andE₂) h.andE₁.andE₂.andE₁ hE
  exact upper_mono _ _ C (E*unit (precision p T)) one (unit p)
    (positive_product _ _ hE (unit_positive _)) native
    (le_congr (.eqRefl _) (one_mul _).eqSymm (clock_budget p C E T width))

theorem actual_original_real_Euler_compact_nonnegative_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      (source (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7) ⟶
        upper scalarZero (fstT (ap2 nameF (var 0) (data (var 1) (var 2) (var 3) (var 4) (var 5) (var 6) (var 7))))
          one (unit (var 0))) :=
  closeUniv 8 (.impI (original_compact_nonnegative _ _ _ _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.GaussianEulerIncompleteRealCompactNonnegative
