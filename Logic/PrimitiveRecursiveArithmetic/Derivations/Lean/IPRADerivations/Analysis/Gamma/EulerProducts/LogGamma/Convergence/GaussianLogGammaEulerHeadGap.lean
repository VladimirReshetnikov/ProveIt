import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.Intervals.GaussianLogGammaEulerResidualInterval
import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.Intervals.GaussianLogGammaEulerWeightedIntervalError
import IPRADerivations.Analysis.Integration.Partitions.GaussianRationalPanelTailDistance
import IPRADerivations.Analysis.Names.Rates.Moduli.GaussianNamedLipschitzRate

/-!
# Uniform tail of the original log-Gamma Euler heads

Compare the weighted logarithm and residual sum to the same exact
Gaussian-rational harmonic interval. Remove the common auxiliary sampling
error while retaining the two observation errors of the original heads.
-/

set_option autoImplicit false
set_option maxHeartbeats 1200000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerHeadGap

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open GaussianEuclideanDistanceName (pointCN subst_pointCN)
open GaussianLogGammaEulerNormalizedDifference (weightedLogF weightedLogData rangeF rangeData windowF windowData)
open GaussianNameEquivalence (crossEquivalent cross_at subst_crossEquivalent)
open GaussianRationalDistanceOrder (distance_radius_mono distance_symmetric distance_triangle_same)
open GaussianRationalHorner (positive_product qzero)
open GaussianRationalMetric (distanceBounded qsub)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "F" => GaussianNamedDifference.nameF
local notation "X" => GaussianNamedDifference.data

private theorem synchronous_from_window (f g j : PR 2) (x y u v p lin A B C D N : PTm n)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN f y)
    (hu : Γ ⊢[PRAAx] pointCN g u) (hv : Γ ⊢[PRAAx] pointCN j v)
    (hN : Γ ⊢[PRAAx] le one N) (he : Γ ⊢[PRAAx] crossEquivalent (F f f) (F g j) (X x y) (X u v))
    (hleft : Γ ⊢[PRAAx] distanceBounded (ap2 g p u) lin (A*unit p+C*N) (N*unit p))
    (hright : Γ ⊢[PRAAx] distanceBounded (ap2 j p v) lin (B*unit p+D*N) (N*unit p)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 f p y)
      ((A+B)*unit p+(num 14+C+D)*N) (N*unit p) := by
  let U := unit p
  let K := N*U
  let first := ap2 f p x
  let last := ap2 f p y
  let left := ap2 g p u
  let right := ap2 j p v
  let dx := qsub first last
  let wx := qsub left right
  let a := ap2 (F f f) p (X x y)
  let b := ap2 (F g j) p (X u v)
  have hU := unit_positive (Γ := Γ) p
  have hK := positive_product (Γ := Γ) N U hN hU
  have m₁ : Γ ⊢[PRAAx] distanceBounded dx a (num 6) U :=
    distance_symmetric _ _ _ _ hU (GaussianNamedDifference.sample_error f f x y p hx hy)
  have m₂ : Γ ⊢[PRAAx] distanceBounded a b two U :=
    GaussianNameEquivalence.cross_diagonal_at p he
  have m₃ : Γ ⊢[PRAAx] distanceBounded b wx (num 6) U :=
    GaussianNamedDifference.sample_error g j u v p hu hv
  have m₄ := distance_triangle_same dx a b (num 6) two U hU m₁ m₂
  have moved := distance_triangle_same dx b wx (num 6+two) (num 6) U hU m₄ m₃
  have window := distance_triangle_same left lin right (A*U+C*N) (B*U+D*N) K hK hleft
    (distance_symmetric _ _ _ _ hK hright)
  have toZero := (GaussianReconstructionRoots.distance_zero_iff wx _ K hK).iffMpr window
  have full := GaussianRationalPanelTailDistance.triangle dx wx qzero _ U _ K hU hK moved toZero
  have reduced := distance_radius_mono dx qzero _ _ ((A+B)*U+(num 14+C+D)*N) K
    (positive_product U K hU hK) hK (le_of_eq_add (d := zero) (by dsimp only [K]; ipra_ring)) full
  exact (GaussianReconstructionRoots.distance_zero_iff dx _ K hK).iffMp reduced

open GaussianLogGammaEulerResidualDomain (source subst_source)

private theorem diagonal_gap_from_window (f : PR 2) (x y t A B D neg R N r : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N) (hlarge : Γ ⊢[PRAAx] le (two*R) N)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN f y)
    (he : Γ ⊢[PRAAx] crossEquivalent (F f f) windowF (X x y) (windowData A B D neg N r)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f t x) (ap2 f t y)
      ((R*R+R)*unit t+(num 14+num 8*R+num 3)*N) (N*unit t) := by
  let C := num 14+num 8*R+num 3
  have left := GaussianLogGammaEulerWeightedIntervalError.sample_error t A B D neg R N r h hN
  have right := GaussianLogGammaEulerResidualInterval.sharp_named_interval_sample_error t A B D neg R N r h hN hlarge
  have adjusted := GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _)
    (show Γ ⊢[PRAAx] GaussianLogGammaEulerWeightedIntervalError.errorNumerator t R N ≐ R*unit t+(num 8*R)*N by
      unfold GaussianLogGammaEulerWeightedIntervalError.errorNumerator
      ipra_ring) (.eqRefl (N*unit t)) left
  have localGap := synchronous_from_window f weightedLogF rangeF x y
    (weightedLogData A B D neg N r) (rangeData A B D neg N r) t
    (GaussianLogGammaEulerLinearInterval.linearSum A B D neg N r) R (R*R) (num 8*R) (num 3) N hx hy
    (GaussianLogGammaEulerNormalizedDifference.weighted_log_regular A B D neg N r hN)
    (GaussianLogGammaEulerNormalizedDifference.range_regular A B D neg N r h.andE₁) hN he adjusted right
  exact GaussianRationalDistanceOrder.distance_congr (.eqRefl _) (.eqRefl _)
    (show Γ ⊢[PRAAx] (R+R*R)*unit t+C*N ≐ (R*R+R)*unit t+C*N by ipra_ring)
    (.eqRefl (N*unit t)) localGap

private theorem gap_from_window (f : PR 2) (x y p q A B D neg R N r : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N) (hlarge : Γ ⊢[PRAAx] le (two*R) N)
    (hx : Γ ⊢[PRAAx] pointCN f x) (hy : Γ ⊢[PRAAx] pointCN f y)
    (he : Γ ⊢[PRAAx] crossEquivalent (F f f) windowF (X x y) (windowData A B D neg N r)) :
    Γ ⊢[PRAAx] distanceBounded (ap2 f p x) (ap2 f q y)
      ((R*R+R)*unit p*unit q+N*(unit p+unit q)) (N*unit p*unit q) := by
  apply GaussianNamedLipschitzRate.independent_at f f x y (R*R+R) N (num 14+num 8*R+num 3) p q hN hx hy
  refine .allI ?_
  let Δ := Γ.map Fm.shift
  let s (a : PTm n) := Syn.shift a
  have hs : Δ ⊢[PRAAx] source (s A) (s B) (s D) (s neg) (s R) := by
    simpa only [Δ,s,Fm.shift,Syn.shift,subst_source] using h.shift
  have hn : Δ ⊢[PRAAx] le one (s N) := by
    simpa [Δ,s,Fm.shift,Syn.shift] using hN.shift
  have hl : Δ ⊢[PRAAx] le (two*s R) (s N) := by
    simpa [Δ,s,Fm.shift,Syn.shift] using hlarge.shift
  have hrx : Δ ⊢[PRAAx] pointCN f (s x) := by
    simpa only [Δ,s,Fm.shift,subst_pointCN,Syn.shift] using hx.shift
  have hry : Δ ⊢[PRAAx] pointCN f (s y) := by
    simpa only [Δ,s,Fm.shift,subst_pointCN,Syn.shift] using hy.shift
  have hes : Δ ⊢[PRAAx] crossEquivalent (F f f) windowF (X (s x) (s y))
      (windowData (s A) (s B) (s D) (s neg) (s N) (s r)) := by
    simpa only [Δ,s,Fm.shift,subst_crossEquivalent,GaussianNamedDifference.subst_data,
      GaussianLogGammaEulerNormalizedDifference.subst_windowData,Syn.shift] using he.shift
  simpa only [GaussianNamedLipschitzRate.diagonalNumerator,GaussianNamedLipschitzRate.diagonalDenominator,
    Syn.shift,PTm.subst_add,PTm.subst_mul,LeanProofs.IPRA.PTm.subst_num,s,Δ] using
    diagonal_gap_from_window f (s x) (s y) (var 0) (s A) (s B) (s D) (s neg) (s R) (s N) (s r) hs hn hl hrx hry hes

theorem sharp_ordered_gap (p q A B D neg R N r : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N) (hlarge : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianLogGammaEulerHead.nameF p (GaussianLogGammaEulerHead.data A B D neg (N+r)))
      (ap2 GaussianLogGammaEulerHead.nameF q (GaussianLogGammaEulerHead.data A B D neg N))
      ((R*R+R)*unit p*unit q+N*(unit p+unit q)) (N*unit p*unit q) :=
  gap_from_window GaussianLogGammaEulerHead.nameF (GaussianLogGammaEulerHead.data A B D neg (N+r))
    (GaussianLogGammaEulerHead.data A B D neg N) p q A B D neg R N r h hN hlarge
    (GaussianLogGammaEulerHead.regular A B D neg (N+r) h.andE₁ (le_trans hN (le_add_right N r)))
    (GaussianLogGammaEulerHead.regular A B D neg N h.andE₁ hN)
    (GaussianLogGammaEulerNormalizedDifference.original_equivalent A B D neg N r h.andE₁ hN)

theorem sharp_normalized_ordered_gap (p q A B D neg R N r : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N) (hlarge : Γ ⊢[PRAAx] le (two*R) N) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianLogGammaEulerNormalizedHead.nameF p (GaussianLogGammaEulerNormalizedHead.data A B D neg (N+r)))
      (ap2 GaussianLogGammaEulerNormalizedHead.nameF q (GaussianLogGammaEulerNormalizedHead.data A B D neg N))
      ((R*R+R)*unit p*unit q+N*(unit p+unit q)) (N*unit p*unit q) :=
  gap_from_window GaussianLogGammaEulerNormalizedHead.nameF (GaussianLogGammaEulerNormalizedHead.data A B D neg (N+r))
    (GaussianLogGammaEulerNormalizedHead.data A B D neg N) p q A B D neg R N r h hN hlarge
    (GaussianLogGammaEulerNormalizedHead.regular A B D neg (N+r) h.andE₁ (le_trans hN (le_add_right N r)))
    (GaussianLogGammaEulerNormalizedHead.regular A B D neg N h.andE₁ hN)
    (GaussianLogGammaEulerNormalizedDifference.equivalent A B D neg N r h.andE₁ hN)

theorem ordered_gap (p q A B D neg R N r : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N) (hlarge : Γ ⊢[PRAAx] le (num 8*R) N) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianLogGammaEulerHead.nameF p (GaussianLogGammaEulerHead.data A B D neg (N+r)))
      (ap2 GaussianLogGammaEulerHead.nameF q (GaussianLogGammaEulerHead.data A B D neg N))
      ((R*R+R)*unit p*unit q+N*(unit p+unit q)) (N*unit p*unit q) :=
  sharp_ordered_gap p q A B D neg R N r h hN
    (le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (by ipra_le 6) (le_refl R)) hlarge)

theorem normalized_ordered_gap (p q A B D neg R N r : PTm n)
    (h : Γ ⊢[PRAAx] source A B D neg R) (hN : Γ ⊢[PRAAx] le one N) (hlarge : Γ ⊢[PRAAx] le (num 8*R) N) :
    Γ ⊢[PRAAx] distanceBounded
      (ap2 GaussianLogGammaEulerNormalizedHead.nameF p (GaussianLogGammaEulerNormalizedHead.data A B D neg (N+r)))
      (ap2 GaussianLogGammaEulerNormalizedHead.nameF q (GaussianLogGammaEulerNormalizedHead.data A B D neg N))
      ((R*R+R)*unit p*unit q+N*(unit p+unit q)) (N*unit p*unit q) :=
  sharp_normalized_ordered_gap p q A B D neg R N r h hN
    (le_trans (AnalyticNumberTheory.PhiLower.le_mul_mono (by ipra_le 6) (le_refl R)) hlarge)

theorem actual_original_Euler_logarithm_head_gap_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      ((source (var 0) (var 1) (var 2) (var 3) (var 4) ⋏ (le one (var 5) ⋏ le (num 8*var 4) (var 5))) ⟶
        distanceBounded (ap2 GaussianLogGammaEulerHead.nameF (var 7)
            (GaussianLogGammaEulerHead.data (var 0) (var 1) (var 2) (var 3) (var 5+var 6)))
          (ap2 GaussianLogGammaEulerHead.nameF (var 8)
            (GaussianLogGammaEulerHead.data (var 0) (var 1) (var 2) (var 3) (var 5)))
          ((var 4*var 4+var 4)*unit (var 7)*unit (var 8)+var 5*(unit (var 7)+unit (var 8)))
          (var 5*unit (var 7)*unit (var 8))) :=
  closeUniv 9 (.impI (ordered_gap _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

theorem actual_original_Euler_logarithm_sharp_head_gap_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 9
      ((source (var 0) (var 1) (var 2) (var 3) (var 4) ⋏ (le one (var 5) ⋏ le (two*var 4) (var 5))) ⟶
        distanceBounded (ap2 GaussianLogGammaEulerHead.nameF (var 7)
            (GaussianLogGammaEulerHead.data (var 0) (var 1) (var 2) (var 3) (var 5+var 6)))
          (ap2 GaussianLogGammaEulerHead.nameF (var 8)
            (GaussianLogGammaEulerHead.data (var 0) (var 1) (var 2) (var 3) (var 5)))
          ((var 4*var 4+var 4)*unit (var 7)*unit (var 8)+var 5*(unit (var 7)+unit (var 8)))
          (var 5*unit (var 7)*unit (var 8))) :=
  closeUniv 9 (.impI (sharp_ordered_gap _ _ _ _ _ _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerHeadGap
