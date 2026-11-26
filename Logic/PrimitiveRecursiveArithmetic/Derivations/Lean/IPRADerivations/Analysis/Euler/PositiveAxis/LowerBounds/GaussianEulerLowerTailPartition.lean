import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerTailRootGrid
import IPRADerivations.Analysis.Euler.PositiveAxis.LowerBounds.GaussianEulerLowerTailPowerPanel
import IPRADerivations.Analysis.Integration.Partitions.GaussianPartitionedFiniteSum

/-!
# Partitioning the original lower Euler grid at the transformed roots

The original uniform time grid is grouped at the integer offsets of
the power-transformed roots. The grouped sum is literally the original
weighted Gaussian sum. The group endpoints are numerical, and each
group width has the uniform power-gap bound needed for the local
comparison with its right endpoint.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianEulerLowerTailPartition

open_ipra
open GaussianEulerLowerTailRootGrid (rootRatio rootNumerator rootDenominator timeNumerator timeDenominator)
open GaussianGammaIntegralCutoffs (height)
open GaussianGammaCompactCutoffGeometry (delta lowerWidth)
open GaussianPartitionedFiniteSum (increasing blockBody grouped_from_zero)
open GaussianCompactRiemannName (sampleBody sampleData quadrature)
open GaussianRationalFiniteSum (sum)
open GaussianRationalHorner (qmul)
open GaussianRationalRiemannRefinement (weight)
open GaussianRationalSyntheticDivision (qmul_congr)
open GaussianCoefficientNameBounds (unit unit_positive)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk Γ t)

def rootStep (p q : PTm n) : PTm n := monus (rootRatio p q) one
def offset (i N p q A : PTm n) : PTm n :=
  monus (timeNumerator i N p q A) (timeNumerator zero N p q A)
def panelWidth (i N p q A : PTm n) : PTm n := monus (offset (succ i) N p q A) (offset i N p q A)
def totalWidth (N p q A : PTm n) : PTm n := offset N N p q A
def cutData (N p q A : PTm n) : PTm n := pairT N (pairT p (pairT q A))
def cutF : PR 2 := PTm.toPR
  (offset (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1)))) (sndT (sndT (sndT (var 1)))) : PTm 2)

ipra_subst rootStep [rootRatio]
ipra_subst offset [timeNumerator, rootNumerator, rootRatio]
ipra_subst cutData

theorem offset_at (i N p q A : PTm n) : Γ ⊢[PRAAx] ap2 cutF i (cutData N p q A) ≐ offset i N p q A := by
  let d := cutData N p q A
  have eval : Γ ⊢[PRAAx] ap2 cutF i d ≐ offset i (fstT d) (fstT (sndT d)) (fstT (sndT (sndT d))) (sndT (sndT (sndT d))) := by
    simpa [cutF,ap2] using toPR_eq (Γ := Γ)
      (offset (var 0) (fstT (var 1)) (fstT (sndT (var 1))) (fstT (sndT (sndT (var 1))))
        (sndT (sndT (sndT (var 1)))) : PTm 2) ![i,d]
  have tail : Γ ⊢[PRAAx] sndT d ≐ pairT p (pairT q A) := snd_pair _ _
  have tail₂ := (congrSnd tail).eqTrans (snd_pair p (pairT q A))
  have value := Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (offset (var 0) (var 1) (var 2) (var 3) (var 4) : PTm 5)
    (σ := ![i,fstT d,fstT (sndT d),fstT (sndT (sndT d)),sndT (sndT (sndT d))]) (σ' := ![i,N,p,q,A])
    (fun k => by
      fin_cases k
      · exact .eqRefl _
      · exact fst_pair _ _
      · exact tail.fstE
      · exact tail₂.fstE
      · exact tail₂.sndE)
  exact eval.eqTrans (by simpa using value)

theorem offset_zero (N p q A : PTm n) : Γ ⊢[PRAAx] offset zero N p q A ≐ zero :=
  monus_self _

theorem absolute_offset (i N p q A : PTm n) :
    Γ ⊢[PRAAx] timeNumerator zero N p q A+offset i N p q A ≐ timeNumerator i N p q A :=
  (eq_add_of_le (GaussianEulerLowerTailRootGrid.time_monotone zero i N p q A (zero_le i))).eqSymm

theorem offset_monotone (i j N p q A : PTm n) (h : Γ ⊢[PRAAx] le i j) :
    Γ ⊢[PRAAx] le (offset i N p q A) (offset j N p q A) := by
  have lo := natEq (absolute_offset (Γ := Γ) i N p q A)
  have hi := natEq (absolute_offset (Γ := Γ) j N p q A)
  have cmp := GaussianEulerLowerTailRootGrid.time_monotone i j N p q A h
  ipra_le sl cmp using linear_combination hi-lo

theorem cut_increasing (N p q A : PTm n) : Γ ⊢[PRAAx] increasing cutF (cutData N p q A) := by
  refine .allI ?_
  let i : PTm (n+1) := var 0
  have cmp := offset_monotone (Γ := Γ.map Fm.shift) i (succ i) (Syn.shift N) (Syn.shift p) (Syn.shift q) (Syn.shift A) (le_succ_self i)
  simpa only [increasing,Syn.shift,subst_cutData,i] using le_congr (offset_at (Γ := Γ.map Fm.shift) _ _ _ _ _).eqSymm
    (offset_at (Γ := Γ.map Fm.shift) _ _ _ _ _).eqSymm cmp

theorem exact_panel_width (i N p q A : PTm n) :
    Γ ⊢[PRAAx] panelWidth i N p q A ≐ monus (timeNumerator (succ i) N p q A) (timeNumerator i N p q A) := by
  have a := natEq (absolute_offset (Γ := Γ) i N p q A)
  have b := natEq (absolute_offset (Γ := Γ) (succ i) N p q A)
  have c := natEq (eq_add_of_le (offset_monotone (Γ := Γ) i (succ i) N p q A (le_succ_self i)))
  have e := natEq (eq_add_of_le (GaussianEulerLowerTailRootGrid.time_monotone (Γ := Γ) i (succ i) N p q A (le_succ_self i)))
  apply deriveNat
  unfold panelWidth
  ipra_simps
  linear_combination -a+b-c+e

theorem root_step_exact (i N p q : PTm n) : Γ ⊢[PRAAx] rootNumerator (succ i) N p q ≐ rootNumerator i N p q+rootStep p q := by
  unfold rootNumerator rootStep
  ipra_ring

theorem root_right_guard (i N p q A R : PTm n) (hN : Γ ⊢[PRAAx] le one N) (h : Γ ⊢[PRAAx] le p q)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx]
    le one (rootNumerator (succ i) N p q) ⋏ le (rootNumerator (succ i) N p q) (rootDenominator N q A R) := by
  have step : Γ ⊢[PRAAx] le (succ i) N := hi
  let width := rootStep p q
  have cap : Γ ⊢[PRAAx] le (width*succ i) (width*N) :=
    le_congr (mul_comm _ _) (mul_comm _ _) (mul_le_mul_right width step)
  have last : Γ ⊢[PRAAx] le (rootNumerator (succ i) N p q) (rootRatio p q*N) :=
    le_congr (.eqRefl _) (GaussianEulerLowerTailRootGrid.root_last N p q) (add_le_add₂ (le_refl N) cap)
  have clocks : Γ ⊢[PRAAx] le (delta p q) (height q A R) :=
    le_of_eq_add ((GaussianGammaCompactCutoffGeometry.height_refinement p q A R h).eqTrans (add_comm _ _))
  exact .andI (le_trans hN (le_add_right _ _))
    (le_trans last (mul_le_mul_right N (GaussianExponentialReference.unit_monotone clocks)))

theorem uniform_panel_width (i N p q k R : PTm n) (hN : Γ ⊢[PRAAx] le one N)
    (h : Γ ⊢[PRAAx] le p q) (hi : Γ ⊢[PRAAx] lt i N) :
    Γ ⊢[PRAAx] le (panelWidth i N p q (succ k)) (rootStep p q*(succ k*pw (rootDenominator N q (succ k) R) k)) := by
  have exactWidth := exact_panel_width (Γ := Γ) i N p q (succ k)
  let a := rootNumerator i N p q
  let b := rootNumerator (succ i) N p q
  let D := rootDenominator N q (succ k) R
  let C := rootStep p q
  have gap := PowerGap.power_gap (root_step_exact (Γ := Γ) i N p q)
    (root_right_guard i N p q (succ k) R hN h hi).andE₂ k
  have e := natEq (eq_add_of_le (GaussianEulerLowerTailRootGrid.time_monotone (Γ := Γ) i (succ i) N p q (succ k) (le_succ_self _)))
  have cleared : Γ ⊢[PRAAx] le (monus (pw b (succ k)) (pw a (succ k))) (C*(succ k*pw D k)) := by
    unfold timeNumerator at e
    dsimp only [a,b,D,C]
    ipra_le sl gap using linear_combination e
  exact le_congr exactWidth.eqSymm (.eqRefl _) cleared

theorem grouped_original_quadrature (F : PR 3) (s N p q A R x : PTm n) :
    Γ ⊢[PRAAx] quadrature F s (totalWidth N p q A) (timeNumerator zero N p q A) (totalWidth N p q A) (timeDenominator N q A R) x ≐
      qmul (weight (totalWidth N p q A) (timeDenominator N q A R) (totalWidth N p q A))
        (sum (blockBody cutF (sampleBody F)) N
          (pairT (cutData N p q A)
            (sampleData s (totalWidth N p q A) (timeNumerator zero N p q A) (totalWidth N p q A) (timeDenominator N q A R) x))) := by
  let d := cutData N p q A
  let W := totalWidth N p q A
  let y := sampleData s W (timeNumerator zero N p q A) W (timeDenominator N q A R) x
  have exact := grouped_from_zero (Γ := Γ) cutF (sampleBody F) N d y (cut_increasing N p q A)
    ((offset_at zero N p q A).eqTrans (offset_zero N p q A))
  exact qmul_congr (.eqRefl _) ((exact.eqTrans
    (GaussianRationalFiniteSum.sum_index_congr (sampleBody F) (offset_at N N p q A) (.eqRefl y))).eqSymm)

theorem actual_lower_partition_width_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
    (totalWidth (var 0) (var 1) (var 2) (var 3) ≐ lowerWidth (var 1) (var 2) (var 3)*pw (var 0) (var 3)) :=
  closeUniv 4 (GaussianEulerLowerTailRootGrid.time_width _ _ _ _)

end LeanProofs.IPRA.Analysis.GaussianEulerLowerTailPartition
