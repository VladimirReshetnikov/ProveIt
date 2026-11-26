import IPRADerivations.Analysis.Barnes.Logarithms.PositiveAxis.ThirdDerivative.GaussianBarnesCanonicalThirdDerivativePositiveMargin
import IPRADerivations.Analysis.Barnes.HeadProducts.GaussianBarnesCanonicalFactorApartness
import IPRADerivations.Analysis.Barnes.Taylor.CenteredCharts.GaussianBarnesCanonicalHeadRelativeLogMargin
import IPRADerivations.Analysis.Barnes.Taylor.FirstDerivative.GaussianBarnesCanonicalDerivativeTailBinding
import IPRADerivations.Analysis.Barnes.Taylor.RelativeExpansions.GaussianBarnesCanonicalRelativeLogIncrement
import IPRADerivations.Analysis.Names.FiniteOperations.GaussianNamedFiniteProductApartness

/-! The positive real margin bounds the original retained powers from below, giving a
denominator-independent step threshold for the original relative logarithm. -/

set_option autoImplicit false
set_option maxHeartbeats 650000

namespace LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveRelativeLogarithmChart

open_ipra
open Common
open ComplexLogarithmRemainder (add oneCode normSq_one)
open GaussianBarnesCanonicalBaseProductShift (powerBody powerProduct power_at)
open GaussianBarnesCanonicalFactor (powerValue)
open GaussianBarnesCanonicalLogSchedule (initial initial_positive)
open GaussianBarnesCanonicalThirdDerivativePositiveMargin (source step base_lower shifted_center)
open GaussianBarnesCanonicalThirdLogarithmRows (center)
open GaussianFactorBudget (power_positive power_monotone_length)
open GaussianNamedFiniteProductApartness (weaken_margin)
open GaussianRationalFiniteProduct (product_zero product_succ)
open GaussianRationalHorner (ofGaussian_represents)
open GaussianRationalLowerBounds (lower lower_congr lower_from_representation product_lower)
open GaussianRationalReciprocal (qone)
open GaussianRationalSyntheticDivision (qmul_congr)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "disk" => GaussianBarnesCanonicalLogCofinal.source
local notation "pointData" => GaussianBarnesCanonicalPolynomialShift.data

def margin (K N : PTm n) : PTm n := pw (pw K N) N

def threshold (R K : PTm n) : PTm n :=
  num 16 + num 4*GaussianBarnesCanonicalHeadRelativeLogMargin.gain R (initial R) (margin K (initial R))

private def prefixLaw (A B K N i : PTm n) : Fm PTm n :=
  le i N ⟶ lower (powerProduct (center A B) B i) one (pw (pw K N) i)

@[simp] private theorem subst_prefixLaw {m : ℕ} (σ : Fin n → PTm m) (A B K N i : PTm n) :
    (prefixLaw A B K N i).subst σ =
      prefixLaw (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ K) (Syn.subst σ N) (Syn.subst σ i) := by
  simp [prefixLaw,one]

private theorem prefix_zero (A B K N : PTm n) : Γ ⊢[PRAAx] prefixLaw A B K N zero := by
  have u : Γ ⊢[PRAAx] lower (qone : PTm n) one one :=
    lower_from_representation _ oneCode one one one (le_refl _) (le_refl _) (ofGaussian_represents _ _ (le_refl _))
      (le_congr (by ipra_ring) (congrMul (.eqRefl _) normSq_one).eqSymm (le_refl _))
  exact .impI (lower_congr (product_zero powerBody (pointData (center A B) B)).eqSymm
    (.eqRefl _) (pw_zero (pw K N)).eqSymm u).wk

private theorem prefix_succ (A B K N i : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hK : Γ ⊢[PRAAx] le one K) (hA : Γ ⊢[PRAAx] le B (K*A))
    (previous : Γ ⊢[PRAAx] prefixLaw A B K N i) : Γ ⊢[PRAAx] prefixLaw A B K N (succ i) := by
  refine .impI ?_
  let z := center A B
  let D := pw K N
  let Δ := le (succ i) N :: Γ
  have hi : Δ ⊢[PRAAx] lt i N := Prf.hyp0
  have hD := power_positive (Γ := Δ) K N hK.wk
  have prev := Prf.impE previous.wk (le_of_lt hi)
  let b := GaussianBarnesCanonicalFactor.base z B (succ i)
  have rb := base_lower (Γ := Δ) A B i K hB.wk hK.wk hA.wk
  have hp := GaussianBarnesCanonicalFactorApartness.power_lower b K (succ i) hK.wk rb
  have last : Δ ⊢[PRAAx] lower (powerValue z B (succ i)) one D :=
    weaken_margin _ _ _ (power_positive K (succ i) hK.wk)
      (power_monotone_length K (succ i) N hK.wk hi) hp
  have prod := product_lower (powerProduct z B i) (powerValue z B (succ i)) one (pw D i) one D
    (power_positive D i hD) hD prev last
  have read := (product_succ (Γ := Δ) powerBody i (pointData z B)).eqTrans
    (qmul_congr (.eqRefl _) (power_at i z B))
  exact lower_congr read.eqSymm (one_mul one) (pw_succ D i).eqSymm prod

theorem power_margin (A B K N : PTm n) (hB : Γ ⊢[PRAAx] le one B)
    (hK : Γ ⊢[PRAAx] le one K) (hA : Γ ⊢[PRAAx] le B (K*A)) : Γ ⊢[PRAAx]
    GaussianNameReciprocal.lower (powerProduct (center A B) B N) (margin K N) := by
  let sh (x : PTm n) := Syn.shift x
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,Syn.shift,sh,one] using hB.shift
  have hk : Γ.map Fm.shift ⊢[PRAAx] le one (sh K) := by simpa [Fm.shift,Syn.shift,sh,one] using hK.shift
  have ha : Γ.map Fm.shift ⊢[PRAAx] le (sh B) (sh K*sh A) := by simpa [Fm.shift,Syn.shift,sh] using hA.shift
  have all : Γ ⊢[PRAAx] .all (prefixLaw (sh A) (sh B) (sh K) (sh N) (var 0)) := by
    refine PRA.qfInd _ ⟨le_QF _ _,le_QF _ _⟩ ?_ ?_
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using
        prefix_zero (Γ := Γ) A B K N
    · simpa only [subst_prefixLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift,sh] using
        prefix_succ (sh A) (sh B) (sh K) (sh N) (var 0) hb.wk hk.wk ha.wk Prf.hyp0
  have last : Γ ⊢[PRAAx] prefixLaw A B K N N := by
    simpa only [subst_prefixLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift,sh] using all.allE N
  exact .impE last (le_refl N)

theorem admission (A C B R H K : PTm n) (h : Γ ⊢[PRAAx] source A C B H K)
    (hz : Γ ⊢[PRAAx] disk (center A B) R B) (hw : Γ ⊢[PRAAx] disk (center C B) R B)
    (hs : Γ ⊢[PRAAx] le (threshold R K*H) B) : Γ ⊢[PRAAx]
    GaussianBarnesCanonicalRelativeLogIncrement.source (center A B) (step A C) R B ⋏
      GaussianBarnesCanonicalDerivativeTailBinding.input (center A B) (step A C) R B H := by
  let N := initial R
  let z := center A B
  let v := step A C
  let M := margin K N
  let G := GaussianBarnesCanonicalHeadRelativeLogMargin.gain R N M
  have hB := h.andE₁
  have hK := h.andE₂.andE₂.andE₂.andE₁
  have hl := power_margin A B K N hB hK h.andE₂.andE₂.andE₂.andE₂.andE₁
  have hM := power_positive (pw K N) N (power_positive K N hK)
  have hh := h.andE₂.andE₂.andE₂.andE₂.andE₂.andE₂
  have eq := GaussianRootAlgebra.normSq_equal (shifted_center (Γ := Γ) A C B)
  have raw : Γ ⊢[PRAAx] disk (add z v) R B := .andI hB (le_congr eq.eqSymm (.eqRefl _) hw.andE₂)
  have stay : Γ ⊢[PRAAx] le (num 16*H) B := le_trans (le_of_eq_add (d := num 4*G*H)
    (by dsimp only [threshold,G,N,M]; ipra_ring)) hs
  have small : Γ ⊢[PRAAx] le (num 4*(G*H)) B := le_trans (le_of_eq_add (d := num 16*H)
    (by dsimp only [threshold,G,N,M]; ipra_ring)) hs
  have hH : Γ ⊢[PRAAx] le H B := le_trans (le_of_eq_add (d := num 15*H) (by ipra_ring)) stay
  have enlarge : Γ ⊢[PRAAx] le B (B*N) :=
    le_congr (one_mul B) (mul_comm N B) (mul_le_mul_right B (initial_positive R))
  have head := GaussianBarnesCanonicalHeadRelativeLogMargin.source_of_small z v R B H N M
    (.andI hB (.andI hz.andE₂ (.andI raw.andE₂ hh))) hH hM hl small
  have row₀ := GaussianBarnesCanonicalLogCofinalRate.initial_source z R B hz
  have row₁ := GaussianBarnesCanonicalLogCofinalRate.initial_source (add z v) R B raw
  exact .andI (.andI hz (.andI raw head)) (.andI row₀ (.andI row₁ (.andI hh (.andI (le_trans stay enlarge) hH))))

end LeanProofs.IPRA.Analysis.GaussianBarnesCanonicalPositiveRelativeLogarithmChart
