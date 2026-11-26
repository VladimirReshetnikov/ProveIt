import IPRADerivations.Analysis.Gamma.CriticalPoints.NegativeIntervals.GaussianGammaNegativeCriticalEndpoints
import IPRADerivations.Analysis.Gamma.Digamma.Series.GaussianGammaDigammaRescale

/-!
# Rescaling the shifted negative digamma

Multiplying both rational coordinates by a positive integer preserves
each reciprocal correction row exactly. Native positive digamma
rescaling then preserves the shifted name, including its confluence
across the successive dyadic grids.
-/

set_option autoImplicit false
set_option maxHeartbeats 1500000

namespace LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalRescale

open_ipra
open GaussianGammaCanonicalExponent (constantF constant_regular)
open GaussianGammaNegativeCriticalCorrection (guard row body bottomDen correction positiveSum row_at row_den_positive)
open GaussianGammaNegativeCriticalEndpoints (nameF nameData shifted_source)
open GaussianNameArithmetic (add_equivalent)
open GaussianNameEquivalence (crossEquivalent cross_to_diagonal)
open GaussianPositiveRationalLogarithm (fraction)
open GaussianRationalHorner (positive_product)
open GaussianRationalSyntheticDivision (qsub_congr)
open GaussianStirlingRationalTelescopers (fraction_same)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)
local notation "DF" => GaussianGammaDigammaNative.nameF
local notation "dd" => GaussianGammaDigammaNative.data

theorem scaled_guard (a b s : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] guard (s*a) (s*b) := by
  have lt' := h.andE₂
  unfold lt at lt'
  exact .andI (positive_product _ _ hs h.andE₁) (by unfold lt; ipra_le 𝔞(s)*sl lt'+sl hs)

theorem scaled_denominator (a b j s : PTm n) (h : Γ ⊢[PRAAx] lt a b) :
    Γ ⊢[PRAAx] bottomDen (s*a) (s*b) j ≐ s*bottomDen a b j := by
  have bound : Γ ⊢[PRAAx] le a (succ j*b) := le_trans (le_of_lt h) (by ipra_le 𝔞(j)*𝔞(b))
  have e := natEq (eq_add_of_le bound)
  have eq : Γ ⊢[PRAAx] succ j*(s*b) ≐ s*bottomDen a b j+s*a := by
    unfold bottomDen
    apply deriveNat
    ipra_simps
    linear_combination 𝔞(s)*e
  exact (congrMonus eq (.eqRefl _)).eqTrans (add_monus _ _)

theorem row_rescale (a b j s : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] row (s*a) (s*b) j ≐ row a b j := by
  have original := row_den_positive a b j h.andE₂
  have scaled := row_den_positive (s*a) (s*b) j (scaled_guard a b s h hs).andE₂
  have e := natEq (scaled_denominator a b j s h.andE₂)
  exact fraction_same (s*b) (bottomDen (s*a) (s*b) j) b (bottomDen a b j) scaled original
    (by apply deriveNat; ipra_simps; linear_combination -𝔞(b)*e)

theorem sum_rescale (a b N s : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] positiveSum (s*a) (s*b) N ≐ positiveSum a b N := by
  apply GaussianRationalFiniteSum.sum_congr_bounded
  refine .allI (.impI ?_)
  have h' : Γ.map Fm.shift ⊢[PRAAx] guard (Syn.shift a) (Syn.shift b) :=
    by simpa only [Fm.shift,Syn.shift,GaussianGammaNegativeCriticalCorrection.subst_guard] using h.shift
  have hs' : Γ.map Fm.shift ⊢[PRAAx] le one (Syn.shift s) := by simpa [Fm.shift,Syn.shift] using hs.shift
  simpa only [Syn.shift,subst_pairT,PTm.subst_mul] using
    (row_at (Syn.shift s*Syn.shift a) (Syn.shift s*Syn.shift b) (var 0)).eqTrans
      ((row_rescale (Syn.shift a) (Syn.shift b) (var 0) (Syn.shift s) h'.wk hs'.wk).eqTrans
        (row_at (Syn.shift a) (Syn.shift b) (var 0)).eqSymm)

theorem correction_rescale (a b N s : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] correction (s*a) (s*b) N ≐ correction a b N :=
  qsub_congr (sum_rescale a b (succ N) s h hs)
    (fraction_same (s*b) (s*a) b a (positive_product _ _ hs h.andE₁) h.andE₁ (by ipra_ring))

theorem original_rescale (a b N s : PTm n) (h : Γ ⊢[PRAAx] guard a b) (hs : Γ ⊢[PRAAx] le one s) :
    Γ ⊢[PRAAx] crossEquivalent nameF nameF (nameData (s*a) (s*b) N) (nameData a b N) := by
  let x := dd (s*b+s*a) (s*b)
  let y := dd (b+a) b
  let l := correction (s*a) (s*b) N
  let r := correction a b N
  have hx := GaussianGammaDigammaNative.name_regular _ _ (shifted_source _ _ (scaled_guard a b s h hs))
  have hy := GaussianGammaDigammaNative.name_regular _ _ (shifted_source a b h)
  have e := GaussianGammaDigammaRescale.native_rescale (b+a) b s (shifted_source a b h) hs
  have E : Γ ⊢[PRAAx] crossEquivalent DF DF x y :=
    GaussianGammaCompactCutoffAlignment.cross_data_congr DF DF _ x _ y
      (GaussianGammaDigammaRescale.datum_congr (by ipra_ring) (.eqRefl _)) (.eqRefl _) e
  have C := GaussianSignedNameExponentialOrder.constant_equal_cross l r (correction_rescale a b N s h hs)
  exact add_equivalent DF DF constantF constantF x y l r hx hy (constant_regular l) (constant_regular r)
    (cross_to_diagonal _ _ _ _ E) (cross_to_diagonal _ _ _ _ C)

end LeanProofs.IPRA.Analysis.GaussianGammaNegativeCriticalRescale
