import IPRADerivations.Analysis.Gamma.Digamma.CriticalPoints.GaussianGammaDigammaDyadicCrossing
import IPRADerivations.Analysis.Gamma.Digamma.Comparison.GaussianGammaDigammaLipschitz
import IPRADerivations.Analysis.Euler.PositiveAxis.SharpRates.GaussianEulerSharpScheduledApproximation

/-!
# The dyadic mesh and adjacent digamma observations

At requested precision p, the grid on [1,2] has 2^(p+6) equal cells, with
the digamma observation clock p+6. The upper slope and the two independent
observation errors give an explicit upper bound of 4/2^(p+6) on the
increase between adjacent actual observations.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianGammaDigammaDyadicMesh

open_ipra
open GaussianCoefficientNameBounds (unit unit_positive subst_unit)
open GaussianEulerSharpScheduledApproximation (two_bit_identity four_bit_identity)
open GaussianGammaDigammaDyadicCrossing (sample)
open GaussianNamedInverseRate (rateNumerator rateDenominator denominator_positive)
open RationalValueBounds (upper upper_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}
local notation "𝔞" t:max => Groth.ι (Q.mk Γ t)

def clock (p : PTm n) : PTm n := p+num 6
def grid (p : PTm n) : PTm n := unit (clock p)

ipra_subst clock

@[simp] theorem subst_grid {k : ℕ} (σ : Fin n → PTm k) (p : PTm n) :
    Syn.subst σ (grid p) = grid (Syn.subst σ p) := by simp only [grid, subst_unit, subst_clock]

theorem grid_scale (p : PTm n) : Γ ⊢[PRAAx] grid p ≐ num 64*unit p := by
  have e : Γ ⊢[PRAAx] clock p ≐ (p+num 4)+num 2 := by unfold clock; ipra_ring
  exact (congrAp2 powF e (.eqRefl two)).eqTrans
    ((two_bit_identity (p+num 4)).eqTrans ((congrMul (.eqRefl _) (four_bit_identity p)).eqTrans (by ipra_ring)))

theorem grid_positive (p : PTm n) : Γ ⊢[PRAAx] le one (grid p) := unit_positive (clock p)

theorem grid_threshold (p : PTm n) : Γ ⊢[PRAAx] le (num 16) (grid p) := by
  have h := unit_positive (Γ := Γ) p
  have e := grid_scale (Γ := Γ) p
  refine le_congr (.eqRefl _) e.eqSymm ?_
  ipra_le 64*sl h+48

theorem adjacent_upper (p i : PTm n) : Γ ⊢[PRAAx]
    upper (sample (clock p) (grid p) (succ i)) (sample (clock p) (grid p) i) (num 4) (grid p) := by
  let N := grid p
  let t := clock p
  let a := N+i
  let b := N+succ i
  have e : Γ ⊢[PRAAx] b ≐ one+a := by dsimp only [a,b]; ipra_ring
  have hab : Γ ⊢[PRAAx] le a b := le_of_eq_add (e.eqTrans (add_comm _ _))
  have gap : Γ ⊢[PRAAx] monus b a ≐ one := (congrMonus e (.eqRefl _)).eqTrans (add_monus _ _)
  have h := GaussianGammaDigammaLipschitz.unit_upper_at t t a b N (grid_positive p) (le_add_right _ _) hab
  refine upper_mono _ _ _ _ _ _ (denominator_positive N t t (grid_positive p)) h ?_
  apply le_congr ?_ (.eqRefl _) (le_refl (num 4*rateDenominator N t t))
  dsimp only [rateNumerator,rateDenominator]
  change Γ ⊢[PRAAx] num 4*(N*N*N) ≐ (two*monus b a*N*N+N*(N+N))*N
  have eg := natEq gap
  apply deriveNat
  ipra_simps
  linear_combination (-2*𝔞(N)^3)*eg

theorem actual_original_digamma_adjacent_grid_upper_closed :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2
      (upper (sample (clock (var 0)) (grid (var 0)) (succ (var 1)))
        (sample (clock (var 0)) (grid (var 0)) (var 1)) (num 4) (grid (var 0))) :=
  closeUniv 2 (adjacent_upper _ _)

end LeanProofs.IPRA.Analysis.GaussianGammaDigammaDyadicMesh
