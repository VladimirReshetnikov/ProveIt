import IPRADerivations.AnalyticNumberTheory.EnergyRecovery
import IPRADerivations.AnalyticNumberTheory.LocalFactor

/-!
# The witness conversion "energy bound `c` ⇒ `8^r c` for `M`" (`thm:energy`)

Packet: `analytic-number-theory/riemann_ipra_equivalences_2026-11-20`, `energy.tex`, `thm:energy`: "replace
`G_r(c, N, M(N))` by `Q_N^r ≤ c (N!)^{2r} N^{r+1}` … An energy bound `c` gives `8^r c` for `M`", where
`G_r(c, N, z)` is `|z|^{2r} ≤ c N^{r+1}` (`matrices.tex`). Proof: "Taking the `r`th power gives the second witness"
(the packet's metatheory: `EnergyInequality.power_transfer`).

From `EnergyRecovery.energy_recovery`, `(N!)² M(N)² ≤ 8 Q_N`. Raising to the `r`th power (`pw_le_pw`) and splitting
the powers (`LocalFactor.pw_mul_base`, `pw_add`):

  `(N!)^{2r} |M(N)|^{2r} ≤ 8^r Q_N^r ≤ 8^r c (N!)^{2r} N^{r+1}`,

and the positive factor `(N!)^{2r}` cancels (`energy_witness`). The conversion holds for every `r`, every `N ≥ 1` and
every pair of bodies `M^±`; it does not depend on any parameter carried by `x`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.EnergyWitness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.EnergyRecovery (QN Mabs energy_recovery)
open LeanProofs.IPRA.AnalyticNumberTheory.EnergyJordan (pos_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.LocalFactor (pw_mul_base)
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.SquareReciprocal (cancel_le)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.Analysis.Products (fact)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

theorem pw_sq (a r : PTm n) : Γ ⊢[PRAAx] pw (a * a) r ≐ pw a (r + r) :=
  (pw_mul_base a a r).eqTrans (pw_add a r r).eqSymm

theorem pw_fact_pos (N m : PTm n) : Γ ⊢[PRAAx] pw (fact N) m ≐ succ (pred (pw (fact N) m)) := by
  have c := congrPw (Γ := Γ) (fact_pos N) (.eqRefl m)
  exact c.eqTrans ((pw_pos _ _).eqTrans (congrSucc (congrPred c.eqSymm)))

/-- Abstract step: `P₁ ≤ P₂`, `P₁ = A B`, `P₂ = E Q`, `Q ≤ c A R` give `A B ≤ A (E c R)`. -/
theorem witness_alg {A B E Qr c R P₁ P₂ : PTm n} (pr : Γ ⊢[PRAAx] le P₁ P₂) (e₁ : Γ ⊢[PRAAx] P₁ ≐ A * B)
    (e₂ : Γ ⊢[PRAAx] P₂ ≐ E * Qr) (hE : Γ ⊢[PRAAx] le Qr (c * A * R)) :
    Γ ⊢[PRAAx] le (A * B) (A * (E * c * R)) :=
  le_trans (le_congr e₁ e₂ pr)
    (le_congr (.eqRefl _) (by apply deriveNat; ipra_simps; ring) (le_mul_mono (le_refl E) hE))

/-- `thm:energy`, the second witness: `Q_N^r ≤ c (N!)^{2r} N^{r+1}` gives `|M(N)|^{2r} ≤ 8^r c N^{r+1}`. -/
theorem energy_witness (Mp Mn : PTm 2) {N x c r : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N))
    (hE : Γ ⊢[PRAAx] le (pw (QN Mp Mn N x) r) (c * pw (fact N) (r + r) * pw N (succ r))) :
    Γ ⊢[PRAAx] le (pw (Mabs Mp Mn N x) (r + r)) (pw (num 8) r * c * pw N (succ r)) := by
  have pr := pw_le_pw r (energy_recovery (Γ := Γ) Mp Mn (x := x) hN)
  have e₁ : Γ ⊢[PRAAx] pw ((fact N * fact N) * (Mabs Mp Mn N x * Mabs Mp Mn N x)) r ≐
      pw (fact N) (r + r) * pw (Mabs Mp Mn N x) (r + r) :=
    (pw_mul_base _ _ r).eqTrans (congrMul (pw_sq _ _) (pw_sq _ _))
  have e₂ := pw_mul_base (Γ := Γ) (num 8) (QN Mp Mn N x) r
  exact cancel_le (pw_fact_pos N (r + r)) (witness_alg pr e₁ e₂ hE)

/-- Variables `0 = N'` (`N = N' + 1`), `1 = x`, `2 = c`, `3 = r`. -/
abbrev witnessFormula (Mp Mn : PTm 2) : Fm PTm 4 :=
  le (pw (QN Mp Mn (succ (var 0)) (var 1)) (var 3))
      (var 2 * pw (fact (succ (var 0))) (var 3 + var 3) * pw (succ (var 0)) (succ (var 3))) ⟶
    le (pw (Mabs Mp Mn (succ (var 0)) (var 1)) (var 3 + var 3)) (pw (num 8) (var 3) * var 2 * pw (succ (var 0)) (succ (var 3)))

/-- The witness conversion as a closed sentence of iPRA, for every pair of bodies `M^±`. -/
theorem energy_witness_closed (Mp Mn : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4 (witnessFormula Mp Mn) :=
  closeUniv 4 (.impI (energy_witness Mp Mn (pos_succ _) Prf.hyp0))

end LeanProofs.IPRA.AnalyticNumberTheory.EnergyWitness
