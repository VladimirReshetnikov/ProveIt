import IPRADerivations.AnalyticNumberTheory.HeadDeficit

/-!
# Weighted block sums along a chain of blocks (`pnt_ipra_constructive_2026-11-14`, `con:one-step`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, proof of Lemma `con:one-step`:
"Place consecutive full blocks of length `H` starting at `s` … On all these blocks the weight `t − u` is at least
`t/2`." Discretely the weight is `u_d` (the harmonic logarithm of the divisor), and on a block `D₂ < d ≤ D₃` it is at
least `u_{D₂}`. For the weighted deficit sum `Σ [D₁ < d ≤ D₂] u_d g` (`HeadDeficit.hgB`):

* `bv_add`: `[D₁ < d ≤ D₃] = [D₁ < d ≤ D₂] + [D₂ < d ≤ D₃]` for `D₁ ≤ D₂ ≤ D₃`;
* `hg_split`: the weighted sum over `(D₁, D₃]` splits at `D₂`;
* `hg_weight`: `u_{D₂} Σ_{D₂<d≤D₃} g ≤ Σ_{D₂<d≤D₃} u_d g` (`u` is monotone, `HarmonicChebyshev.S_mono`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.BlockFamily

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.Harmonic (S hB)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicChebyshev (wt S_mono)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicMertens (le_scale)
open LeanProofs.IPRA.AnalyticNumberTheory.HarmonicLogSquareSum (U)
open LeanProofs.IPRA.AnalyticNumberTheory.LcmUpto (Psi)
open LeanProofs.IPRA.AnalyticNumberTheory.SummatoryCompose (hRB)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockSums (biB)
open LeanProofs.IPRA.AnalyticNumberTheory.BlockDeficit (gzB gz_at term_at bv bv_below bv_above bv_in tw tw_cases Bs')
open LeanProofs.IPRA.AnalyticNumberTheory.PointDeficit (dg)
open LeanProofs.IPRA.AnalyticNumberTheory.HeadDeficit (hgB hg_at)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.DiophantineNumberTheory.KhinchinBlock (sum_le_lin1)
open LeanProofs.IPRA.AnalyticNumberTheory.DivisorHarmonic (shift_fact')
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Signum (sg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `[D₁ < d ≤ D₃] = [D₁ < d ≤ D₂] + [D₂ < d ≤ D₃]`. -/
theorem bv_add {d D₁ D₂ D₃ : PTm n} (h12 : Γ ⊢[PRAAx] le D₁ D₂) (h23 : Γ ⊢[PRAAx] le D₂ D₃) :
    Γ ⊢[PRAAx] bv d D₁ D₃ ≐ bv d D₁ D₂ + bv d D₂ D₃ := by
  have h13 := le_trans h12 h23
  refine .orE (lt_or_le D₁ d) ?_ ?_
  · refine .orE (lt_or_le D₂ d) ?_ ?_
    · refine .orE (lt_or_le D₃ d) ?_ ?_
      · exact (bv_above h13.wk.wk.wk Prf.hyp0).eqTrans ((add_zero _).eqSymm.eqTrans
          (congrAdd (bv_above h12.wk.wk.wk Prf.hyp1).eqSymm (bv_above h23.wk.wk.wk Prf.hyp0).eqSymm))
      · exact (bv_in (show ((le d D₃) :: (lt D₂ d) :: (lt D₁ d) :: Γ) ⊢[PRAAx] lt D₁ d from .hyp (by simp)) Prf.hyp0).eqTrans ((zero_add _).eqSymm.eqTrans
          (congrAdd (bv_above h12.wk.wk.wk Prf.hyp1).eqSymm (bv_in Prf.hyp1 Prf.hyp0).eqSymm))
    · exact (bv_in Prf.hyp1 (le_trans Prf.hyp0 h23.wk.wk)).eqTrans ((add_zero _).eqSymm.eqTrans
        (congrAdd (bv_in Prf.hyp1 Prf.hyp0).eqSymm (bv_below h23.wk.wk Prf.hyp0).eqSymm))
  · exact (bv_below h13.wk Prf.hyp0).eqTrans ((add_zero _).eqSymm.eqTrans
      (congrAdd (bv_below h12.wk Prf.hyp0).eqSymm (bv_below h23.wk (le_trans Prf.hyp0 h12.wk)).eqSymm))

theorem split_alg {s a b c u g : PTm n} (h : Γ ⊢[PRAAx] a ≐ b + c) :
    Γ ⊢[PRAAx] (s * (a * u)) * g ≐ (s * (b * u)) * g + (s * (c * u)) * g := by
  have e := natEq h; apply deriveNat; ipra_simps; linear_combination 𝔞 s * 𝔞 u * 𝔞 g * e

abbrev Lay (x D₁ D₂ A Ds K L : PTm n) : PTm n := pairT x (BlockSums.Y D₁ D₂ (pairT A Ds) (pairT K (fact L)))

/-- `monus` is monotone in its first argument. -/
theorem monus_le_monus {a b c : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ ⊢[PRAAx] le (monus a c) (monus b c) := by
  refine .orE (le_total a c) ?_ ?_
  · exact le_congr (Prf.hyp0 : ((le a c) :: Γ) ⊢[PRAAx] monus a c ≐ zero).eqSymm (.eqRefl _) (zero_le _)
  · have e1 := natEq (eq_add_of_le (Prf.hyp0 : ((le c a) :: Γ) ⊢[PRAAx] le c a))
    have e2 := natEq (eq_add_of_le (le_trans (Prf.hyp0 : ((le c a) :: Γ) ⊢[PRAAx] le c a) h.wk))
    have h' := h.wk (ψ := le c a)
    ipra_le sl h' with e2 - e1

/-- The weighted deficit sum over `(D₁, D₃]` splits at `D₂`. -/
theorem hg_split {x D₁ D₂ D₃ A Ds K L : PTm n} (h12 : Γ ⊢[PRAAx] le D₁ D₂) (h23 : Γ ⊢[PRAAx] le D₂ D₃) :
    Γ ⊢[PRAAx] ap2 (sumF hgB) (succ x) (Lay x D₁ D₃ A Ds K L) ≐
      ap2 (sumF hgB) (succ x) (Lay x D₁ D₂ A Ds K L) + ap2 (sumF hgB) (succ x) (Lay x D₂ D₃ A Ds K L) := by
  have h12' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift D₁) (Syn.shift D₂) := by simpa [Fm.shift, Syn.shift] using h12.shift
  have h23' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift D₂) (Syn.shift D₃) := by simpa [Fm.shift, Syn.shift] using h23.shift
  refine sum_add2 _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT, shift_fact']
  exact (hg_at _ _ _ _ _ _ _ _).eqTrans ((split_alg (bv_add h12'.wk h23'.wk)).eqTrans
    (congrAdd (hg_at _ _ _ _ _ _ _ _).eqSymm (hg_at _ _ _ _ _ _ _ _).eqSymm))

/-- `u_{D₂} Σ_{D₂<d≤D₃} g ≤ Σ_{D₂<d≤D₃} u_d g`, for `K D₃ ≤ L` irrelevant: `u` is monotone. -/
theorem hg_weight {x D₂ D₃ A Ds K L : PTm n} (h23 : Γ ⊢[PRAAx] le D₂ D₃) :
    Γ ⊢[PRAAx] le (U D₂ K (fact L) * Bs' gzB x D₂ D₃ A Ds K L)
      (one * ap2 (sumF hgB) (succ x) (Lay x D₂ D₃ A Ds K L)) := by
  have h23' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift D₂) (Syn.shift D₃) := by simpa [Fm.shift, Syn.shift] using h23.shift
  refine sum_le_lin1 _ _ _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pairT, shift_fact', show Syn.shift (one : PTm n) = one by simp [Syn.shift],
    show Syn.shift (U D₂ K (fact L)) = U (Syn.shift D₂) (Syn.shift K) (fact (Syn.shift L)) by simp [Syn.shift]]
  refine le_congr (congrMul (.eqRefl _) ((term_at _ _ _ _ _ _ _).eqTrans (congrMul (.eqRefl _) (gz_at _ _ _ _ _ _ _)))).eqSymm
    (congrMul (.eqRefl _) (hg_at _ _ _ _ _ _ _ _)).eqSymm ?_
  refine tw_cases (d := var 0) h23'.wk _ ?_ ?_
  · have t := natEq (Prf.hyp0 : ((tw (var 0) (Syn.shift D₂) (Syn.shift D₃) ≐ zero) ::
      lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx] _)
    ipra_le 𝔞 (sg (var 0)) * 𝔞 (bv (var 0) (Syn.shift D₂) (Syn.shift D₃)) *
        𝔞 (U (var 0) (Syn.shift K) (fact (Syn.shift L))) *
        𝔞 (dg (Syn.shift A) (Syn.shift Ds) (Psi wt (quo (Syn.shift x) (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L))))
          (fact (Syn.shift L) * quo (Syn.shift x) (var 0))) with
      𝔞 (U (Syn.shift D₂) (Syn.shift K) (fact (Syn.shift L))) *
        𝔞 (dg (Syn.shift A) (Syn.shift Ds) (Psi wt (quo (Syn.shift x) (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L))))
          (fact (Syn.shift L) * quo (Syn.shift x) (var 0))) * t
  · have t := natEq (Prf.hyp0 : ((tw (var 0) (Syn.shift D₂) (Syn.shift D₃) ≐ one) :: le (var 0) (Syn.shift D₃) ::
      lt (Syn.shift D₂) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx] _)
    have hlt : ((tw (var 0) (Syn.shift D₂) (Syn.shift D₃) ≐ one) :: le (var 0) (Syn.shift D₃) ::
        lt (Syn.shift D₂) (var 0) :: lt (var 0) (Syn.shift (succ x)) :: Γ.map Fm.shift) ⊢[PRAAx]
        lt (Syn.shift D₂) (var 0) := .hyp (by simp)
    have um := monus_le_monus (c := S (Syn.shift K) (fact (Syn.shift L)))
      (S_mono (fact (Syn.shift L)) (le_scale (Syn.shift K) (le_of_lt hlt)))
    have pg := le_scale (dg (Syn.shift A) (Syn.shift Ds) (Psi wt (quo (Syn.shift x) (var 0))
      (pairT (Syn.shift K) (fact (Syn.shift L)))) (fact (Syn.shift L) * quo (Syn.shift x) (var 0))) um
    ipra_le sl pg with
      (𝔞 (U (var 0) (Syn.shift K) (fact (Syn.shift L))) - 𝔞 (U (Syn.shift D₂) (Syn.shift K) (fact (Syn.shift L)))) *
        𝔞 (dg (Syn.shift A) (Syn.shift Ds) (Psi wt (quo (Syn.shift x) (var 0)) (pairT (Syn.shift K) (fact (Syn.shift L))))
          (fact (Syn.shift L) * quo (Syn.shift x) (var 0))) * t

end LeanProofs.IPRA.AnalyticNumberTheory.BlockFamily
