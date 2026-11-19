import IPRADerivations.DiophantineNumberTheory.Coprime
import IPRADerivations.AnalyticNumberTheory.CrtBijection
import IPRADerivations.Foundations.AuxiliaryEnvelope

/-!
# Weights of reduced monomials and the cover count (`ipra_coherent_methods_2026-11-15`, `thm:weighted-norm-degree`, `cor:weighted-cover`)

Packet: `foundations/ipra_coherent_methods_2026-11-15`, `05_norms.tex`.

`thm:weighted-norm-degree`, first step: "If `mi + dj = mi' + dj'` with `0 ≤ j, j' < m`, then
`m` divides `d(j − j')`. Coprimality implies that `m` divides `j − j'`, and its absolute value
is less than `m`. Thus `j = j'` and `i = i'`. Distinct reduced monomials therefore have distinct
weights. This proves the uniqueness of the maximum."

`cor:weighted-cover`: "Suppose every finite list of distinct points in `S` has its `Φ_L`
vectors covered by at most `M` supplied proper rational subspaces. Then every such list has
length at most `ML`." Proof: "For each point scan the finite list of subspaces and assign it to
the first one containing its vector. ... The points assigned to one subspace form a distinct
sublist, so the preceding corollary bounds that sublist by `L`. The original length is the sum
of at most `M` such lengths, hence at most `ML`."

* `weight_core`, `weight_unique`: for `m ≥ 1`, `gcd(m, d) = 1` and `j, j' < m`:
  `m i + d j = m i' + d j'` gives `j = j'` and `i = i'`;
* `weight_unique_closed`: the same, closed over `m − 1, d, i, i', j, j'`;
* `weighted_cover`: an assignment of the positions `i < N` to classes below `M`, each class
  receiving at most `L` positions, gives `N ≤ M · L`
  (`Foundations/AuxiliaryEnvelope.fibre_count`).

Not derived here: the determinant computation of the leading coefficient and the degree of
the norm (`thm:weighted-norm-degree`, the rescaling argument), `lem:weighted-fiber`.
-/

namespace LeanProofs.IPRA.Foundations.WeightedMonomials

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gauss dvd_of_eq')
open LeanProofs.IPRA.AnalyticNumberTheory.CrtBijection (rem_small)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Distinct reduced monomials have distinct weights -/

/-- `m ∣ d (j' ∸ j)` from the equality of the weights, for `j ≤ j'`. -/
theorem weight_dvd {m d i i' j j' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hle : Γ ⊢[PRAAx] le j j') (h : Γ ⊢[PRAAx] m * i + d * j ≐ m * i' + d * j') :
    Γ ⊢[PRAAx] dvd m (d * monus j' j) := by
  refine .orE (le_total i' i) ?_ ?_
  · refine dvd_of_eq' hm.wk (w := monus i i') ?_
    have a := natEq (h.wk (ψ := le i' i))
    have e₁ := natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le i' i)))
    have e₂ := natEq (eq_add_of_le (hle.wk (ψ := le i' i)))
    apply deriveNat; ipra_simps
    linear_combination -a + 𝔞 m * e₁ - 𝔞 d * e₂
  · refine dvd_of_eq' hm.wk (w := zero) ?_
    have z : (le i i' :: Γ) ⊢[PRAAx] zero ≐ d * monus j' j + m * monus i' i := by
      have a := natEq (h.wk (ψ := le i i'))
      have e₁ := natEq (eq_add_of_le (Prf.hyp0 (Γ := Γ) (φ := le i i')))
      have e₂ := natEq (eq_add_of_le (hle.wk (ψ := le i i')))
      apply deriveNat; ipra_simps
      linear_combination a + 𝔞 m * e₁ + 𝔞 d * e₂
    exact ((monus_zero _).eqSymm.eqTrans (le_of_eq_add z)).eqTrans (mul_zero m).eqSymm

/-- The case `j ≤ j'`. -/
theorem weight_core {m d i i' j j' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hg : Γ ⊢[PRAAx] gcd m d ≐ one) (hj' : Γ ⊢[PRAAx] lt j' m) (hle : Γ ⊢[PRAAx] le j j')
    (h : Γ ⊢[PRAAx] m * i + d * j ≐ m * i' + d * j') : Γ ⊢[PRAAx] (j ≐ j') ⋏ (i ≐ i') := by
  have ej := eq_add_of_le hle
  have hlt : Γ ⊢[PRAAx] lt (monus j' j) m :=
    lt_of_le_of_lt (le_of_eq_add (ej.eqTrans (add_comm _ _))) hj'
  have he : Γ ⊢[PRAAx] monus j' j ≐ zero :=
    (rem_small hm hlt).eqSymm.eqTrans (gauss hm hg (weight_dvd hm hle h))
  refine .andI (ej.eqTrans ((congrAdd (.eqRefl j) he).eqTrans (add_zero j))).eqSymm
    (mul_cancel hm ?_)
  have a := natEq h
  have e₁ := natEq ej
  have e₂ := natEq he
  apply deriveNat; ipra_simps
  linear_combination a + 𝔞 d * e₁ + 𝔞 d * e₂

/-- `thm:weighted-norm-degree`, uniqueness of weights: reduced monomials `X^i Y^j`, `j < m`,
of equal weight `m i + d j` are equal, when `gcd(m, d) = 1`. -/
theorem weight_unique {m d i i' j j' : PTm n} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (hg : Γ ⊢[PRAAx] gcd m d ≐ one) (hj : Γ ⊢[PRAAx] lt j m) (hj' : Γ ⊢[PRAAx] lt j' m)
    (h : Γ ⊢[PRAAx] m * i + d * j ≐ m * i' + d * j') : Γ ⊢[PRAAx] (j ≐ j') ⋏ (i ≐ i') :=
  .orE (le_total j j') (weight_core hm.wk hg.wk hj'.wk Prf.hyp0 h.wk)
    (.andI (Prf.andE₁ (weight_core hm.wk hg.wk hj.wk Prf.hyp0 h.wk.eqSymm)).eqSymm
      (Prf.andE₂ (weight_core hm.wk hg.wk hj.wk Prf.hyp0 h.wk.eqSymm)).eqSymm)

/-- Variables: `0 = m − 1`, `1 = d`, `2 = i`, `3 = i'`, `4 = j`, `5 = j'`. -/
abbrev weightFormula : Fm PTm 6 :=
  (gcd (succ (var 0)) (var 1) ≐ one) ⟶ lt (var 4) (succ (var 0)) ⟶ lt (var 5) (succ (var 0)) ⟶
    (succ (var 0) * var 2 + var 1 * var 4 ≐ succ (var 0) * var 3 + var 1 * var 5) ⟶
      ((var 4 ≐ var 5) ⋏ (var 2 ≐ var 3))

theorem weight_unique_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 6 weightFormula :=
  closeUniv 6 (.impI (.impI (.impI (.impI
    (weight_unique (congrSucc (pred_succ _).eqSymm) (.hyp (by simp)) hyp2 Prf.hyp1 Prf.hyp0)))))

/-! ## The cover count -/

/-- `cor:weighted-cover`: if every position `i < N` is assigned a class below `M` (the first
subspace containing its vector) and every class receives at most `L` positions, then
`N ≤ M · L`. -/
theorem weighted_cover (σ : PTm 2) {M L x : PTm n} (N : PTm n)
    (hr : Γ ⊢[PRAAx] Permutation.rangeAll σ M x)
    (hc : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶
      le (AuxiliaryEnvelope.cnt σ (Syn.shift N) (var 0) (Syn.shift x)) (Syn.shift L))) :
    Γ ⊢[PRAAx] le N (M * L) :=
  AuxiliaryEnvelope.fibre_count σ N hr hc

end LeanProofs.IPRA.Foundations.WeightedMonomials
