import IPRADerivations.Probability.MedianCounts
import IPRADerivations.Core.LinearCombination

/-!
# Finite Bernoulli bounds and the finite product bound of the FTA iteration

Packet: `FTA_iPRA`, Section "All constants and the primitive recursive iteration": the finite
Bernoulli arithmetic behind `eq:rho-q` and the block inequality `eq:block`, and the finite product
bound `eq:finite-product`, all cleared of denominators. With `K = y + 1` and `ρ = y/K = 1 − 1/K`:

* `binom_lower`: `y^(m+1) + (m+1) y^m ≤ (y+1)^(m+1)`;
* `block_half` (`eq:block`): `2 y^K ≤ K^K`, i.e. `ρ^K ≤ 1/2`;
* `bernoulli_down` (`eq:rho-q`): `K^n (K ∸ n) ≤ K y^n`, i.e. `ρ^n ≥ 1 − n/K`;
* `prod_pt`, `prod_bound` (`eq:finite-product`): for `x_i = a_i/D ≥ 0` with partial sum `s`,
  `∏_{i<m} (D + a_i) · (D ∸ ∑_{i<m} a_i) ≤ D^m · D`, i.e. `∏ (1 + x_i) ≤ 1/(1 − S)` when `S < 1`
  (and trivially otherwise).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Algebra.FTABounds

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.Probability.MedianCounts (subst_data)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Bernoulli -/

theorem binom_step {y m : PTm n}
    (ih : Γ ⊢[PRAAx] le (pw y (succ m) + succ m * pw y m) (pw (succ y) (succ m))) :
    Γ ⊢[PRAAx] le (pw y (succ (succ m)) + succ (succ m) * pw y (succ m)) (pw (succ y) (succ (succ m))) := by
  have a := natEq (pw_succ (Γ := Γ) y (succ m)); have b := natEq (pw_succ (Γ := Γ) y m)
  have c := natEq (pw_succ (Γ := Γ) (succ y) (succ m))
  refine le_trans (le_of_eq_add (d := succ m * pw y m) ?_)
    (le_congr (.eqRefl _) (pw_succ _ _).eqSymm (le_mul_mono ih (le_refl (succ y))))
  ipra_lc -a - (𝔞 m + 1) * b

/-- Variables: `0 = m`, `1 = y`. -/
private abbrev binomF : Fm PTm 2 :=
  le (pw (var 1) (succ (var 0)) + succ (var 0) * pw (var 1) (var 0)) (pw (succ (var 1)) (succ (var 0)))

private theorem binom₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] binomF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    have d := natEq (pw_zero (Γ := ([] : List (Fm PTm 1))) (succ (var 0)))
    refine le_of_eq_add (d := zero) ?_
    ipra_lc natEq (pw_succ (Γ := ([] : List (Fm PTm 1))) (succ (var 0)) zero) -
      natEq (pw_succ (Γ := ([] : List (Fm PTm 1))) (var 0) zero) + (𝔞 (var 0 : PTm 1) + 1) * d -
      (𝔞 (var 0 : PTm 1) + 1) * natEq (pw_zero (Γ := ([] : List (Fm PTm 1))) (var 0))
  · simp only [subst_le, PTm.subst_add, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact binom_step Prf.hyp0

/-- `y^(m+1) + (m+1) y^m ≤ (y+1)^(m+1)`. -/
theorem binom_lower (y m : PTm n) :
    Γ ⊢[PRAAx] le (pw y (succ m) + succ m * pw y m) (pw (succ y) (succ m)) := by
  have h := inst (Γ := Γ) binom₀ (![m, y] : Fin 2 → PTm n)
  simpa using h

/-- `eq:block`: `2 y^K ≤ K^K` for `K = y + 1`, i.e. `ρ^K ≤ 1/2`. -/
theorem block_half (y : PTm n) : Γ ⊢[PRAAx] le (two * pw y (succ y)) (pw (succ y) (succ y)) := by
  have b := binom_lower (Γ := Γ) y y
  refine le_trans (le_of_eq_add (d := pw y y) ?_) b
  ipra_lc -natEq (pw_succ (Γ := Γ) y y)

theorem bern_le {y m : PTm n} (h : Γ ⊢[PRAAx] le (succ m) (succ y))
    (ih : Γ ⊢[PRAAx] le (pw (succ y) m * monus (succ y) m) (succ y * pw y m)) :
    Γ ⊢[PRAAx] le (pw (succ y) (succ m) * monus (succ y) (succ m)) (succ y * pw y (succ m)) := by
  have e := eq_add_of_le h
  have m₁ : Γ ⊢[PRAAx] monus (succ y) m ≐ succ (monus (succ y) (succ m)) :=
    (congrMonus (e.eqTrans (by ipra_ring)) (.eqRefl m)).eqTrans (add_monus' _ _)
  -- K t ≤ y (t + 1)
  have kt : Γ ⊢[PRAAx] le (succ y * monus (succ y) (succ m)) (y * succ (monus (succ y) (succ m))) := by
    refine le_of_eq_add (d := m) ?_
    ipra_lc natEq e
  have step₁ := le_mul_mono (le_refl (pw (succ y) m)) kt
  have step₂ := le_mul_mono (le_refl y) (le_congr (congrMul (.eqRefl _) m₁) (.eqRefl _) ih)
  refine le_congr ?_ ?_ (le_trans step₁ (le_congr ?_ (.eqRefl _) step₂))
  · have p := natEq (pw_succ (Γ := Γ) (succ y) m)
    apply deriveNat; ipra_simps; linear_combination -𝔞 (monus (succ y) (succ m)) * p
  · have p := natEq (pw_succ (Γ := Γ) y m)
    apply deriveNat; ipra_simps; linear_combination -(𝔞 y + 1) * p
  · ipra_ring

theorem bern_step {y m : PTm n}
    (ih : Γ ⊢[PRAAx] le (pw (succ y) m * monus (succ y) m) (succ y * pw y m)) :
    Γ ⊢[PRAAx] le (pw (succ y) (succ m) * monus (succ y) (succ m)) (succ y * pw y (succ m)) := by
  refine .orE (le_total (succ m) (succ y)) (bern_le Prf.hyp0 ih.wk) ?_
  exact le_congr ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)).eqSymm (.eqRefl _) (zero_le _)

/-- Variables: `0 = m`, `1 = y`. -/
private abbrev bernF : Fm PTm 2 :=
  le (pw (succ (var 1)) (var 0) * monus (succ (var 1)) (var 0)) (succ (var 1) * pw (var 1) (var 0))

private theorem bern₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] bernF := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, PTm.subst_monus, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine le_congr ?_ ?_ (le_refl (succ (var 0) : PTm 1))
    · exact ((congrMul (pw_zero _) (monus_zero _)).eqTrans (one_mul _)).eqSymm
    · exact ((congrMul (.eqRefl _) (pw_zero _)).eqTrans ((mul_comm _ _).eqTrans (one_mul _))).eqSymm
  · simp only [subst_le, PTm.subst_monus, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact bern_step Prf.hyp0

/-- `eq:rho-q`: `K^m (K ∸ m) ≤ K y^m` for `K = y + 1`, i.e. `ρ^m ≥ 1 − m/K`. -/
theorem bernoulli_down (y m : PTm n) :
    Γ ⊢[PRAAx] le (pw (succ y) m * monus (succ y) m) (succ y * pw y m) := by
  have h := inst (Γ := Γ) bern₀ (![m, y] : Fin 2 → PTm n)
  simpa using h

/-! ## The finite product bound -/

theorem prod_pt_le {D α s : PTm n} (h : Γ ⊢[PRAAx] le (s + α) D) :
    Γ ⊢[PRAAx] le ((D + α) * monus D (s + α)) (D * monus D s) := by
  have e := eq_add_of_le h
  have m₁ : Γ ⊢[PRAAx] monus D s ≐ α + monus D (s + α) :=
    (congrMonus (e.eqTrans (by ipra_ring)) (.eqRefl s)).eqTrans (add_monus' _ _)
  have m₁' := natEq m₁
  refine le_of_eq_add (d := α * (s + α)) ?_
  ipra_lc 𝔞 D * m₁' + 𝔞 α * natEq e

/-- `(D + α)(D ∸ (s + α)) ≤ D (D ∸ s)`. -/
theorem prod_pt (D α s : PTm n) : Γ ⊢[PRAAx] le ((D + α) * monus D (s + α)) (D * monus D s) := by
  refine .orE (le_total (s + α) D) (prod_pt_le Prf.hyp0) ?_
  exact le_congr ((congrMul (.eqRefl _) Prf.hyp0).eqTrans (mul_zero _)).eqSymm (.eqRefl _) (zero_le _)

section Product

variable (a : PTm 2)

/-- `D + a(i, x)`, over `0 = i`, `1 = ⟨D, x⟩`. -/
def pB : PTm 2 := fstT (var 1) + Syn.subst ![var 0, sndT (var 1)] a

/-- `a(i, x)`, over `0 = i`, `1 = ⟨D, x⟩`. -/
def aB : PTm 2 := Syn.subst ![var 0, sndT (var 1)] a

theorem pB_at (i D x : PTm n) : Γ ⊢[PRAAx] Syn.subst ![i, pairT D x] (pB a) ≐ D + inst2 a i x := by
  have e : Syn.subst ![i, pairT D x] (pB a) = fstT (pairT D x) + inst2 a i (sndT (pairT D x)) := by
    simp only [pB, PTm.subst_add, subst_fstT, Syn.subst_var, subst_data]; simp
  rw [e]; exact congrAdd (fst_pair _ _) (congrInst2 a (.eqRefl _) (snd_pair _ _))

theorem aB_at (i D x : PTm n) : Γ ⊢[PRAAx] inst2 (aB a) i (pairT D x) ≐ inst2 a i x := by
  have e : inst2 (aB a) i (pairT D x) = inst2 a i (sndT (pairT D x)) := subst_data i (pairT D x) a
  rw [e]; exact congrInst2 a (.eqRefl _) (snd_pair _ _)

/-- `∏_{i<m} (D + a_i)`. -/
abbrev Pm (m D x : PTm n) : PTm n := ap2 (prodF (pB a)) m (pairT D x)
/-- `∑_{i<m} a_i`. -/
abbrev Sm (m D x : PTm n) : PTm n := ap2 (sumF (aB a)) m (pairT D x)

theorem prod_bound_step {m D x : PTm n}
    (ih : Γ ⊢[PRAAx] le (Pm a m D x * monus D (Sm a m D x)) (pw D m * D)) :
    Γ ⊢[PRAAx] le (Pm a (succ m) D x * monus D (Sm a (succ m) D x)) (pw D (succ m) * D) := by
  have pe := (prod_succ (Γ := Γ) (pB a) m (pairT D x)).eqTrans (congrMul (.eqRefl _) (pB_at a m D x))
  have se := (sum_succ' (Γ := Γ) (aB a) m (pairT D x)).eqTrans (congrAdd (.eqRefl _) (aB_at a m D x))
  have pt := prod_pt (Γ := Γ) D (inst2 a m x) (Sm a m D x)
  have c₁ := le_mul_mono (le_refl (Pm a m D x)) pt
  have c₂ := le_mul_mono (le_refl D) ih
  refine le_congr ?_ ?_ (le_trans c₁ (le_congr ?_ (.eqRefl _) c₂))
  · have p := natEq pe
    have q := natEq (congrMonus (.eqRefl D) se)
    apply deriveNat; ipra_simps
    linear_combination -𝔞 (monus D (Sm a m D x + inst2 a m x)) * p - 𝔞 (Pm a (succ m) D x) * q
  · have p := natEq (pw_succ (Γ := Γ) D m)
    apply deriveNat; ipra_simps; linear_combination -𝔞 D * p
  · ipra_ring

/-- Variables: `0 = m`, `1 = D`, `2 = x`. -/
private abbrev prodBF : Fm PTm 3 :=
  le (ap2 (prodF (pB a)) (var 0) (pairT (var 1) (var 2)) *
      monus (var 1) (ap2 (sumF (aB a)) (var 0) (pairT (var 1) (var 2))))
    (pw (var 1) (var 0) * var 1)

private theorem prodB₀ : ([] : List (Fm PTm 3)) ⊢[PRAAx] prodBF a := by
  refine ind _ (le_QF _ _) ?_ ?_
  · simp only [subst_le, PTm.subst_monus, PTm.subst_mul, subst_ap2, subst_ap2, subst_pairT, Syn.subst_var,
      Syn.inst_zero, Syn.inst_one, inst_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    refine le_congr ?_ ?_ (le_refl (var 0 : PTm 2))
    · exact ((congrMul (prod_zero _ _) ((congrMonus (.eqRefl _) (sum_zero _ _)).eqTrans (monus_zero _))).eqTrans
        (one_mul _)).eqSymm
    · exact ((congrMul (pw_zero _) (.eqRefl _)).eqTrans (one_mul _)).eqSymm
  · simp only [subst_le, PTm.subst_monus, PTm.subst_mul, subst_ap2, subst_ap2, subst_pairT, Syn.subst_var,
      Syn.repl_zero, repl_one, repl_two, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact prod_bound_step a Prf.hyp0

/-- `eq:finite-product`: `∏_{i<m} (D + a_i) · (D ∸ ∑_{i<m} a_i) ≤ D^m D`, i.e.
`∏ (1 + x_i) ≤ 1/(1 − S)` for `x_i = a_i/D`, `S < 1`. -/
theorem prod_bound (m D x : PTm n) :
    Γ ⊢[PRAAx] le (Pm a m D x * monus D (Sm a m D x)) (pw D m * D) := by
  have h := inst (Γ := Γ) (prodB₀ a) (![m, D, x] : Fin 3 → PTm n)
  simpa using h

end Product

end LeanProofs.IPRA.Algebra.FTABounds
