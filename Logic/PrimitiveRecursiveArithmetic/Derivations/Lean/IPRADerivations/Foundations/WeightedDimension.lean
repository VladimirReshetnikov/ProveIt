import IPRADerivations.Foundations.SumLinear
import IPRADerivations.Foundations.FiniteSetExponential
import IPRADerivations.Foundations.BoundedFormulas
import IPRADerivations.Foundations.EigenvalueGrid
import IPRADerivations.Core.Fubini

/-!
# The eventual dimension formula (`ipra_coherent_methods_2026-11-15`, `prop:weighted-dimension`)

Packet: `foundations/ipra_coherent_methods_2026-11-15`, proposition `prop:weighted-dimension`:
with `n(L) = ∑_{j<m} max(0, 1 + ⌊(L - d j)/m⌋)` and `g_0 = (m - 1)(d - 1)/2`, for
`L ≥ max(0, m d - m - d)`, `n(L) = L + 1 - g_0`. Proof in the packet: "each summand is
nonnegative and the maximum with zero can be removed. The residues `r_j` of `L - d j` modulo
`m` are a permutation of `0, …, m - 1` ... Summing these `m` equations gives ..."

Natural-number form, with `m = m' + 1`, `d = d' + 1`. The numerators are shifted by `m d`:
`T_j = L + m d - d j ≥ 0`, so `⌊T_j / m⌋ = ⌊(L - d j)/m⌋ + d`. The row count is the packet's
natural-number program: zero if `L < d j`, and `1 + ⌊(L - d j)/m⌋` otherwise (`CG`).

* `T_add`: `T_j + d j = L + m d` for `j < m`;
* `count_pt`: `C_j + d = 1 + ⌊T_j / m⌋` for `j < m`, in both branches of the program, under
  `d (m - 1) ≤ L + m` (that is, `L ≥ m d - m - d`);
* `weighted_dimension`: if the residues `T_j mod m` (`j < m`) have the same sum as
  `0, …, m - 1`, then `2 n(L) + (m - 1)(d - 1) = 2 (L + 1)`.

The three summations are instances of `sum_linear` (`Foundations/SumLinear`), and the factor
`m` is cancelled at the end. The hypothesis on the sum of residues is what "the residues are a
permutation" provides; the permutation itself (from coprimality of `m` and `d`) is not derived
in this module. That `(m - 1)(d - 1)` is even is a consequence of the displayed equation.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.WeightedDimension

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Signum (sg)
open LeanProofs.IPRA.Probability.ProductPower (div_eq' rem_lt'')
open LeanProofs.IPRA.Foundations.FiniteSetExponential (pair_fst)
open LeanProofs.IPRA.Foundations.BoundedFormulas (sg_of_pos sg_of_zero)
open LeanProofs.IPRA.Foundations.SumLinear
open LeanProofs.IPRA.Foundations.EigenvalueGrid (mul_cancel)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem sh_zero : Syn.shift (zero : PTm k) = zero := by simp [Syn.shift]
theorem sh_succ (a : PTm k) : Syn.shift (succ a) = succ (Syn.shift a) := by simp [Syn.shift]
theorem sh_add (a b : PTm k) : Syn.shift (a + b) = Syn.shift a + Syn.shift b := by
  simp [Syn.shift]
theorem sh_mul (a b : PTm k) : Syn.shift (a * b) = Syn.shift a * Syn.shift b := by
  simp [Syn.shift]

theorem inst2_zB (j x : PTm k) : inst2 (zero : PTm 2) j x = zero := by simp [inst2]

/-! ## The bodies; variables `0 = j`, `1 = L`, `2 = m`, `3 = d` -/

/-- `T_j = L + m d ∸ d j`. -/
def TG : PTm 4 := monus (var 1 + var 2 * var 3) (var 3 * var 0)
/-- `⌊T_j / m⌋`. -/
def QG : PTm 4 := quo (monus (var 1 + var 2 * var 3) (var 3 * var 0)) (var 2)
/-- `T_j mod m`. -/
def RG : PTm 4 := rem (monus (var 1 + var 2 * var 3) (var 3 * var 0)) (var 2)
/-- The row count: `0` if `L < d j`, and `1 + ⌊(L ∸ d j) / m⌋` otherwise. -/
def CG : PTm 4 :=
  sg (monus (succ (var 1)) (var 3 * var 0)) * (one + quo (monus (var 1) (var 3 * var 0)) (var 2))

/-- `T_j`. -/
abbrev T (j L m d : PTm k) : PTm k := monus (L + m * d) (d * j)

theorem T_at (j L m d : PTm k) :
    Γ ⊢[PRAAx] inst2 (bd TG) j (pairT L (pairT m d)) ≐ T j L m d := by
  have e : Syn.subst ![j, L, m, d] TG = T j L m d := by simp [TG]
  rw [← e]
  exact bd_at TG j L m d

theorem Q_at (j L m d : PTm k) :
    Γ ⊢[PRAAx] inst2 (bd QG) j (pairT L (pairT m d)) ≐ quo (T j L m d) m := by
  have e : Syn.subst ![j, L, m, d] QG = quo (T j L m d) m := by simp [QG]
  rw [← e]
  exact bd_at QG j L m d

theorem R_at (j L m d : PTm k) :
    Γ ⊢[PRAAx] inst2 (bd RG) j (pairT L (pairT m d)) ≐ rem (T j L m d) m := by
  have e : Syn.subst ![j, L, m, d] RG = rem (T j L m d) m := by simp [RG]
  rw [← e]
  exact bd_at RG j L m d

theorem C_at (j L m d : PTm k) :
    Γ ⊢[PRAAx] inst2 (bd CG) j (pairT L (pairT m d)) ≐
      sg (monus (succ L) (d * j)) * (one + quo (monus L (d * j)) m) := by
  have e : Syn.subst ![j, L, m, d] CG =
      sg (monus (succ L) (d * j)) * (one + quo (monus L (d * j)) m) := by simp [CG]
  rw [← e]
  exact bd_at CG j L m d

/-! ## Pointwise facts -/

/-- `T_j + d j = L + m d` for `j < m`. -/
theorem T_add {j L m' d : PTm k} (hj : Γ ⊢[PRAAx] lt j (succ m')) :
    Γ ⊢[PRAAx] T j L (succ m') d + d * j ≐ L + succ m' * d := by
  have e := natEq (eq_add_of_le hj)
  have hle : Γ ⊢[PRAAx] le (d * j) (L + succ m' * d) :=
    le_of_eq_add (d := L + d * succ (monus (succ m') (succ j)))
      (by apply deriveNat; ipra_simps; linear_combination 𝔞 d * e)
  have t := natEq (eq_add_of_le hle)
  apply deriveNat; ipra_simps
  linear_combination -t

/-- The slack `L + m - d j`, written without subtraction of `d j`. -/
abbrev s2 (j L m' d' : PTm k) : PTm k :=
  succ d' * monus m' j + monus (L + succ m') (succ d' * m')

/-- `C_j + d = 1 + ⌊T_j / m⌋` for `j < m`, when `d (m - 1) ≤ L + m`. -/
theorem count_pt {j L m' d' : PTm k} (hj : Γ ⊢[PRAAx] lt j (succ m'))
    (hL : Γ ⊢[PRAAx] le (succ d' * m') (L + succ m')) :
    Γ ⊢[PRAAx] sg (monus (succ L) (succ d' * j)) *
        (one + quo (monus L (succ d' * j)) (succ m')) + succ d' ≐
      one + quo (T j L (succ m') (succ d')) (succ m') := by
  have hm : Γ ⊢[PRAAx] succ m' ≐ succ (pred (succ m')) := pos_of_eq_succ (c := m') (.eqRefl _)
  have ta := T_add (L := L) (d := succ d') hj
  refine .orE (lt_or_le L (succ d' * j)) ?_ ?_
  · -- `L < d j`: the row is empty and `⌊T_j / m⌋ = d - 1`
    have hlt : (lt L (succ d' * j) :: Γ) ⊢[PRAAx] lt L (succ d' * j) := Prf.hyp0
    have sgz := natEq (sg_of_zero (x := monus (succ L) (succ d' * j)) hlt)
    have hjle : (lt L (succ d' * j) :: Γ) ⊢[PRAAx] le j m' :=
      ((succ_monus_succ j m').eqSymm.eqTrans hj).wk
    have ej := natEq (eq_add_of_le hjle)
    have el := natEq (eq_add_of_le (hL.wk (ψ := lt L (succ d' * j))))
    have ex := natEq (eq_add_of_le hlt)
    have ta' := natEq (ta.wk (ψ := lt L (succ d' * j)))
    have hT : (lt L (succ d' * j) :: Γ) ⊢[PRAAx]
        T j L (succ m') (succ d') ≐ d' * succ m' + s2 j L m' d' := by
      refine add_right_cancel (c := succ d' * j) ?_
      apply deriveNat; ipra_simps
      linear_combination ta' + el + (𝔞 d' + 1) * ej
    have hs : (lt L (succ d' * j) :: Γ) ⊢[PRAAx] lt (s2 j L m' d') (succ m') :=
      le_of_eq_add (d := monus (succ d' * j) (succ L))
        (by apply deriveNat; ipra_simps; linear_combination el + ex + (𝔞 d' + 1) * ej)
    have hq := natEq ((congrAp2 quoF hT (.eqRefl _)).eqTrans (pair_fst hm.wk hs))
    apply deriveNat; ipra_simps
    linear_combination (1 + 𝔞 (quo (monus L (succ d' * j)) (succ m'))) * sgz - hq
  · -- `d j ≤ L`: `⌊T_j / m⌋ = ⌊(L - d j) / m⌋ + d`
    have hle : (le (succ d' * j) L :: Γ) ⊢[PRAAx] le (succ d' * j) L := Prf.hyp0
    have ex := natEq (eq_add_of_le hle)
    have hs1 : (le (succ d' * j) L :: Γ) ⊢[PRAAx]
        monus (succ L) (succ d' * j) ≐ succ (monus L (succ d' * j)) := by
      have e1 : (le (succ d' * j) L :: Γ) ⊢[PRAAx]
          succ L ≐ succ d' * j + succ (monus L (succ d' * j)) := by
        apply deriveNat; ipra_simps; linear_combination ex
      exact (congrMonus e1 (.eqRefl _)).eqTrans (add_monus' _ _)
    have sg1 := natEq (sg_of_pos hs1)
    have dv := natEq (div_eq' (t := monus L (succ d' * j)) (hm.wk (ψ := le (succ d' * j) L)))
    have ta' := natEq (ta.wk (ψ := le (succ d' * j) L))
    have hT : (le (succ d' * j) L :: Γ) ⊢[PRAAx] T j L (succ m') (succ d') ≐
        (quo (monus L (succ d' * j)) (succ m') + succ d') * succ m' +
          rem (monus L (succ d' * j)) (succ m') := by
      refine add_right_cancel (c := succ d' * j) ?_
      apply deriveNat; ipra_simps
      linear_combination ta' + ex + dv
    have hq := natEq ((congrAp2 quoF hT (.eqRefl _)).eqTrans
      (pair_fst hm.wk (rem_lt'' hm.wk _)))
    apply deriveNat; ipra_simps
    linear_combination (1 + 𝔞 (quo (monus L (succ d' * j)) (succ m'))) * sg1 - hq

/-! ## The three pointwise relations in the form of `sum_linear` -/

theorem ptA {j L m' d' : PTm k} (hj : Γ ⊢[PRAAx] lt j (succ m')) :
    Γ ⊢[PRAAx] inst2 (bd TG) j (pairT L (pairT (succ m') (succ d'))) + zero + succ d' * j ≐
      (L + succ m' * succ d') + zero * zero + zero := by
  have t := natEq (T_at (Γ := Γ) j L (succ m') (succ d'))
  have ta := natEq (T_add (L := L) (d := succ d') hj)
  apply deriveNat; ipra_simps
  linear_combination t + ta

theorem ptB (j L m' d' : PTm k) :
    Γ ⊢[PRAAx] inst2 (bd TG) j (pairT L (pairT (succ m') (succ d'))) + zero + zero * zero ≐
      zero + succ m' * inst2 (bd QG) j (pairT L (pairT (succ m') (succ d'))) +
        inst2 (bd RG) j (pairT L (pairT (succ m') (succ d'))) := by
  have t := natEq (T_at (Γ := Γ) j L (succ m') (succ d'))
  have q := natEq (Q_at (Γ := Γ) j L (succ m') (succ d'))
  have r := natEq (R_at (Γ := Γ) j L (succ m') (succ d'))
  have dv := natEq (div_eq' (Γ := Γ) (t := T j L (succ m') (succ d'))
    (pos_of_eq_succ (c := m') (.eqRefl _)))
  apply deriveNat; ipra_simps
  linear_combination t - (𝔞 m' + 1) * q - r + dv

theorem ptC {j L m' d' : PTm k} (hj : Γ ⊢[PRAAx] lt j (succ m'))
    (hL : Γ ⊢[PRAAx] le (succ d' * m') (L + succ m')) :
    Γ ⊢[PRAAx] inst2 (bd CG) j (pairT L (pairT (succ m') (succ d'))) + succ d' + zero * zero ≐
      one + one * inst2 (bd QG) j (pairT L (pairT (succ m') (succ d'))) + zero := by
  have c := natEq (C_at (Γ := Γ) j L (succ m') (succ d'))
  have q := natEq (Q_at (Γ := Γ) j L (succ m') (succ d'))
  have p := natEq (count_pt hj hL)
  apply deriveNat; ipra_simps
  linear_combination c - q + p

/-! ## The dimension formula -/

/-- `n(L)`: the number of monomials `X^i Y^j` with `j < m` and `m i + d j ≤ L`. -/
abbrev nL (L m' d' : PTm k) : PTm k :=
  ap2 (sumF (bd CG)) (succ m') (pairT L (pairT (succ m') (succ d')))

/-- `prop:weighted-dimension`, cleared of the division by two: if the residues of the shifted
numerators have the same sum as `0, …, m - 1`, then `2 n(L) + (m - 1)(d - 1) = 2 (L + 1)`. -/
theorem weighted_dimension {L m' d' : PTm k}
    (hL : Γ ⊢[PRAAx] le (succ d' * m') (L + succ m'))
    (hR : Γ ⊢[PRAAx] ap2 (sumF (bd RG)) (succ m') (pairT L (pairT (succ m') (succ d'))) ≐
      ap2 (sumF idB) (succ m') (pairT L (pairT (succ m') (succ d')))) :
    Γ ⊢[PRAAx] nL L m' d' + nL L m' d' + m' * d' ≐ (L + one) + (L + one) := by
  have ra := natEq (sum_linear (bd TG) idB (zero : PTm 2) (zero : PTm 2)
    (N := succ m') (lam := zero) (al := succ d') (kap := L + succ m' * succ d') (be := zero)
    (x := pairT L (pairT (succ m') (succ d'))) (Γ := Γ) (.allI (.impI (by
      simp only [shift_pairT, sh_zero, sh_succ, sh_add, sh_mul, inst2_idB, inst2_zB]
      exact ptA Prf.hyp0))))
  have rb := natEq (sum_linear (bd TG) (zero : PTm 2) (bd QG) (bd RG)
    (N := succ m') (lam := zero) (al := zero) (kap := zero) (be := succ m')
    (x := pairT L (pairT (succ m') (succ d'))) (Γ := Γ) (.allI (.impI (by
      simp only [shift_pairT, sh_zero, sh_succ, sh_add, sh_mul, inst2_zB]
      exact ptB _ _ _ _))))
  have hL' := hL.shift
  have eL : Fm.shift (le (succ d' * m') (L + succ m')) =
      le (succ (Syn.shift d') * Syn.shift m') (Syn.shift L + succ (Syn.shift m')) := by
    simp [Fm.shift, Syn.shift]
  rw [eL] at hL'
  have rc := natEq (sum_linear (bd CG) (zero : PTm 2) (bd QG) (zero : PTm 2)
    (N := succ m') (lam := succ d') (al := zero) (kap := one) (be := one)
    (x := pairT L (pairT (succ m') (succ d'))) (Γ := Γ) (.allI (.impI (by
      simp only [shift_pairT, sh_zero, sh_succ, sh_add, sh_mul, inst2_zB]
      exact ptC Prf.hyp0 hL'.wk))))
  have tr := natEq (tri (Γ := Γ) (succ m') (pairT L (pairT (succ m') (succ d'))))
  have z := natEq (sum_zeroB (Γ := Γ) (succ m') (pairT L (pairT (succ m') (succ d'))))
  have hr := natEq hR
  refine mul_cancel (d' := m') ?_
  apply deriveNat; ipra_simps
  linear_combination (2 * (𝔞 m' + 1)) * rc + (2 * (𝔞 m' + 1) + 2) * z - 2 * rb + 2 * ra -
    2 * hr - (𝔞 d' + 2) * tr

end LeanProofs.IPRA.Foundations.WeightedDimension
