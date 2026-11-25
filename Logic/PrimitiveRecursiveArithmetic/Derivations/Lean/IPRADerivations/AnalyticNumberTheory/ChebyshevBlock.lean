import IPRADerivations.AnalyticNumberTheory.HyperbolaSwap
import IPRADerivations.AnalyticNumberTheory.FactorialLambda
import IPRADerivations.Probability.Variance
import IPRADerivations.Core.LinearCombination

/-!
# The Chebyshev block identity (`pnt_ipra_constructive_2026-11-14`, `con:signed`)

Packet: `analytic-number-theory/pnt_ipra_constructive_2026-11-14`, `contraction.tex`, Lemma `con:deficit`: the
signed integral `∫_u^v r` over a block of the contraction is, discretely, a sum `Σ_{D₁<d≤D₂} R(⌊x/d⌋)` over
divisors. Its order of summation is exchanged by `HyperbolaSwap.hyp_swap` with `a = [d ≤ D]`:

  `Σ_{1≤d≤min(x,D)} B(⌊x/d⌋) + Σ_{1≤n≤x} b(n) (⌊x/n⌋ ∸ D) = Σ_{1≤n≤x} b(n) ⌊x/n⌋`

for every body `b` with summatory function `B` (`block_id`). With `b = Λ` this is Chebyshev's
`Σ_{d≤D} ψ(x/d) = Σ_n Λ(n) min(⌊x/n⌋, D)`; with `b = F` it counts lattice points. The two differ only in `b`, so a
difference of two levels `D₁ ≤ D₂` gives the block sum as `Σ_n (Λ(n) − F) c(n)` with
`c(n) = min(⌊x/n⌋, D₂) − min(⌊x/n⌋, D₁)`.

* `iB`, `ind_one`, `ind_zero`: the indicator `[d ≤ D]`, read from the parameter `y = (D, z)`;
* `bs_low`, `bs_high`, `min_add`: `Σ_{k<m} [k + 1 ≤ D] = min(m, D)`, and `min(q, D) + (q ∸ D) = q`;
* `block_id`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBlock

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.AnalyticNumberTheory.ConvSummatory (RB RB_at bS inst2_bS Bs)
open LeanProofs.IPRA.AnalyticNumberTheory.HyperbolaSwap (hyp_swap)
open LeanProofs.IPRA.AnalyticNumberTheory.FactorialLambda (sum_add2)
open LeanProofs.IPRA.Probability.Variance (sum_const_of)
open LeanProofs.IPRA.Signum (sg)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

set_option autoImplicit false

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem dist_alg {s B M q : PTm n} (h : Γ ⊢[PRAAx] B + M ≐ q) : Γ ⊢[PRAAx] s * B + s * M ≐ s * q := by
  ipra_lc 𝔞 s * natEq h

/-- `[d ≤ D]` over `0 = d`, `1 = (D, z)`. -/
abbrev iB : PTm 2 := monus one (monus (var 0) (fstT (var 1)))

theorem inst2_iB (k y : PTm n) : inst2 iB k y = monus one (monus k (fstT y)) := by simp [inst2]

theorem ind_one {k D z : PTm n} (h : Γ ⊢[PRAAx] le k D) : Γ ⊢[PRAAx] inst2 iB k (pairT D z) ≐ one := by
  rw [inst2_iB]
  exact (congrMonus (.eqRefl one) ((congrMonus (.eqRefl k) (fst_pair _ _)).eqTrans h)).eqTrans (monus_zero _)

theorem ind_zero {k D z : PTm n} (h : Γ ⊢[PRAAx] lt D k) : Γ ⊢[PRAAx] inst2 iB k (pairT D z) ≐ zero := by
  rw [inst2_iB]
  have e : Γ ⊢[PRAAx] k ≐ succ (monus k (succ D)) + D := by
    ipra_lc natEq (eq_add_of_le h)
  have m : Γ ⊢[PRAAx] monus k (fstT (pairT D z)) ≐ succ (monus k (succ D)) :=
    (congrMonus e (fst_pair _ _)).eqTrans (add_monus _ _)
  exact (congrMonus (.eqRefl one) m).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))

/-- `Σ_{k<m} [k + 1 ≤ D] = m` for `m ≤ D`. -/
theorem bs_low {m D z : PTm n} (h : Γ ⊢[PRAAx] le m D) : Γ ⊢[PRAAx] Bs iB m (pairT D z) ≐ m := by
  have h' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift m) (Syn.shift D) := by simpa [Fm.shift, Syn.shift] using h.shift
  have s := sum_const_of (Γ := Γ) (bS iB) m one (pairT D z) (.allI (.impI (by
    rw [inst2_bS, shift_pairT, show Syn.shift (one : PTm n) = one by simp [Syn.shift]]
    have hv : (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift m) := Prf.hyp0
    exact ind_one (le_trans hv h'.wk))))
  exact s.eqTrans (by ipra_ring)

/-- `Σ_{k<m} [k + 1 ≤ D] = D` for `D ≤ m`. -/
theorem bs_high {m D z : PTm n} (h : Γ ⊢[PRAAx] le D m) : Γ ⊢[PRAAx] Bs iB m (pairT D z) ≐ D := by
  have e := eq_add_of_le h
  have sp := sum_split (Γ := Γ) (bS iB) D (monus m D) (pairT D z)
  have lo := bs_low (Γ := Γ) (z := z) (le_refl D)
  have hi := sum_const_of (Γ := Γ) (offB (bS iB)) (monus m D) zero (pairT D (pairT D z)) (.allI (.impI (by
    rw [inst2_offB, inst2_bS, shift_pairT, show Syn.shift (zero : PTm n) = zero by simp [Syn.shift]]
    have c : (lt (var 0) (Syn.shift (monus m D)) :: Γ.map Fm.shift) ⊢[PRAAx]
        succ (fstT (pairT (Syn.shift D) (Syn.shift (pairT D z))) + var 0) ≐ succ (Syn.shift D + var 0) :=
      congrSucc (congrAdd (fst_pair _ _) (.eqRefl _))
    refine (congrInst2 iB c (snd_pair _ _)).eqTrans ?_
    rw [shift_pairT]
    exact ind_zero ((succ_monus_succ _ _).eqTrans (le_add_right _ _)))))
  refine (congrAp2 (sumF (bS iB)) e (.eqRefl _)).eqTrans (sp.eqTrans ?_)
  exact (congrAdd lo hi).eqTrans (by ipra_ring)

/-- `min(q, D) + (q ∸ D) = q`. -/
theorem min_add (q D z : PTm n) : Γ ⊢[PRAAx] Bs iB q (pairT D z) + monus q D ≐ q := by
  refine .orE (le_total q D) ?_ ?_
  · exact (congrAdd (bs_low Prf.hyp0) Prf.hyp0).eqTrans (add_zero _)
  · exact (congrAdd (bs_high Prf.hyp0) (.eqRefl _)).eqTrans (eq_add_of_le Prf.hyp0).eqSymm

/-- `[n ≥ 1] b(n) (⌊x/n⌋ ∸ D)` over `0 = n`, `1 = (x, (D, z))`. -/
abbrev eB (b : PTm 2) : PTm 2 :=
  (sg (var 0) * Syn.subst ![var 0, sndT (var 1)] b) * monus (quo (fstT (var 1)) (var 0)) (fstT (sndT (var 1)))

/-- `[n ≥ 1] b(n) ⌊x/n⌋` over `0 = n`, `1 = (x, y)`. -/
abbrev gB (b : PTm 2) : PTm 2 := (sg (var 0) * Syn.subst ![var 0, sndT (var 1)] b) * quo (fstT (var 1)) (var 0)

theorem eB_at (b : PTm 2) (k X D z : PTm n) :
    Γ ⊢[PRAAx] inst2 (eB b) k (pairT X (pairT D z)) ≐ (sg k * inst2 b k (pairT D z)) * monus (quo X k) D := by
  have h : Syn.subst ![k, pairT X (pairT D z)] (Syn.subst ![var 0, sndT (var 1)] b) =
      inst2 b k (sndT (pairT X (pairT D z))) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  have raw : inst2 (eB b) k (pairT X (pairT D z)) = (sg k * inst2 b k (sndT (pairT X (pairT D z)))) *
      monus (quo (fstT (pairT X (pairT D z))) k) (fstT (sndT (pairT X (pairT D z)))) := by
    simp only [inst2, eB, PTm.subst_mul, PTm.subst_monus, h]; simp [sg]
  rw [raw]
  exact congrMul (congrMul (.eqRefl _) (congrInst2 b (.eqRefl _) (snd_pair _ _)))
    (congrMonus (congrAp2 quoF (fst_pair _ _) (.eqRefl _)) ((congrFst (snd_pair _ _)).eqTrans (fst_pair _ _)))

theorem gB_at (b : PTm 2) (k X y : PTm n) :
    Γ ⊢[PRAAx] inst2 (gB b) k (pairT X y) ≐ (sg k * inst2 b k y) * quo X k := by
  have h : Syn.subst ![k, pairT X y] (Syn.subst ![var 0, sndT (var 1)] b) = inst2 b k (sndT (pairT X y)) := by
    simp only [inst2, Syn.subst_subst]; congr 1; funext i; fin_cases i <;> simp
  have raw : inst2 (gB b) k (pairT X y) = (sg k * inst2 b k (sndT (pairT X y))) * quo (fstT (pairT X y)) k := by
    simp only [inst2, gB, PTm.subst_mul, h]; simp [sg]
  rw [raw]
  exact congrMul (congrMul (.eqRefl _) (congrInst2 b (.eqRefl _) (snd_pair _ _))) (congrAp2 quoF (fst_pair _ _) (.eqRefl _))

/-- `Σ_{1≤d≤min(x,D)} B(⌊x/d⌋) + Σ_{1≤n≤x} b(n)(⌊x/n⌋ ∸ D) = Σ_{1≤n≤x} b(n)⌊x/n⌋`. -/
theorem block_id (b : PTm 2) (x D z : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (RB iB b)) (succ x) (pairT x (pairT D z)) +
        ap2 (sumF (eB b)) (succ x) (pairT x (pairT D z)) ≐
      ap2 (sumF (gB b)) (succ x) (pairT x (pairT D z)) := by
  refine (congrAdd (hyp_swap iB b x (pairT D z)) (.eqRefl _)).eqTrans ?_
  refine (sum_add2 (Γ := Γ) (RB b iB) (eB b) (gB b) (K := succ x) (x := pairT x (pairT D z))
    (x' := pairT x (pairT D z)) (z := pairT x (pairT D z)) (.allI (.impI ?_))).eqSymm
  simp only [shift_pairT]
  refine (gB_at _ _ _ _).eqTrans (.eqSymm ((congrAdd (RB_at _ _ _ _ _) (eB_at _ _ _ _ _)).eqTrans ?_))
  exact dist_alg (min_add _ _ _)

end LeanProofs.IPRA.AnalyticNumberTheory.ChebyshevBlock
