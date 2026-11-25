import IPRADerivations.Foundations.WeightedDimension
import IPRADerivations.AnalyticNumberTheory.Totatives
import IPRADerivations.Core.LinearCombination

/-!
# The residues are a permutation (`ipra_coherent_methods_2026-11-15`, `prop:weighted-dimension`)

Packet: `foundations/ipra_coherent_methods_2026-11-15`, proposition `prop:weighted-dimension`:
"The residues `r_j` of `L - d j` modulo `m` are a permutation of `0, 1, …, m - 1`, by
coprimality."

`Foundations/WeightedDimension` proves the dimension formula from the equality of the sum of
those residues with `0 + ⋯ + (m - 1)`. Here that equality is derived, with coprimality given by
a Bezout relation `u d = v m + 1` (`m = m' + 1`):

* `rem_unique`: `a m + ρ = b m + j` with `ρ, j < m` gives `ρ = j`;
* `σ(j) = (L + m d ∸ d j) mod m` and `τ(r) = u (L + (m ∸ r)) mod m` (`SG`, `UG`);
* `sig_tau`: `σ(τ(r)) = r` for `r < m`; `tau_sig`: `τ(σ(j)) = j` for `j < m`. Each is one
  linear combination of the division equations and the Bezout relation, followed by
  `rem_unique`;
* `residue_sum`: `∑_{j<m} σ(j) = ∑_{j<m} j`, by `sum_perm` of
  `AnalyticNumberTheory/Totatives`;
* `weighted_dimension_coprime`: `prop:weighted-dimension` without the hypothesis on residues:
  for `d (m - 1) ≤ L + m` and `u d = v m + 1`, `2 n(L) + (m - 1)(d - 1) = 2 (L + 1)`.

The Bezout coefficients are a hypothesis (they exist for coprime `m`, `d`; their computation
by the extended Euclidean algorithm is not derived here).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.ResiduePermutation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Probability.ProductPower (div_eq' rem_lt'')
open LeanProofs.IPRA.Foundations.FiniteSetExponential (pair_snd)
open LeanProofs.IPRA.Foundations.SumLinear
open LeanProofs.IPRA.Foundations.WeightedDimension
open LeanProofs.IPRA.AnalyticNumberTheory.Totatives (sum_perm)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- Two decompositions with remainders below `m` have the same remainder. -/
theorem rem_unique {a b ρ j m : PTm k} (hm : Γ ⊢[PRAAx] m ≐ succ (pred m))
    (e : Γ ⊢[PRAAx] a * m + ρ ≐ b * m + j) (hρ : Γ ⊢[PRAAx] lt ρ m)
    (hj : Γ ⊢[PRAAx] lt j m) : Γ ⊢[PRAAx] ρ ≐ j :=
  (pair_snd hm hρ).eqSymm.eqTrans ((congrAp2 remF e (.eqRefl _)).eqTrans (pair_snd hm hj))

/-! ## Bodies with four packed parameters -/

/-- The body reading `1 = L`, `2 = m`, `3 = d`, `4 = u` of a five-variable term from the packed
parameter `⟨L, ⟨m, ⟨d, u⟩⟩⟩`. -/
def bd4 (X : PTm 5) : PTm 2 :=
  Syn.subst ![var 0, fstT (var 1), fstT (sndT (var 1)), fstT (sndT (sndT (var 1))),
    sndT (sndT (sndT (var 1)))] X

theorem bd4_at (X : PTm 5) (j L m d u : PTm k) :
    Γ ⊢[PRAAx] inst2 (bd4 X) j (pairT L (pairT m (pairT d u))) ≐
      Syn.subst ![j, L, m, d, u] X := by
  have e₁ : inst2 (bd4 X) j (pairT L (pairT m (pairT d u))) =
      Syn.subst ![j, fstT (pairT L (pairT m (pairT d u))),
        fstT (sndT (pairT L (pairT m (pairT d u)))),
        fstT (sndT (sndT (pairT L (pairT m (pairT d u))))),
        sndT (sndT (sndT (pairT L (pairT m (pairT d u)))))] X := by
    simp only [inst2, bd4, Syn.subst_subst]
    congr 1; funext l; fin_cases l <;> simp
  rw [e₁]
  have s₁ : Γ ⊢[PRAAx] sndT (pairT L (pairT m (pairT d u))) ≐ pairT m (pairT d u) :=
    snd_pair _ _
  have s₂ : Γ ⊢[PRAAx] sndT (sndT (pairT L (pairT m (pairT d u)))) ≐ pairT d u :=
    (congrSnd s₁).eqTrans (snd_pair _ _)
  exact Prf.eqCongr _ fun l => by
    fin_cases l
    · exact .eqRefl _
    · exact fst_pair _ _
    · exact (congrFst s₁).eqTrans (fst_pair _ _)
    · exact (congrFst s₂).eqTrans (fst_pair _ _)
    · exact (congrSnd s₂).eqTrans (snd_pair _ _)

/-- `σ(j) = (L + m d ∸ d j) mod m`; variables `0 = j`, `1 = L`, `2 = m`, `3 = d`, `4 = u`. -/
def SG : PTm 5 := rem (monus (var 1 + var 2 * var 3) (var 3 * var 0)) (var 2)

/-- `τ(r) = u (L + (m ∸ r)) mod m`. -/
def UG : PTm 5 := rem (var 4 * (var 1 + monus (var 2) (var 0))) (var 2)

theorem S_at (j L m d u : PTm k) :
    Γ ⊢[PRAAx] inst2 (bd4 SG) j (pairT L (pairT m (pairT d u))) ≐ rem (T j L m d) m := by
  have e : Syn.subst ![j, L, m, d, u] SG = rem (T j L m d) m := by simp [SG]
  rw [← e]
  exact bd4_at SG j L m d u

theorem U_at (r L m d u : PTm k) :
    Γ ⊢[PRAAx] inst2 (bd4 UG) r (pairT L (pairT m (pairT d u))) ≐
      rem (u * (L + monus m r)) m := by
  have e : Syn.subst ![r, L, m, d, u] UG = rem (u * (L + monus m r)) m := by simp [UG]
  rw [← e]
  exact bd4_at UG r L m d u

/-! ## The two inverse laws -/

/-- `σ(τ(r)) = r` for `r < m`. -/
theorem sig_tau {r L m' d u v : PTm k} (hBz : Γ ⊢[PRAAx] u * d ≐ v * succ m' + one)
    (hr : Γ ⊢[PRAAx] lt r (succ m')) :
    Γ ⊢[PRAAx] rem (T (rem (u * (L + monus (succ m') r)) (succ m')) L (succ m') d) (succ m') ≐
      r := by
  have hm : Γ ⊢[PRAAx] succ m' ≐ succ (pred (succ m')) := pos_of_eq_succ (c := m') (.eqRefl _)
  have hτ := rem_lt'' hm (u * (L + monus (succ m') r))
  have e₃ := natEq (div_eq'
    (t := T (rem (u * (L + monus (succ m') r)) (succ m')) L (succ m') d) hm)
  refine rem_unique (a := quo (T (rem (u * (L + monus (succ m') r)) (succ m')) L (succ m') d)
      (succ m') + v * (L + monus (succ m') r) + one)
    (b := d + d * quo (u * (L + monus (succ m') r)) (succ m')) hm ?_ (rem_lt'' hm _) hr
  ipra_lc natEq (T_add (L := L) (d := d) hτ) - (𝔞 L + 𝔞 (monus (succ m') r)) * natEq hBz +
    𝔞 d * natEq (div_eq' (t := u * (L + monus (succ m') r)) hm) - e₃ + natEq (eq_add_of_le (le_of_lt hr))

/-- `τ(σ(j)) = j` for `j < m`. -/
theorem tau_sig {j L m' d u v : PTm k} (hBz : Γ ⊢[PRAAx] u * d ≐ v * succ m' + one)
    (hj : Γ ⊢[PRAAx] lt j (succ m')) :
    Γ ⊢[PRAAx]
      rem (u * (L + monus (succ m') (rem (T j L (succ m') d) (succ m')))) (succ m') ≐ j := by
  have hm : Γ ⊢[PRAAx] succ m' ≐ succ (pred (succ m')) := pos_of_eq_succ (c := m') (.eqRefl _)
  have hσ := rem_lt'' hm (T j L (succ m') d)
  have e₂ := natEq (div_eq'
    (t := u * (L + monus (succ m') (rem (T j L (succ m') d) (succ m')))) hm)
  refine rem_unique
    (a := quo (u * (L + monus (succ m') (rem (T j L (succ m') d) (succ m')))) (succ m') + u * d)
    (b := v * j + u + u * quo (T j L (succ m') d) (succ m')) hm ?_ (rem_lt'' hm _) hj
  ipra_lc 𝔞 u * natEq (div_eq' (t := T j L (succ m') d) hm) - 𝔞 u * natEq (T_add (L := L) (d := d) hj) -
    𝔞 u * natEq (eq_add_of_le (le_of_lt hσ)) - e₂ + 𝔞 j * natEq hBz

/-! ## The permutation hypotheses -/

theorem inv_pt {r L m' d u v : PTm k} (hBz : Γ ⊢[PRAAx] u * d ≐ v * succ m' + one)
    (hr : Γ ⊢[PRAAx] lt r (succ m')) :
    Γ ⊢[PRAAx] lt (inst2 (bd4 UG) r (pairT L (pairT (succ m') (pairT d u)))) (succ m') ⋏
      (inst2 (bd4 SG) (inst2 (bd4 UG) r (pairT L (pairT (succ m') (pairT d u))))
        (pairT L (pairT (succ m') (pairT d u))) ≐ r) := by
  have hm : Γ ⊢[PRAAx] succ m' ≐ succ (pred (succ m')) := pos_of_eq_succ (c := m') (.eqRefl _)
  refine .andI (lt_congr (U_at r L (succ m') d u).eqSymm (.eqRefl _) (rem_lt'' hm _)) ?_
  exact (congrInst2 (bd4 SG) (U_at r L (succ m') d u) (.eqRefl _)).eqTrans
    ((S_at _ L (succ m') d u).eqTrans (sig_tau hBz hr))

theorem ret_pt {j L m' d u v : PTm k} (hBz : Γ ⊢[PRAAx] u * d ≐ v * succ m' + one)
    (hj : Γ ⊢[PRAAx] lt j (succ m')) :
    Γ ⊢[PRAAx] inst2 (bd4 UG) (inst2 (bd4 SG) j (pairT L (pairT (succ m') (pairT d u))))
      (pairT L (pairT (succ m') (pairT d u))) ≐ j :=
  (congrInst2 (bd4 UG) (S_at j L (succ m') d u) (.eqRefl _)).eqTrans
    ((U_at _ L (succ m') d u).eqTrans (tau_sig hBz hj))

theorem shift_bez {m' d u v : PTm k} (hBz : Γ ⊢[PRAAx] u * d ≐ v * succ m' + one) :
    Γ.map Fm.shift ⊢[PRAAx]
      Syn.shift u * Syn.shift d ≐ Syn.shift v * succ (Syn.shift m') + one := by
  have h := hBz.shift
  have e : Fm.shift (u * d ≐ v * succ m' + one) =
      (Syn.shift u * Syn.shift d ≐ Syn.shift v * succ (Syn.shift m') + one) := by
    simp [Fm.shift, Syn.shift]
  rw [e] at h
  exact h

/-- The sum of the residues is `0 + 1 + ⋯ + (m - 1)`. -/
theorem residue_sum {L m' d u v : PTm k} (hBz : Γ ⊢[PRAAx] u * d ≐ v * succ m' + one) :
    Γ ⊢[PRAAx] ap2 (sumF (bd RG)) (succ m') (pairT L (pairT (succ m') d)) ≐
      ap2 (sumF idB) (succ m') (pairT L (pairT (succ m') d)) := by
  have hm : Γ ⊢[PRAAx] succ m' ≐ succ (pred (succ m')) := pos_of_eq_succ (c := m') (.eqRefl _)
  have hB' := shift_bez hBz
  have hr : Γ ⊢[PRAAx] Permutation.rangeAll (bd4 SG) (succ m')
      (pairT L (pairT (succ m') (pairT d u))) := by
    refine .allI ?_
    simp only [shift_pairT, sh_succ]
    exact lt_congr (S_at _ _ _ _ _).eqSymm (.eqRefl _)
      (rem_lt'' (pos_of_eq_succ (c := Syn.shift m') (.eqRefl _)) _)
  have hinv : Γ ⊢[PRAAx] Permutation.invAll (bd4 SG) (bd4 UG) (succ m')
      (pairT L (pairT (succ m') (pairT d u))) := by
    refine .allI (.impI ?_)
    simp only [shift_pairT, sh_succ]
    exact inv_pt hB'.wk Prf.hyp0
  have hret : Γ ⊢[PRAAx] Permutation.retAll (bd4 SG) (bd4 UG) (succ m')
      (pairT L (pairT (succ m') (pairT d u))) := by
    refine .allI (.impI ?_)
    simp only [shift_pairT, sh_succ]
    exact ret_pt hB'.wk Prf.hyp0
  have p := sum_perm (f := idB) hr hinv hret
  have eF : Permutation.FS idB (bd4 SG) = bd4 SG := by simp [Permutation.FS, idB]
  rw [eF] at p
  have c₁ : Γ ⊢[PRAAx] ap2 (sumF (bd RG)) (succ m') (pairT L (pairT (succ m') d)) ≐
      ap2 (sumF (bd4 SG)) (succ m') (pairT L (pairT (succ m') (pairT d u))) := by
    refine sum_congr_bounded (bd RG) (bd4 SG) _ _ (succ m') (.allI (.impI ?_))
    simp only [shift_pairT, sh_succ]
    exact (R_at _ _ _ _).eqTrans (S_at _ _ _ _ _).eqSymm
  have c₂ : Γ ⊢[PRAAx] ap2 (sumF idB) (succ m') (pairT L (pairT (succ m') (pairT d u))) ≐
      ap2 (sumF idB) (succ m') (pairT L (pairT (succ m') d)) := by
    refine sum_congr_bounded idB idB _ _ (succ m') (.allI (.impI ?_))
    rw [inst2_idB, inst2_idB]
    exact .eqRefl _
  exact c₁.eqTrans (p.eqTrans c₂)

/-- `prop:weighted-dimension`: for coprime `m = m' + 1` and `d = d' + 1` (Bezout relation
`u d = v m + 1`) and `d (m - 1) ≤ L + m`, `2 n(L) + (m - 1)(d - 1) = 2 (L + 1)`. -/
theorem weighted_dimension_coprime {L m' d' u v : PTm k}
    (hL : Γ ⊢[PRAAx] le (succ d' * m') (L + succ m'))
    (hBz : Γ ⊢[PRAAx] u * succ d' ≐ v * succ m' + one) :
    Γ ⊢[PRAAx] nL L m' d' + nL L m' d' + m' * d' ≐ (L + one) + (L + one) :=
  weighted_dimension hL (residue_sum hBz)

/-- `prop:weighted-dimension` as a closed sentence. Variables: `0 = L`, `1 = m'`, `2 = d'`,
`3 = u`, `4 = v`. -/
theorem weighted_dimension_closed : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
    (le (succ (var 2) * var 1) (var 0 + succ (var 1)) ⟶
      (var 3 * succ (var 2) ≐ var 4 * succ (var 1) + one) ⟶
        (nL (var 0) (var 1) (var 2) + nL (var 0) (var 1) (var 2) + var 1 * var 2 ≐
          (var 0 + one) + (var 0 + one))) :=
  closeUniv 5 (.impI (.impI (weighted_dimension_coprime Prf.hyp1 Prf.hyp0)))

end LeanProofs.IPRA.Foundations.ResiduePermutation
