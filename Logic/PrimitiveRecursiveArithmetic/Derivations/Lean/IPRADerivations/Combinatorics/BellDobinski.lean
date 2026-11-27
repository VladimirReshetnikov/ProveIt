import IPRADerivations.Combinatorics.StirlingInclusion
import IPRADerivations.Combinatorics.FallingFactorial
import IPRADerivations.Probability.Independence

/-!
# The finite Dobinski formula

Packet: `combinatorics/bell_numbers_ipra`, Theorem `thm:finite-dobinski` (`eq:bell-finite-dobinski`,
and `eq:bell-derangements` with `D_t` read as its alternating-sum value). With the exact quotients
`t!/j! = (t)_{t−j}` (falling factorials) and

  `d(t) = t! ∑_{j ≤ t} (−1)^j / j! = ∑_{j ≤ t} (−1)^j (t)_{t−j}`,

split by the parity of `j` into natural numbers `d⁺(t)`, `d⁻(t)`, the formula
`B_n = ∑_{i ≤ n} (iⁿ / i!) ∑_{j ≤ n−i} (−1)^j / j!`, multiplied by `n!`, reads

  `n! B_n + ∑_{i ≤ n} C(n, i) iⁿ d⁻(n − i) = ∑_{i ≤ n} C(n, i) iⁿ d⁺(n − i)` (`finite_dobinski`).

* `ff_gb`: `(n)_{n−k} C(k, i) = C(n, i) (n − i)_{n−k}` for `k ≤ n` (both sides times `i! (k − i)!`
  are `n!`), i.e. `(n!/k!) C(k, i) = n!/(i! (k − i)!)`;
* the inclusion–exclusion identity `StirlingInclusion.stirling_ie`, scaled by `n!/k! = (n)_{n−k}`, is summed
  over `k ≤ n`, the square double sum is exchanged (`Core/Fubini`), and the inner sum over `k` is
  reindexed by `j = k − i` (`reindex`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellDobinski

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (binom bden)
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.Combinatorics.Stirling (gle gle_of_le stir)
open LeanProofs.IPRA.Combinatorics.StirlingPowers (ffB ff ff_zero_above congrFF)
open LeanProofs.IPRA.Combinatorics.FallingFactorial (ff_fact monus_monus_add)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_above)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (ev od congrEv congrOd)
open LeanProofs.IPRA.Combinatorics.StirlingInclusion (Ep Om eB_at oB_at stirling_ie mul_one' sum1)
open LeanProofs.IPRA.Probability.Independence (sum_scale)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

alias monus_of_eq := Common.monus_of_eq

/-- `(n)_{n−k} k! = n!` for `k ≤ n`. -/
theorem ff_fact_k {N k : PTm n} (hk : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] ff N (monus N k) * fact k ≐ fact N :=
  let m := Common.monus_monus_of_le hk
  (congrMul (.eqRefl _) (congrAp2 factF m (.eqRefl _))).eqSymm.eqTrans
    (ff_fact (Common.monus_le_self N k))

/-- `(n)_{n−k} C(k, i) = C(n, i) (n − i)_{n−k}` for `k ≤ n` (guarded binomials, any `i`). -/
theorem ff_gb {N k i : PTm n} (hk : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] ff N (monus N k) * gb k i ≐ gb N i * ff (monus N i) (monus N k) := by
  refine .orE (lt_or_le k i) ?_ ?_
  · -- `i > k`: both sides vanish.
    have z : (lt k i :: Γ) ⊢[PRAAx] gb k i ≐ zero := gb_above Prf.hyp0
    refine (congrMul (.eqRefl _) z).eqTrans ((mul_zero _).eqTrans ?_)
    refine .orE (lt_or_le N i) ?_ ?_
    · exact ((congrMul (gb_above Prf.hyp0) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm
    · have hki := (Prf.hyp1 : (le i N :: lt k i :: Γ) ⊢[PRAAx] lt k i)
      have e2 := natEq (eq_add_of_le hki)
      have e3 := natEq (eq_add_of_le (Prf.hyp0 : (le i N :: lt k i :: Γ) ⊢[PRAAx] le i N))
      have mk : (le i N :: lt k i :: Γ) ⊢[PRAAx] monus N k ≐ succ (monus N i) + monus i (succ k) :=
        monus_of_eq (by apply deriveNat; ipra_simps; linear_combination e3 + e2)
      have l : (le i N :: lt k i :: Γ) ⊢[PRAAx] lt (monus N i) (monus N k) :=
        le_of_eq_add (d := monus i (succ k)) mk
      exact ((congrMul (.eqRefl _) (ff_zero_above l)).eqTrans (mul_zero _)).eqSymm
  · -- `i ≤ k ≤ N`.
    have hik : (le i k :: Γ) ⊢[PRAAx] le i k := Prf.hyp0
    have hiN : (le i k :: Γ) ⊢[PRAAx] le i N := le_trans hik hk.wk
    have g1 : (le i k :: Γ) ⊢[PRAAx] gle i k ≐ one := gle_of_le hik
    have g2 : (le i k :: Γ) ⊢[PRAAx] gle i N ≐ one := gle_of_le hiN
    have e1 := natEq (eq_add_of_le (hk.wk : (le i k :: Γ) ⊢[PRAAx] le k N)); have e2 := natEq (eq_add_of_le hik)
    -- monus arithmetic
    have m2 : (le i k :: Γ) ⊢[PRAAx] monus N i ≐ monus N k + monus k i :=
      monus_of_eq (by apply deriveNat; ipra_simps; linear_combination e1 + e2)
    have m3 : (le i k :: Γ) ⊢[PRAAx] monus (monus N i) (monus N k) ≐ monus k i := monus_of_eq m2
    have f1 : (le i k :: Γ) ⊢[PRAAx] ff N (monus N k) * fact k ≐ fact N :=
      ff_fact_k hk.wk
    have f2 : (le i k :: Γ) ⊢[PRAAx] ff (monus N i) (monus N k) * fact (monus k i) ≐ fact (monus N i) :=
      (congrMul (.eqRefl _) (congrAp2 factF m3 (.eqRefl _))).eqSymm.eqTrans
        (ff_fact (le_of_eq_add (d := monus k i) m2))
    have b1 := natEq (binom_eq hik); have b2 := natEq (binom_eq hiN)
    have x1 := natEq f1; have x2 := natEq f2; have y1 := natEq g1; have y2 := natEq g2
    refine mul_cancel (D := bden k i) (Binomial.bden_pos _ _) ?_
    ipra_lc 𝔞(ff N (monus N k)) * 𝔞(binom k i) * 𝔞(fact i) * 𝔞(fact (monus k i)) * y1 - 𝔞(ff N (monus N k)) * b1 +
      x1 + b2 - 𝔞(binom N i) * 𝔞(fact i) * x2 -
      𝔞(binom N i) * 𝔞(fact i) * 𝔞(fact (monus k i)) * 𝔞(ff (monus N i) (monus N k)) * y2

/-! ## The double sum -/

/-- `[k − i even] C(n, i) iⁿ (n − i)_{n−k}`, over `0 = k`, `1 = i`, `2 = n`. -/
abbrev aP : PTm 3 := ev (monus (var 0) (var 1)) * (gb (var 2) (var 1) * (pw (var 1) (var 2) * ff (monus (var 2) (var 1)) (monus (var 2) (var 0))))
abbrev aM : PTm 3 := od (monus (var 0) (var 1)) * (gb (var 2) (var 1) * (pw (var 1) (var 2) * ff (monus (var 2) (var 1)) (monus (var 2) (var 0))))

theorem aP_eq (k i N : PTm n) : inst3 aP k i N = ev (monus k i) * (gb N i * (pw i N * ff (monus N i) (monus N k))) := by
  simp [inst3]
theorem aM_eq (k i N : PTm n) : inst3 aM k i N = od (monus k i) * (gb N i * (pw i N * ff (monus N i) (monus N k))) := by
  simp [inst3]

theorem row_at (a : PTm 3) (i k N : PTm n) : Γ ⊢[PRAAx] inst2 (rowB a) i (pairT k N) ≐ inst3 a k i N := by
  rw [inst2_rowB]; exact congrInst3 a (fst_pair _ _) (.eqRefl _) (snd_pair _ _)
theorem col_at (a : PTm 3) (k i N : PTm n) : Γ ⊢[PRAAx] inst2 (colB a) k (pairT i N) ≐ inst3 a k i N := by
  rw [inst2_colB]; exact congrInst3 a (.eqRefl _) (fst_pair _ _) (snd_pair _ _)

theorem le_shift {a b : PTm n} (h : Γ ⊢[PRAAx] le a b) : Γ.map Fm.shift ⊢[PRAAx] le (Syn.shift a) (Syn.shift b) :=
  LeanProofs.IPRA.Order.shift_le h

/-- `(n)_{n−k} [k − i even] C(k, i) iⁿ = [k − i even] C(n, i) iⁿ (n − i)_{n−k}`. -/
theorem pt_e {N K i : PTm n} (hk : Γ ⊢[PRAAx] le K N) :
    Γ ⊢[PRAAx] inst3 aP K i N ≐ ff N (monus N K) * inst2 StirlingInclusion.eB i (pairT N K) := by
  rw [aP_eq]
  refine .eqTrans ?_ (congrMul (.eqRefl _) (eB_at _ _ _)).eqSymm
  ipra_lc -(𝔞(ev (monus K i)) * 𝔞(pw i N)) * natEq (ff_gb (i := i) hk)

theorem pt_o {N K i : PTm n} (hk : Γ ⊢[PRAAx] le K N) :
    Γ ⊢[PRAAx] inst3 aM K i N ≐ ff N (monus N K) * inst2 StirlingInclusion.oB i (pairT N K) := by
  rw [aM_eq]
  refine .eqTrans ?_ (congrMul (.eqRefl _) (StirlingInclusion.oB_at _ _ _)).eqSymm
  ipra_lc -(𝔞(od (monus K i)) * 𝔞(pw i N)) * natEq (ff_gb (i := i) hk)

/-- Above `k` the double-sum terms vanish. -/
theorem tail_zero (a : PTm 3) (ha : ∀ {m : ℕ} {Δ : List (Fm PTm m)} {K i N : PTm m}, (Δ ⊢[PRAAx] le K N) →
      (Δ ⊢[PRAAx] lt K i) → (Δ ⊢[PRAAx] inst3 a K i N ≐ zero))
    {N K : PTm n} (hk : Γ ⊢[PRAAx] le K N) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB a)) (succ N) (pairT K N) ≐ ap2 (sumF (rowB a)) (succ K) (pairT K N) := by
  have e := natEq (eq_add_of_le hk)
  have hN : Γ ⊢[PRAAx] succ N ≐ succ K + monus N K := by apply deriveNat; ipra_simps; linear_combination e
  refine (congrAp2 _ hN (.eqRefl _)).eqTrans ((sum_split _ _ _ _).eqTrans ((congrAdd (.eqRefl _) ?_).eqTrans (add_zero _)))
  refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
  rw [shift_pairT, shift_pairT, inst2_offB, show Syn.shift (succ K) = succ (Syn.shift K) by simp [Syn.shift]]
  refine (congrInst2 _ (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans ((row_at a _ _ _).eqTrans ?_)
  exact ha (le_shift hk).wk (le_of_eq_add (d := var 0) (by apply deriveNat; ipra_simps))

theorem aP_tail {m : ℕ} {Δ : List (Fm PTm m)} {K i N : PTm m} (hk : Δ ⊢[PRAAx] le K N) (hi : Δ ⊢[PRAAx] lt K i) :
    Δ ⊢[PRAAx] inst3 aP K i N ≐ zero :=
  (pt_e hk).eqTrans ((congrMul (.eqRefl _) ((eB_at _ _ _).eqTrans ((congrMul (.eqRefl _)
    ((congrMul (gb_above hi) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)))).eqTrans (mul_zero _))

theorem aM_tail {m : ℕ} {Δ : List (Fm PTm m)} {K i N : PTm m} (hk : Δ ⊢[PRAAx] le K N) (hi : Δ ⊢[PRAAx] lt K i) :
    Δ ⊢[PRAAx] inst3 aM K i N ≐ zero :=
  (pt_o hk).eqTrans ((congrMul (.eqRefl _) ((StirlingInclusion.oB_at _ _ _).eqTrans ((congrMul (.eqRefl _)
    ((congrMul (gb_above hi) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans (mul_zero _)))).eqTrans (mul_zero _))

/-- `(n)_{n−k} E⁺(n, k) = ∑_{i ≤ n} [k − i even] C(n, i) iⁿ (n − i)_{n−k}` for `k ≤ n`. -/
theorem scaled_e {N K : PTm n} (hk : Γ ⊢[PRAAx] le K N) :
    Γ ⊢[PRAAx] ff N (monus N K) * Ep N K ≐ ap2 (sumF (rowB aP)) (succ N) (pairT K N) := by
  refine (sum_scale (rowB aP) StirlingInclusion.eB (succ K) (ff N (monus N K)) (pairT N K) (pairT K N)
    (.allI (.impI ?_))).eqSymm.eqTrans (tail_zero aP aP_tail hk).eqSymm
  simp only [shift_pairT]
  rw [show Syn.shift (ff N (monus N K)) = ff (Syn.shift N) (monus (Syn.shift N) (Syn.shift K)) by simp [Syn.shift]]
  exact (row_at aP _ _ _).eqTrans (pt_e (le_shift hk).wk)

theorem scaled_o {N K : PTm n} (hk : Γ ⊢[PRAAx] le K N) :
    Γ ⊢[PRAAx] ff N (monus N K) * Om N K ≐ ap2 (sumF (rowB aM)) (succ N) (pairT K N) := by
  refine (sum_scale (rowB aM) StirlingInclusion.oB (succ K) (ff N (monus N K)) (pairT N K) (pairT K N)
    (.allI (.impI ?_))).eqSymm.eqTrans (tail_zero aM aM_tail hk).eqSymm
  simp only [shift_pairT]
  rw [show Syn.shift (ff N (monus N K)) = ff (Syn.shift N) (monus (Syn.shift N) (Syn.shift K)) by simp [Syn.shift]]
  exact (row_at aM _ _ _).eqTrans (pt_o (le_shift hk).wk)

/-! ## Reindexing the inner sum by `j = k − i` -/

/-- `[j even] (t)_{t−j}`, over `0 = j`, `1 = t`. -/
abbrev dpB : PTm 2 := ev (var 0) * ff (var 1) (monus (var 1) (var 0))
abbrev dmB : PTm 2 := od (var 0) * ff (var 1) (monus (var 1) (var 0))
/-- `d⁺(t) = ∑_{j ≤ t} [j even] t!/j!` and the odd part `d⁻(t)`: `d⁺ − d⁻ = t! ∑_{j≤t} (−1)^j / j!`. -/
abbrev dP (t : PTm n) : PTm n := ap2 (sumF dpB) (succ t) t
abbrev dM (t : PTm n) : PTm n := ap2 (sumF dmB) (succ t) t

/-- `[k − i even] (n − i)_{n−k}`, over `0 = k`, `1 = ⟨i, n⟩`. -/
abbrev rPB : PTm 2 := ev (monus (var 0) (fstT (var 1))) * ff (monus (sndT (var 1)) (fstT (var 1))) (monus (sndT (var 1)) (var 0))
abbrev rMB : PTm 2 := od (monus (var 0) (fstT (var 1))) * ff (monus (sndT (var 1)) (fstT (var 1))) (monus (sndT (var 1)) (var 0))

theorem rPB_at (k i N : PTm n) :
    Γ ⊢[PRAAx] inst2 rPB k (pairT i N) ≐ ev (monus k i) * ff (monus N i) (monus N k) := by
  have e : inst2 rPB k (pairT i N) = ev (monus k (fstT (pairT i N))) *
      ff (monus (sndT (pairT i N)) (fstT (pairT i N))) (monus (sndT (pairT i N)) k) := by simp [inst2]
  rw [e]
  have f : Γ ⊢[PRAAx] fstT (pairT i N) ≐ i := fst_pair _ _
  have s : Γ ⊢[PRAAx] sndT (pairT i N) ≐ N := snd_pair _ _
  exact congrMul (congrEv (congrMonus (.eqRefl _) f)) (congrFF (congrMonus s f) (congrMonus s (.eqRefl _)))

theorem rMB_at (k i N : PTm n) :
    Γ ⊢[PRAAx] inst2 rMB k (pairT i N) ≐ od (monus k i) * ff (monus N i) (monus N k) := by
  have e : inst2 rMB k (pairT i N) = od (monus k (fstT (pairT i N))) *
      ff (monus (sndT (pairT i N)) (fstT (pairT i N))) (monus (sndT (pairT i N)) k) := by simp [inst2]
  rw [e]
  have f : Γ ⊢[PRAAx] fstT (pairT i N) ≐ i := fst_pair _ _
  have s : Γ ⊢[PRAAx] sndT (pairT i N) ≐ N := snd_pair _ _
  exact congrMul (congrOd (congrMonus (.eqRefl _) f)) (congrFF (congrMonus s f) (congrMonus s (.eqRefl _)))

theorem ff_below {N i k : PTm n} (hi : Γ ⊢[PRAAx] le i N) (hk : Γ ⊢[PRAAx] lt k i) :
    Γ ⊢[PRAAx] ff (monus N i) (monus N k) ≐ zero := by
  have e1 := natEq (eq_add_of_le hi); have e2 := natEq (eq_add_of_le hk)
  have m : Γ ⊢[PRAAx] monus N k ≐ succ (monus N i) + monus i (succ k) :=
    monus_of_eq (by apply deriveNat; ipra_simps; linear_combination e1 + e2)
  exact ff_zero_above (le_of_eq_add (d := monus i (succ k)) m)

theorem reindex_split {i N : PTm n} (hi : Γ ⊢[PRAAx] le i N) : Γ ⊢[PRAAx] succ N ≐ i + succ (monus N i) := by
  ipra_lc natEq (eq_add_of_le hi)

theorem reindex_e {i N : PTm n} (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] ap2 (sumF rPB) (succ N) (pairT i N) ≐ dP (monus N i) := by
  refine (congrAp2 _ (reindex_split hi) (.eqRefl _)).eqTrans ((sum_split _ _ _ _).eqTrans ?_)
  refine (congrAdd (sum_zero_of_bounded _ _ _ (.allI (.impI ?_))) (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))).eqTrans
    (zero_add _)
  · simp only [shift_pairT]
    exact (rPB_at _ _ _).eqTrans ((congrMul (.eqRefl _) (ff_below (le_shift hi).wk Prf.hyp0)).eqTrans (mul_zero _))
  · simp only [shift_pairT]
    rw [inst2_offB]
    have e : inst2 dpB (var 0) (Syn.shift (monus N i)) =
        ev (var 0) * ff (Syn.shift (monus N i)) (monus (Syn.shift (monus N i)) (var 0)) := by simp [inst2]
    rw [e, show Syn.shift (monus N i) = monus (Syn.shift N) (Syn.shift i) by simp [Syn.shift]]
    refine (congrInst2 _ (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans ((rPB_at _ _ _).eqTrans ?_)
    have m1 : (lt (var 0) (Syn.shift (succ (monus N i))) :: Γ.map Fm.shift) ⊢[PRAAx]
        monus (Syn.shift i + var 0) (Syn.shift i) ≐ var 0 :=
      (congrMonus (add_comm _ _) (.eqRefl _)).eqTrans (add_monus _ _)
    exact congrMul (congrEv m1) (congrFF (.eqRefl _) (monus_monus_add _ _ _).eqSymm)

theorem reindex_o {i N : PTm n} (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] ap2 (sumF rMB) (succ N) (pairT i N) ≐ dM (monus N i) := by
  refine (congrAp2 _ (reindex_split hi) (.eqRefl _)).eqTrans ((sum_split _ _ _ _).eqTrans ?_)
  refine (congrAdd (sum_zero_of_bounded _ _ _ (.allI (.impI ?_))) (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))).eqTrans
    (zero_add _)
  · simp only [shift_pairT]
    exact (rMB_at _ _ _).eqTrans ((congrMul (.eqRefl _) (ff_below (le_shift hi).wk Prf.hyp0)).eqTrans (mul_zero _))
  · simp only [shift_pairT]
    rw [inst2_offB]
    have e : inst2 dmB (var 0) (Syn.shift (monus N i)) =
        od (var 0) * ff (Syn.shift (monus N i)) (monus (Syn.shift (monus N i)) (var 0)) := by simp [inst2]
    rw [e, show Syn.shift (monus N i) = monus (Syn.shift N) (Syn.shift i) by simp [Syn.shift]]
    refine (congrInst2 _ (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans ((rMB_at _ _ _).eqTrans ?_)
    have m1 : (lt (var 0) (Syn.shift (succ (monus N i))) :: Γ.map Fm.shift) ⊢[PRAAx]
        monus (Syn.shift i + var 0) (Syn.shift i) ≐ var 0 :=
      (congrMonus (add_comm _ _) (.eqRefl _)).eqTrans (add_monus _ _)
    exact congrMul (congrOd m1) (congrFF (.eqRefl _) (monus_monus_add _ _ _).eqSymm)

/-! ## Column sums and the formula -/

theorem colsum_e {i N : PTm n} (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] ap2 (sumF (colB aP)) (succ N) (pairT i N) ≐ (gb N i * pw i N) * dP (monus N i) := by
  refine (sum_scale (colB aP) rPB (succ N) (gb N i * pw i N) (pairT i N) (pairT i N) (.allI (.impI ?_))).eqTrans
    (congrMul (.eqRefl _) (reindex_e hi))
  simp only [shift_pairT]
  rw [show Syn.shift (gb N i * pw i N) = gb (Syn.shift N) (Syn.shift i) * pw (Syn.shift i) (Syn.shift N) by simp [Syn.shift]]
  refine (col_at aP _ _ _).eqTrans ?_
  rw [aP_eq]
  refine .eqTrans ?_ (congrMul (.eqRefl _) (rPB_at _ _ _)).eqSymm
  ipra_ring

theorem colsum_o {i N : PTm n} (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] ap2 (sumF (colB aM)) (succ N) (pairT i N) ≐ (gb N i * pw i N) * dM (monus N i) := by
  refine (sum_scale (colB aM) rMB (succ N) (gb N i * pw i N) (pairT i N) (pairT i N) (.allI (.impI ?_))).eqTrans
    (congrMul (.eqRefl _) (reindex_o hi))
  simp only [shift_pairT]
  rw [show Syn.shift (gb N i * pw i N) = gb (Syn.shift N) (Syn.shift i) * pw (Syn.shift i) (Syn.shift N) by simp [Syn.shift]]
  refine (col_at aM _ _ _).eqTrans ?_
  rw [aM_eq]
  refine .eqTrans ?_ (congrMul (.eqRefl _) (rMB_at _ _ _)).eqSymm
  ipra_ring

/-- `C(n, i) iⁿ d⁺(n − i)`, over `0 = i`, `1 = n`. -/
abbrev RPB : PTm 2 := (gb (var 1) (var 0) * pw (var 0) (var 1)) *
  ap2 (sumF dpB) (succ (monus (var 1) (var 0))) (monus (var 1) (var 0))
abbrev RMB : PTm 2 := (gb (var 1) (var 0) * pw (var 0) (var 1)) *
  ap2 (sumF dmB) (succ (monus (var 1) (var 0))) (monus (var 1) (var 0))

/-- `R^±(n) = ∑_{i ≤ n} C(n, i) iⁿ d^±(n − i)`. -/
abbrev Rp (N : PTm n) : PTm n := ap2 (sumF RPB) (succ N) N
abbrev Rm (N : PTm n) : PTm n := ap2 (sumF RMB) (succ N) N

/-- `(n)_{n−k} E^±(n, k)` and `n! S(n, k)`, over `0 = k`, `1 = n`. -/
abbrev pkB : PTm 2 := ff (var 1) (monus (var 1) (var 0)) *
  ap2 (sumF StirlingInclusion.eB) (succ (var 0)) (pairT (var 1) (var 0))
abbrev mkB : PTm 2 := ff (var 1) (monus (var 1) (var 0)) *
  ap2 (sumF StirlingInclusion.oB) (succ (var 0)) (pairT (var 1) (var 0))
abbrev hkB : PTm 2 := fact (var 1) * stir (var 1) (var 0)

alias le_of_lt_succ' := Common.le_of_lt_succ

theorem shift_succ' (a : PTm n) : Syn.shift (succ a) = succ (Syn.shift a) := by simp [Syn.shift]

theorem sumP (N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF pkB) (succ N) N ≐ Rp N := by
  refine (sum_congr_bounded pkB (oB aP) N (pairT (succ N) N) (succ N) (.allI (.impI ?_))).eqTrans
    ((fubini aP (succ N) (succ N) N).eqTrans (sum_congr_bounded (pB aP) RPB (pairT (succ N) N) N (succ N) (.allI (.impI ?_))))
  · have hk := le_of_lt_succ' (by rw [← shift_succ']; exact Prf.hyp0 :
      (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift N)))
    have e : inst2 pkB (var 0) (Syn.shift N) = ff (Syn.shift N) (monus (Syn.shift N) (var 0)) * Ep (Syn.shift N) (var 0) := by
      simp [inst2]
    rw [e, shift_pairT, shift_succ']
    exact (scaled_e hk).eqTrans (oB_at aP _ _ _).eqSymm
  · have hk := le_of_lt_succ' (by rw [← shift_succ']; exact Prf.hyp0 :
      (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift N)))
    have e : inst2 RPB (var 0) (Syn.shift N) = (gb (Syn.shift N) (var 0) * pw (var 0) (Syn.shift N)) *
        dP (monus (Syn.shift N) (var 0)) := by simp [inst2]
    rw [e, shift_pairT, shift_succ', inst2_pB]
    exact (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans (colsum_e hk)

theorem sumM (N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF mkB) (succ N) N ≐ Rm N := by
  refine (sum_congr_bounded mkB (oB aM) N (pairT (succ N) N) (succ N) (.allI (.impI ?_))).eqTrans
    ((fubini aM (succ N) (succ N) N).eqTrans (sum_congr_bounded (pB aM) RMB (pairT (succ N) N) N (succ N) (.allI (.impI ?_))))
  · have hk := le_of_lt_succ' (by rw [← shift_succ']; exact Prf.hyp0 :
      (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift N)))
    have e : inst2 mkB (var 0) (Syn.shift N) = ff (Syn.shift N) (monus (Syn.shift N) (var 0)) * Om (Syn.shift N) (var 0) := by
      simp [inst2]
    rw [e, shift_pairT, shift_succ']
    exact (scaled_o hk).eqTrans (oB_at aM _ _ _).eqSymm
  · have hk := le_of_lt_succ' (by rw [← shift_succ']; exact Prf.hyp0 :
      (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift N)))
    have e : inst2 RMB (var 0) (Syn.shift N) = (gb (Syn.shift N) (var 0) * pw (var 0) (Syn.shift N)) *
        dM (monus (Syn.shift N) (var 0)) := by simp [inst2]
    rw [e, shift_pairT, shift_succ', inst2_pB]
    exact (congrAp2 _ (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans (colsum_o hk)

theorem split_P (N : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF pkB) (succ N) N ≐ ap2 (sumF hkB) (succ N) N + ap2 (sumF mkB) (succ N) N := by
  refine (sum_congr_bounded pkB (addBody hkB mkB) N N (succ N) (.allI (.impI ?_))).eqTrans (sum_add _ _ _ _)
  have hk := le_of_lt_succ' (by rw [← shift_succ']; exact Prf.hyp0 :
    (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (succ (Syn.shift N)))
  rw [inst2_addBody]
  have e1 : inst2 pkB (var 0) (Syn.shift N) = ff (Syn.shift N) (monus (Syn.shift N) (var 0)) * Ep (Syn.shift N) (var 0) := by
    simp [inst2]
  have e2 : inst2 mkB (var 0) (Syn.shift N) = ff (Syn.shift N) (monus (Syn.shift N) (var 0)) * Om (Syn.shift N) (var 0) := by
    simp [inst2]
  have e3 : inst2 hkB (var 0) (Syn.shift N) = fact (Syn.shift N) * stir (Syn.shift N) (var 0) := by simp [inst2]
  rw [e1, e2, e3]
  ipra_lc -(𝔞(ff (Syn.shift N) (monus (Syn.shift N) (var 0)))) * natEq (stirling_ie (Γ := lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift) (Syn.shift N) (var 0)) +
    𝔞(gle (var 0) (Syn.shift N)) * 𝔞(Bell.nth (Stirling.row (Syn.shift N)) (monus (Syn.shift N) (var 0))) * natEq (ff_fact_k hk)

theorem sumH (N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF hkB) (succ N) N ≐ fact N * Bell.bell N := by
  refine (sum_scale hkB BellStirling.tB (succ N) (fact N) N N (.allI (.impI ?_))).eqTrans
    (congrMul (.eqRefl _) (BellStirling.bell_stirling N))
  have e3 : inst2 hkB (var 0) (Syn.shift N) = fact (Syn.shift N) * stir (Syn.shift N) (var 0) := by simp [inst2]
  have e4 : inst2 BellStirling.tB (var 0) (Syn.shift N) = stir (Syn.shift N) (var 0) := by simp [inst2]
  rw [e3, e4, show Syn.shift (fact N) = fact (Syn.shift N) by simp [Syn.shift]]
  exact .eqRefl _

/-- `eq:bell-finite-dobinski` (and `eq:bell-derangements` with `D_t = d(t)`), cleared of `n!`:
`n! B_n + ∑_{i ≤ n} C(n, i) iⁿ d⁻(n − i) = ∑_{i ≤ n} C(n, i) iⁿ d⁺(n − i)`, i.e.
`n! B_n = ∑_{i ≤ n} C(n, i) iⁿ (n − i)! ∑_{j ≤ n−i} (−1)^j / j!`. -/
theorem finite_dobinski (N : PTm n) : Γ ⊢[PRAAx] fact N * Bell.bell N + Rm N ≐ Rp N := by
  ipra_lc natEq (sumP (Γ := Γ) N) - natEq (sumM (Γ := Γ) N) - natEq (split_P (Γ := Γ) N) - natEq (sumH (Γ := Γ) N)

end LeanProofs.IPRA.Combinatorics.BellDobinski
