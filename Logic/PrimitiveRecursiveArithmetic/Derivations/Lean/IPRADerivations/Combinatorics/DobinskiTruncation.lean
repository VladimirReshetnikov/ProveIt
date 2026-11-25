import IPRADerivations.Combinatorics.BellDobinski
import IPRADerivations.Combinatorics.BellTouchardPower
import IPRADerivations.Probability.Lotus
import IPRADerivations.Core.LinearCombination

/-!
# The exact truncation identity of Dobinski's formula (`bell_numbers_ipra`, `thm:dobinski`, `eq:finite-dobinski`)

Packet: `combinatorics/bell_numbers_ipra`, `paper/03_series.tex`: "The polynomial identity
`x^n = ∑_{j=0}^n S(n, j) (x)_j` ... Substituting the integers `k = 0, …, M` and interchanging two
finite sums gives, for `M ≥ n`,

  `A_{n,M} := ∑_{k=0}^M k^n / k! = ∑_{j=0}^n S(n, j) E_{M−j}(1)` (`eq:finite-dobinski`).

The cancellation `(k)_j / k! = 1/(k − j)!` is used only when `k ≥ j`; for `k < j` the falling
factorial vanishes." Here `E_r(1) = ∑_{i ≤ r} 1/i!`.

Multiplied by `M!`, with `M!/k! = (M)_{M−k}` (a falling factorial, so no division occurs):

* `finite_dobinski`: for `N ≤ M`,
  `∑_{k ≤ M} k^N (M)_{M−k} = ∑_{j ≤ N} S(N, j) ∑_{i ≤ M−j} (M)_{M−i}`.

The proof is the packet's: the double sum of `S(N, j) (k)_j (M)_{M−k}` over `k ≤ M`, `j ≤ N`
is summed by rows with `Combinatorics/StirlingPowers.stirling_powers` (`row_eval`) and by
columns with `(k)_j (M)_{M−k} = (M)_{M−(k−j)}` for `j ≤ k ≤ M` and `(k)_j = 0` for `k < j`
(`ff_shift`, `col_eval`); the two orders agree by `Core/Fubini`.

Not derived: the error bound (`eq:dobinski-error`) and the infinite series, which involve the
real number `e`, and `thm:comtet`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.DobinskiTruncation

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Stirling (stir)
open LeanProofs.IPRA.Combinatorics.StirlingPowers (ff ff_zero_above congrFF congrStir tB tB_at Am
  stirling_powers)
open LeanProofs.IPRA.Combinatorics.FallingFactorial (ff_add)
open LeanProofs.IPRA.Combinatorics.Bell (monus_monus)
open LeanProofs.IPRA.Combinatorics.BellDobinski (row_at col_at)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (shift_pair shift_succ shift_monus
  le_of_lt_succ)
open LeanProofs.IPRA.Probability.Lotus (cmB inst2_cmB sum_const_mul)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The bodies -/

/-- `S(N, j) (k)_j (M)_{M−k}`, over `0 = k`, `1 = j`, `2 = ⟨N, M⟩`. -/
abbrev aD : PTm 3 :=
  stir (fstT (var 2)) (var 1) *
    (ff (var 0) (var 1) * ff (sndT (var 2)) (monus (sndT (var 2)) (var 0)))

theorem aD_at (k j N M : PTm n) :
    Γ ⊢[PRAAx] inst3 aD k j (pairT N M) ≐ stir N j * (ff k j * ff M (monus M k)) := by
  have h : inst3 aD k j (pairT N M) = stir (fstT (pairT N M)) j *
      (ff k j * ff (sndT (pairT N M)) (monus (sndT (pairT N M)) k)) := by simp [inst3]
  rw [h]
  exact congrMul (congrStir (fst_pair _ _) (.eqRefl _))
    (congrMul (.eqRefl _) (congrFF (snd_pair _ _) (congrMonus (snd_pair _ _) (.eqRefl _))))

/-- `k^N (M)_{M−k}`, over `0 = k`, `1 = ⟨N, M⟩`. -/
abbrev lB : PTm 2 :=
  pw (var 0) (fstT (var 1)) * ff (sndT (var 1)) (monus (sndT (var 1)) (var 0))

theorem l_at (k N M : PTm n) :
    Γ ⊢[PRAAx] inst2 lB k (pairT N M) ≐ pw k N * ff M (monus M k) := by
  have h : inst2 lB k (pairT N M) = pw k (fstT (pairT N M)) *
      ff (sndT (pairT N M)) (monus (sndT (pairT N M)) k) := by simp [inst2]
  rw [h]
  exact congrMul (congrPw (.eqRefl _) (fst_pair _ _))
    (congrFF (snd_pair _ _) (congrMonus (snd_pair _ _) (.eqRefl _)))

/-- `(M)_{M−i}`, over `0 = i`, `1 = M`. -/
abbrev eD : PTm 2 := ff (var 1) (monus (var 1) (var 0))

theorem inst2_eD (i M : PTm n) : inst2 eD i M = ff M (monus M i) := by simp [inst2]

/-- `S(N, j) ∑_{i ≤ M−j} (M)_{M−i}`, over `0 = j`, `1 = ⟨N, M⟩`. -/
abbrev rD : PTm 2 :=
  stir (fstT (var 1)) (var 0) *
    ap2 (sumF eD) (succ (monus (sndT (var 1)) (var 0))) (sndT (var 1))

theorem r_at (j N M : PTm n) :
    Γ ⊢[PRAAx] inst2 rD j (pairT N M) ≐ stir N j * ap2 (sumF eD) (succ (monus M j)) M := by
  have h : inst2 rD j (pairT N M) = stir (fstT (pairT N M)) j *
      ap2 (sumF eD) (succ (monus (sndT (pairT N M)) j)) (sndT (pairT N M)) := by simp [inst2]
  rw [h]
  exact congrMul (congrStir (fst_pair _ _) (.eqRefl _))
    (congrAp2 _ (congrSucc (congrMonus (snd_pair _ _) (.eqRefl _))) (snd_pair _ _))

/-! ## Rows: `∑_j S(N, j) (k)_j = k^N` -/

theorem row_cm {j k N M c : PTm n} (hc : Γ ⊢[PRAAx] c ≐ ff M (monus M k)) :
    Γ ⊢[PRAAx] inst2 (rowB aD) j (pairT k (pairT N M)) ≐
      inst2 (cmB tB) j (pairT c (pairT N k)) := by
  rw [inst2_cmB]
  have r : Γ ⊢[PRAAx] fstT (pairT c (pairT N k)) * inst2 tB j (sndT (pairT c (pairT N k))) ≐
      ff M (monus M k) * (stir N j * ff k j) :=
    congrMul ((fst_pair _ _).eqTrans hc)
      ((congrInst2 tB (.eqRefl _) (snd_pair _ _)).eqTrans (tB_at j N k))
  refine ((row_at aD j k (pairT N M)).eqTrans (aD_at k j N M)).eqTrans (.eqTrans ?_ r.eqSymm)
  ipra_ring

theorem row_eval (k N M : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB aD)) (succ N) (pairT k (pairT N M)) ≐
      pw k N * ff M (monus M k) := by
  refine (sum_congr_bounded (rowB aD) (cmB tB) (pairT k (pairT N M))
    (pairT (ff M (monus M k)) (pairT N k)) (succ N) (.allI (.impI ?_))).eqTrans
    ((sum_const_mul tB (succ N) (ff M (monus M k)) (pairT N k)).eqTrans ?_)
  · have e : Syn.shift (ff M (monus M k)) =
        ff (Syn.shift M) (monus (Syn.shift M) (Syn.shift k)) := by simp [Syn.shift]
    simp only [shift_pair]
    exact row_cm (by rw [e]; exact .eqRefl _)
  · have e := natEq (stirling_powers (Γ := Γ) N k)
    apply deriveNat; ipra_simps
    linear_combination 𝔞 (ff M (monus M k)) * e

/-! ## Columns: `(k)_j (M)_{M−k} = (M)_{M−(k−j)}` -/

/-- `(j + i)_j (M)_{M−(j+i)} = (M)_{M−i}` for `j + i ≤ M`. -/
theorem ff_shift {i j M : PTm n} (hi : Γ ⊢[PRAAx] le (j + i) M) :
    Γ ⊢[PRAAx] ff (j + i) j * ff M (monus M (j + i)) ≐ ff M (monus M i) := by
  have eM := eq_add_of_le hi
  have m1 : Γ ⊢[PRAAx] monus M (monus M (j + i)) ≐ j + i := monus_monus hi
  have m2 : Γ ⊢[PRAAx] monus M i ≐ monus M (j + i) + j := by
    have w : Γ ⊢[PRAAx] M ≐ i + (monus M (j + i) + j) := by
      ipra_lc natEq eM
    exact (congrMonus w (.eqRefl i)).eqTrans (add_monus' _ i)
  have k1 : Γ ⊢[PRAAx] ff M (monus M i) ≐ ff M (monus M (j + i)) * ff (j + i) j :=
    (congrFF (.eqRefl M) m2).eqTrans
      ((ff_add M (monus M (j + i)) j).eqTrans (congrMul (.eqRefl _) (congrFF m1 (.eqRefl j))))
  exact (mul_comm _ _).eqTrans k1.eqSymm

theorem col_zero {k j N M : PTm n} (h : Γ ⊢[PRAAx] lt k j) :
    Γ ⊢[PRAAx] inst2 (colB aD) k (pairT j (pairT N M)) ≐ zero :=
  ((col_at aD k j (pairT N M)).eqTrans (aD_at k j N M)).eqTrans
    ((congrMul (.eqRefl _) ((congrMul (ff_zero_above h) (.eqRefl _)).eqTrans (zero_mul _))).eqTrans
      (mul_zero _))

theorem col_pt {i j N M s : PTm n} (hs : Γ ⊢[PRAAx] s ≐ stir N j)
    (hi : Γ ⊢[PRAAx] le (j + i) M) :
    Γ ⊢[PRAAx] inst2 (offB (colB aD)) i (pairT j (pairT j (pairT N M))) ≐
      inst2 (cmB eD) i (pairT s M) := by
  rw [inst2_offB, inst2_cmB, inst2_eD]
  have l : Γ ⊢[PRAAx] inst2 (colB aD) (fstT (pairT j (pairT j (pairT N M))) + i)
      (sndT (pairT j (pairT j (pairT N M)))) ≐ stir N j * ff M (monus M i) :=
    (congrInst2 (colB aD) (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans
      (((col_at aD (j + i) j (pairT N M)).eqTrans (aD_at (j + i) j N M)).eqTrans
        (congrMul (.eqRefl _) (ff_shift hi)))
  exact l.eqTrans (congrMul ((fst_pair _ _).eqTrans hs)
    (congrFF (snd_pair _ _) (congrMonus (snd_pair _ _) (.eqRefl _)))).eqSymm

theorem add_le_of {i j M : PTm n} (hj : Γ ⊢[PRAAx] le j M)
    (hi : Γ ⊢[PRAAx] lt i (succ (monus M j))) : Γ ⊢[PRAAx] le (j + i) M := by
  refine le_of_eq_add (d := monus (monus M j) i) ?_
  ipra_lc natEq (eq_add_of_le hj) + natEq (eq_add_of_le (le_of_lt_succ hi))

theorem col_eval {j N M : PTm n} (hj : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] ap2 (sumF (colB aD)) (succ M) (pairT j (pairT N M)) ≐
      stir N j * ap2 (sumF eD) (succ (monus M j)) M := by
  have split : Γ ⊢[PRAAx] succ M ≐ j + succ (monus M j) := by
    ipra_lc natEq (eq_add_of_le hj)
  have hj' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift j) (Syn.shift M) := by
    simpa [Fm.shift, Syn.shift] using hj.shift
  refine (congrAp2 _ split (.eqRefl _)).eqTrans
    ((sum_split (colB aD) j (succ (monus M j)) (pairT j (pairT N M))).eqTrans ?_)
  refine (congrAdd (sum_zero_of_bounded _ _ _ (.allI (.impI ?_)))
    ((sum_congr_bounded (offB (colB aD)) (cmB eD) (pairT j (pairT j (pairT N M)))
      (pairT (stir N j) M) (succ (monus M j)) (.allI (.impI ?_))).eqTrans
      (sum_const_mul eD (succ (monus M j)) (stir N j) M))).eqTrans (zero_add _)
  · simp only [shift_pair]
    exact col_zero Prf.hyp0
  · have e : Syn.shift (stir N j) = stir (Syn.shift N) (Syn.shift j) := by simp [Syn.shift]
    simp only [shift_pair, shift_succ, shift_monus]
    exact col_pt (by rw [e]; exact .eqRefl _) (add_le_of hj'.wk Prf.hyp0)

/-! ## The identity -/

/-- `eq:finite-dobinski` times `M!`: for `N ≤ M`,
`∑_{k ≤ M} k^N (M)_{M−k} = ∑_{j ≤ N} S(N, j) ∑_{i ≤ M−j} (M)_{M−i}`. -/
theorem finite_dobinski {N M : PTm n} (h : Γ ⊢[PRAAx] le N M) :
    Γ ⊢[PRAAx] ap2 (sumF lB) (succ M) (pairT N M) ≐ ap2 (sumF rD) (succ N) (pairT N M) := by
  have h' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift N) (Syn.shift M) := by
    simpa [Fm.shift, Syn.shift] using h.shift
  have lhs : Γ ⊢[PRAAx] ap2 (sumF (oB aD)) (succ M) (pairT (succ N) (pairT N M)) ≐
      ap2 (sumF lB) (succ M) (pairT N M) := by
    refine sum_congr_bounded (oB aD) lB (pairT (succ N) (pairT N M)) (pairT N M) (succ M)
      (.allI (.impI ?_))
    simp only [shift_pair, shift_succ]
    exact (oB_at aD _ _ _).eqTrans ((row_eval _ _ _).eqTrans (l_at _ _ _).eqSymm)
  have rhs : Γ ⊢[PRAAx] ap2 (sumF (pB aD)) (succ N) (pairT (succ M) (pairT N M)) ≐
      ap2 (sumF rD) (succ N) (pairT N M) := by
    refine sum_congr_bounded (pB aD) rD (pairT (succ M) (pairT N M)) (pairT N M) (succ N)
      (.allI (.impI ?_))
    simp only [shift_pair, shift_succ]
    rw [inst2_pB]
    refine (congrAp2 (sumF (colB aD)) (fst_pair _ _)
      (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
    exact (col_eval (le_trans (le_of_lt_succ Prf.hyp0) h'.wk)).eqTrans (r_at _ _ _).eqSymm
  exact lhs.eqSymm.eqTrans ((fubini aD (succ M) (succ N) (pairT N M)).eqTrans rhs)

end LeanProofs.IPRA.Combinatorics.DobinskiTruncation
