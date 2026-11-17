import IPRADerivations.Core.SumSplit
import IPRADerivations.Core.Fubini
import IPRADerivations.Core.Division

/-!
# Block regrouping of a finite sum

For a body `g(k, x)`, the sum over `k < m n` regroups into `m` blocks of length `n`:

  `∑_{k<mn} g(k) = ∑_{i<m} ∑_{j<n} g(i n + j)`   (`block_sum`),

by induction on `m` with `sum_split`. With `g(k) = a(⌊k/n⌋, k mod n)` and the division identity
`⌊(i n + j)/n⌋ = i`, `(i n + j) mod n = j` for `j < n` (`qr_block`), this is the flattening form of
finite Fubini (`expected_value_ipra_2026-11-16`, `cor:finite-fubini`):

  `∑_{k<mn} a(⌊k/n⌋, k mod n) = ∑_{i<m} ∑_{j<n} a(i, j)`   (`flatten`).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.BlockSum

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The block `∑_{j<n} g(i n + j, x)`, over `0 = i`, `1 = ⟨n, x⟩`. -/
abbrev blkB (g : PTm 2) : PTm 2 := ap2 (sumF (offB g)) (fstT (var 1)) (pairT (var 0 * fstT (var 1)) (sndT (var 1)))

theorem blk_at (g : PTm 2) (i N x : PTm n) :
    Γ ⊢[PRAAx] inst2 (blkB g) i (pairT N x) ≐ ap2 (sumF (offB g)) N (pairT (i * N) x) := by
  have e : inst2 (blkB g) i (pairT N x) =
      ap2 (sumF (offB g)) (fstT (pairT N x)) (pairT (i * fstT (pairT N x)) (sndT (pairT N x))) := by simp [inst2]
  rw [e]
  exact congrAp2 (sumF (offB g)) (fst_pair _ _) (congrPairT (congrMul (.eqRefl _) (fst_pair _ _)) (snd_pair _ _))

/-- `∑_{k<mn} g(k) = ∑_{i<m} ∑_{j<n} g(i n + j)`. -/
theorem block_sum (g : PTm 2) (m N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF g) (m * N) x ≐ ap2 (sumF (blkB g)) m (pairT N x) := by
  have hall : Γ ⊢[PRAAx] Fm.all (ap2 (sumF g) (var 0 * Syn.shift N) (Syn.shift x) ≐
      ap2 (sumF (blkB g)) (var 0) (pairT (Syn.shift N) (Syn.shift x))) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [Fm.subst_eq, PTm.subst_mul, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero,
        Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero]
      exact ((congrAp2 (sumF g) (zero_mul _) (.eqRefl _)).eqTrans (sum_zero _ _)).eqTrans (sum_zero _ _).eqSymm
    · simp only [Fm.subst_eq, PTm.subst_mul, subst_ap2, subst_pairT, Syn.subst_var, Syn.repl_zero,
        subst_repl_shift, ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
      let D : List (Fm PTm (n + 1)) := (ap2 (sumF g) (var 0 * Syn.shift N) (Syn.shift x) ≐
        ap2 (sumF (blkB g)) (var 0) (pairT (Syn.shift N) (Syn.shift x))) :: Γ.map Fm.shift
      have c : D ⊢[PRAAx] succ (var 0) * Syn.shift N ≐ var 0 * Syn.shift N + Syn.shift N := by
        apply deriveNat; ipra_simps; ring
      refine (congrAp2 (sumF g) c (.eqRefl _)).eqTrans ((sum_split g _ _ _).eqTrans ?_)
      refine .eqTrans ?_ (sum_succ' (blkB g) (var 0) (pairT (Syn.shift N) (Syn.shift x))).eqSymm
      exact congrAdd Prf.hyp0 (blk_at g _ _ _).eqSymm
  have h := Prf.allE m hall
  simp only [Fm.subst_eq, PTm.subst_mul, subst_ap2, subst_pairT, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero] at h
  exact h

/-- `⌊(i n + j)/n⌋ = i` and `(i n + j) mod n = j` for `j < n`. -/
theorem qr_block {i j N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) (hj : Γ ⊢[PRAAx] lt j N) :
    Γ ⊢[PRAAx] (quo (i * N + j) N ≐ i) ⋏ (rem (i * N + j) N ≐ j) := by
  have u := div_mod_unique (z := i * N + j) (q := i) (r := j) (K' := pred N)
    ((congrAdd ((congrMul (.eqRefl _) hN).eqTrans (mul_comm _ _)) (.eqRefl _)) : Γ ⊢[PRAAx] _)
    (lt_congr (.eqRefl _) hN hj)
  exact .andI ((congrAp2 quoF (.eqRefl _) hN).eqTrans (Prf.andE₁ u))
    ((congrAp2 remF (.eqRefl _) hN).eqTrans (Prf.andE₂ u))

/-- `a(⌊k/n⌋, k mod n, x)`, over `0 = k`, `1 = ⟨n, x⟩`. -/
abbrev flatB (a : PTm 3) : PTm 2 :=
  Syn.subst ![quo (var 0) (fstT (var 1)), rem (var 0) (fstT (var 1)), sndT (var 1)] a

theorem flat_at (a : PTm 3) (k N x : PTm n) :
    Γ ⊢[PRAAx] inst2 (flatB a) k (pairT N x) ≐ inst3 a (quo k N) (rem k N) x := by
  have e : inst2 (flatB a) k (pairT N x) =
      inst3 a (quo k (fstT (pairT N x))) (rem k (fstT (pairT N x))) (sndT (pairT N x)) := by
    simp only [inst2, inst3, flatB, Syn.subst_subst]; congr 1; funext j; fin_cases j <;> simp
  rw [e]
  exact congrInst3 a (congrAp2 quoF (.eqRefl _) (fst_pair _ _)) (congrAp2 remF (.eqRefl _) (fst_pair _ _)) (snd_pair _ _)

/-- `cor:finite-fubini`, flattening: `∑_{k<mn} a(⌊k/n⌋, k mod n) = ∑_{i<m} ∑_{j<n} a(i, j)` for `n ≥ 1`. -/
theorem flatten (a : PTm 3) {m N x : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] ap2 (sumF (flatB a)) (m * N) (pairT N x) ≐ ap2 (sumF (oB a)) m (pairT N x) := by
  have hN' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift N ≐ succ (pred (Syn.shift N)) := by
    simpa [Fm.shift, Syn.shift] using hN.shift
  refine (block_sum (flatB a) m N (pairT N x)).eqTrans (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
  simp only [shift_pairT]
  refine (blk_at (flatB a) _ _ _).eqTrans ?_
  rw [inst2_oB]
  refine .eqTrans ?_ (congrAp2 (sumF (rowB a)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_offB, inst2_rowB]
  simp only [shift_pairT]
  rw [show Syn.shift (var 0 * Syn.shift N) = Syn.shift (var 0) * Syn.shift (Syn.shift N) by simp [Syn.shift]]
  let C : List (Fm PTm (n + 1 + 1)) := lt (var 0) (Syn.shift (Syn.shift N)) ::
    (lt (var 0) (Syn.shift m) :: Γ.map Fm.shift).map Fm.shift
  have hN'' : C ⊢[PRAAx] Syn.shift (Syn.shift N) ≐ succ (pred (Syn.shift (Syn.shift N))) := by
    have e := hN'.shift
    simp only [Fm.shift, Fm.subst_eq] at e
    exact (by simpa [Syn.shift] using e : (Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] _).weaken
      (fun f hf => List.mem_cons_of_mem _ (List.mem_map.2 (by
        obtain ⟨g, hg, rfl⟩ := List.mem_map.1 hf; exact ⟨g, List.mem_cons_of_mem _ hg, rfl⟩)))
  have qr := qr_block (i := Syn.shift (var 0)) hN'' Prf.hyp0
  have f1 : C ⊢[PRAAx] fstT (pairT (Syn.shift (var 0) * Syn.shift (Syn.shift N))
      (pairT (Syn.shift (Syn.shift N)) (Syn.shift (Syn.shift x)))) + var 0 ≐
        Syn.shift (var 0) * Syn.shift (Syn.shift N) + var 0 := congrAdd (fst_pair _ _) (.eqRefl _)
  refine (congrInst2 (flatB a) f1 (snd_pair _ _)).eqTrans ((flat_at a _ _ _).eqTrans ?_)
  exact congrInst3 a (Prf.andE₁ qr) (Prf.andE₂ qr) (.eqRefl _) |>.eqTrans
    (congrInst3 a (fst_pair _ _).eqSymm (.eqRefl _) (snd_pair _ _).eqSymm)

end LeanProofs.IPRA.BlockSum
