import IPRADerivations.Combinatorics.CatalanConvolution
import IPRADerivations.Combinatorics.LinearFactorTable
import IPRADerivations.Foundations.BoundedReflection
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# The iterated Catalan convolution

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16`, Section 7, (7.2): the sum
"`Σ_{i_1 + ⋯ + i_k = n} Cat_{i_1} ⋯ Cat_{i_k}`" counting forests of `k` ordered full binary trees
with `n` internal nodes.

The sum is the iterated convolution `T(0, n) = [n = 0]`, `T(k + 1, n) = Σ_{i ≤ n} Cat_i T(k, n − i)`.
The step uses all entries `T(k, 0), …, T(k, n)`, so the values are kept in coded rows: `row k N`
is the list of `T(k, m)`, `m ≤ N`, and `Tb k m N` is its entry at `m`.

* `eqB`, `allEq_elim`, `allEq_intro`: the bit of an equation between two bodies under a bounded
  universal (`Foundations/BoundedReflection.allB`);
* `Tb_zero`, `Tb_succ`: the entries of the rows, for `m ≤ N`;
* `indep_all`, `indep_at`, `Tb_add`, `Tb_eq`: an entry does not depend on the bound,
  `Tb k m N = Tb k m m` for `m ≤ N`. The induction is on `k`, and its formula is the bit of the
  statement for all `m ≤ N`, because the step at `m` uses the hypothesis at all `m − i`;
* `T k m = Tb k m m`, with `T_zero`: `T(0, m) = [m = 0]` and `T_succ`:
  `T(k + 1, m) = Σ_{i ≤ m} Cat_i T(k, m − i)`;
* `T_col_zero`: `T(k, 0) = 1`; `T_one`: `T(1, m) = Cat_m`;
* `T_rec`: `T(k + 1, m + 1) = T(k, m + 1) + T(k + 2, m)`, the coefficient form of
  `C^{k+1} = C^k + x C^{k+2}`. The induction is on `k`, with the bit of the statement for all
  `m < M`; the base is Segner's recurrence (`Combinatorics/CatalanConvolution.segner`), so no
  associativity of the convolution is needed.

The closed form (7.3) is derived from `T_rec` in `Combinatorics/CatalanKFold`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanPowers

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Bell (nth monus_monus monus_le')
open LeanProofs.IPRA.Combinatorics.Stirling (build nth_build congrNth gle_above)
open LeanProofs.IPRA.Combinatorics.Catalan (cat cat_zero)
open LeanProofs.IPRA.Combinatorics.CatalanConvolution (convB inst2_conv segner)
open LeanProofs.IPRA.Combinatorics.BellTouchardPower (pair_congr succ_monus_of_le le_of_lt_succ)
open LeanProofs.IPRA.Combinatorics.LinearFactorTable (sum_lin)
open LeanProofs.IPRA.Foundations.BoundedReflection (allB all_elim all_intro one_ne_zero)
open LeanProofs.IPRA.AnalyticNumberTheory.Valuation (eq_of_eqb_ne)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## Shifts and order -/

theorem shift_pair (a b : PTm n) : Syn.shift (pairT a b) = pairT (Syn.shift a) (Syn.shift b) := by
  simp [Syn.shift]

theorem shift_succ (a : PTm n) : Syn.shift (succ a) = succ (Syn.shift a) := by simp [Syn.shift]

theorem shift_zero : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]

alias monus_le_left := Common.monus_le_self

alias lt_succ_of_le := Common.lt_succ_of_le

/-! ## The bit of an equation under a bounded universal -/

section EqBit

variable (L R : PTm 2)

/-- The bit `[L(i, x) = R(i, x)]`. -/
def eqB : PTm 2 := eqb L R

theorem inst2_eqB (i x : PTm n) : inst2 (eqB L R) i x = eqb (inst2 L i x) (inst2 R i x) := by
  simp [inst2, eqB]

theorem allEq_elim {N i x : PTm n} (h : Γ ⊢[PRAAx] allB (eqB L R) N x ≐ one)
    (hi : Γ ⊢[PRAAx] lt i N) : Γ ⊢[PRAAx] inst2 L i x ≐ inst2 R i x := by
  have a := all_elim (eqB L R) h hi
  rw [inst2_eqB] at a
  exact eq_of_eqb_ne a

theorem allEq_intro {N x : PTm n}
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      (inst2 L (var 0) (Syn.shift x) ≐ inst2 R (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] allB (eqB L R) N x ≐ one := by
  refine all_intro (eqB L R) (.allI (.impI ?_))
  rw [inst2_eqB]
  exact .impI (one_ne_zero _
    ((eqb_of_eq (.impE h.allOpen.wk Prf.hyp0)).wk.eqSymm.eqTrans Prf.hyp0))

end EqBit

/-! ## The rows -/

/-- `Cat_i · R[m − i]` for a row `R` of bound `N`, over `0 = i`, `1 = ⟨m, ⟨N, R⟩⟩`. -/
abbrev cB : PTm 2 :=
  cat (var 0) * nth (sndT (sndT (var 1)))
    (monus (fstT (sndT (var 1))) (monus (fstT (var 1)) (var 0)))

theorem inst2_cB (i y : PTm n) : inst2 cB i y =
    cat i * nth (sndT (sndT y)) (monus (fstT (sndT y)) (monus (fstT y) i)) := by
  simp [inst2]

/-- The entry `m` of the next row, over `0 = m`, `1 = ⟨N, R⟩`. -/
abbrev eT : PTm 2 := ap2 (sumF cB) (succ (var 0)) (pairT (var 0) (var 1))

theorem inst2_eT (m y : PTm n) : inst2 eT m y = ap2 (sumF cB) (succ m) (pairT m y) := by
  simp [inst2]

/-- The entry `m` of row `0`: `[m = 0]`. -/
abbrev e0 : PTm 2 := monus one (var 0)

theorem inst2_e0 (m y : PTm n) : inst2 e0 m y = monus one m := by simp [inst2]

/-- Row `0` of bound `N`; variable `0 = N`. -/
abbrev rowBase : PTm 1 := build e0 (succ (var 0)) zero
/-- The row step; variables `0 = k`, `1 = R_k`, `2 = N`. -/
abbrev rowStep : PTm 3 := build eT (succ (var 2)) (pairT (var 2) (var 1))
abbrev RF : PR 2 := rec2 rowBase rowStep
/-- The coded row `(T(k, m))_{m ≤ N}`. -/
abbrev row (k N : PTm n) : PTm n := ap2 RF k N

theorem shift_row (k N : PTm n) : Syn.shift (row k N) = row (Syn.shift k) (Syn.shift N) := by
  simp [Syn.shift]

theorem row_zero (N : PTm n) : Γ ⊢[PRAAx] row zero N ≐ build e0 (succ N) zero := by
  have h := rec2_zero (Γ := Γ) rowBase rowStep N
  simpa using h

theorem row_succ (k N : PTm n) :
    Γ ⊢[PRAAx] row (succ k) N ≐ build eT (succ N) (pairT N (row k N)) := by
  have h := rec2_succ (Γ := Γ) rowBase rowStep k N
  simpa using h

/-- The entry `m` of the row `k` of bound `N`. -/
abbrev Tb (k m N : PTm n) : PTm n := nth (row k N) (monus N m)

theorem congrTb {k k' m m' N N' : PTm n} (hk : Γ ⊢[PRAAx] k ≐ k') (hm : Γ ⊢[PRAAx] m ≐ m')
    (hN : Γ ⊢[PRAAx] N ≐ N') : Γ ⊢[PRAAx] Tb k m N ≐ Tb k' m' N' :=
  congrNth (congrAp2 RF hk hN) (congrMonus hN hm)

/-- `T_N(0, m) = [m = 0]` for `m ≤ N`. -/
theorem Tb_zero {m N : PTm n} (h : Γ ⊢[PRAAx] le m N) : Γ ⊢[PRAAx] Tb zero m N ≐ monus one m := by
  have a : Γ ⊢[PRAAx] nth (row zero N) (monus N m) ≐ inst2 e0 (monus N (monus N m)) zero :=
    (congrNth (row_zero N) (.eqRefl _)).eqTrans (nth_build e0 zero (monus_le' h))
  rw [inst2_e0] at a
  exact a.eqTrans (congrMonus (.eqRefl _) (monus_monus h))

/-- `Cat_i · T_N(k, m − i)`, over `0 = i`, `1 = ⟨m, ⟨k, N⟩⟩`. -/
abbrev tbB : PTm 2 :=
  cat (var 0) * Tb (fstT (sndT (var 1))) (monus (fstT (var 1)) (var 0)) (sndT (sndT (var 1)))

theorem tb_at (i m k N : PTm n) :
    Γ ⊢[PRAAx] inst2 tbB i (pairT m (pairT k N)) ≐ cat i * Tb k (monus m i) N := by
  have h : inst2 tbB i (pairT m (pairT k N)) =
      cat i * Tb (fstT (sndT (pairT m (pairT k N)))) (monus (fstT (pairT m (pairT k N))) i)
        (sndT (sndT (pairT m (pairT k N)))) := by simp [inst2]
  rw [h]
  have s : Γ ⊢[PRAAx] sndT (pairT m (pairT k N)) ≐ pairT k N := snd_pair _ _
  exact congrMul (.eqRefl _) (congrTb ((congrFst s).eqTrans (fst_pair _ _))
    (congrMonus (fst_pair _ _) (.eqRefl _)) ((congrSnd s).eqTrans (snd_pair _ _)))

theorem c_at (i m k N : PTm n) :
    Γ ⊢[PRAAx] inst2 cB i (pairT m (pairT N (row k N))) ≐ inst2 tbB i (pairT m (pairT k N)) := by
  rw [inst2_cB]
  have s : Γ ⊢[PRAAx] sndT (pairT m (pairT N (row k N))) ≐ pairT N (row k N) := snd_pair _ _
  exact (congrMul (.eqRefl _) (congrNth ((congrSnd s).eqTrans (snd_pair _ _))
    (congrMonus ((congrFst s).eqTrans (fst_pair _ _))
      (congrMonus (fst_pair _ _) (.eqRefl _))))).eqTrans (tb_at i m k N).eqSymm

/-- `T_N(k + 1, m) = Σ_{i ≤ m} Cat_i T_N(k, m − i)` for `m ≤ N`. -/
theorem Tb_succ {k m N : PTm n} (h : Γ ⊢[PRAAx] le m N) :
    Γ ⊢[PRAAx] Tb (succ k) m N ≐ ap2 (sumF tbB) (succ m) (pairT m (pairT k N)) := by
  have hm := monus_monus h
  have a : Γ ⊢[PRAAx] Tb (succ k) m N ≐ inst2 eT (monus N (monus N m)) (pairT N (row k N)) :=
    (congrNth (row_succ k N) (.eqRefl _)).eqTrans (nth_build eT _ (monus_le' h))
  rw [inst2_eT] at a
  refine a.eqTrans ((congrAp2 _ (congrSucc hm) (pair_congr hm (.eqRefl _))).eqTrans ?_)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  simp only [shift_pair, shift_row]
  exact c_at _ _ _ _

/-! ## Independence of the bound -/

/-- `T_N(k, m)`, over `0 = m`, `1 = ⟨k, N⟩`. -/
abbrev iL : PTm 2 := Tb (fstT (var 1)) (var 0) (sndT (var 1))
/-- `T_{N+1}(k, m)`, over `0 = m`, `1 = ⟨k, N⟩`. -/
abbrev iR : PTm 2 := Tb (fstT (var 1)) (var 0) (succ (sndT (var 1)))

theorem iL_at (m k N : PTm n) : Γ ⊢[PRAAx] inst2 iL m (pairT k N) ≐ Tb k m N := by
  have h : inst2 iL m (pairT k N) = Tb (fstT (pairT k N)) m (sndT (pairT k N)) := by simp [inst2]
  rw [h]
  exact congrTb (fst_pair _ _) (.eqRefl _) (snd_pair _ _)

theorem iR_at (m k N : PTm n) : Γ ⊢[PRAAx] inst2 iR m (pairT k N) ≐ Tb k m (succ N) := by
  have h : inst2 iR m (pairT k N) = Tb (fstT (pairT k N)) m (succ (sndT (pairT k N))) := by
    simp [inst2]
  rw [h]
  exact congrTb (fst_pair _ _) (.eqRefl _) (congrSucc (snd_pair _ _))

theorem indep_base_pt {m N : PTm n} (h : Γ ⊢[PRAAx] le m N) :
    Γ ⊢[PRAAx] Tb zero m N ≐ Tb zero m (succ N) :=
  (Tb_zero h).eqTrans (Tb_zero (le_trans h (le_succ_self N))).eqSymm

theorem indep_step_pt {k m N : PTm n}
    (hQ : Γ ⊢[PRAAx] allB (eqB iL iR) (succ N) (pairT k N) ≐ one) (h : Γ ⊢[PRAAx] le m N) :
    Γ ⊢[PRAAx] Tb (succ k) m N ≐ Tb (succ k) m (succ N) := by
  refine (Tb_succ h).eqTrans (.eqTrans ?_ (Tb_succ (le_trans h (le_succ_self N))).eqSymm)
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  have hQ' : (Γ.map Fm.shift) ⊢[PRAAx]
      allB (eqB iL iR) (succ (Syn.shift N)) (pairT (Syn.shift k) (Syn.shift N)) ≐ one := by
    simpa [Fm.shift, Syn.shift] using hQ.shift
  have h' : (Γ.map Fm.shift) ⊢[PRAAx] le (Syn.shift m) (Syn.shift N) := by
    simpa [Fm.shift, Syn.shift] using h.shift
  simp only [shift_pair, shift_succ]
  have hi : (lt (var 0) (succ (Syn.shift m)) :: Γ.map Fm.shift) ⊢[PRAAx]
      lt (monus (Syn.shift m) (var 0)) (succ (Syn.shift N)) :=
    lt_succ_of_le (le_trans (monus_le_left _ _) h'.wk)
  have e := allEq_elim iL iR hQ'.wk hi
  exact (tb_at _ _ _ _).eqTrans ((congrMul (.eqRefl _)
    ((iL_at _ _ _).eqSymm.eqTrans (e.eqTrans (iR_at _ _ _)))).eqTrans (tb_at _ _ _ _).eqSymm)

theorem indep_step {k N : PTm n} (hQ : Γ ⊢[PRAAx] allB (eqB iL iR) (succ N) (pairT k N) ≐ one) :
    Γ ⊢[PRAAx] allB (eqB iL iR) (succ N) (pairT (succ k) N) ≐ one := by
  refine allEq_intro iL iR (.allI (.impI ?_))
  have hQ' : (Γ.map Fm.shift) ⊢[PRAAx]
      allB (eqB iL iR) (succ (Syn.shift N)) (pairT (Syn.shift k) (Syn.shift N)) ≐ one := by
    simpa [Fm.shift, Syn.shift] using hQ.shift
  simp only [shift_pair, shift_succ]
  exact (iL_at _ _ _).eqTrans ((indep_step_pt hQ'.wk (le_of_lt_succ Prf.hyp0)).eqTrans
    (iR_at _ _ _).eqSymm)

/-- The induction formula of `indep_all`; variable `0 = k`. -/
abbrev indF (N : PTm n) : Fm PTm (n + 1) :=
  allB (eqB iL iR) (succ (Syn.shift N)) (pairT (var 0) (Syn.shift N)) ≐ one

/-- The entries `m ≤ N` of the rows of bounds `N` and `N + 1` agree. -/
theorem indep_all (k N : PTm n) : Γ ⊢[PRAAx] allB (eqB iL iR) (succ N) (pairT k N) ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (indF N) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have b : Γ ⊢[PRAAx] allB (eqB iL iR) (succ N) (pairT zero N) ≐ one := by
        refine allEq_intro iL iR (.allI (.impI ?_))
        simp only [shift_pair, shift_succ, shift_zero]
        exact (iL_at _ _ _).eqTrans ((indep_base_pt (le_of_lt_succ Prf.hyp0)).eqTrans
          (iR_at _ _ _).eqSymm)
      simpa using b
    · have st : (indF N :: Γ.map Fm.shift) ⊢[PRAAx]
          allB (eqB iL iR) (succ (Syn.shift N)) (pairT (succ (var 0)) (Syn.shift N)) ≐ one :=
        indep_step Prf.hyp0
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE k hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

theorem indep_at {k m N : PTm n} (h : Γ ⊢[PRAAx] le m N) :
    Γ ⊢[PRAAx] Tb k m N ≐ Tb k m (succ N) :=
  (iL_at m k N).eqSymm.eqTrans
    ((allEq_elim iL iR (indep_all k N) (lt_succ_of_le h)).eqTrans (iR_at m k N))

/-! ## The iterated convolution -/

/-- `T(k, m) = Σ_{i_1 + ⋯ + i_k = m} Cat_{i_1} ⋯ Cat_{i_k}`. -/
abbrev T (k m : PTm n) : PTm n := Tb k m m

theorem congrT {k k' m m' : PTm n} (hk : Γ ⊢[PRAAx] k ≐ k') (hm : Γ ⊢[PRAAx] m ≐ m') :
    Γ ⊢[PRAAx] T k m ≐ T k' m' := congrTb hk hm hm

/-- The induction formula of `Tb_add`; variable `0 = d`. -/
abbrev teF (k m : PTm n) : Fm PTm (n + 1) :=
  Tb (Syn.shift k) (Syn.shift m) (Syn.shift m + var 0) ≐ T (Syn.shift k) (Syn.shift m)

theorem Tb_add (k m d : PTm n) : Γ ⊢[PRAAx] Tb k m (m + d) ≐ T k m := by
  have hall : Γ ⊢[PRAAx] Fm.all (teF k m) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have b : Γ ⊢[PRAAx] Tb k m (m + zero) ≐ T k m :=
        congrTb (.eqRefl _) (.eqRefl _) (add_zero _)
      simpa using b
    · have st : (teF k m :: Γ.map Fm.shift) ⊢[PRAAx]
          Tb (Syn.shift k) (Syn.shift m) (Syn.shift m + succ (var 0)) ≐
            T (Syn.shift k) (Syn.shift m) :=
        (congrTb (.eqRefl _) (.eqRefl _) (add_succ _ _)).eqTrans
          ((indep_at (le_add_right _ _)).eqSymm.eqTrans Prf.hyp0)
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE d hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

/-- An entry does not depend on the bound of its row. -/
theorem Tb_eq {k m N : PTm n} (h : Γ ⊢[PRAAx] le m N) : Γ ⊢[PRAAx] Tb k m N ≐ T k m :=
  (congrTb (.eqRefl _) (.eqRefl _) (eq_add_of_le h)).eqTrans (Tb_add k m (monus N m))

/-- `Cat_i · T(k, m − i)`, over `0 = i`, `1 = ⟨k, m⟩`. -/
abbrev tB : PTm 2 := cat (var 0) * T (fstT (var 1)) (monus (sndT (var 1)) (var 0))

theorem t_at (i k m : PTm n) : Γ ⊢[PRAAx] inst2 tB i (pairT k m) ≐ cat i * T k (monus m i) := by
  have h : inst2 tB i (pairT k m) =
      cat i * T (fstT (pairT k m)) (monus (sndT (pairT k m)) i) := by simp [inst2]
  rw [h]
  exact congrMul (.eqRefl _) (congrT (fst_pair _ _) (congrMonus (snd_pair _ _) (.eqRefl _)))

/-- `T(0, m) = [m = 0]`. -/
theorem T_zero (m : PTm n) : Γ ⊢[PRAAx] T zero m ≐ monus one m := Tb_zero (le_refl m)

/-- `T(k + 1, m) = Σ_{i ≤ m} Cat_i T(k, m − i)`. -/
theorem T_succ (k m : PTm n) :
    Γ ⊢[PRAAx] T (succ k) m ≐ ap2 (sumF tB) (succ m) (pairT k m) := by
  refine (Tb_succ (le_refl m)).eqTrans (sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_)))
  simp only [shift_pair, shift_succ]
  exact (tb_at _ _ _ _).eqTrans ((congrMul (.eqRefl _) (Tb_eq (monus_le_left _ _))).eqTrans
    (t_at _ _ _).eqSymm)

/-! ## The column `m = 0` and the row `k = 1` -/

theorem col_zero_step {k : PTm n} (ih : Γ ⊢[PRAAx] T k zero ≐ one) :
    Γ ⊢[PRAAx] T (succ k) zero ≐ one := by
  have s₁ := T_succ (Γ := Γ) k zero
  have s₂ := sum_succ' (Γ := Γ) tB zero (pairT k zero)
  have s₃ : Γ ⊢[PRAAx] ap2 (sumF tB) zero (pairT k zero) + inst2 tB zero (pairT k zero) ≐
      zero + one * one :=
    congrAdd (sum_zero tB _) ((t_at zero k zero).eqTrans
      (congrMul cat_zero ((congrT (.eqRefl _) (monus_zero zero)).eqTrans ih)))
  exact (s₁.eqTrans (s₂.eqTrans s₃)).eqTrans (by ipra_ring)

/-- The induction formula of `T_col_zero`; variable `0 = k`. -/
abbrev czF : Fm PTm (n + 1) := T (var 0) zero ≐ one

/-- `T(k, 0) = 1`. -/
theorem T_col_zero (k : PTm n) : Γ ⊢[PRAAx] T k zero ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (czF (n := n)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have b : Γ ⊢[PRAAx] T (zero : PTm n) zero ≐ one := (T_zero zero).eqTrans (monus_zero one)
      simpa using b
    · have st : (czF (n := n) :: Γ.map Fm.shift) ⊢[PRAAx] T (succ (var 0)) zero ≐ one :=
        col_zero_step Prf.hyp0
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE k hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

/-- `T(1, m) = Cat_m`. -/
theorem T_one (m : PTm n) : Γ ⊢[PRAAx] T (succ zero) m ≐ cat m := by
  have s₁ := T_succ (Γ := Γ) zero m
  have s₂ := sum_succ' (Γ := Γ) tB m (pairT zero m)
  have z : Γ ⊢[PRAAx] ap2 (sumF tB) m (pairT zero m) ≐ zero := by
    refine sum_zero_of_bounded _ _ _ (.allI (.impI ?_))
    simp only [shift_pair, shift_zero]
    exact (t_at _ _ _).eqTrans ((congrMul (.eqRefl _)
      ((T_zero _).eqTrans (gle_above Prf.hyp0))).eqTrans (mul_zero _))
  have l : Γ ⊢[PRAAx] inst2 tB m (pairT zero m) ≐ cat m * one :=
    (t_at m zero m).eqTrans (congrMul (.eqRefl _)
      ((T_zero _).eqTrans ((congrMonus (.eqRefl _) (monus_self m)).eqTrans (monus_zero one))))
  exact (s₁.eqTrans (s₂.eqTrans (congrAdd z l))).eqTrans (by ipra_ring)

/-! ## The three-term recurrence -/

/-- `T(k + 1, m + 1)`, over `0 = m`, `1 = k`. -/
abbrev rL : PTm 2 := T (succ (var 1)) (succ (var 0))
/-- `T(k, m + 1) + T(k + 2, m)`, over `0 = m`, `1 = k`. -/
abbrev rR : PTm 2 := T (var 1) (succ (var 0)) + T (succ (succ (var 1))) (var 0)

theorem inst2_rL (m k : PTm n) : inst2 rL m k = T (succ k) (succ m) := by simp [inst2]

theorem inst2_rR (m k : PTm n) :
    inst2 rR m k = T k (succ m) + T (succ (succ k)) m := by simp [inst2]

/-- The base `k = 0`: Segner's recurrence. -/
theorem rec_base_pt (m : PTm n) :
    Γ ⊢[PRAAx] T (succ zero) (succ m) ≐ T zero (succ m) + T (succ (succ zero)) m := by
  have a : Γ ⊢[PRAAx] T zero (succ m) ≐ zero :=
    (T_zero (succ m)).eqTrans ((succ_monus_succ zero m).eqTrans (zero_monus m))
  have b : Γ ⊢[PRAAx] T (succ (succ zero)) m ≐ cat (succ m) := by
    refine (T_succ (succ zero) m).eqTrans (.eqTrans ?_ (segner m))
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_pair, shift_succ, shift_zero]
    rw [inst2_conv]
    exact (t_at _ _ _).eqTrans (congrMul (.eqRefl _) (T_one _))
  exact (T_one (succ m)).eqTrans ((congrAdd a b).eqTrans (zero_add _)).eqSymm

/-- The step at one index `m < M`. -/
theorem rec_step_pt {k m M : PTm n} (hQ : Γ ⊢[PRAAx] allB (eqB rL rR) M k ≐ one)
    (hm : Γ ⊢[PRAAx] lt m M) :
    Γ ⊢[PRAAx] T (succ (succ k)) (succ m) ≐
      T (succ k) (succ m) + T (succ (succ (succ k))) m := by
  -- the three sums over `i ≤ m`
  have lin : Γ ⊢[PRAAx] ap2 (sumF tB) (succ m) (pairT (succ k) (succ m)) ≐
      one * ap2 (sumF tB) (succ m) (pairT k (succ m)) +
        ap2 (sumF tB) (succ m) (pairT (succ (succ k)) m) := by
    refine sum_lin tB tB tB (.allI (.impI ?_))
    have hQ' : (Γ.map Fm.shift) ⊢[PRAAx] allB (eqB rL rR) (Syn.shift M) (Syn.shift k) ≐ one := by
      simpa [Fm.shift, Syn.shift] using hQ.shift
    have hm' : (Γ.map Fm.shift) ⊢[PRAAx] lt (Syn.shift m) (Syn.shift M) := by
      simpa [Fm.shift, Syn.shift] using hm.shift
    simp only [shift_pair, shift_succ, shift_zero]
    have hv : (lt (var 0) (succ (Syn.shift m)) :: Γ.map Fm.shift) ⊢[PRAAx]
        le (var 0) (Syn.shift m) := le_of_lt_succ Prf.hyp0
    have sm := succ_monus_of_le hv
    have ih : (lt (var 0) (succ (Syn.shift m)) :: Γ.map Fm.shift) ⊢[PRAAx]
        inst2 rL (monus (Syn.shift m) (var 0)) (Syn.shift k) ≐
          inst2 rR (monus (Syn.shift m) (var 0)) (Syn.shift k) :=
      allEq_elim rL rR hQ'.wk
        (lt_of_le_of_lt (monus_le_left (Syn.shift m) (var 0)) hm'.wk)
    rw [inst2_rL, inst2_rR] at ih
    have abc : (lt (var 0) (succ (Syn.shift m)) :: Γ.map Fm.shift) ⊢[PRAAx]
        T (succ (Syn.shift k)) (monus (succ (Syn.shift m)) (var 0)) ≐
          T (Syn.shift k) (monus (succ (Syn.shift m)) (var 0)) +
            T (succ (succ (Syn.shift k))) (monus (Syn.shift m) (var 0)) :=
      (congrT (.eqRefl _) sm).eqTrans (ih.eqTrans
        (congrAdd (congrT (.eqRefl _) sm.eqSymm) (.eqRefl _)))
    refine (t_at _ _ _).eqTrans (.eqTrans ?_
      (congrAdd (congrMul (.eqRefl _) (t_at _ _ _)) (t_at _ _ _)).eqSymm)
    ipra_lc (𝔞 (cat (var 0))) * natEq abc
  have top : ∀ j : PTm n, Γ ⊢[PRAAx] inst2 tB (succ m) (pairT j (succ m)) ≐ cat (succ m) * one :=
    fun j => (t_at (succ m) j (succ m)).eqTrans (congrMul (.eqRefl _)
      ((congrT (.eqRefl _) (monus_self (succ m))).eqTrans (T_col_zero j)))
  ipra_lc natEq ((T_succ (Γ := Γ) (succ k) (succ m)).eqTrans ((sum_succ' tB (succ m) _).eqTrans (congrAdd lin (top (succ k))))) -
    natEq ((T_succ (Γ := Γ) k (succ m)).eqTrans ((sum_succ' tB (succ m) _).eqTrans (congrAdd (.eqRefl _) (top k)))) -
    natEq (T_succ (Γ := Γ) (succ (succ k)) m)

theorem rec_step {k M : PTm n} (hQ : Γ ⊢[PRAAx] allB (eqB rL rR) M k ≐ one) :
    Γ ⊢[PRAAx] allB (eqB rL rR) M (succ k) ≐ one := by
  refine allEq_intro rL rR (.allI (.impI ?_))
  have hQ' : (Γ.map Fm.shift) ⊢[PRAAx] allB (eqB rL rR) (Syn.shift M) (Syn.shift k) ≐ one := by
    simpa [Fm.shift, Syn.shift] using hQ.shift
  simp only [shift_succ]
  rw [inst2_rL, inst2_rR]
  exact rec_step_pt hQ'.wk Prf.hyp0

/-- The induction formula of `rec_all`; variable `0 = k`. -/
abbrev recF (M : PTm n) : Fm PTm (n + 1) := allB (eqB rL rR) (Syn.shift M) (var 0) ≐ one

theorem rec_all (k M : PTm n) : Γ ⊢[PRAAx] allB (eqB rL rR) M k ≐ one := by
  have hall : Γ ⊢[PRAAx] Fm.all (recF M) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · have b : Γ ⊢[PRAAx] allB (eqB rL rR) M zero ≐ one := by
        refine allEq_intro rL rR (.allI (.impI ?_))
        simp only [shift_zero]
        rw [inst2_rL, inst2_rR]
        exact rec_base_pt _
      simpa using b
    · have st : (recF M :: Γ.map Fm.shift) ⊢[PRAAx]
          allB (eqB rL rR) (Syn.shift M) (succ (var 0)) ≐ one := rec_step Prf.hyp0
      simpa [subst_repl_shift, Syn.repl_zero] using st
  have h2 := Prf.allE k hall
  simpa [Syn.subst_inst_shift, Syn.inst_zero] using h2

/-- `T(k + 1, m + 1) = T(k, m + 1) + T(k + 2, m)`: the coefficient form of
`C^{k+1} = C^k + x C^{k+2}`. -/
theorem T_rec (k m : PTm n) :
    Γ ⊢[PRAAx] T (succ k) (succ m) ≐ T k (succ m) + T (succ (succ k)) m := by
  have h := allEq_elim rL rR (rec_all (Γ := Γ) k (succ m)) (le_refl (succ m))
  rw [inst2_rL, inst2_rR] at h
  exact h

end LeanProofs.IPRA.Combinatorics.CatalanPowers
