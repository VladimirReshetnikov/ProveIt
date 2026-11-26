import IPRADerivations.Combinatorics.BellPascalInversion
import IPRADerivations.Combinatorics.BinomialTwo
import IPRADerivations.AnalyticNumberTheory.Order
import IPRADerivations.Combinatorics.BellStirling
import IPRADerivations.AnalyticNumberTheory.PhiLower
import IPRADerivations.Analysis.RationalArithmetic.PowerSums
import IPRADerivations.Core.LinearCombination

/-!
# Spivey's identity

Packet: `combinatorics/bell_numbers_ipra` (`thm:spivey`, `eq:spivey`, and the lower bound of
`eq:bell-product-bounds`): for all `n, m`,

  `B_{n+m} = ∑_{k ≤ n} ∑_{j ≤ m} C(n, k) S(m, j) j^{n−k} B_k`,

and hence `B_m B_n ≤ B_{m+n}`. The packet's proof is a bijection. Here, with
`G(n, j) = ∑_{k ≤ n} C(n, k) j^{n−k} B_k` (the umbral `𝓛((X + j)^n)`):

* `revision`: `C(n, k) C(k, i) = C(n, i) C(n − i, k − i)` for `i ≤ k ≤ n`;
* `conv_inner`: `∑_{k ≤ n} C(n, k) C(k, i) x^{n−k} = C(n, i) (x + 1)^{n−i}`, by the revision and the
  binomial theorem;
* `G_shift`: `∑_{k ≤ n} C(n, k) j^{n−k} B_{k+1} = G(n, j + 1)`, by the Bell recurrence, an exchange of
  sums and `conv_inner`;
* `G_succ`: `G(n + 1, j) = j G(n, j) + G(n, j + 1)`, by Pascal's rule (the derivative rule for
  `e^{jt} B(t)`);
* `F_succ`: with `F(n, m) = ∑_{j ≤ m} S(m, j) G(n, j)`, the Stirling recurrence gives
  `F(n, m + 1) = F(n + 1, m)`;
* `spivey`: `F(n, m) = B_{n+m}`, by induction on `m` for all `n` at once (a violation count over
  `n < M − m`), from `F(n, 0) = G(n, 0) = B_n`;
* `bell_product`: `B_m B_n ≤ B_{m+n}`, keeping the terms `k = n`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.BellSpivey

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Analysis.Products (fact)
open LeanProofs.IPRA.AnalyticNumberTheory.Primes (fact_pos)
open LeanProofs.IPRA.AnalyticNumberTheory.Order (pw_one_base)
open LeanProofs.IPRA.Combinatorics.Binomial (binom bden pos_mul)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (binom_eq mul_cancel)
open LeanProofs.IPRA.Combinatorics.Stirling (gle gle_of_le gle_above)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_self gb_above gb_pascal zB zsum inst2_z)
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Combinatorics.BinomialTwo (bt S binomial_two bt_at fM fX fY)
open LeanProofs.IPRA.Combinatorics.StirlingBinomial (shift_y)
open LeanProofs.IPRA.Combinatorics.CatalanNarayana (le_of_lt_succ)
open LeanProofs.IPRA.Combinatorics.Bell (bell bell_succ recB inst2_rec bell_zero)
open LeanProofs.IPRA.Combinatorics.BellPascalInversion (congrBell lt_shift)
open LeanProofs.IPRA.Combinatorics.Stirling (stir stir_zero stir_above stir_succ_zero)
open LeanProofs.IPRA.Combinatorics.StirlingPowers (congrStir)
open LeanProofs.IPRA.Combinatorics.StirlingBinomial (stir_rec)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eq_of_viol viol_of_eq)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem shift_succ (a : PTm n) : Syn.shift (succ a) = succ (Syn.shift a) := by simp [Syn.shift]

/-! ## The revision of binomial coefficients -/

/-- `C(n, k) C(k, i) = C(n, i) C(n − i, k − i)` for `i ≤ k ≤ n`. -/
theorem revision {N k i : PTm n} (hik : Γ ⊢[PRAAx] le i k) (hkn : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] gb N k * gb k i ≐ gb N i * gb (monus N i) (monus k i) := by
  have hin := le_trans hik hkn
  have a₁ := natEq (eq_add_of_le hik); have a₂ := natEq (eq_add_of_le hkn)
  -- `N − i = (k − i) + (N − k)`.
  have hNi : Γ ⊢[PRAAx] monus N i ≐ monus k i + monus N k := by
    have e : Γ ⊢[PRAAx] N ≐ (monus k i + monus N k) + i := by
      ipra_lc a₂ + a₁
    exact (congrMonus e (.eqRefl _)).eqTrans (add_monus _ _)
  have hle : Γ ⊢[PRAAx] le (monus k i) (monus N i) := le_of_eq_add hNi
  have e5 : Γ ⊢[PRAAx] monus (monus N i) (monus k i) ≐ monus N k :=
    (congrMonus hNi (.eqRefl _)).eqTrans (add_monus' _ _)
  have g₁ := natEq (gle_of_le hkn); have g₂ := natEq (gle_of_le hik); have g₃ := natEq (gle_of_le hin)
  have D := pos_mul (pos_mul (fact_pos (Γ := Γ) i) (fact_pos (Γ := Γ) (monus k i))) (fact_pos (Γ := Γ) (monus N k))
  have f₁ := natEq (binom_eq hkn); have f₂ := natEq (binom_eq hik); have f₃ := natEq (binom_eq hin)
  refine mul_cancel D ?_
  ipra_lc 𝔞 (fact i) * 𝔞 (fact (monus k i)) * 𝔞 (fact (monus N k)) * (𝔞 (binom N k) * 𝔞 (binom k i) * (𝔞 (gle i k) * g₁ + g₂) - 𝔞 (binom N i) * 𝔞 (binom (monus N i) (monus k i)) * (𝔞 (gle (monus k i) (monus N i)) * g₃ + natEq (gle_of_le hle))) -
    f₁ - 𝔞 (fact (monus N k)) * 𝔞 (binom N k) * f₂ + f₃ + 𝔞 (fact i) * 𝔞 (binom N i) * natEq (binom_eq hle) +
    𝔞 (fact i) * 𝔞 (binom N i) * 𝔞 (fact (monus k i)) * 𝔞 (binom (monus N i) (monus k i)) * natEq (congrAp2 factF e5 (.eqRefl zero) : Γ ⊢[PRAAx] fact (monus (monus N i) (monus k i)) ≐ fact (monus N k))

/-! ## The inner convolution -/

/-- `C(N, k) C(k, i) x^{N−k}`, over `0 = k`, `1 = ⟨N, ⟨i, x⟩⟩`. -/
abbrev cvB : PTm 2 := gb (fstT (var 1)) (var 0) * gb (var 0) (fstT (sndT (var 1))) *
  pw (sndT (sndT (var 1))) (monus (fstT (var 1)) (var 0))

abbrev CV {n : ℕ} (N i x : PTm n) : PTm n := ap2 (sumF cvB) (succ N) (pairT N (pairT i x))

theorem cv_at (k N i x : PTm n) :
    Γ ⊢[PRAAx] inst2 cvB k (pairT N (pairT i x)) ≐ gb N k * gb k i * pw x (monus N k) := by
  have h : inst2 cvB k (pairT N (pairT i x)) = gb (fstT (pairT N (pairT i x))) k *
      gb k (fstT (sndT (pairT N (pairT i x)))) *
      pw (sndT (sndT (pairT N (pairT i x)))) (monus (fstT (pairT N (pairT i x))) k) := by simp [inst2]
  rw [h]
  exact congrMul (congrMul (congrGb (fM _ _ _) (.eqRefl _)) (congrGb (.eqRefl _) (fX _ _ _)))
    (congrPw (fY _ _ _) (congrMonus (fM _ _ _) (.eqRefl _)))

/-- A term `k = i + l` of the inner sum, for `i + l ≤ N`. -/
theorem conv_pt {l i N x : PTm n} (hl : Γ ⊢[PRAAx] le l (monus N i)) (hi : Γ ⊢[PRAAx] le i N) :
    Γ ⊢[PRAAx] inst2 (offB cvB) l (pairT i (pairT N (pairT i x))) ≐
      gb N i * inst2 bt l (pairT (monus N i) (pairT one x)) := by
  rw [inst2_offB]
  have a₁ := natEq (eq_add_of_le hi); have a₂ := natEq (eq_add_of_le hl)
  have eN : Γ ⊢[PRAAx] N ≐ monus (monus N i) l + (i + l) := by
    ipra_lc a₁ + a₂
  have hle : Γ ⊢[PRAAx] le (i + l) N := le_of_eq_add (eN.eqTrans (add_comm _ _))
  have em : Γ ⊢[PRAAx] monus N (i + l) ≐ monus (monus N i) l := (congrMonus eN (.eqRefl _)).eqTrans (add_monus _ _)
  have el : Γ ⊢[PRAAx] monus (i + l) i ≐ l := add_monus' _ _
  refine (congrInst2 cvB (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans ?_
  refine (cv_at _ _ _ _).eqTrans ?_
  refine (congrMul (revision (le_add_right i l) hle) (congrPw (.eqRefl _) em)).eqTrans ?_
  refine (congrMul (congrMul (.eqRefl _) (congrGb (.eqRefl _) el)) (.eqRefl _)).eqTrans ?_
  refine (mul_assoc _ _ _).eqTrans (congrMul (.eqRefl _) ?_)
  refine .eqTrans ?_ (bt_at _ _ _ _).eqSymm
  have h : Γ ⊢[PRAAx] gb (monus N i) l * pw one l ≐ gb (monus N i) l :=
    (congrMul (.eqRefl _) (pw_one_base l)).eqTrans ((mul_comm _ _).eqTrans (one_mul _))
  exact congrMul h.eqSymm (.eqRefl _)

/-- `∑_{k ≤ N} C(N, k) C(k, i) x^{N−k} = C(N, i) (x + 1)^{N−i}`. -/
theorem conv_inner (N i x : PTm n) : Γ ⊢[PRAAx] CV N i x ≐ gb N i * pw (succ x) (monus N i) := by
  refine .orE (lt_or_le N i) ?_ ?_
  · have hl : (lt N i :: Γ) ⊢[PRAAx] lt N i := Prf.hyp0
    refine (sum_congr_bounded cvB zB (pairT N (pairT i x)) (pairT N (pairT i x)) (succ N)
      (.allI (.impI ?_))).eqTrans ((zsum _ _).eqTrans ?_)
    · rw [shift_succ, LeanProofs.IPRA.Combinatorics.BinomialTwo.shift_y, inst2_z]
      have hk := le_of_lt_succ (Prf.hyp0 (Ax := PRAAx) (Γ := (lt N i :: Γ).map Fm.shift)
        (φ := lt (var 0) (succ (Syn.shift N))))
      have hl' : (lt N i :: Γ).map Fm.shift ⊢[PRAAx] lt (Syn.shift N) (Syn.shift i) := by
        simpa [Fm.shift, Syn.shift] using hl.shift
      have gz : _ ⊢[PRAAx] gb (var 0) (Syn.shift i) ≐ zero :=
        gb_above (le_trans ((succ_monus_succ _ _).eqTrans hk) hl'.wk)
      exact (cv_at _ _ _ _).eqTrans ((congrMul ((congrMul (.eqRefl _) gz).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans
        (zero_mul _))
    · exact ((congrMul (gb_above hl) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm
  · have hi : (le i N :: Γ) ⊢[PRAAx] le i N := Prf.hyp0
    have eS : (le i N :: Γ) ⊢[PRAAx] succ N ≐ i + succ (monus N i) := by
      ipra_lc natEq (eq_add_of_le hi)
    refine (congrAp2 (sumF cvB) eS (.eqRefl _)).eqTrans ((sum_split cvB i _ _).eqTrans ?_)
    have z₁ : (le i N :: Γ) ⊢[PRAAx] ap2 (sumF cvB) i (pairT N (pairT i x)) ≐ zero := by
      refine (sum_congr_bounded cvB zB (pairT N (pairT i x)) (pairT N (pairT i x)) i
        (.allI (.impI ?_))).eqTrans (zsum _ _)
      rw [LeanProofs.IPRA.Combinatorics.BinomialTwo.shift_y, inst2_z]
      have gz : (lt (var 0) (Syn.shift i) :: (le i N :: Γ).map Fm.shift) ⊢[PRAAx] gb (var 0) (Syn.shift i) ≐ zero :=
        gb_above Prf.hyp0
      exact (cv_at _ _ _ _).eqTrans ((congrMul ((congrMul (.eqRefl _) gz).eqTrans (mul_zero _)) (.eqRefl _)).eqTrans
        (zero_mul _))
    have hs : (le i N :: Γ) ⊢[PRAAx] ap2 (sumF (offB cvB)) (succ (monus N i)) (pairT i (pairT N (pairT i x))) ≐
        gb N i * S (monus N i) one x := by
      refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
      have e₁ : Syn.shift (gb N i) = gb (Syn.shift N) (Syn.shift i) := by simp [Syn.shift]
      have e₂ : Syn.shift (pairT i (pairT N (pairT i x))) =
          pairT (Syn.shift i) (pairT (Syn.shift N) (pairT (Syn.shift i) (Syn.shift x))) := by simp [Syn.shift]
      have e₃ : Syn.shift (pairT (monus N i) (pairT (one : PTm n) x)) =
          pairT (monus (Syn.shift N) (Syn.shift i)) (pairT one (Syn.shift x)) := by simp [Syn.shift]
      have e₄ : Syn.shift (succ (monus N i)) = succ (monus (Syn.shift N) (Syn.shift i)) := by simp [Syn.shift]
      rw [e₁, e₂, e₃, e₄]
      have hl := le_of_lt_succ (Prf.hyp0 (Ax := PRAAx) (Γ := (le i N :: Γ).map Fm.shift)
        (φ := lt (var 0) (succ (monus (Syn.shift N) (Syn.shift i)))))
      have hi' : (le i N :: Γ).map Fm.shift ⊢[PRAAx] le (Syn.shift i) (Syn.shift N) := by
        simpa [Fm.shift, Syn.shift] using hi.shift
      exact conv_pt hl hi'.wk
    refine (congrAdd z₁ hs).eqTrans ((zero_add _).eqTrans (congrMul (.eqRefl _) ?_))
    exact (binomial_two _ _ _).eqTrans (congrPw (by ipra_ring) (.eqRefl _))

/-! ## `G(n, j) = ∑_{k ≤ n} C(n, k) j^{n−k} B_k` -/

/-- Over `0 = k`, `1 = ⟨N, j⟩`. -/
abbrev gB : PTm 2 := gb (fstT (var 1)) (var 0) * pw (sndT (var 1)) (monus (fstT (var 1)) (var 0)) * bell (var 0)
/-- `C(N, k) j^{N−k} B_{k+1}`. -/
abbrev tB : PTm 2 := gb (fstT (var 1)) (var 0) * pw (sndT (var 1)) (monus (fstT (var 1)) (var 0)) * bell (succ (var 0))

abbrev G {n : ℕ} (N j : PTm n) : PTm n := ap2 (sumF gB) (succ N) (pairT N j)
abbrev T {n : ℕ} (N j : PTm n) : PTm n := ap2 (sumF tB) (succ N) (pairT N j)

theorem g_at (k N j : PTm n) : Γ ⊢[PRAAx] inst2 gB k (pairT N j) ≐ gb N k * pw j (monus N k) * bell k := by
  have h : inst2 gB k (pairT N j) = gb (fstT (pairT N j)) k * pw (sndT (pairT N j)) (monus (fstT (pairT N j)) k) *
      bell k := by simp [inst2]
  rw [h]
  exact congrMul (congrMul (congrGb (fst_pair _ _) (.eqRefl _)) (congrPw (snd_pair _ _) (congrMonus (fst_pair _ _) (.eqRefl _))))
    (.eqRefl _)

theorem t_at (k N j : PTm n) : Γ ⊢[PRAAx] inst2 tB k (pairT N j) ≐ gb N k * pw j (monus N k) * bell (succ k) := by
  have h : inst2 tB k (pairT N j) = gb (fstT (pairT N j)) k * pw (sndT (pairT N j)) (monus (fstT (pairT N j)) k) *
      bell (succ k) := by simp [inst2]
  rw [h]
  exact congrMul (congrMul (congrGb (fst_pair _ _) (.eqRefl _)) (congrPw (snd_pair _ _) (congrMonus (fst_pair _ _) (.eqRefl _))))
    (.eqRefl _)

/-- `C(k, i) B_i`, over `0 = i`, `1 = k`. -/
abbrev biB : PTm 2 := gb (var 1) (var 0) * bell (var 0)

theorem inst2_bi (i k : PTm n) : inst2 biB i k = gb k i * bell i := by simp [inst2]

/-- `∑_{i ≤ k} C(k, i) B_i = B_{k+1}`. -/
theorem bi_bell (k : PTm n) : Γ ⊢[PRAAx] ap2 (sumF biB) (succ k) k ≐ bell (succ k) := by
  refine .eqTrans ?_ (bell_succ k).eqSymm
  refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
  rw [inst2_bi, inst2_rec, shift_succ]
  have hk := le_of_lt_succ (Prf.hyp0 (Ax := PRAAx) (Γ := Γ.map Fm.shift) (φ := lt (var 0) (succ (Syn.shift k))))
  exact congrMul ((congrMul (gle_of_le hk) (.eqRefl _)).eqTrans (one_mul _)) (.eqRefl _)

/-- The sum may run past `i = k`. -/
theorem bi_ext {k N : PTm n} (h : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] ap2 (sumF biB) (succ N) k ≐ ap2 (sumF biB) (succ k) k := by
  have eD : Γ ⊢[PRAAx] succ N ≐ succ k + monus N k := by
    ipra_lc natEq (eq_add_of_le h)
  refine (congrAp2 (sumF biB) eD (.eqRefl _)).eqTrans ((sum_split biB (succ k) (monus N k) k).eqTrans ?_)
  refine (congrAdd (.eqRefl _) ?_).eqTrans (add_zero _)
  refine (sum_congr_bounded (offB biB) zB (pairT (succ k) k) (pairT (succ k) k) _ (.allI (.impI ?_))).eqTrans
    (zsum _ _)
  rw [shift_y, inst2_z, inst2_offB, inst2_bi, shift_succ]
  refine (congrMul (congrGb (snd_pair _ _) (congrAdd (fst_pair _ _) (.eqRefl _))) (.eqRefl _)).eqTrans ?_
  exact (congrMul (gb_above (le_add_right _ _)) (.eqRefl _)).eqTrans (zero_mul _)

/-- `a(k, i, ⟨N, j⟩) = C(N, k) j^{N−k} · C(k, i) B_i`. -/
abbrev a3 : PTm 3 := gb (fstT (var 2)) (var 0) * pw (sndT (var 2)) (monus (fstT (var 2)) (var 0)) *
  (gb (var 0) (var 1) * bell (var 1))

theorem inst3_a (k i x : PTm n) : inst3 a3 k i x =
    gb (fstT x) k * pw (sndT x) (monus (fstT x) k) * (gb k i * bell i) := by simp [inst3]

/-- The row `k`: `∑_{i ≤ N} C(N, k) j^{N−k} C(k, i) B_i = C(N, k) j^{N−k} B_{k+1}`. -/
theorem row_pt {k N j : PTm n} (hk : Γ ⊢[PRAAx] le k N) :
    Γ ⊢[PRAAx] inst2 (oB a3) k (pairT (succ N) (pairT N j)) ≐ inst2 tB k (pairT N j) := by
  rw [inst2_oB]
  refine (congrAp2 (sumF (rowB a3)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  have sc : Γ ⊢[PRAAx] ap2 (sumF (rowB a3)) (succ N) (pairT k (pairT N j)) ≐
      (gb N k * pw j (monus N k)) * ap2 (sumF biB) (succ N) k := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    have e : Syn.shift (gb N k * pw j (monus N k)) = gb (Syn.shift N) (Syn.shift k) * pw (Syn.shift j)
        (monus (Syn.shift N) (Syn.shift k)) := by simp [Syn.shift]
    simp only [shift_y]
    rw [e, inst2_rowB, inst3_a, inst2_bi]
    have f := fst_pair (Γ := (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift)) (Syn.shift k)
      (pairT (Syn.shift N) (Syn.shift j))
    have s := snd_pair (Γ := (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift)) (Syn.shift k)
      (pairT (Syn.shift N) (Syn.shift j))
    have fN := (congrFst s).eqTrans (fst_pair _ _); have sJ := (congrSnd s).eqTrans (snd_pair _ _)
    exact congrMul (congrMul (congrGb fN f) (congrPw sJ (congrMonus fN f))) (congrMul (congrGb f (.eqRefl _)) (.eqRefl _))
  exact sc.eqTrans ((congrMul (.eqRefl _) ((bi_ext hk).eqTrans (bi_bell k))).eqTrans (t_at _ _ _).eqSymm)

/-- The column `i`: `∑_{k ≤ N} C(N, k) j^{N−k} C(k, i) B_i = C(N, i) (j + 1)^{N−i} B_i`. -/
theorem col_pt (i N j : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB a3) i (pairT (succ N) (pairT N j)) ≐ inst2 gB i (pairT N (succ j)) := by
  rw [inst2_pB]
  refine (congrAp2 (sumF (colB a3)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans ?_
  have sc : Γ ⊢[PRAAx] ap2 (sumF (colB a3)) (succ N) (pairT i (pairT N j)) ≐ bell i * CV N i j := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    have e : Syn.shift (bell i) = bell (Syn.shift i) := by simp [Syn.shift]
    simp only [shift_y]
    rw [e, inst2_colB, inst3_a]
    have f := fst_pair (Γ := (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift)) (Syn.shift i)
      (pairT (Syn.shift N) (Syn.shift j))
    have s := snd_pair (Γ := (lt (var 0) (Syn.shift (succ N)) :: Γ.map Fm.shift)) (Syn.shift i)
      (pairT (Syn.shift N) (Syn.shift j))
    have fN := (congrFst s).eqTrans (fst_pair _ _); have sJ := (congrSnd s).eqTrans (snd_pair _ _)
    refine (congrMul (congrMul (congrGb fN (.eqRefl _)) (congrPw sJ (congrMonus fN (.eqRefl _))))
      (congrMul (congrGb (.eqRefl _) f) (congrBell f))).eqTrans ?_
    refine .eqTrans ?_ (congrMul (.eqRefl _) (cv_at _ _ _ _)).eqSymm
    ipra_ring
  refine sc.eqTrans ((congrMul (.eqRefl _) (conv_inner N i j)).eqTrans ?_)
  refine .eqTrans ?_ (g_at _ _ _).eqSymm
  ipra_ring

/-- `∑_{k ≤ n} C(n, k) j^{n−k} B_{k+1} = G(n, j + 1)`. -/
theorem G_shift (N j : PTm n) : Γ ⊢[PRAAx] T N j ≐ G N (succ j) := by
  have e : Syn.shift (pairT (succ N) (pairT N j)) = pairT (succ (Syn.shift N)) (pairT (Syn.shift N) (Syn.shift j)) := by
    simp [Syn.shift]
  have h₁ : Γ ⊢[PRAAx] T N j ≐ ap2 (sumF (oB a3)) (succ N) (pairT (succ N) (pairT N j)) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [shift_y, e, shift_succ]
    exact (row_pt (le_of_lt_succ Prf.hyp0)).eqSymm
  have h₂ : Γ ⊢[PRAAx] ap2 (sumF (pB a3)) (succ N) (pairT (succ N) (pairT N j)) ≐ G N (succ j) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [e, shift_y, shift_succ]
    exact col_pt _ _ _
  exact h₁.eqTrans ((fubini a3 _ _ _).eqTrans h₂)

/-! ## `G(n + 1, j) = j G(n, j) + G(n, j + 1)` -/

/-- `C(N, k + 1) j^{N−k} B_{k+1}`, over `0 = k`, `1 = ⟨N, j⟩`. -/
abbrev hB : PTm 2 := gb (fstT (var 1)) (succ (var 0)) * pw (sndT (var 1)) (monus (fstT (var 1)) (var 0)) *
  bell (succ (var 0))

theorem h_at (k N j : PTm n) :
    Γ ⊢[PRAAx] inst2 hB k (pairT N j) ≐ gb N (succ k) * pw j (monus N k) * bell (succ k) := by
  have h : inst2 hB k (pairT N j) = gb (fstT (pairT N j)) (succ k) * pw (sndT (pairT N j)) (monus (fstT (pairT N j)) k) *
      bell (succ k) := by simp [inst2]
  rw [h]
  exact congrMul (congrMul (congrGb (fst_pair _ _) (.eqRefl _)) (congrPw (snd_pair _ _) (congrMonus (fst_pair _ _) (.eqRefl _))))
    (.eqRefl _)

theorem gpas (k N j : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody gB) k (pairT (succ N) j) ≐ inst2 (addBody hB tB) k (pairT N j) := by
  rw [inst2_shiftBody, inst2_addBody]
  refine (g_at _ _ _).eqTrans (.eqTrans ?_ (congrAdd (h_at _ _ _) (t_at _ _ _)).eqSymm)
  refine (congrMul (congrMul (gb_pascal _ _) (congrPw (.eqRefl _) (succ_monus_succ _ _))) (.eqRefl _)).eqTrans ?_
  ipra_ring

/-- `C(N, k + 1) j^{N−k} B_{k+1} = j · C(N, k + 1) j^{N−k−1} B_{k+1}`. -/
theorem hpt (k N j : PTm n) : Γ ⊢[PRAAx] inst2 hB k (pairT N j) ≐ j * inst2 (shiftBody gB) k (pairT N j) := by
  rw [inst2_shiftBody]
  refine (h_at _ _ _).eqTrans (.eqTrans ?_ (congrMul (.eqRefl _) (g_at _ _ _)).eqSymm)
  refine .orE (lt_or_le k N) ?_ ?_
  · have hl : (lt k N :: Γ) ⊢[PRAAx] lt k N := Prf.hyp0
    have e₀ : (lt k N :: Γ) ⊢[PRAAx] N ≐ succ (monus N (succ k)) + k := by
      ipra_lc natEq (eq_add_of_le hl)
    have e : (lt k N :: Γ) ⊢[PRAAx] monus N k ≐ succ (monus N (succ k)) :=
      (congrMonus e₀ (.eqRefl _)).eqTrans (add_monus _ _)
    refine (congrMul (congrMul (.eqRefl _) ((congrPw (.eqRefl _) e).eqTrans (pw_succ _ _))) (.eqRefl _)).eqTrans ?_
    ipra_ring
  · have z : (le N k :: Γ) ⊢[PRAAx] gb N (succ k) ≐ zero := gb_above ((succ_monus_succ _ _).eqTrans Prf.hyp0)
    refine ((congrMul (congrMul z (.eqRefl _)) (.eqRefl _)).eqTrans ?_).eqTrans
      (congrMul (.eqRefl _) (congrMul (congrMul z (.eqRefl _)) (.eqRefl _))).eqSymm
    exact (congrMul (zero_mul _) (.eqRefl _)).eqTrans ((zero_mul _).eqTrans
      ((mul_zero _).eqSymm.eqTrans (congrMul (.eqRefl _) ((congrMul (zero_mul _) (.eqRefl _)).eqTrans (zero_mul _)).eqSymm)))

theorem g_zero_term (N j : PTm n) : Γ ⊢[PRAAx] inst2 gB zero (pairT N j) ≐ pw j N :=
  (g_at _ _ _).eqTrans ((congrMul ((congrMul (gb_zero N) (congrPw (.eqRefl _) (monus_zero N))).eqTrans (one_mul _))
    bell_zero).eqTrans ((mul_comm _ _).eqTrans (one_mul _)))

/-- `G(N, j) = j^N + ∑_{k ≤ N} C(N, k + 1) j^{N−k−1} B_{k+1}`. -/
theorem G_split (N j : PTm n) :
    Γ ⊢[PRAAx] G N j ≐ pw j N + ap2 (sumF (shiftBody gB)) (succ N) (pairT N j) := by
  have ext : Γ ⊢[PRAAx] ap2 (sumF gB) (succ (succ N)) (pairT N j) ≐ G N j := by
    refine (sum_succ' gB (succ N) (pairT N j)).eqTrans ?_
    refine (congrAdd (.eqRefl _) ((g_at _ _ _).eqTrans ?_)).eqTrans (add_zero _)
    exact (congrMul ((congrMul (gb_above (le_refl (succ N))) (.eqRefl _)).eqTrans (zero_mul _)) (.eqRefl _)).eqTrans
      (zero_mul _)
  exact ext.eqSymm.eqTrans ((sum_shift gB (succ N) (pairT N j)).eqTrans (congrAdd (g_zero_term N j) (.eqRefl _)))

/-- `G(n + 1, j) = j G(n, j) + G(n, j + 1)`. -/
theorem G_succ (N j : PTm n) : Γ ⊢[PRAAx] G (succ N) j ≐ j * G N j + G N (succ j) := by
  have s₁ := (sum_shift gB (succ N) (pairT (succ N) j) : Γ ⊢[PRAAx] _)
  have hs : Γ ⊢[PRAAx] ap2 (sumF (shiftBody gB)) (succ N) (pairT (succ N) j) ≐
      ap2 (sumF (addBody hB tB)) (succ N) (pairT N j) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_y, shift_succ]
    exact gpas _ _ _
  have hh : Γ ⊢[PRAAx] ap2 (sumF hB) (succ N) (pairT N j) ≐ j * ap2 (sumF (shiftBody gB)) (succ N) (pairT N j) := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_y]
    exact hpt _ _ _
  ipra_lc natEq s₁ + natEq (g_zero_term (Γ := Γ) (succ N) j) + natEq (hs.eqTrans (sum_add _ _ _ _)) + natEq hh -
    𝔞 j * natEq (G_split (Γ := Γ) N j) + natEq (G_shift (Γ := Γ) N j) + natEq (pw_succ (Γ := Γ) j N)

theorem G_zero (N : PTm n) : Γ ⊢[PRAAx] G N zero ≐ bell N := by
  refine (sum_succ' gB N (pairT N zero)).eqTrans ?_
  have z : Γ ⊢[PRAAx] ap2 (sumF gB) N (pairT N zero) ≐ zero := by
    refine (sum_congr_bounded gB zB (pairT N zero) (pairT N zero) N (.allI (.impI ?_))).eqTrans (zsum _ _)
    have ez : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
    simp only [shift_y, ez]
    rw [inst2_z]
    have hl : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx] lt (var 0) (Syn.shift N) := Prf.hyp0
    have e₀ : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
        Syn.shift N ≐ succ (monus (Syn.shift N) (succ (var 0))) + var 0 := by
      ipra_lc natEq (eq_add_of_le hl)
    have e : (lt (var 0) (Syn.shift N) :: Γ.map Fm.shift) ⊢[PRAAx]
        monus (Syn.shift N) (var 0) ≐ succ (monus (Syn.shift N) (succ (var 0))) :=
      (congrMonus e₀ (.eqRefl _)).eqTrans (add_monus _ _)
    refine (g_at _ _ _).eqTrans ?_
    refine (congrMul (congrMul (.eqRefl _) ((congrPw (.eqRefl _) e).eqTrans ((pw_succ _ _).eqTrans (mul_zero _))))
      (.eqRefl _)).eqTrans ?_
    exact (congrMul (mul_zero _) (.eqRefl _)).eqTrans (zero_mul _)
  refine (congrAdd z ((g_at _ _ _).eqTrans ?_)).eqTrans (zero_add _)
  refine (congrMul ((congrMul (gb_self N) (congrPw (.eqRefl _) (monus_self N))).eqTrans ((congrMul (.eqRefl _)
    (pw_zero _)).eqTrans (one_mul _))) (.eqRefl _)).eqTrans (one_mul _)

/-! ## `F(n, m) = ∑_{j ≤ m} S(m, j) G(n, j)` -/

/-- `G(N, J)` read from `y = ⟨m, N⟩`. -/
abbrev GyT (J : PTm 2) : PTm 2 := ap2 (sumF gB) (succ (sndT (var 1))) (pairT (sndT (var 1)) J)

/-- Over `0 = j`, `1 = ⟨m, N⟩`. -/
abbrev fB : PTm 2 := stir (fstT (var 1)) (var 0) * GyT (var 0)
abbrev u1B : PTm 2 := succ (var 0) * stir (fstT (var 1)) (succ (var 0)) * GyT (succ (var 0))
abbrev u2B : PTm 2 := stir (fstT (var 1)) (var 0) * GyT (succ (var 0))
abbrev u3B : PTm 2 := stir (fstT (var 1)) (var 0) * (var 0 * GyT (var 0))

abbrev F {n : ℕ} (N m : PTm n) : PTm n := ap2 (sumF fB) (succ m) (pairT m N)

theorem gy (m N J : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF gB) (succ (sndT (pairT m N))) (pairT (sndT (pairT m N)) J) ≐ G N J :=
  congrAp2 (sumF gB) (congrSucc (snd_pair _ _)) (congrPairT (snd_pair _ _) (.eqRefl _))

theorem f_at (j m N : PTm n) : Γ ⊢[PRAAx] inst2 fB j (pairT m N) ≐ stir m j * G N j := by
  have h : inst2 fB j (pairT m N) = stir (fstT (pairT m N)) j *
      ap2 (sumF gB) (succ (sndT (pairT m N))) (pairT (sndT (pairT m N)) j) := by simp [inst2]
  rw [h]; exact congrMul (congrStir (fst_pair _ _) (.eqRefl _)) (gy _ _ _)

theorem u1_at (j m N : PTm n) :
    Γ ⊢[PRAAx] inst2 u1B j (pairT m N) ≐ succ j * stir m (succ j) * G N (succ j) := by
  have h : inst2 u1B j (pairT m N) = succ j * stir (fstT (pairT m N)) (succ j) *
      ap2 (sumF gB) (succ (sndT (pairT m N))) (pairT (sndT (pairT m N)) (succ j)) := by simp [inst2]
  rw [h]; exact congrMul (congrMul (.eqRefl _) (congrStir (fst_pair _ _) (.eqRefl _))) (gy _ _ _)

theorem u2_at (j m N : PTm n) : Γ ⊢[PRAAx] inst2 u2B j (pairT m N) ≐ stir m j * G N (succ j) := by
  have h : inst2 u2B j (pairT m N) = stir (fstT (pairT m N)) j *
      ap2 (sumF gB) (succ (sndT (pairT m N))) (pairT (sndT (pairT m N)) (succ j)) := by simp [inst2]
  rw [h]; exact congrMul (congrStir (fst_pair _ _) (.eqRefl _)) (gy _ _ _)

theorem u3_at (j m N : PTm n) : Γ ⊢[PRAAx] inst2 u3B j (pairT m N) ≐ stir m j * (j * G N j) := by
  have h : inst2 u3B j (pairT m N) = stir (fstT (pairT m N)) j *
      (j * ap2 (sumF gB) (succ (sndT (pairT m N))) (pairT (sndT (pairT m N)) j)) := by simp [inst2]
  rw [h]; exact congrMul (congrStir (fst_pair _ _) (.eqRefl _)) (congrMul (.eqRefl _) (gy _ _ _))

/-- The left side: `S(m + 1, j + 1) G(N, j + 1) = (j + 1) S(m, j + 1) G(N, j + 1) + S(m, j) G(N, j + 1)`. -/
theorem lpt (j m N : PTm n) :
    Γ ⊢[PRAAx] inst2 (shiftBody fB) j (pairT (succ m) N) ≐ inst2 (addBody u1B u2B) j (pairT m N) := by
  rw [inst2_shiftBody, inst2_addBody]
  refine (f_at _ _ _).eqTrans (.eqTrans ?_ (congrAdd (u1_at _ _ _) (u2_at _ _ _)).eqSymm)
  refine (congrMul (stir_rec _ _) (.eqRefl _)).eqTrans ?_
  ipra_ring

/-- The right side: `S(m, j) G(N + 1, j) = S(m, j) (j G(N, j)) + S(m, j) G(N, j + 1)`. -/
theorem rpt (j m N : PTm n) :
    Γ ⊢[PRAAx] inst2 fB j (pairT m (succ N)) ≐ inst2 (addBody u3B u2B) j (pairT m N) := by
  rw [inst2_addBody]
  refine (f_at _ _ _).eqTrans (.eqTrans ?_ (congrAdd (u3_at _ _ _) (u2_at _ _ _)).eqSymm)
  refine (congrMul (.eqRefl _) (G_succ _ _)).eqTrans ?_
  ipra_ring

/-- `∑_{j ≤ m} S(m, j) j G(N, j) = ∑_{j ≤ m} (j + 1) S(m, j + 1) G(N, j + 1)`. -/
theorem u31 (m N : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF u3B) (succ m) (pairT m N) ≐ ap2 (sumF u1B) (succ m) (pairT m N) := by
  have ext : Γ ⊢[PRAAx] ap2 (sumF u3B) (succ (succ m)) (pairT m N) ≐ ap2 (sumF u3B) (succ m) (pairT m N) := by
    refine (sum_succ' _ _ _).eqTrans ((congrAdd (.eqRefl _) ((u3_at _ _ _).eqTrans ?_)).eqTrans (add_zero _))
    exact (congrMul (stir_above (le_refl _)) (.eqRefl _)).eqTrans (zero_mul _)
  have z : Γ ⊢[PRAAx] inst2 u3B zero (pairT m N) ≐ zero :=
    (u3_at _ _ _).eqTrans ((congrMul (.eqRefl _) (zero_mul _)).eqTrans (mul_zero _))
  have sh : Γ ⊢[PRAAx] ap2 (sumF (shiftBody u3B)) (succ m) (pairT m N) ≐ ap2 (sumF u1B) (succ m) (pairT m N) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_y]
    rw [inst2_shiftBody]
    refine (u3_at _ _ _).eqTrans (.eqTrans ?_ (u1_at _ _ _).eqSymm)
    ipra_ring
  exact ext.eqSymm.eqTrans ((sum_shift _ _ _).eqTrans ((congrAdd z sh).eqTrans (zero_add _)))

/-- `F(N, m + 1) = F(N + 1, m)`. -/
theorem F_succ (N m : PTm n) : Γ ⊢[PRAAx] F N (succ m) ≐ F (succ N) m := by
  have s := sum_shift (Γ := Γ) fB (succ m) (pairT (succ m) N)
  have z : Γ ⊢[PRAAx] inst2 fB zero (pairT (succ m) N) ≐ zero :=
    (f_at _ _ _).eqTrans ((congrMul (stir_succ_zero _) (.eqRefl _)).eqTrans (zero_mul _))
  have hl : Γ ⊢[PRAAx] ap2 (sumF (shiftBody fB)) (succ m) (pairT (succ m) N) ≐
      ap2 (sumF (addBody u1B u2B)) (succ m) (pairT m N) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_y, shift_succ]
    exact lpt _ _ _
  have hr : Γ ⊢[PRAAx] F (succ N) m ≐ ap2 (sumF (addBody u3B u2B)) (succ m) (pairT m N) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [shift_y, shift_succ]
    exact rpt _ _ _
  refine s.eqTrans ((congrAdd z (hl.eqTrans (sum_add _ _ _ _))).eqTrans ?_)
  refine (zero_add _).eqTrans (.eqTrans ?_ (hr.eqTrans (sum_add _ _ _ _)).eqSymm)
  exact congrAdd (u31 m N).eqSymm (.eqRefl _)

theorem F_zero (N : PTm n) : Γ ⊢[PRAAx] F N zero ≐ bell (N + zero) := by
  refine (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (f_at _ _ _)).eqTrans ((zero_add _).eqTrans ?_))
  exact (congrMul stir_zero (G_zero N)).eqTrans ((one_mul _).eqTrans (congrBell (add_zero N)).eqSymm)

/-! ## The induction -/

/-- `1 ∸ [F(N, m) = B_{N+m}]`, over `0 = N`, `1 = m`. -/
abbrev vB : PTm 2 := monus one (eqb (F (var 0) (var 1)) (bell (var 0 + var 1)))

theorem inst2_v (N m : PTm n) : inst2 vB N m = monus one (eqb (F N m) (bell (N + m))) := by simp [inst2]

theorem psi_base (M : PTm n) : Γ ⊢[PRAAx] ap2 (sumF vB) (monus M zero) zero ≐ zero := by
  refine sum_zero_of_all vB zero (.allI ?_) _
  have ez : Syn.shift (zero : PTm n) = zero := by simp [Syn.shift]
  rw [ez, inst2_v]
  exact viol_of_eq (F_zero _)

theorem step_pt {M m j : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF vB) (monus M m) m ≐ zero)
    (hj : Γ ⊢[PRAAx] lt j (monus M (succ m))) :
    Γ ⊢[PRAAx] monus one (eqb (F j (succ m)) (bell (j + succ m))) ≐ zero := by
  have v := sum_zero_elim vB ih (lt_shift hj)
  rw [inst2_v] at v
  exact viol_of_eq ((F_succ j m).eqTrans ((eq_of_viol v).eqTrans (congrBell (by ipra_ring))))

theorem psi_step {M m : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF vB) (monus M m) m ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF vB) (monus M (succ m)) (succ m) ≐ zero := by
  refine (sum_congr_bounded vB zB (succ m) (succ m) (monus M (succ m)) (.allI (.impI ?_))).eqTrans (zsum _ _)
  have e₃ : Syn.shift (monus M (succ m)) = monus (Syn.shift M) (succ (Syn.shift m)) := by simp [Syn.shift]
  rw [inst2_z, inst2_v, shift_succ, e₃]
  have ih' : Γ.map Fm.shift ⊢[PRAAx] ap2 (sumF vB) (monus (Syn.shift M) (Syn.shift m)) (Syn.shift m) ≐ zero := by
    simpa [Fm.shift, Syn.shift] using ih.shift
  exact step_pt ih'.wk Prf.hyp0

/-- Variables: `0 = m`, `1 = M`. -/
private abbrev psiF : Fm PTm 2 := ap2 (sumF vB) (monus (var 1) (var 0)) (var 0) ≐ zero

private theorem psi₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] psiF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_monus, Syn.subst_var, Syn.inst_zero, Syn.inst_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact psi_base _
  · simp only [Fm.subst_eq, subst_ap2, PTm.subst_monus, Syn.subst_var, Syn.repl_zero, repl_one,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact psi_step Prf.hyp0

/-- `eq:spivey`: `B_{n+m} = ∑_{j ≤ m} S(m, j) ∑_{k ≤ n} C(n, k) j^{n−k} B_k`. -/
theorem spivey (N m : PTm n) : Γ ⊢[PRAAx] F N m ≐ bell (N + m) := by
  have h := inst (Γ := Γ) psi₀ (![m, succ (N + m)] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, PTm.subst_monus, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_zero] at h
  have e : Γ ⊢[PRAAx] monus (succ (N + m)) m ≐ succ N :=
    (congrMonus (by ipra_ring : Γ ⊢[PRAAx] succ (N + m) ≐ succ N + m) (.eqRefl _)).eqTrans (add_monus _ _)
  have v := sum_zero_elim vB h (le_congr (.eqRefl _) e.eqSymm (le_refl (succ N)))
  rw [inst2_v] at v
  exact eq_of_viol v

/-! ## The product bound -/

/-- `S(m, j) B_N`, over `0 = j`, `1 = ⟨m, N⟩`. -/
abbrev lB : PTm 2 := stir (fstT (var 1)) (var 0) * bell (sndT (var 1))

theorem G_ge (N j : PTm n) : Γ ⊢[PRAAx] le (bell N) (G N j) := by
  have t := term_le_sum (Γ := Γ) gB (i := N) (x := pairT N j) ((succ_monus_succ _ _).eqTrans (le_refl N))
  refine le_congr ((g_at _ _ _).eqTrans ?_) (.eqRefl _) t
  exact (congrMul ((congrMul (gb_self N) (congrPw (.eqRefl _) (monus_self N))).eqTrans ((congrMul (.eqRefl _)
    (pw_zero _)).eqTrans (one_mul _))) (.eqRefl _)).eqTrans (one_mul _)

/-- The lower bound of `eq:bell-product-bounds`: `B_m B_n ≤ B_{m+n}`. -/
theorem bell_product (m N : PTm n) : Γ ⊢[PRAAx] le (bell m * bell N) (bell (m + N)) := by
  have hle : Γ ⊢[PRAAx] le (ap2 (sumF lB) (succ m) (pairT m N)) (F N m) := by
    refine sum_le _ _ _ _ (.allI (.impI ?_))
    simp only [shift_y]
    have h : inst2 lB (var 0) (pairT (Syn.shift m) (Syn.shift N)) = stir (fstT (pairT (Syn.shift m) (Syn.shift N))) (var 0) *
        bell (sndT (pairT (Syn.shift m) (Syn.shift N))) := by simp [inst2]
    rw [h]
    refine le_congr (congrMul (congrStir (fst_pair _ _) (.eqRefl _)) (congrBell (snd_pair _ _))).eqSymm
      (f_at _ _ _).eqSymm ?_
    exact LeanProofs.IPRA.AnalyticNumberTheory.PhiLower.le_mul_mono (le_refl _) (G_ge _ _)
  have hs : Γ ⊢[PRAAx] ap2 (sumF lB) (succ m) (pairT m N) ≐ bell N * ap2 (sumF LeanProofs.IPRA.Combinatorics.BellStirling.tB) (succ m) m := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    have e : Syn.shift (bell N) = bell (Syn.shift N) := by simp [Syn.shift]
    simp only [shift_y]
    rw [e]
    have h : inst2 lB (var 0) (pairT (Syn.shift m) (Syn.shift N)) = stir (fstT (pairT (Syn.shift m) (Syn.shift N))) (var 0) *
        bell (sndT (pairT (Syn.shift m) (Syn.shift N))) := by simp [inst2]
    rw [h, LeanProofs.IPRA.Combinatorics.BellStirling.inst2_t]
    exact (congrMul (congrStir (fst_pair _ _) (.eqRefl _)) (congrBell (snd_pair _ _))).eqTrans (mul_comm _ _)
  have hb := (hs.eqTrans ((congrMul (.eqRefl _) (LeanProofs.IPRA.Combinatorics.BellStirling.bell_stirling m)).eqTrans (mul_comm _ _)))
  exact le_congr hb ((spivey N m).eqTrans (congrBell (add_comm _ _))) hle

end LeanProofs.IPRA.Combinatorics.BellSpivey
