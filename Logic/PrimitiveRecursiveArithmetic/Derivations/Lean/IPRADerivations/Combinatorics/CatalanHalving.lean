import IPRADerivations.Combinatorics.CatalanSquares
import IPRADerivations.Core.SumPalindrome
import IPRADerivations.Combinatorics.CatalanConvolution

/-!
# The square sum, halved

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16` (theorem "Square sum", (2.20)): with
`d_k = C(n, k) − C(n, k − 1)`, the symmetry `d_{n+1−k} = −d_k` makes `∑_{k=0}^{n+1} d_k²` twice
`∑_{k ≤ ⌊n/2⌋} d_k²`, with a zero middle term when `n` is odd. Here `d_k²` is
`abs(C(n, k) − C(n, k − 1))²` (`Combinatorics/CatalanSquares`).

* `t_sym`: `d_{n+1−k}² = d_k²` for `k ≤ n + 1`;
* `t_full`: `∑_{k ≤ n+1} d_k² = 2 Cat_n`;
* `t_middle`: the middle term vanishes, `[n + 2 odd] · d_{⌊(n+2)/2⌋}² = 0`;
* `square_sum_half`: `∑_{k < ⌊n/2⌋ + 1} d_k² = Cat_n`, i.e. `Cat_n = ∑_{k ≤ ⌊n/2⌋} d_k²`.

The rewriting of `d_k` as `(n − 2k + 1)/(n − k + 1) · C(n, n − k)` is `Combinatorics/CatalanBallot`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanHalving

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial (binom)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.Stirling (sg sg_zero sg_succ)
open LeanProofs.IPRA.Combinatorics.Vandermonde (gb congrGb gb_zero gb_above)
open LeanProofs.IPRA.Combinatorics.CatalanNarayana (gb_symm)
open LeanProofs.IPRA.Combinatorics.CatalanSquares (inst2_d signed_square signed_square_zero)
open LeanProofs.IPRA.Combinatorics.CatalanConvolution (congrCat)
open LeanProofs.IPRA.Combinatorics.Catalan (cat succ_pos)
open LeanProofs.IPRA.Probability.Variance (ad)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- The body `abs(C(n, j + 1) − C(n, j))²` of `Combinatorics/CatalanSquares`. -/
abbrev sqD : PTm 2 := LeanProofs.IPRA.Combinatorics.CatalanSquares.dB

/-- `C(N, k − 1)`, zero at `k = 0`. -/
abbrev pv {n : ℕ} (N k : PTm n) : PTm n := sg k * gb N (pred k)

/-- `d_k² = abs(C(N, k) − C(N, k − 1))²`, over `0 = k`, `1 = N`. -/
abbrev tB : PTm 2 := ad (gb (var 1) (var 0)) (pv (var 1) (var 0)) * ad (gb (var 1) (var 0)) (pv (var 1) (var 0))

theorem inst2_t (k N : PTm n) :
    inst2 tB k N = ad (gb N k) (pv N k) * ad (gb N k) (pv N k) := by simp [inst2]

theorem congrAd {a a' b b' : PTm n} (ha : Γ ⊢[PRAAx] a ≐ a') (hb : Γ ⊢[PRAAx] b ≐ b') :
    Γ ⊢[PRAAx] ad a b ≐ ad a' b' := congrAdd (congrMonus ha hb) (congrMonus hb ha)

theorem ad_comm (a b : PTm n) : Γ ⊢[PRAAx] ad a b ≐ ad b a := add_comm _ _

theorem congrPv {N k k' : PTm n} (h : Γ ⊢[PRAAx] k ≐ k') : Γ ⊢[PRAAx] pv N k ≐ pv N k' :=
  congrMul (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) h)) (congrGb (.eqRefl _) (congrPred h))

theorem pv_zero (N : PTm n) : Γ ⊢[PRAAx] pv N zero ≐ zero := (congrMul sg_zero (.eqRefl _)).eqTrans (zero_mul _)

theorem pv_succ (N k : PTm n) : Γ ⊢[PRAAx] pv N (succ k) ≐ gb N k :=
  (congrMul (sg_succ k) (congrGb (.eqRefl _) (pred_succ k))).eqTrans (one_mul _)

/-! ## The full sum -/

theorem shift_pt (j N : PTm n) : Γ ⊢[PRAAx] inst2 (shiftBody tB) j N ≐ inst2 sqD j N := by
  rw [inst2_shiftBody, inst2_t, inst2_d]
  exact congrMul (congrAd (.eqRefl _) (pv_succ _ _)) (congrAd (.eqRefl _) (pv_succ _ _))

theorem t_zero (N : PTm n) : Γ ⊢[PRAAx] inst2 tB zero N ≐ one := by
  rw [inst2_t]
  have d : Γ ⊢[PRAAx] ad (gb N zero) (pv N zero) ≐ one :=
    (congrAd (gb_zero N) (pv_zero N)).eqTrans ((congrAdd (monus_zero _) (zero_monus _)).eqTrans (add_zero _))
  exact (congrMul d d).eqTrans (one_mul one)

theorem square_all (N : PTm n) : Γ ⊢[PRAAx] one + ap2 (sumF sqD) (succ N) N ≐ two * cat N := by
  refine .orE (zero_or_succ N) ?_ ?_
  · have e : ((N ≐ zero) :: Γ) ⊢[PRAAx] N ≐ zero := Prf.hyp0
    exact (congrAdd (.eqRefl _) (congrAp2 (sumF sqD) (congrSucc e) e)).eqTrans
      (signed_square_zero.eqTrans (congrMul (.eqRefl _) (congrCat e.eqSymm)))
  · have e : ((N ≐ succ (pred N)) :: Γ) ⊢[PRAAx] N ≐ succ (pred N) := Prf.hyp0
    exact (congrAdd (.eqRefl _) (congrAp2 (sumF sqD) (congrSucc e) e)).eqTrans
      ((signed_square _).eqTrans (congrMul (.eqRefl _) (congrCat e.eqSymm)))

/-- `∑_{k ≤ n+1} d_k² = 2 Cat_n`. -/
theorem t_full (N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF tB) (succ (succ N)) N ≐ two * cat N := by
  refine (sum_shift tB (succ N) N).eqTrans ((congrAdd (t_zero N) ?_).eqTrans (square_all N))
  exact sum_congr_bounded _ _ _ _ _ (.allI (.impI (shift_pt _ _)))

/-! ## The symmetry -/

theorem monus_succ_le {k N : PTm n} (h : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] monus (succ N) k ≐ succ (monus N k) := by
  have e := natEq (eq_add_of_le h)
  have a : Γ ⊢[PRAAx] succ N ≐ succ (monus N k) + k := by
    apply deriveNat; ipra_simps; linear_combination e
  exact (congrMonus a (.eqRefl _)).eqTrans (add_monus _ _)

/-- `C(N, N + 1 − k) = C(N, k − 1)` for `k ≤ N + 1`. -/
theorem gb_K {k N : PTm n} (hk : Γ ⊢[PRAAx] le k (succ N)) : Γ ⊢[PRAAx] gb N (monus (succ N) k) ≐ pv N k := by
  refine .orE (zero_or_succ k) ?_ ?_
  · have e : ((k ≐ zero) :: Γ) ⊢[PRAAx] k ≐ zero := Prf.hyp0
    refine (congrGb (.eqRefl _) ((congrMonus (.eqRefl _) e).eqTrans (monus_zero _))).eqTrans ?_
    exact (gb_above (le_refl _)).eqTrans ((pv_zero N).eqSymm.eqTrans (congrPv e.eqSymm))
  · have e : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] k ≐ succ (pred k) := Prf.hyp0
    have hk' : ((k ≐ succ (pred k)) :: Γ) ⊢[PRAAx] le (pred k) N :=
      (succ_monus_succ _ _).eqSymm.eqTrans ((congrMonus e.eqSymm (.eqRefl _)).eqTrans hk.wk)
    refine (congrGb (.eqRefl _) ((congrMonus (.eqRefl _) e).eqTrans (succ_monus_succ _ _))).eqTrans ?_
    refine (gb_symm hk').eqTrans ?_
    exact (pv_succ N (pred k)).eqSymm.eqTrans (congrPv e.eqSymm)

/-- `C(N, N − k) = C(N, k)` read as `pv N (N + 1 − k) = C(N, k)` for `k ≤ N + 1`. -/
theorem pv_K {k N : PTm n} (hk : Γ ⊢[PRAAx] le k (succ N)) : Γ ⊢[PRAAx] pv N (monus (succ N) k) ≐ gb N k := by
  refine .orE (lt_or_le k (succ N)) ?_ ?_
  · have h : (lt k (succ N) :: Γ) ⊢[PRAAx] le k N := (succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0
    exact (congrPv (monus_succ_le h)).eqTrans ((pv_succ _ _).eqTrans (gb_symm h))
  · have e : (le (succ N) k :: Γ) ⊢[PRAAx] k ≐ succ N := le_antisymm hk.wk Prf.hyp0
    have K : (le (succ N) k :: Γ) ⊢[PRAAx] monus (succ N) k ≐ zero :=
      (congrMonus (.eqRefl _) e).eqTrans (monus_self _)
    refine (congrPv K).eqTrans ?_
    exact (pv_zero N).eqTrans ((gb_above (le_congr (.eqRefl _) e.eqSymm (le_refl _))).eqSymm)

/-- `d_{n+1−k}² = d_k²` for `k ≤ n + 1`. -/
theorem t_sym {k N : PTm n} (hk : Γ ⊢[PRAAx] lt k (succ (succ N))) :
    Γ ⊢[PRAAx] inst2 tB (monus (succ (succ N)) (succ k)) N ≐ inst2 tB k N := by
  have hk' : Γ ⊢[PRAAx] le k (succ N) := (succ_monus_succ _ _).eqSymm.eqTrans hk
  rw [inst2_t, inst2_t]
  have K := succ_monus_succ (Γ := Γ) (succ N) k
  have a : Γ ⊢[PRAAx] ad (gb N (monus (succ (succ N)) (succ k))) (pv N (monus (succ (succ N)) (succ k))) ≐
      ad (gb N k) (pv N k) :=
    (congrAd (congrGb (.eqRefl _) K) (congrPv K)).eqTrans ((congrAd (gb_K hk') (pv_K hk')).eqTrans (ad_comm _ _))
  exact congrMul a a

/-! ## The middle term -/

theorem t_middle (N : PTm n) :
    Γ ⊢[PRAAx] par (succ (succ N)) * inst2 tB (half (succ (succ N))) N ≐ zero := by
  refine .orE (par_cases (succ (succ N))) ?_ ?_
  · exact (congrMul Prf.hyp0 (.eqRefl _)).eqTrans (zero_mul _)
  · have p : ((par (succ (succ N)) ≐ one) :: Γ) ⊢[PRAAx] par (succ (succ N)) ≐ one := Prf.hyp0
    refine (congrMul p (.eqRefl _)).eqTrans ((one_mul _).eqTrans ?_)
    refine .orE (zero_or_succ (half (succ (succ N)))) ?_ ?_
    · have z := natEq (Prf.hyp0 (Ax := PRAAx) (Γ := (par (succ (succ N)) ≐ one) :: Γ)
        (φ := half (succ (succ N)) ≐ zero))
      have hp := natEq (half_par (Γ := (half (succ (succ N)) ≐ zero) :: (par (succ (succ N)) ≐ one) :: Γ) (succ (succ N)))
      have pp := natEq (p.wk (ψ := half (succ (succ N)) ≐ zero))
      have bad : ((half (succ (succ N)) ≐ zero) :: (par (succ (succ N)) ≐ one) :: Γ) ⊢[PRAAx] succ N ≐ zero := by
        apply deriveNat; ipra_simps; linear_combination hp + pp + 2 * z
      exact succ_ne_zero' _ bad
    · have hp := natEq (half_par (Γ := (half (succ (succ N)) ≐ succ (pred (half (succ (succ N))))) ::
        (par (succ (succ N)) ≐ one) :: Γ) (succ (succ N)))
      have pp := natEq (p.wk (ψ := half (succ (succ N)) ≐ succ (pred (half (succ (succ N))))))
      set h := half (succ (succ N))
      have eh : ((h ≐ succ (pred h)) :: (par (succ (succ N)) ≐ one) :: Γ) ⊢[PRAAx] h ≐ succ (pred h) := Prf.hyp0
      have ehn := natEq eh
      have eN : ((h ≐ succ (pred h)) :: (par (succ (succ N)) ≐ one) :: Γ) ⊢[PRAAx] N ≐ pred h + succ (pred h) := by
        apply deriveNat; ipra_simps; linear_combination hp + pp + 2 * ehn
      have l : ((h ≐ succ (pred h)) :: (par (succ (succ N)) ≐ one) :: Γ) ⊢[PRAAx] le (pred h) N :=
        le_of_eq_add eN
      have m : ((h ≐ succ (pred h)) :: (par (succ (succ N)) ≐ one) :: Γ) ⊢[PRAAx] monus N (pred h) ≐ h :=
        (congrMonus (eN.eqTrans (add_comm _ _)) (.eqRefl _)).eqTrans ((add_monus _ _).eqTrans eh.eqSymm)
      -- `C(N, h) = C(N, h − 1)`, so `d_h = 0`.
      have g : ((h ≐ succ (pred h)) :: (par (succ (succ N)) ≐ one) :: Γ) ⊢[PRAAx] gb N h ≐ pv N h :=
        (congrGb (.eqRefl _) m).eqSymm.eqTrans ((gb_symm l).eqTrans
          ((pv_succ N (pred h)).eqSymm.eqTrans (congrPv eh.eqSymm)))
      rw [inst2_t]
      have z : ((h ≐ succ (pred h)) :: (par (succ (succ N)) ≐ one) :: Γ) ⊢[PRAAx] ad (gb N h) (pv N h) ≐ zero :=
        (congrAd g (.eqRefl _)).eqTrans ((congrAdd (monus_self _) (monus_self _)).eqTrans (add_zero _))
      exact (congrMul z (.eqRefl _)).eqTrans (zero_mul _)

/-! ## The halved sum -/

/-- `Cat_n = ∑_{k < ⌊(n+2)/2⌋} d_k²`, i.e. `Cat_n = ∑_{k ≤ ⌊n/2⌋} d_k²`. -/
theorem square_sum_half (N : PTm n) : Γ ⊢[PRAAx] ap2 (sumF tB) (half (succ (succ N))) N ≐ cat N := by
  have hs : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift (succ (succ N))) ⟶
      (inst2 tB (monus (Syn.shift (succ (succ N))) (succ (var 0))) (Syn.shift N) ≐ inst2 tB (var 0) (Syn.shift N))) := by
    refine .allI (.impI ?_)
    have e : Syn.shift (succ (succ N)) = succ (succ (Syn.shift N)) := by simp [Syn.shift]
    rw [e]
    exact t_sym Prf.hyp0
  have P := natEq (sum_palindrome tB (succ (succ N)) N hs)
  have F := natEq (t_full (Γ := Γ) N)
  have M := natEq (t_middle (Γ := Γ) N)
  refine mul_cancel (D := two) (succ_pos _) ?_
  apply deriveNat; ipra_simps
  linear_combination -P + F - M

/-- `⌊(n+2)/2⌋ = ⌊n/2⌋ + 1`. -/
theorem half_succ_succ (N : PTm n) : Γ ⊢[PRAAx] half (succ (succ N)) ≐ succ (half N) := by
  refine .orE (par_cases N) ?_ ?_
  · have a := natEq (half_succ (Γ := (par N ≐ zero) :: Γ) (succ N))
    have b := natEq (half_succ (Γ := (par N ≐ zero) :: Γ) N)
    have c := natEq (par_succ (Γ := (par N ≐ zero) :: Γ) N)
    have p := natEq (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := par N ≐ zero))
    have q := natEq ((congrMonus (Γ := (par N ≐ zero) :: Γ) (.eqRefl one) Prf.hyp0).eqTrans (monus_zero one))
    apply deriveNat; ipra_simps; linear_combination a + b + c + p + q
  · have a := natEq (half_succ (Γ := (par N ≐ one) :: Γ) (succ N))
    have b := natEq (half_succ (Γ := (par N ≐ one) :: Γ) N)
    have c := natEq (par_succ (Γ := (par N ≐ one) :: Γ) N)
    have p := natEq (Prf.hyp0 (Ax := PRAAx) (Γ := Γ) (φ := par N ≐ one))
    have q := natEq ((congrMonus (Γ := (par N ≐ one) :: Γ) (.eqRefl one) Prf.hyp0).eqTrans (monus_self one))
    apply deriveNat; ipra_simps; linear_combination a + b + c + p + q

end LeanProofs.IPRA.Combinatorics.CatalanHalving
