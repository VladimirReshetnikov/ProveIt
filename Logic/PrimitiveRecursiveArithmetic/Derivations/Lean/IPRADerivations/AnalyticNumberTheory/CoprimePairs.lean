import IPRADerivations.Core.SquareLayers
import IPRADerivations.AnalyticNumberTheory.Totatives
import IPRADerivations.AnalyticNumberTheory.EulerProduct
import IPRADerivations.AnalyticNumberTheory.Mobius
import IPRADerivations.DiophantineNumberTheory.QuarticStep
import IPRADerivations.Core.LinearCombination

/-!
# Counting coprime pairs

Packet: `analytic-number-theory/von_mangoldt_totient_ipra_2026-11-15`, Theorem `thm:summatory-phi`,
the counting half: the number `C_N` of ordered pairs `(a, b)` with `1 ≤ a, b ≤ N` and
`gcd(a, b) = 1` satisfies `C_N = 2 ∑_{n ≤ N} φ(n) − 1`.

The square `[1, N]²` is cut into L-shaped layers (`Core/SquareLayers`). The layer at `b` holds the
pairs `(a, b)` and `(b, a)` with `a < b`, each counted by `φ(b)` once `b ≥ 2` (the term `a = 0` of
`φ(b)` vanishes), and the corner `(b, b)`, coprime only for `b = 1`:

* `cop_symm`: `[i, j ≥ 1][gcd(i, j) = 1]` is symmetric;
* `layer`: `L(b) + [b = 1] = 2 φ(b)` for every `b`;
* `coprime_pairs`: `C_N + 1 = 2 ∑_{b ≤ N} φ(b)` for `N ≥ 1`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.AnalyticNumberTheory.CoprimePairs

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.SquareLayers
open LeanProofs.IPRA.AnalyticNumberTheory.Totient (phi totBody)
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (phi_one eqb_comm')
open LeanProofs.IPRA.AnalyticNumberTheory.Mobius (congrSg zero_mul_l congrEqb' one_ne_zero' zero_ne_one')
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (gcd_comm_one eq_one_of_dvd_one gcd_dvd' gcd_greatest'
  dvd_self')
open LeanProofs.IPRA.DiophantineNumberTheory.QuarticStep (congrGcd)
open LeanProofs.IPRA.Foundations.ChineseRemainder (gcd_pos)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `[i, j ≥ 1][gcd(i, j) = 1]`, over `0 = i`, `1 = j`, `2 = x` (unused). -/
abbrev gB3 : PTm 3 := (sg (var 0) * sg (var 1)) * eqb (gcd (var 0) (var 1)) one

theorem inst3_g (i j x : PTm n) : inst3 gB3 i j x = (sg i * sg j) * eqb (gcd i j) one := by
  simp only [inst3, PTm.subst_mul, PTm.subst_monus, subst_eqb, subst_ex2, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero]

theorem cop_symm (i j : PTm n) :
    Γ ⊢[PRAAx] (sg i * sg j) * eqb (gcd i j) one ≐ (sg j * sg i) * eqb (gcd j i) one := by
  refine .orE (zero_or_succ i) ?_ ?_
  · have s : ((i ≐ zero) :: Γ) ⊢[PRAAx] sg i ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
    exact (zero_mul_l (zero_mul_l s _) _).eqTrans
      ((congrMul ((congrMul (.eqRefl _) s).eqTrans (by ipra_ring)) (.eqRefl _)).eqTrans
        (zero_mul_l (.eqRefl _) _)).eqSymm
  · refine .orE (zero_or_succ j) ?_ ?_
    · have s : ((j ≐ zero) :: (i ≐ succ (pred i)) :: Γ) ⊢[PRAAx] sg j ≐ zero := (congrSg Prf.hyp0).eqTrans sg_zero
      exact ((congrMul ((congrMul (.eqRefl _) s).eqTrans (by ipra_ring)) (.eqRefl _)).eqTrans
        (zero_mul_l (.eqRefl _) _)).eqTrans (zero_mul_l (zero_mul_l s _) _).eqSymm
    · let C : List (Fm PTm n) := (j ≐ succ (pred j)) :: (i ≐ succ (pred i)) :: Γ
      have hj : C ⊢[PRAAx] j ≐ succ (pred j) := Prf.hyp0
      have hi : C ⊢[PRAAx] i ≐ succ (pred i) := Prf.hyp1
      have e : C ⊢[PRAAx] eqb (gcd i j) one ≐ eqb (gcd j i) one := by
        refine .orE (eq_or_ne (gcd i j) one) ?_ ?_
        · exact (eqb_of_eq Prf.hyp0).eqTrans (eqb_of_eq (gcd_comm_one hj.wk Prf.hyp0)).eqSymm
        · have ne : (neg (gcd i j ≐ one) :: C) ⊢[PRAAx] neg (gcd j i ≐ one) :=
            .impI (Prf.impE Prf.hyp1 (gcd_comm_one hi.wk.wk Prf.hyp0))
          exact (eqb_of_ne Prf.hyp0).eqTrans (eqb_of_ne ne).eqSymm
      exact congrMul (mul_comm _ _) e

/-! ## One layer -/

/-- `φ`, over `0 = b`. -/
abbrev PhiB : PTm 2 := ap2 (sumF totBody) (var 0) (var 0)

theorem inst2_Phi (b x : PTm n) : inst2 PhiB b x = phi b := by simp [inst2]

/-- `∑_{i<b} [i, b ≥ 1][gcd(i, b) = 1] + [gcd(0, b) = 1] = φ(b)` for `b ≥ 1`. -/
theorem col_phi {b x : PTm n} (hb : Γ ⊢[PRAAx] b ≐ succ (pred b)) :
    Γ ⊢[PRAAx] ap2 (sumF (colB gB3)) b (pairT b x) + eqb (gcd zero b) one ≐ phi b := by
  have sb : Γ ⊢[PRAAx] sg b ≐ one := (congrSg hb).eqTrans (sg_succ _)
  have c₁ := (congrAp2 (sumF (colB gB3)) hb (.eqRefl _)).eqTrans (sum_shift (colB gB3) (pred b) (pairT b x))
  have c₂ := (congrAp2 (sumF totBody) hb (.eqRefl b)).eqTrans (sum_shift totBody (pred b) b)
  have z₀ : Γ ⊢[PRAAx] inst2 (colB gB3) zero (pairT b x) ≐ zero := by
    rw [inst2_colB, inst3_g]
    exact zero_mul_l (zero_mul_l sg_zero _) _
  have t₀ : inst2 totBody zero b = eqb (gcd zero b) one := Totient.inst2_tot _ _
  have sh : Γ ⊢[PRAAx] ap2 (sumF (shiftBody (colB gB3))) (pred b) (pairT b x) ≐
      ap2 (sumF (shiftBody totBody)) (pred b) b := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_shiftBody, inst2_shiftBody, inst2_colB, inst3_g, shift_pairT]
    have t₁ : inst2 totBody (succ (var 0)) (Syn.shift b) = eqb (gcd (succ (var 0)) (Syn.shift b)) one :=
      Totient.inst2_tot _ _
    rw [t₁]
    have hb' : (Γ.map Fm.shift) ⊢[PRAAx] Syn.shift b ≐ succ (pred (Syn.shift b)) := by
      simpa [Fm.shift, Syn.shift] using hb.shift
    have sb' : (lt (var 0) (Syn.shift (pred b)) :: Γ.map Fm.shift) ⊢[PRAAx] sg (Syn.shift b) ≐ one :=
      (congrSg hb'.wk).eqTrans (sg_succ _)
    have f₁ := fst_pair (Γ := lt (var 0) (Syn.shift (pred b)) :: Γ.map Fm.shift) (Syn.shift b) (Syn.shift x)
    refine (congrMul (congrMul ((sg_succ _).eqTrans (.eqRefl _)) ((congrSg f₁).eqTrans sb'))
      (congrEqb' (congrGcd (.eqRefl _) f₁) (.eqRefl _))).eqTrans ?_
    ipra_ring
  have a := natEq c₁; have b' := natEq c₂; have z := natEq z₀; have s := natEq sh
  rw [t₀] at b'
  ipra_lc a - b' + z + s

/-- `[gcd(b, b) = 1] = [b = 1]`, in the form needed: zero for `b ≥ 2`, one for `b = 1`. -/
theorem gcd_self_two {b : PTm n} (hb : Γ ⊢[PRAAx] le two b) : Γ ⊢[PRAAx] eqb (gcd b b) one ≐ zero := by
  have hp : Γ ⊢[PRAAx] b ≐ succ (pred b) := Mobius.pos_of_two hb
  refine eqb_of_ne (.impI ?_)
  let C : List (Fm PTm n) := (gcd b b ≐ one) :: Γ
  have hp' : C ⊢[PRAAx] b ≐ succ (pred b) := hp.wk
  have d := gcd_greatest' hp' (dvd_self' hp') (dvd_self' hp')
  have e := eq_one_of_dvd_one hp' (dvd_congr Prf.hyp0 d)
  exact lt_irrefl one _ (le_congr (.eqRefl _) e hb.wk)

theorem gcd_one_one : Γ ⊢[PRAAx] eqb (gcd (one : PTm n) one) one ≐ one := by
  have h1 : Γ ⊢[PRAAx] (one : PTm n) ≐ succ (pred one) := congrSucc (pred_succ _).eqSymm
  exact eqb_of_eq (eq_one_of_dvd_one (gcd_pos h1) (Prf.andE₁ (gcd_dvd' (b := one) h1)))

/-- The layer at `b`: `L(b) + [b = 1] = 2 φ(b)`. -/
theorem layer (b x : PTm n) :
    Γ ⊢[PRAAx] inst2 (LB gB3) b x + eqb b one ≐ two * phi b := by
  rw [inst2_LB, inst3_g]
  -- the row sum equals the column sum
  have rc : Γ ⊢[PRAAx] ap2 (sumF (rowB gB3)) b (pairT b x) ≐ ap2 (sumF (colB gB3)) b (pairT b x) := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    rw [inst2_rowB, inst2_colB, inst3_g, inst3_g]
    exact cop_symm _ _
  have r := natEq rc
  refine .orE (zero_or_succ b) ?_ ?_
  · let C : List (Fm PTm n) := (b ≐ zero) :: Γ
    have h0 : C ⊢[PRAAx] b ≐ zero := Prf.hyp0
    have c0 : C ⊢[PRAAx] ap2 (sumF (colB gB3)) b (pairT b x) ≐ zero :=
      (congrAp2 (sumF (colB gB3)) h0 (.eqRefl _)).eqTrans (sum_zero _ _)
    have p0 : C ⊢[PRAAx] phi b ≐ zero := (congrAp2 (sumF totBody) h0 h0).eqTrans (sum_zero _ _)
    have s0 : C ⊢[PRAAx] sg b ≐ zero := (congrSg h0).eqTrans sg_zero
    have q0 : C ⊢[PRAAx] eqb b one ≐ zero := (congrEqb' h0 (.eqRefl _)).eqTrans (eqb_of_ne zero_ne_one')
    have e₁ := natEq c0; have e₂ := natEq p0; have e₃ := natEq s0; have e₄ := natEq q0
    have r' := natEq (rc.wk : C ⊢[PRAAx] _)
    apply deriveNat; ipra_simps
    linear_combination 2 * e₁ + r' + e₄ - 2 * e₂ +
      (𝔞 (sg b) + 0) * 𝔞 (eqb (gcd b b) one) * e₃
  · let C : List (Fm PTm n) := (b ≐ succ (pred b)) :: Γ
    have hb : C ⊢[PRAAx] b ≐ succ (pred b) := Prf.hyp0
    have cp := natEq (col_phi (x := x) hb)
    have sb := natEq ((congrSg hb).eqTrans (sg_succ _) : C ⊢[PRAAx] sg b ≐ one)
    have r' := natEq (rc.wk : C ⊢[PRAAx] _)
    refine .orE (lt_or_le one b) ?_ ?_
    · let D : List (Fm PTm n) := lt one b :: C
      have h2 : D ⊢[PRAAx] le two b := Prf.hyp0
      have ez := natEq (Totatives.e_zero h2)
      have gs := natEq (gcd_self_two h2)
      have q := natEq (eqb_of_ne (.impI (lt_irrefl one _ (le_congr (.eqRefl _) Prf.hyp0 h2.wk))) :
        D ⊢[PRAAx] eqb b one ≐ zero)
      have cp' := natEq ((col_phi (x := x) hb).wk : D ⊢[PRAAx] _)
      have r'' := natEq (rc.wk.wk : D ⊢[PRAAx] _)
      have sb' := natEq (((congrSg hb).eqTrans (sg_succ _)).wk : D ⊢[PRAAx] sg b ≐ one)
      apply deriveNat; ipra_simps
      linear_combination 2 * cp' + r'' + q + 𝔞 (sg b) * 𝔞 (sg b) * gs - 2 * ez
    · let D : List (Fm PTm n) := le b one :: C
      have e1 : D ⊢[PRAAx] b ≐ one := le_antisymm Prf.hyp0 (LeanProofs.IPRA.DiophantineNumberTheory.Coprime.one_le_of_pos hb.wk)
      have c1 : D ⊢[PRAAx] ap2 (sumF (colB gB3)) b (pairT b x) ≐ zero := by
        refine (congrAp2 (sumF (colB gB3)) e1 (.eqRefl _)).eqTrans ((sum_succ' _ _ _).eqTrans ?_)
        rw [inst2_colB, inst3_g]
        exact (congrAdd (sum_zero _ _) (zero_mul_l (zero_mul_l sg_zero _) _)).eqTrans (add_zero _)
      have g1 := natEq ((congrEqb' (congrGcd e1 e1) (.eqRefl _)).eqTrans gcd_one_one : D ⊢[PRAAx] eqb (gcd b b) one ≐ one)
      have p1 := natEq ((congrAp2 (sumF totBody) e1 e1).eqTrans phi_one : D ⊢[PRAAx] phi b ≐ one)
      have q1 := natEq ((eqb_of_eq e1) : D ⊢[PRAAx] eqb b one ≐ one)
      have sb' := natEq (((congrSg hb).eqTrans (sg_succ _)).wk : D ⊢[PRAAx] sg b ≐ one)
      have r'' := natEq (rc.wk.wk : D ⊢[PRAAx] _)
      have e₁ := natEq c1
      apply deriveNat; ipra_simps
      linear_combination 2 * e₁ + r'' + q1 - 2 * p1 + 𝔞 (sg b) * 𝔞 (sg b) * g1 +
        (𝔞 (sg b) + 1) * sb'

/-- `thm:summatory-phi`, the counting half: `C_N + 1 = 2 ∑_{b ≤ N} φ(b)` for `N ≥ 1`, where
`C_N = ∑_{a, b ≤ N} [a, b ≥ 1][gcd(a, b) = 1]`. -/
theorem coprime_pairs {N : PTm n} (hN : Γ ⊢[PRAAx] N ≐ succ (pred N)) :
    Γ ⊢[PRAAx] Sq gB3 (succ N) zero + one ≐ two * ap2 (sumF PhiB) (succ N) zero := by
  have lay : Γ ⊢[PRAAx] ap2 (sumF (addBody (LB gB3) (eqb (var 0) one))) (succ N) zero ≐
      ap2 (sumF (two * PhiB)) (succ N) zero := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    have t₁ : inst2 (eqb (var 0) one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift zero) = eqb (var 0) one := by
      simp [inst2]
    have t₂ : inst2 (two * PhiB) (var 0 : PTm (n + 1)) (Syn.shift zero) = two * phi (var 0) := by simp [inst2]
    rw [inst2_addBody, t₁, t₂]
    exact layer _ _
  have sc : Γ ⊢[PRAAx] ap2 (sumF (two * PhiB)) (succ N) zero ≐ two * ap2 (sumF PhiB) (succ N) zero := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    have t₂ : inst2 (two * PhiB) (var 0 : PTm (n + 1)) (Syn.shift zero) = two * phi (var 0) := by simp [inst2]
    rw [t₂, inst2_Phi]
    have h2 : Syn.shift (two : PTm n) = two := by simp [Syn.shift]
    rw [h2]
    exact .eqRefl _
  have dl : Γ ⊢[PRAAx] ap2 (sumF (eqb (var 0) one)) (succ N) zero ≐ one := by
    refine (sum_congr_bounded (eqb (var 0) one) (dB (one : PTm 2)) zero (pairT one zero) (succ N)
      (.allI (.impI ?_))).eqTrans ((sum_delta (one : PTm 2) (x := zero) ?_).eqTrans ?_)
    · have t₁ : inst2 (eqb (var 0) one : PTm 2) (var 0 : PTm (n + 1)) (Syn.shift zero) = eqb (var 0) one := by
        simp [inst2]
      rw [t₁, inst2_dB, shift_pairT]
      have o : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (sndT (pairT (Syn.shift one) (Syn.shift zero))) = one := by
        simp [inst2]
      have h1 : Syn.shift (one : PTm n) = one := by simp [Syn.shift]
      rw [o, h1]
      exact (eqb_comm' _ _).eqTrans ((congrEqb' (fst_pair _ _).eqSymm (.eqRefl _)).eqTrans
        (by ipra_ring))
    · exact (succ_monus_succ _ _).eqTrans (LeanProofs.IPRA.DiophantineNumberTheory.Coprime.one_le_of_pos hN)
    · simp [inst2]; exact .eqRefl _
  ipra_lc natEq (square_layers (Γ := Γ) gB3 (succ N) zero) + natEq lay -
    natEq (sum_add (Γ := Γ) (LB gB3) (eqb (var 0) one) (succ N) zero) + natEq sc - natEq dl

end LeanProofs.IPRA.AnalyticNumberTheory.CoprimePairs
