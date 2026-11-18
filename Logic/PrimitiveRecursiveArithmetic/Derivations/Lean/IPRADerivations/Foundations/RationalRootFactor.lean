import IPRADerivations.Core.SumSplit
import IPRADerivations.Foundations.RationalRootConstant
import IPRADerivations.Foundations.EigenvalueBound
import IPRADerivations.DiophantineNumberTheory.FLTMultiples
import IPRADerivations.Combinatorics.BinomialIdentities

/-!
# Rational roots: removing the factor `T^e` (`ipra_presentations_to_witnesses`, `lem:norm-rational-roots`; `ipra_resources_and_elimination_2026-11-15`, `lem:elim-rational-roots`)

Packets: `foundations/ipra_presentations_to_witnesses`, lemma `lem:norm-rational-roots`: "Scan for
its first and last nonzero coefficients and write `h(T) = T^e (c_0 + c_1 T + ⋯ + c_d T^d)`,
`c_0 c_d ≠ 0`. ... Suppose `p ≠ 0`. Cancelling the nonzero factor `(p/q)^e` and multiplying by
`q^d` gives `c_0 q^d + c_1 p q^{d−1} + ⋯ + c_d p^d = 0` (RR2)"; and
`foundations/ipra_resources_and_elimination_2026-11-15`, lemma `lem:elim-rational-roots`:
"`P(T) = T^k Q(T)`, `Q(T) = a_0 + a_1 T + ⋯ + a_m T^m`, `a_0 a_m ≠ 0`".

`Foundations/RationalRootDegree`, `RationalRootConstant` and `RationalRootScan` treat the
cleared equation of a polynomial with nonzero constant coefficient. This module derives the
cancellation step, in their natural-number form (coefficients split by sign into two lists
`a`, `b`; `P a (n + 1) p q n x = Σ_{i ≤ n} a_i p^i q^{n ∸ i}`):

* `shC a`, `shC_at`: the shifted coefficient list, `(shC a)(j, ⟨e, x⟩) = a(e + j, x)`;
* `high_pt`, `low_pt`: the summands above the factor are `p^e` times the summands of the
  shifted polynomial, and the summands below it agree for `a` and `b`;
* `decompose`: `Σ_{i ≤ e + m} a_i p^i q^{e + m ∸ i} = Σ_{i < e} a_i p^i q^{e + m ∸ i}
    + p^e Σ_{j ≤ m} a_{e+j} p^j q^{m ∸ j}`;
* `factor_out`: if `a_i = b_i` for `i < e` (the coefficients below `T^e` vanish), `p ≠ 0`, and
  the cleared equation of degree `e + m` holds, then the cleared equation of degree `m` holds
  for the shifted lists: this is (RR2) for the cofactor of `T^e`.

After `factor_out` the constant coefficient of the shifted polynomial is `c_e`, and the bounds
and the scan of the other three modules apply whenever `c_e ≠ 0`. Not derived: the bounded
scans that find the first and last nonzero coefficient indices, and clearing the denominators
of a rational polynomial.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Foundations.RationalRootFactor

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.BinomialTheorem (congrPw)
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Foundations.RationalRootDegree (tB tB_at P)
open LeanProofs.IPRA.Foundations.EigenvalueBound (mB mB_at sum_scale)
open LeanProofs.IPRA.DiophantineNumberTheory.FLTMultiples (pw_pos)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {k : ℕ} {Γ : List (Fm PTm k)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem shift_pairT₁ (s t : PTm k) : Syn.shift (pairT s t) = pairT (Syn.shift s) (Syn.shift t) := by
  simp [Syn.shift]

theorem shift_pw₁ (s t : PTm k) : Syn.shift (pw s t) = pw (Syn.shift s) (Syn.shift t) := by
  simp [Syn.shift]

theorem shift_add₁ (s t : PTm k) : Syn.shift (s + t) = Syn.shift s + Syn.shift t := by
  simp [Syn.shift]

theorem shift_succ₁ (t : PTm k) : Syn.shift (succ t) = succ (Syn.shift t) := by
  simp [Syn.shift]

variable (a : PTm 2)

/-- The shifted coefficient list; variables `0 = j`, `1 = ⟨e, x⟩`. -/
def shC : PTm 2 := Syn.subst ![fstT (var 1) + var 0, sndT (var 1)] a

theorem shC_at (j e x : PTm k) :
    Γ ⊢[PRAAx] inst2 (shC a) j (pairT e x) ≐ inst2 a (e + j) x := by
  have h : inst2 (shC a) j (pairT e x) =
      inst2 a (fstT (pairT e x) + j) (sndT (pairT e x)) := by
    simp only [inst2, shC, Syn.subst_subst]
    congr 1; funext l; fin_cases l <;> simp
  rw [h]
  exact congrInst2 a (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

/-- A summand above the factor: `a_{e+j} p^{e+j} q^{(e+m) ∸ (e+j)} = p^e · a_{e+j} p^j q^{m ∸ j}`. -/
theorem high_pt (j p q e m x : PTm k) :
    Γ ⊢[PRAAx]
      inst2 (offB (tB a)) j (pairT e (pairT p (pairT q (pairT (e + m) x)))) ≐
        inst2 (mB (tB (shC a))) j
          (pairT (pw p e) (pairT p (pairT q (pairT m (pairT e x))))) := by
  rw [inst2_offB]
  have l₀ : Γ ⊢[PRAAx]
      inst2 (tB a) (fstT (pairT e (pairT p (pairT q (pairT (e + m) x)))) + j)
          (sndT (pairT e (pairT p (pairT q (pairT (e + m) x))))) ≐
        inst2 (tB a) (e + j) (pairT p (pairT q (pairT (e + m) x))) :=
    congrInst2 (tB a) (congrAdd (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)
  have e₁ := natEq (l₀.eqTrans (tB_at a (e + j) p q (e + m) x))
  have e₂ := natEq (mB_at (Γ := Γ) (tB (shC a)) j (pw p e)
    (pairT p (pairT q (pairT m (pairT e x)))))
  have e₃ := natEq (tB_at (Γ := Γ) (shC a) j p q m (pairT e x))
  have e₄ := natEq (shC_at (Γ := Γ) a j e x)
  have e₅ := natEq (pw_add (Γ := Γ) p e j)
  have e₆ := natEq (congrPw (Γ := Γ) (.eqRefl q)
    ((congrMonus (add_comm e m) (add_comm e j)).eqTrans (monus_add_add m j e)))
  apply deriveNat; ipra_simps
  linear_combination e₁ - e₂ +
    𝔞 (inst2 a (e + j) x) * 𝔞 (pw q (monus (e + m) (e + j))) * e₅ +
    𝔞 (inst2 a (e + j) x) * 𝔞 (pw p e) * 𝔞 (pw p j) * e₆ - 𝔞 (pw p e) * e₃ -
    𝔞 (pw p e) * 𝔞 (pw p j) * 𝔞 (pw q (monus m j)) * e₄

variable (b : PTm 2)

/-- Equal coefficients give equal summands. -/
theorem low_pt {i p q d x : PTm k} (h : Γ ⊢[PRAAx] inst2 a i x ≐ inst2 b i x) :
    Γ ⊢[PRAAx] inst2 (tB a) i (pairT p (pairT q (pairT d x))) ≐
      inst2 (tB b) i (pairT p (pairT q (pairT d x))) := by
  have e₁ := natEq (tB_at (Γ := Γ) a i p q d x)
  have e₂ := natEq (tB_at (Γ := Γ) b i p q d x)
  have e₃ := natEq h
  apply deriveNat; ipra_simps
  linear_combination e₁ - e₂ + 𝔞 (pw p i) * 𝔞 (pw q (monus d i)) * e₃

/-- The homogeneous sum, split at the factor `T^e`. -/
theorem decompose (p q e m x : PTm k) :
    Γ ⊢[PRAAx] P a (succ (e + m)) p q (e + m) x ≐
      ap2 (sumF (tB a)) e (pairT p (pairT q (pairT (e + m) x))) +
        pw p e * P (shC a) (succ m) p q m (pairT e x) := by
  have s₁ : Γ ⊢[PRAAx] P a (succ (e + m)) p q (e + m) x ≐
      ap2 (sumF (tB a)) (e + succ m) (pairT p (pairT q (pairT (e + m) x))) :=
    congrAp2 (sumF (tB a)) (add_succ e m).eqSymm (.eqRefl _)
  have s₂ := sum_split (Γ := Γ) (tB a) e (succ m) (pairT p (pairT q (pairT (e + m) x)))
  have s₃ : Γ ⊢[PRAAx]
      ap2 (sumF (offB (tB a))) (succ m) (pairT e (pairT p (pairT q (pairT (e + m) x)))) ≐
        ap2 (sumF (mB (tB (shC a)))) (succ m)
          (pairT (pw p e) (pairT p (pairT q (pairT m (pairT e x))))) := by
    refine sum_congr_bounded _ _ _ _ (succ m) (.allI (.impI ?_))
    simp only [shift_pairT₁, shift_pw₁, shift_add₁]
    exact high_pt a _ _ _ _ _ _
  have s₄ := sum_scale (Γ := Γ) (tB (shC a)) (succ m) (pw p e)
    (pairT p (pairT q (pairT m (pairT e x))))
  exact s₁.eqTrans (s₂.eqTrans (congrAdd (.eqRefl _) (s₃.eqTrans s₄)))

/-- `lem:norm-rational-roots`, cancelling `(p/q)^e`: the cleared equation of the cofactor of
`T^e`. -/
theorem factor_out {p' q e m x : PTm k}
    (hlow : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift e) ⟶
      (inst2 a (var 0) (Syn.shift x) ≐ inst2 b (var 0) (Syn.shift x))))
    (hE : Γ ⊢[PRAAx] P a (succ (e + m)) (succ p') q (e + m) x ≐
      P b (succ (e + m)) (succ p') q (e + m) x) :
    Γ ⊢[PRAAx] P (shC a) (succ m) (succ p') q m (pairT e x) ≐
      P (shC b) (succ m) (succ p') q m (pairT e x) := by
  have hl : Γ ⊢[PRAAx]
      ap2 (sumF (tB a)) e (pairT (succ p') (pairT q (pairT (e + m) x))) ≐
        ap2 (sumF (tB b)) e (pairT (succ p') (pairT q (pairT (e + m) x))) := by
    refine sum_congr_bounded _ _ _ _ e (.allI (.impI ?_))
    simp only [shift_pairT₁, shift_add₁, shift_succ₁]
    exact low_pt a b (.impE hlow.allOpen.wk Prf.hyp0)
  have da := natEq (decompose (Γ := Γ) a (succ p') q e m x)
  have db := natEq (decompose (Γ := Γ) b (succ p') q e m x)
  have el := natEq hl
  have eE := natEq hE
  refine mul_cancel (D := pw (succ p') e) (pw_pos p' e) ?_
  apply deriveNat; ipra_simps
  linear_combination eE - da + db - el

end LeanProofs.IPRA.Foundations.RationalRootFactor
