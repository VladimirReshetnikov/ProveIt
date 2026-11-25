import IPRADerivations.Combinatorics.Catalan
import IPRADerivations.Core.SumReflect
import IPRADerivations.Probability.Independence
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.CommonLemmas

/-!
# The Segner convolution of the Catalan numbers

Packet: `combinatorics/catalan_numbers_ipra_2026-11-16` (`thm:segner`, (2.11)). The convolution
is also the general form, for square roots, of the finite binomial identity of `algebra/FTA_iPRA`. With `c_i = Cat_i`, `S(m) = ∑_{i ≤ m} c_i c_{m−i}` and
`T(m) = ∑_{i ≤ m} i c_i c_{m−i}`:

* `conv_symm`: `2 T(m) = m S(m)`, by reflecting the sum;
* `u_eq`: `∑_{i ≤ m} (i + 2) c_{i+1} c_{m−i} = 4 T(m) + 2 S(m)`, from the ratio recurrence
  `(i + 2) c_{i+1} = (4i + 2) c_i`;
* `shift_eq`: `T(m + 1) + S(m + 1) = c_{m+1} + ∑_{i ≤ m} (i + 2) c_{i+1} c_{m−i}`, by shifting
  the index;
* `segner`: `∑_{i ≤ m} c_i c_{m−i} = c_{m+1}` for every `m`, by quantifier-free induction: the
  three identities give `(m + 3) S(m + 1) = 2 c_{m+1} + (4m + 4) S(m)`, and the ratio
  recurrence turns the right side into `(m + 3) c_{m+2}`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.CatalanConvolution

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Combinatorics.Binomial
open LeanProofs.IPRA.Combinatorics.BinomialIdentities (mul_cancel)
open LeanProofs.IPRA.Combinatorics.Catalan (cat cat_zero cat_rec succ_pos)
open LeanProofs.IPRA.Probability.Independence (sum_scale)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)
open LeanProofs.IPRA.PTm (num monus pred)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem congrCat {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) : Γ ⊢[PRAAx] cat a ≐ cat b := by
  have e := Prf.eqCongr (Γ := Γ) (cat (var 0) : PTm 1) (σ := ![a]) (σ' := ![b])
    (fun j => by fin_cases j; assumption)
  simpa using e

/-- `m ∸ (m ∸ i) = i` for `i ≤ m`. -/
alias monus_monus := Common.monus_monus_of_le

/-! ## Bodies; variables `0 = i`, `1 = m` -/

/-- `c_i c_{m−i}`. -/
abbrev convB : PTm 2 := cat (var 0) * cat (monus (var 1) (var 0))
/-- `i c_i c_{m−i}`. -/
abbrev wB : PTm 2 := var 0 * convB
/-- `(m − i) c_i c_{m−i}`. -/
abbrev rB : PTm 2 := monus (var 1) (var 0) * convB
/-- `(i + 2) c_{i+1} c_{m−i}`. -/
abbrev uB : PTm 2 := succ (succ (var 0)) * (cat (succ (var 0)) * cat (monus (var 1) (var 0)))
/-- `(i + 1) c_i c_{m−i}`. -/
abbrev vB : PTm 2 := succ (var 0) * convB
abbrev fourW : PTm 2 := (two * two) * wB
abbrev twoC : PTm 2 := two * convB

theorem inst2_conv (i m : PTm n) : inst2 convB i m = cat i * cat (monus m i) := by simp [inst2]
theorem inst2_w (i m : PTm n) : inst2 wB i m = i * (cat i * cat (monus m i)) := by simp [inst2]
theorem inst2_r (i m : PTm n) : inst2 rB i m = monus m i * (cat i * cat (monus m i)) := by simp [inst2]
theorem inst2_u (i m : PTm n) :
    inst2 uB i m = succ (succ i) * (cat (succ i) * cat (monus m i)) := by simp [inst2]
theorem inst2_v (i m : PTm n) : inst2 vB i m = succ i * (cat i * cat (monus m i)) := by simp [inst2]
theorem inst2_fourW (i m : PTm n) : inst2 fourW i m = (two * two) * inst2 wB i m := by simp [inst2]
theorem inst2_twoC (i m : PTm n) : inst2 twoC i m = two * inst2 convB i m := by simp [inst2]

/-! ## Symmetry -/

theorem refl_pt {i m : PTm n} (h : Γ ⊢[PRAAx] le i m) :
    Γ ⊢[PRAAx] inst2 (rflBody wB) i (pairT (succ m) m) ≐ inst2 rB i m := by
  rw [inst2_rflBody, inst2_w, inst2_r]
  have hk : Γ ⊢[PRAAx] monus (fstT (pairT (succ m) m)) (succ i) ≐ monus m i :=
    (congrMonus (fst_pair _ _) (.eqRefl _)).eqTrans (succ_monus_succ _ _)
  have hs : Γ ⊢[PRAAx] sndT (pairT (succ m) m) ≐ m := snd_pair _ _
  have hmm : Γ ⊢[PRAAx] monus (sndT (pairT (succ m) m)) (monus (fstT (pairT (succ m) m)) (succ i)) ≐ i :=
    (congrMonus hs hk).eqTrans (monus_monus h)
  exact (congrMul hk (congrMul (congrCat hk) (congrCat hmm))).eqTrans (congrMul (.eqRefl _) (mul_comm _ _))

theorem sym_pt {i m : PTm n} (h : Γ ⊢[PRAAx] le i m) :
    Γ ⊢[PRAAx] inst2 (addBody wB rB) i m ≐ m * inst2 convB i m := by
  rw [inst2_addBody, inst2_w, inst2_r, inst2_conv]
  ipra_lc -(𝔞(cat i) * 𝔞(cat (monus m i))) * natEq (eq_add_of_le h)

/-- `2 ∑_{i ≤ m} i c_i c_{m−i} = m ∑_{i ≤ m} c_i c_{m−i}`. -/
theorem conv_symm (m : PTm n) :
    Γ ⊢[PRAAx] two * ap2 (sumF wB) (succ m) m ≐ m * ap2 (sumF convB) (succ m) m := by
  have r := natEq (sum_reflect (Γ := Γ) wB (succ m) m)
  have c : Γ ⊢[PRAAx] ap2 (sumF (rflBody wB)) (succ m) (pairT (succ m) m) ≐ ap2 (sumF rB) (succ m) m := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, subst_pairT, ConciseIPRA.PTm.subst_succ]
    exact refl_pt ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
  have a := natEq (sum_add (Γ := Γ) wB rB (succ m) m)
  have s : Γ ⊢[PRAAx] ap2 (sumF (addBody wB rB)) (succ m) m ≐ m * ap2 (sumF convB) (succ m) m := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, ConciseIPRA.PTm.subst_succ]
    exact sym_pt ((succ_monus_succ _ _).eqSymm.eqTrans Prf.hyp0)
  have c' := natEq c; have s' := natEq s
  apply deriveNat; ipra_simps
  linear_combination r + c' - a + s'

/-! ## The ratio recurrence inside the sum -/

theorem u_pt (i m : PTm n) : Γ ⊢[PRAAx] inst2 uB i m ≐ inst2 (addBody fourW twoC) i m := by
  rw [inst2_addBody, inst2_fourW, inst2_twoC, inst2_u, inst2_w, inst2_conv]
  ipra_lc 𝔞(cat (monus m i)) * natEq (cat_rec (Γ := Γ) i)

/-- `∑_{i ≤ m} (i + 2) c_{i+1} c_{m−i} = 4 T(m) + 2 S(m)`. -/
theorem u_eq (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF uB) (succ m) m ≐
      (two * two) * ap2 (sumF wB) (succ m) m + two * ap2 (sumF convB) (succ m) m := by
  have c : Γ ⊢[PRAAx] ap2 (sumF uB) (succ m) m ≐ ap2 (sumF (addBody fourW twoC)) (succ m) m :=
    sum_congr_bounded _ _ _ _ _ (.allI (.impI (u_pt _ _)))
  have a := natEq (sum_add (Γ := Γ) fourW twoC (succ m) m)
  have s₁ : Γ ⊢[PRAAx] ap2 (sumF fourW) (succ m) m ≐ (two * two) * ap2 (sumF wB) (succ m) m := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    rw [inst2_fourW]
    exact .eqRefl _
  have s₂ : Γ ⊢[PRAAx] ap2 (sumF twoC) (succ m) m ≐ two * ap2 (sumF convB) (succ m) m := by
    refine sum_scale _ _ _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, PTm.subst_mul, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    rw [inst2_twoC]
    exact .eqRefl _
  have c' := natEq c; have e₁ := natEq s₁; have e₂ := natEq s₂
  apply deriveNat; ipra_simps
  linear_combination c' + a + e₁ + e₂

/-! ## Shifting the index -/

theorem shift_pt (j m : PTm n) : Γ ⊢[PRAAx] inst2 (shiftBody vB) j (succ m) ≐ inst2 uB j m := by
  rw [inst2_shiftBody, inst2_v, inst2_u]
  exact congrMul (.eqRefl _) (congrMul (.eqRefl _) (congrCat (succ_monus_succ _ _)))

theorem v_pt (j x : PTm n) : Γ ⊢[PRAAx] inst2 vB j x ≐ inst2 (addBody wB convB) j x := by
  rw [inst2_addBody, inst2_v, inst2_w, inst2_conv]
  ipra_ring

theorem v_zero (m : PTm n) : Γ ⊢[PRAAx] inst2 vB zero (succ m) ≐ cat (succ m) := by
  rw [inst2_v]
  refine (congrMul (.eqRefl _) (congrMul cat_zero (congrCat (monus_zero _)))).eqTrans ?_
  ipra_ring

/-- `T(m + 1) + S(m + 1) = c_{m+1} + ∑_{i ≤ m} (i + 2) c_{i+1} c_{m−i}`. -/
theorem shift_eq (m : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF wB) (succ (succ m)) (succ m) + ap2 (sumF convB) (succ (succ m)) (succ m) ≐
      cat (succ m) + ap2 (sumF uB) (succ m) m := by
  have c₁ : Γ ⊢[PRAAx] ap2 (sumF vB) (succ (succ m)) (succ m) ≐
      ap2 (sumF (addBody wB convB)) (succ (succ m)) (succ m) :=
    sum_congr_bounded _ _ _ _ _ (.allI (.impI (v_pt _ _)))
  have c₂ : Γ ⊢[PRAAx] ap2 (sumF (shiftBody vB)) (succ m) (succ m) ≐ ap2 (sumF uB) (succ m) m := by
    refine sum_congr_bounded _ _ _ _ _ (.allI (.impI ?_))
    simp only [Syn.shift, ConciseIPRA.PTm.subst_succ]
    exact shift_pt _ _
  ipra_lc -natEq (sum_add (Γ := Γ) wB convB (succ (succ m)) (succ m)) - natEq c₁ +
    natEq (sum_shift (Γ := Γ) vB (succ m) (succ m)) + natEq (v_zero (Γ := Γ) m) + natEq c₂

/-! ## The convolution -/

theorem cat_one : Γ ⊢[PRAAx] cat (succ (zero : PTm n)) ≐ one := by
  refine mul_cancel (D := two) (succ_pos _) ?_
  ipra_lc natEq (cat_rec (Γ := Γ) (zero : PTm n)) + 2 * natEq (cat_zero (Γ := Γ) (n := n))

theorem segner_base : Γ ⊢[PRAAx] ap2 (sumF convB) (succ zero) (zero : PTm n) ≐ cat (succ zero) := by
  have e₁ := sum_succ' (Γ := Γ) convB zero (zero : PTm n)
  rw [inst2_conv] at e₁
  have hx : Γ ⊢[PRAAx] cat (zero : PTm n) * cat (monus zero zero) ≐ one :=
    (congrMul cat_zero ((congrCat (monus_zero zero)).eqTrans cat_zero)).eqTrans (one_mul one)
  ipra_lc natEq e₁ + natEq (sum_zero (Γ := Γ) convB (zero : PTm n)) + natEq hx - natEq (cat_one (Γ := Γ) (n := n))

theorem segner_step {m : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF convB) (succ m) m ≐ cat (succ m)) :
    Γ ⊢[PRAAx] ap2 (sumF convB) (succ (succ m)) (succ m) ≐ cat (succ (succ m)) := by
  refine mul_cancel (D := succ (succ (succ m))) (succ_pos _) ?_
  ipra_lc -natEq (conv_symm (Γ := Γ) (succ m)) + 2 * natEq (shift_eq (Γ := Γ) m) + 2 * natEq (u_eq (Γ := Γ) m) +
    4 * natEq (conv_symm (Γ := Γ) m) + (4 * 𝔞(m) + 4) * natEq ih - natEq (cat_rec (Γ := Γ) (succ m))

/-- Variable: `0 = m`. -/
private abbrev segF : Fm PTm 1 := ap2 (sumF convB) (succ (var 0)) (var 0) ≐ cat (succ (var 0))

private theorem seg₀ : ([] : List (Fm PTm 1)) ⊢[PRAAx] segF := by
  refine ind _ trivial ?_ ?_
  · simp only [Fm.subst_eq, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var, Syn.inst_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact segner_base
  · simp only [Fm.subst_eq, PTm.subst_mul, PTm.subst_monus, subst_ap2, Syn.subst_var, Syn.repl_zero,
      ConciseIPRA.PTm.subst_zero, ConciseIPRA.PTm.subst_succ]
    exact segner_step Prf.hyp0

/-- The Segner recurrence: `∑_{i ≤ m} Cat_i Cat_{m−i} = Cat_{m+1}`. -/
theorem segner (m : PTm n) : Γ ⊢[PRAAx] ap2 (sumF convB) (succ m) m ≐ cat (succ m) := by
  have h := inst (Γ := Γ) seg₀ (![m] : Fin 1 → PTm n)
  simpa using h

end LeanProofs.IPRA.Combinatorics.CatalanConvolution
