import IPRADerivations.DiophantineNumberTheory.PellCFStep
import IPRADerivations.Core.Pigeonhole

/-!
# The finite Dirichlet construction for `√D`

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Lemma `lem:dirichlet`. For `D, Q ≥ 1`, with
`t_j = ⌊√(D j²)⌋`, `w_j = ⌊√(D Q² j²)⌋` and the bins `b_j = w_j − Q t_j < Q`, the pigeonhole principle
(`Core/Pigeonhole`) gives `i < j ≤ Q` with `b_i = b_j`; then `q = j − i`, `p = t_j − t_i` satisfy
  `1 ≤ q ≤ Q`, `1 ≤ p ≤ D q`, and `|p − q√D| < 1/Q`,
the last cleared into integer squares as `(Qq)² D < (Qp + 1)²` and `(Qp ∸ 1)² < (Qq)² D`.

The irrational errors `j√D − t_j` are never formed. The comparisons are combined by the integer
square-root subadditivity `sqrt_add_le`/`sqrt_add_lt`: from `u² ≤ v² D` and `b² ≤ d² D` follows
`(u + b)² ≤ (v + d)² D` (since `(ub)² ≤ (v d D)²`), and the strict dual.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellDirichlet

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime (le_of_sq_le)
open LeanProofs.IPRA.Geometry.HypercubeSplit (le_cancel_pos)
open LeanProofs.IPRA.DiophantineNumberTheory.PellCFStep (lt_of_sq_lt pos_of_le_one one_le_of_pos le_add_monus_l)
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Square roots -/

/-- `x² ≤ N` gives `x ≤ ⌊√N⌋`. -/
theorem le_isqrt {x N : PTm n} (h : Γ ⊢[PRAAx] le (x * x) N) : Γ ⊢[PRAAx] le x (isqrt N) := by
  refine .orE (lt_or_le (isqrt N) x) ?_ Prf.hyp0
  let C := lt (isqrt N) x :: Γ
  have s : C ⊢[PRAAx] le ((isqrt N + one) * (isqrt N + one)) (x * x) :=
    le_congr (congrMul (succ_eq_add_one _) (succ_eq_add_one _)) (.eqRefl _) (le_mul_mono Prf.hyp0 Prf.hyp0)
  exact le_lt_absurd _ (le_trans s h.wk) (lt_isqrt_succ_sq N)

/-- Subadditivity of square roots: `u ≤ v√D`, `b ≤ d√D` give `u + b ≤ (v + d)√D`. -/
theorem sqrt_add_le {u v b d D : PTm n} (h₁ : Γ ⊢[PRAAx] le (u * u) (v * v * D)) (h₂ : Γ ⊢[PRAAx] le (b * b) (d * d * D)) :
    Γ ⊢[PRAAx] le ((u + b) * (u + b)) ((v + d) * (v + d) * D) := by
  have x : Γ ⊢[PRAAx] le (u * b) (v * d * D) :=
    le_of_sq_le (le_congr (by ipra_ring) (by ipra_ring) (le_mul_mono h₁ h₂))
  refine le_congr ?_ ?_ (le_add_mono (le_add_mono h₁ (le_add_mono x x)) h₂) <;> (ipra_ring)

/-- The strict dual: `v√D ≤ u`, `d√D < b` give `(v + d)√D < u + b`. -/
theorem sqrt_add_lt {u v b d D : PTm n} (h₁ : Γ ⊢[PRAAx] le (v * v * D) (u * u)) (h₂ : Γ ⊢[PRAAx] lt (d * d * D) (b * b)) :
    Γ ⊢[PRAAx] lt ((v + d) * (v + d) * D) ((u + b) * (u + b)) := by
  have x : Γ ⊢[PRAAx] le (v * d * D) (u * b) :=
    le_of_sq_le (le_congr (by ipra_ring) (by ipra_ring)
      (le_mul_mono h₁ (le_of_lt h₂)))
  refine le_congr ?_ ?_ (le_add_mono (le_add_mono h₁ (le_add_mono x x)) h₂) <;> (ipra_ring)

/-! ## The bins -/

/-- `t_j = ⌊√(D j²)⌋` and `w_j = ⌊√(D Q² j²)⌋`, over `0 = j`, `1 = ⟨D, Q⟩`. -/
abbrev tB : PTm 2 := isqrt (fstT (var 1) * (var 0 * var 0))
abbrev wB : PTm 2 := isqrt (fstT (var 1) * (sndT (var 1) * sndT (var 1)) * (var 0 * var 0))
abbrev bB : PTm 2 := monus wB (sndT (var 1) * tB)

abbrev tj (D j : PTm n) : PTm n := isqrt (D * (j * j))
abbrev wj (D Q j : PTm n) : PTm n := isqrt (D * (Q * Q) * (j * j))

theorem bB_at (j D Q : PTm n) : Γ ⊢[PRAAx] inst2 bB j (pairT D Q) ≐ monus (wj D Q j) (Q * tj D j) := by
  have e : inst2 bB j (pairT D Q) = monus (isqrt (fstT (pairT D Q) * (sndT (pairT D Q) * sndT (pairT D Q)) * (j * j)))
      (sndT (pairT D Q) * isqrt (fstT (pairT D Q) * (j * j))) := by simp [inst2]
  rw [e]
  have f : Γ ⊢[PRAAx] fstT (pairT D Q) ≐ D := fst_pair _ _
  have s : Γ ⊢[PRAAx] sndT (pairT D Q) ≐ Q := snd_pair _ _
  exact congrMonus (congrAp1 _ (congrMul (congrMul f (congrMul s s)) (.eqRefl _)))
    (congrMul s (congrAp1 _ (congrMul f (.eqRefl _))))

/-- `Q t_j ≤ w_j < Q (t_j + 1)`. -/
theorem w_bounds {Q : PTm n} (hQ : Γ ⊢[PRAAx] Q ≐ succ (pred Q)) (D j : PTm n) :
    Γ ⊢[PRAAx] le (Q * tj D j) (wj D Q j) ⋏ lt (wj D Q j) (Q * succ (tj D j)) := by
  refine .andI (le_isqrt (le_congr (by ipra_ring) (by ipra_ring)
    (mul_le_mul_right (Q * Q) (isqrt_le (D * (j * j)))))) ?_
  refine lt_of_sq_lt (lt_of_le_of_lt (isqrt_le _) ?_)
  have l1 := mul_le_mul_right (Q * Q) (lt_isqrt_succ_sq (Γ := Γ) (D * (j * j)))
  refine le_trans (le_of_eq_add (d := pred (Q * Q)) ?_) (le_congr (.eqRefl _) ?_ l1)
  · ipra_lc natEq (pos_mul hQ hQ)
  · ipra_ring

/-! ## The construction -/

/-- The colliding indices `i < j ≤ Q` from the pigeonhole principle, and `q = j − i`, `p = t_j − t_i`. -/
abbrev Iz (D Q : PTm n) : PTm n := Pigeonhole.phpI bB Q (pairT D Q)
abbrev Jz (D Q : PTm n) : PTm n := Pigeonhole.phpJ bB Q (pairT D Q)
abbrev dq (D Q : PTm n) : PTm n := monus (Jz D Q) (Iz D Q)
abbrev dp (D Q : PTm n) : PTm n := monus (tj D (Jz D Q)) (tj D (Iz D Q))

/-- `lem:dirichlet`: `1 ≤ q ≤ Q`, `1 ≤ p ≤ D q`, and `|p − q√D| < 1/Q`, cleared:
`(Qq)² D < (Qp + 1)²` and `(Qp ∸ 1)² < (Qq)² D`. -/
theorem dirichlet {D Q : PTm n} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) (hQ : Γ ⊢[PRAAx] Q ≐ succ (pred Q)) :
    Γ ⊢[PRAAx] le one (dq D Q) ⋏ (le (dq D Q) Q ⋏ (le one (dp D Q) ⋏ (le (dp D Q) (D * dq D Q) ⋏
      (lt (Q * dq D Q * (Q * dq D Q) * D) ((Q * dp D Q + one) * (Q * dp D Q + one)) ⋏
       lt (monus (Q * dp D Q) one * monus (Q * dp D Q) one) (Q * dq D Q * (Q * dq D Q) * D))))) := by
  -- Every bin is below `Q`.
  have hr : Γ ⊢[PRAAx] Permutation.rangeAll bB Q (pairT D Q) := by
    have hQ' : Γ.map Fm.shift ⊢[PRAAx] Syn.shift Q ≐ succ (pred (Syn.shift Q)) := by
      simpa [Fm.shift, Syn.shift] using hQ.shift
    refine .allI ?_
    rw [shift_pairT]
    have wb := w_bounds hQ' (Syn.shift D) (var 0)
    have e := eq_add_of_le (Prf.andE₁ wb)
    refine lt_congr (bB_at _ _ _).eqSymm (.eqRefl _) (le_of_add_le_add_right (c := Syn.shift Q * tj (Syn.shift D) (var 0)) ?_)
    refine le_congr ?_ ?_ (Prf.andE₂ wb)
    · ipra_lc natEq e
    · ipra_ring
  have ph := Pigeonhole.pigeonhole (S := bB) hr
  have hIJ := Prf.andE₁ ph
  have hJQ := Prf.andE₁ (Prf.andE₂ ph)
  have hb := Prf.andE₂ (Prf.andE₂ ph)
  -- `J = I + q`, `t_J = t_I + p`, `w_J = w_I + Q p`.
  have eJ := eq_add_of_le (le_of_lt hIJ)
  have hq1 : Γ ⊢[PRAAx] le one (dq D Q) := le_of_add_le_add_right (c := Iz D Q)
    (le_congr (by ipra_ring) (eJ.eqTrans (add_comm _ _)) hIJ)
  have htm : Γ ⊢[PRAAx] le (tj D (Iz D Q)) (tj D (Jz D Q)) :=
    le_isqrt (le_trans (isqrt_le _) (le_mul_mono (le_refl D) (le_mul_mono (le_of_lt hIJ) (le_of_lt hIJ))))
  have eT := eq_add_of_le htm
  have wI := Prf.andE₁ (w_bounds hQ D (Iz D Q))
  have wJ := Prf.andE₁ (w_bounds hQ D (Jz D Q))
  have bI := (bB_at (Γ := Γ) (Iz D Q) D Q).eqSymm.eqTrans (hb.eqTrans (bB_at _ _ _))
  have eWI := eq_add_of_le wI
  have eWJ := eq_add_of_le wJ
  have eW : Γ ⊢[PRAAx] wj D Q (Jz D Q) ≐ wj D Q (Iz D Q) + Q * dp D Q := by
    ipra_lc natEq eWJ - natEq eWI + 𝔞 Q * natEq eT - natEq bI
  -- Square-root facts at `I` and `J`, in the form `x² ≤ y² D`.
  have sqI : Γ ⊢[PRAAx] le (wj D Q (Iz D Q) * wj D Q (Iz D Q)) (Q * Iz D Q * (Q * Iz D Q) * D) :=
    le_congr (.eqRefl _) (by ipra_ring) (isqrt_le _)
  have ltI : Γ ⊢[PRAAx] lt (Q * Iz D Q * (Q * Iz D Q) * D) ((wj D Q (Iz D Q) + one) * (wj D Q (Iz D Q) + one)) :=
    lt_congr (by ipra_ring) (.eqRefl _) (lt_isqrt_succ_sq _)
  have sqJ : Γ ⊢[PRAAx] le (wj D Q (Jz D Q) * wj D Q (Jz D Q)) (Q * Jz D Q * (Q * Jz D Q) * D) :=
    le_congr (.eqRefl _) (by ipra_ring) (isqrt_le _)
  have ltJ : Γ ⊢[PRAAx] lt (Q * Jz D Q * (Q * Jz D Q) * D) ((wj D Q (Jz D Q) + one) * (wj D Q (Jz D Q) + one)) :=
    lt_congr (by ipra_ring) (.eqRefl _) (lt_isqrt_succ_sq _)
  have eQJ : Γ ⊢[PRAAx] Q * dq D Q + Q * Iz D Q ≐ Q * Jz D Q := by
    ipra_lc -𝔞 Q * natEq eJ
  -- The upper error bound.
  have hU : Γ ⊢[PRAAx] lt (Q * dq D Q * (Q * dq D Q) * D) ((Q * dp D Q + one) * (Q * dp D Q + one)) := by
    refine .orE (lt_or_le (Q * dq D Q * (Q * dq D Q) * D) ((Q * dp D Q + one) * (Q * dp D Q + one))) Prf.hyp0 ?_
    let C := le ((Q * dp D Q + one) * (Q * dp D Q + one)) (Q * dq D Q * (Q * dq D Q) * D) :: Γ
    have sa := sqrt_add_le (Prf.hyp0 : C ⊢[PRAAx] _) sqI.wk
    have e1 : C ⊢[PRAAx] Q * dp D Q + one + wj D Q (Iz D Q) ≐ wj D Q (Jz D Q) + one := by
      ipra_lc -natEq (eW.wk : C ⊢[PRAAx] _)
    refine le_lt_absurd _ (le_congr (congrMul e1 e1) (congrMul (congrMul eQJ.wk eQJ.wk) (.eqRefl _)) sa) ltJ.wk
  -- `p ≥ 1`.
  have hD1 := one_le_of_pos hD
  have hqq : Γ ⊢[PRAAx] Q * dq D Q * (Q * dq D Q) * D ≐ succ (pred (Q * dq D Q * (Q * dq D Q) * D)) :=
    pos_mul (pos_mul (pos_mul hQ (pos_of_le_one hq1)) (pos_mul hQ (pos_of_le_one hq1))) hD
  have hp1 : Γ ⊢[PRAAx] le one (dp D Q) := by
    refine one_le_of_pos (.orE (zero_or_succ (dp D Q)) ?_ Prf.hyp0)
    let C := (dp D Q ≐ zero) :: Γ
    have z : C ⊢[PRAAx] (Q * dp D Q + one) * (Q * dp D Q + one) ≐ one := by
      ipra_lc (𝔞 Q * 𝔞 Q * 𝔞 (dp D Q) + 2 * 𝔞 Q) * natEq (Prf.hyp0 : C ⊢[PRAAx] _)
    have u := lt_congr (.eqRefl _) z hU.wk
    exact not_succ_le_self _ _ (le_trans u (one_le_of_pos hqq.wk))
  -- The lower error bound.
  have hL : Γ ⊢[PRAAx] lt (monus (Q * dp D Q) one * monus (Q * dp D Q) one) (Q * dq D Q * (Q * dq D Q) * D) := by
    refine .orE (zero_or_succ (Q * dp D Q)) ?_ ?_
    · let C := (Q * dp D Q ≐ zero) :: Γ
      have z : C ⊢[PRAAx] monus (Q * dp D Q) one * monus (Q * dp D Q) one ≐ zero :=
        (congrMul ((congrMonus Prf.hyp0 (.eqRefl _)).eqTrans (zero_monus _))
          ((congrMonus Prf.hyp0 (.eqRefl _)).eqTrans (zero_monus _))).eqTrans (zero_mul _)
      exact lt_congr z.eqSymm (.eqRefl _) (one_le_of_pos hqq.wk)
    · let C := (Q * dp D Q ≐ succ (pred (Q * dp D Q))) :: Γ
      have hg : C ⊢[PRAAx] monus (Q * dp D Q) one ≐ pred (Q * dp D Q) :=
        (congrMonus Prf.hyp0 (.eqRefl _)).eqTrans ((succ_monus_succ _ _).eqTrans (monus_zero _))
      refine lt_congr (congrMul hg.eqSymm hg.eqSymm) (.eqRefl _) ?_
      refine .orE (lt_or_le (pred (Q * dp D Q) * pred (Q * dp D Q)) (Q * dq D Q * (Q * dq D Q) * D)) Prf.hyp0 ?_
      let C' := le (Q * dq D Q * (Q * dq D Q) * D) (pred (Q * dp D Q) * pred (Q * dp D Q)) :: C
      have sa := sqrt_add_lt (Prf.hyp0 : C' ⊢[PRAAx] _) ltI.wk.wk
      have e1 : C' ⊢[PRAAx] pred (Q * dp D Q) + (wj D Q (Iz D Q) + one) ≐ wj D Q (Jz D Q) := by
        ipra_lc -natEq (eW.wk.wk : C' ⊢[PRAAx] _) - natEq (Prf.hyp1 : C' ⊢[PRAAx] _)
      exact le_lt_absurd _ sqJ.wk.wk (lt_congr (congrMul (congrMul eQJ.wk.wk eQJ.wk.wk) (.eqRefl _)) (congrMul e1 e1) sa)
  -- `p ≤ D q`.
  have hpD : Γ ⊢[PRAAx] le (dp D Q) (D * dq D Q) := by
    have dD0 : Γ ⊢[PRAAx] le (D * one) (D * D) := le_mul_mono (le_refl D) hD1
    have dD : Γ ⊢[PRAAx] le D (D * D) := le_congr (by ipra_ring) (.eqRefl _) dD0
    have hDD0 : Γ ⊢[PRAAx] le (Q * dq D Q * (Q * dq D Q) * D) (Q * dq D Q * (Q * dq D Q) * (D * D)) :=
      le_mul_mono (le_refl _) dD
    have hDD : Γ ⊢[PRAAx] le (Q * dq D Q * (Q * dq D Q) * D) (Q * dq D Q * D * (Q * dq D Q * D)) :=
      le_congr (.eqRefl _) (by ipra_ring) hDD0
    have l := lt_of_sq_lt (lt_of_lt_of_le hL hDD)
    have l2 : Γ ⊢[PRAAx] le (Q * dp D Q) (Q * (D * dq D Q)) :=
      le_congr (.eqRefl _) (by ipra_ring)
        (le_trans (le_congr (.eqRefl _) (by ipra_ring) (le_add_monus_l (Q * dp D Q) one)) l)
    exact le_cancel_pos hQ l2
  have hqQ : Γ ⊢[PRAAx] le (dq D Q) Q :=
    le_trans (le_of_eq_add (d := Iz D Q) (eJ.eqTrans (add_comm _ _))) hJQ
  exact .andI hq1 (.andI hqQ (.andI hp1 (.andI hpD (.andI hU hL))))

end LeanProofs.IPRA.DiophantineNumberTheory.PellDirichlet
