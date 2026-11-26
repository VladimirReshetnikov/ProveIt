import IPRADerivations.DiophantineNumberTheory.PellAll
import IPRADerivations.DiophantineNumberTheory.PellGenDescent
import IPRADerivations.DiophantineNumberTheory.PellCFStep
import IPRADerivations.Core.LinearCombination
import IPRADerivations.Core.Header

/-!
# Finite seeds and uniform decision for `x² − D y² = N`

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Theorem `thm:general`. Let `A² = 1 + D B²` with
`B, D ≥ 1` (any positive norm-one unit `u = (A, B)`), `N ≠ 0`, `K = |N| ≥ 1`, and put `T = A K`,
`R = D T + K` (`eq:seedbounds`). For a nonnegative solution `(x, y)` of `x² = D y² + K` (`N > 0`) or
`x² + K = D y²` (`N < 0`), a state machine runs `y` stages on the residual `(r, t)` and a counter `c`,
initially `(x, y)` and `0`: a stage with `t > T` applies the uniform descent of `PellGenDescent`
(multiplication by `(A, −B)`) and increments `c`; a stage with `t ≤ T` is stationary. The
quantifier-free invariant `(x, y) = uᶜ (r, t)`, `N(r, t) = N`, `t ≤ T ∨ t + k ≤ y`, `c ≤ k` holds at
every stage `k`.

* `general_pos`, `general_neg` (`thm:general`): every nonnegative solution is `(x, y) = (r, t) uᶜ` with
  `c ≤ y` and a seed `(r, t)` of the same norm in the box `t ≤ T`, `r ≤ R` (`eq:seedset`);
* `seed_pos`, `seed_neg` (the converse): for every seed `(r, t)` of norm `N` and every `c`,
  `(r, t) uᶜ = (X_c r + D Y_c t, Y_c r + X_c t)` is a nonnegative solution (norm multiplicativity with
  `X_c² = D Y_c² + 1`, `Recurrences.pell_powers`).

So solvability is equivalent to nonemptiness of the finite seed box, which is decided by a bounded scan.
Integer solutions are obtained by independent sign changes, since `(±x)² − D(±y)² = x² − D y²`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellGeneral

open_ipra
open LeanProofs.IPRA.Combinatorics.Binomial (pos_mul)
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.PellDescent (rr tt)
open LeanProofs.IPRA.DiophantineNumberTheory.PellGenDescent (gen_descent_pos gen_descent_neg)
open LeanProofs.IPRA.DiophantineNumberTheory.PellAll (alg_x alg_y)
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open LeanProofs.IPRA.DiophantineNumberTheory.SquareArea (le_add_mono)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

@[simp] theorem finCases_six {α : Sort _} (a : α) (f : Fin (n + 6) → α) :
    (Fin.cases a f : Fin (n + 7) → α) 6 = f 5 := rfl
@[simp] theorem finCases_seven {α : Sort _} (a : α) (f : Fin (n + 7) → α) :
    (Fin.cases a f : Fin (n + 8) → α) 7 = f 6 := rfl
@[simp] theorem finCases_eight {α : Sort _} (a : α) (f : Fin (n + 8) → α) :
    (Fin.cases a f : Fin (n + 9) → α) 8 = f 7 := rfl

/-! ## The state machine; step variables `0 = j`, `1 = r`, `2 = ⟨t, c⟩`, `3 = A`, `4 = B`, `5 = D`,
`6 = x`, `7 = y`, `8 = K` -/

abbrev tW : PTm 9 := fstT (var 2)
/-- The guard `[t > A K]`. -/
abbrev gW : PTm 9 := sg (monus tW (var 3 * var 8))
abbrev rStep : PTm 9 := gW * monus (var 3 * var 1) (var 5 * (var 4 * tW)) + monus one gW * var 1
abbrev wStep : PTm 9 := pairT (gW * monus (var 3 * tW) (var 4 * var 1) + monus one gW * tW) (sndT (var 2) + gW)

/-- Parameters `ps = (A, B, D, x, y, K)`. -/
abbrev R (k : PTm n) (ps : Fin 6 → PTm n) : PTm n := sim₁ (var 3) (pairT (var 4) zero) rStep wStep k ps
abbrev W (k : PTm n) (ps : Fin 6 → PTm n) : PTm n := sim₂ (var 3) (pairT (var 4) zero) rStep wStep k ps
abbrev T (k : PTm n) (ps : Fin 6 → PTm n) : PTm n := fstT (W k ps)
abbrev C (k : PTm n) (ps : Fin 6 → PTm n) : PTm n := sndT (W k ps)
abbrev G (k : PTm n) (ps : Fin 6 → PTm n) : PTm n := sg (monus (T k ps) (ps 0 * ps 5))
abbrev p3 (ps : Fin 6 → PTm n) : Fin 3 → PTm n := fun i => ps (Fin.castLE (by omega) i)
abbrev Xp (m : PTm n) (ps : Fin 3 → PTm n) : PTm n := Recurrences.X m ps
abbrev Yp (m : PTm n) (ps : Fin 3 → PTm n) : PTm n := Recurrences.Y m ps

section Equations

variable (ps : Fin 6 → PTm n)

theorem R_zero : Γ ⊢[PRAAx] R zero ps ≐ ps 3 := by
  simpa using sim₁_zero (Γ := Γ) (var 3 : PTm 6) (pairT (var 4) zero) rStep wStep ps

theorem W_zero : Γ ⊢[PRAAx] W zero ps ≐ pairT (ps 4) zero := by
  simpa using sim₂_zero (Γ := Γ) (var 3 : PTm 6) (pairT (var 4) zero) rStep wStep ps

theorem T_zero : Γ ⊢[PRAAx] T zero ps ≐ ps 4 := (congrFst (W_zero ps)).eqTrans (fst_pair _ _)
theorem C_zero : Γ ⊢[PRAAx] C zero ps ≐ zero := (congrSnd (W_zero ps)).eqTrans (snd_pair _ _)

theorem R_succ (k : PTm n) : Γ ⊢[PRAAx] R (succ k) ps ≐
    G k ps * monus (ps 0 * R k ps) (ps 2 * (ps 1 * T k ps)) + monus one (G k ps) * R k ps := by
  have h := sim₁_succ (Γ := Γ) (var 3 : PTm 6) (pairT (var 4) zero) rStep wStep ps k
  simp only [PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_fstT, subst_sndT, subst_pairT,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    Fin.cases_zero, finCases_one, finCases_two, finCases_three, finCases_four, finCases_five,
    finCases_six, finCases_seven, finCases_eight] at h
  exact h

theorem W_succ (k : PTm n) : Γ ⊢[PRAAx] W (succ k) ps ≐
    pairT (G k ps * monus (ps 0 * T k ps) (ps 1 * R k ps) + monus one (G k ps) * T k ps) (C k ps + G k ps) := by
  have h := sim₂_succ (Γ := Γ) (var 3 : PTm 6) (pairT (var 4) zero) rStep wStep ps k
  simp only [PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_fstT, subst_sndT, subst_pairT,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    Fin.cases_zero, finCases_one, finCases_two, finCases_three, finCases_four, finCases_five,
    finCases_six, finCases_seven, finCases_eight] at h
  exact h

theorem T_succ (k : PTm n) : Γ ⊢[PRAAx] T (succ k) ps ≐
    G k ps * monus (ps 0 * T k ps) (ps 1 * R k ps) + monus one (G k ps) * T k ps :=
  (congrFst (W_succ ps k)).eqTrans (fst_pair _ _)

theorem C_succ (k : PTm n) : Γ ⊢[PRAAx] C (succ k) ps ≐ C k ps + G k ps :=
  (congrSnd (W_succ ps k)).eqTrans (snd_pair _ _)

theorem X_succ (m : PTm n) : Γ ⊢[PRAAx] Xp (succ m) (p3 ps) ≐ ps 0 * Xp m (p3 ps) + ps 2 * (ps 1 * Yp m (p3 ps)) :=
  Recurrences.X_succ m (p3 ps)

theorem Y_succ (m : PTm n) : Γ ⊢[PRAAx] Yp (succ m) (p3 ps) ≐ ps 1 * Xp m (p3 ps) + ps 0 * Yp m (p3 ps) :=
  Recurrences.Y_succ m (p3 ps)

theorem X_zero : Γ ⊢[PRAAx] Xp zero (p3 ps) ≐ one :=
  Recurrences.X_zero (p3 ps)
theorem Y_zero : Γ ⊢[PRAAx] Yp zero (p3 ps) ≐ zero :=
  Recurrences.Y_zero (p3 ps)

theorem congrX {m m' : PTm n} (h : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] Xp m (p3 ps) ≐ Xp m' (p3 ps) :=
  Recurrences.congrX (p3 ps) h

theorem congrY {m m' : PTm n} (h : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] Yp m (p3 ps) ≐ Yp m' (p3 ps) :=
  Recurrences.congrY (p3 ps) h

/-- The guard: `[t > A K] = 0` means `t ≤ A K`; otherwise `A K < t`. -/
theorem guard_cases (k : PTm n) :
    Γ ⊢[PRAAx] ((monus (T k ps) (ps 0 * ps 5) ≐ zero) ⋏ le (T k ps) (ps 0 * ps 5)) ⋎
      ((monus (T k ps) (ps 0 * ps 5) ≐ succ (pred (monus (T k ps) (ps 0 * ps 5)))) ⋏ lt (ps 0 * ps 5) (T k ps)) := by
  refine .orE (zero_or_succ (monus (T k ps) (ps 0 * ps 5))) (.orI₁ (.andI Prf.hyp0 Prf.hyp0)) ?_
  refine .orI₂ (.andI Prf.hyp0 ?_)
  refine .orE (lt_or_le (ps 0 * ps 5) (T k ps)) Prf.hyp0 ?_
  exact succ_ne_zero' _ (Prf.hyp1.eqSymm.eqTrans Prf.hyp0)

end Equations

/-- `D T² + K ≤ (D T + K)²` for `D, K ≥ 1`. -/
theorem seed_square {D T K : PTm n} (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) (hK : Γ ⊢[PRAAx] K ≐ succ (pred K)) :
    Γ ⊢[PRAAx] le (D * (T * T) + K) ((D * T + K) * (D * T + K)) := by
  have dd : Γ ⊢[PRAAx] le (D * (T * T)) (D * D * (T * T)) := mul_le_mul_right _ (le_congr (mul_one' _) (.eqRefl _)
    (le_mul_mono (le_refl D) (one_le_of_pos hD)))
  have kk : Γ ⊢[PRAAx] le K (K * K) := le_congr (mul_one' _) (.eqRefl _) (le_mul_mono (le_refl K) (one_le_of_pos hK))
  refine le_trans (le_add_mono dd kk) (le_of_eq_add (d := two * (D * T * K)) ?_)
  ipra_ring
where
  mul_one' (a : PTm n) : Γ ⊢[PRAAx] a * one ≐ a := by ipra_ring

/-! ## The two signs of the norm -/

section Signed

/-- The norm relation of a residual: `r² = D t² + K` (`s = true`, `N > 0`) or `r² + K = D t²` (`s = false`, `N < 0`). -/
abbrev Nm (s : Bool) (D K r t : PTm n) : Fm PTm n :=
  match s with
  | true => r * r ≐ D * (t * t) + K
  | false => r * r + K ≐ D * (t * t)

/-- The uniform descent for either sign (`PellGenDescent.gen_descent_pos`, `gen_descent_neg`). -/
theorem gen_descent {s : Bool} {A B D K x y : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B))
    (hB : Γ ⊢[PRAAx] B ≐ succ (pred B)) (hD : Γ ⊢[PRAAx] D ≐ succ (pred D)) (hK : Γ ⊢[PRAAx] K ≐ succ (pred K))
    (hx : Γ ⊢[PRAAx] Nm s D K x y) (hy : Γ ⊢[PRAAx] lt (A * K) y) :
    Γ ⊢[PRAAx] Nm s D K (rr A B D x y) (tt A B D x y) ⋏
      (le one (rr A B D x y) ⋏ le one (tt A B D x y) ⋏ lt (tt A B D x y) y ⋏
      (x ≐ A * rr A B D x y + D * (B * tt A B D x y)) ⋏ (y ≐ B * rr A B D x y + A * tt A B D x y)) := by
  cases s
  · exact gen_descent_neg hA hB hD hK hx hy
  · exact gen_descent_pos hA hB hD hK hx hy

/-- The invariant for a residual `(r, t)`, counter `c` and stage `k`. -/
abbrev InvAt (s : Bool) (ps : Fin 6 → PTm n) (r t c k : PTm n) : Fm PTm n :=
  (ps 3 ≐ Xp c (p3 ps) * r + ps 2 * (Yp c (p3 ps) * t)) ⋏ (ps 4 ≐ Yp c (p3 ps) * r + Xp c (p3 ps) * t) ⋏
    Nm s (ps 2) (ps 5) r t ⋏ (le t (ps 0 * ps 5) ⋎ le (t + k) (ps 4)) ⋏ le c k

abbrev Inv (s : Bool) (ps : Fin 6 → PTm n) (k : PTm n) : Fm PTm n := InvAt s ps (R k ps) (T k ps) (C k ps) k

theorem subst_Inv {m : ℕ} (σ : Fin n → PTm m) (s : Bool) (ps : Fin 6 → PTm n) (k : PTm n) :
    (Inv s ps k).subst σ = Inv s (fun i => Syn.subst σ (ps i)) (Syn.subst σ k) := by
  cases s <;> simp [Inv, InvAt, Nm, p3]

theorem invAt_congr {s : Bool} {ps : Fin 6 → PTm n} {r r' t t' c c' k : PTm n} (hr : Γ ⊢[PRAAx] r ≐ r')
    (ht : Γ ⊢[PRAAx] t ≐ t') (hc : Γ ⊢[PRAAx] c ≐ c') (h : Γ ⊢[PRAAx] InvAt s ps r t c k) :
    Γ ⊢[PRAAx] InvAt s ps r' t' c' k := by
  have hX := congrX ps hc
  have hY := congrY ps hc
  refine .andI ?_ (.andI ?_ (.andI ?_ (.andI ?_ ?_)))
  · exact (Prf.andE₁ h).eqTrans (congrAdd (congrMul hX hr) (congrMul (.eqRefl _) (congrMul hY ht)))
  · exact (Prf.andE₁ (Prf.andE₂ h)).eqTrans (congrAdd (congrMul hY hr) (congrMul hX ht))
  · cases s
    · exact (congrAdd (congrMul hr hr) (.eqRefl _)).eqSymm.eqTrans ((Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))).eqTrans (congrMul (.eqRefl _) (congrMul ht ht)))
    · exact (congrMul hr hr).eqSymm.eqTrans ((Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))).eqTrans (congrAdd (congrMul (.eqRefl _) (congrMul ht ht)) (.eqRefl _)))
  · refine .orE (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))) ?_ ?_
    · exact .orI₁ (le_congr ht.wk (.eqRefl _) Prf.hyp0)
    · exact .orI₂ (le_congr (congrAdd ht.wk (.eqRefl _)) (.eqRefl _) Prf.hyp0)
  · exact le_congr hc (.eqRefl _) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))

/-- One stage preserves the invariant. -/
theorem inv_step {s : Bool} {ps : Fin 6 → PTm n} {k : PTm n} (hA : Γ ⊢[PRAAx] ps 0 * ps 0 ≐ one + ps 2 * (ps 1 * ps 1))
    (hB : Γ ⊢[PRAAx] ps 1 ≐ succ (pred (ps 1))) (hD : Γ ⊢[PRAAx] ps 2 ≐ succ (pred (ps 2)))
    (hK : Γ ⊢[PRAAx] ps 5 ≐ succ (pred (ps 5))) (ih : Γ ⊢[PRAAx] Inv s ps k) : Γ ⊢[PRAAx] Inv s ps (succ k) := by
  have rs := R_succ (Γ := Γ) ps k
  have ts := T_succ (Γ := Γ) ps k
  have cs := C_succ (Γ := Γ) ps k
  refine .orE (guard_cases ps k) ?_ ?_
  · -- `t ≤ A K`: nothing changes.
    let Δ := ((monus (T k ps) (ps 0 * ps 5) ≐ zero) ⋏ le (T k ps) (ps 0 * ps 5)) :: Γ
    have hz : Δ ⊢[PRAAx] monus (T k ps) (ps 0 * ps 5) ≐ zero := Prf.andE₁ Prf.hyp0
    have hs : Δ ⊢[PRAAx] G k ps ≐ zero := (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hz)).eqTrans sg_zero
    refine invAt_congr (r := R k ps) (t := T k ps) (c := C k ps) (rs.wk.eqTrans (Bezout.guard_zero hz)).eqSymm
      (ts.wk.eqTrans (Bezout.guard_zero hz)).eqSymm ((cs.wk.eqTrans ((congrAdd (.eqRefl _) hs).eqTrans (add_zero _))).eqSymm) ?_
    have i := (ih.wk : Δ ⊢[PRAAx] _)
    refine .andI (Prf.andE₁ i) (.andI (Prf.andE₁ (Prf.andE₂ i)) (.andI (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ i)))
      (.andI (.orI₁ (Prf.andE₂ Prf.hyp0)) ?_)))
    exact le_trans (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ i)))) (le_succ_self _)
  · -- `t > A K`: one uniform descent.
    let Δ := ((monus (T k ps) (ps 0 * ps 5) ≐ succ (pred (monus (T k ps) (ps 0 * ps 5)))) ⋏ lt (ps 0 * ps 5) (T k ps)) :: Γ
    have hg : Δ ⊢[PRAAx] monus (T k ps) (ps 0 * ps 5) ≐ succ (pred (monus (T k ps) (ps 0 * ps 5))) := Prf.andE₁ Prf.hyp0
    have hlt : Δ ⊢[PRAAx] lt (ps 0 * ps 5) (T k ps) := Prf.andE₂ Prf.hyp0
    have i := (ih.wk : Δ ⊢[PRAAx] _)
    have e₃ := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ i))
    have d := gen_descent hA.wk hB.wk hD.wk hK.wk e₃ hlt
    have hs : Δ ⊢[PRAAx] G k ps ≐ one := (congrMonus (.eqRefl _) (congrMonus (.eqRefl _) hg)).eqTrans (sg_succ _)
    refine invAt_congr (rs.wk.eqTrans (Bezout.guard_succ hg)).eqSymm (ts.wk.eqTrans (Bezout.guard_succ hg)).eqSymm
      ((cs.wk.eqTrans (congrAdd (.eqRefl _) hs))).eqSymm ?_
    have hX := X_succ (Γ := Δ) ps (C k ps)
    have hY := Y_succ (Γ := Δ) ps (C k ps)
    have hX' := (congrX ps (succ_eq_add_one (C k ps)).eqSymm).eqTrans hX
    have hY' := (congrY ps (succ_eq_add_one (C k ps)).eqSymm).eqTrans hY
    have hR := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ d))))
    have hT' := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ d))))
    refine .andI (alg_x (Prf.andE₁ i) hR hT' hX' hY') (.andI (alg_y (Prf.andE₁ (Prf.andE₂ i)) hR hT' hX' hY')
      (.andI (Prf.andE₁ d) (.andI ?_ ?_)))
    · -- `t' + k + 1 ≤ t + k ≤ y` (the first disjunct contradicts `A K < t`).
      refine .orE (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ i)))) ?_ ?_
      · exact le_lt_absurd _ Prf.hyp0 hlt.wk
      · refine .orI₂ (le_trans ?_ Prf.hyp0)
        have l := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ d)))
        have w := eq_add_of_le (l.wk (ψ := le (T k ps + k) (ps 4)))
        refine le_of_eq_add (d := monus (T k ps) (succ (tt (ps 0) (ps 1) (ps 2) (R k ps) (T k ps)))) ?_
        refine withEq w fun e => ?_
        apply deriveNat; ipra_simps; rw [e]; ring
    · have l := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ i)))
      exact (succ_monus_succ _ _).eqTrans l |> fun h => le_congr (succ_eq_add_one _) (.eqRefl _) h

/-- `thm:general` for either sign of `N`: `(x, y) = (r, t) uᶜ`, `c ≤ y`, with a seed of norm `N` in the box `t ≤ A K`,
`r ≤ D A K + K`. -/
theorem general {s : Bool} {ps : Fin 6 → PTm n} (hA : Γ ⊢[PRAAx] ps 0 * ps 0 ≐ one + ps 2 * (ps 1 * ps 1))
    (hB : Γ ⊢[PRAAx] ps 1 ≐ succ (pred (ps 1))) (hD : Γ ⊢[PRAAx] ps 2 ≐ succ (pred (ps 2)))
    (hK : Γ ⊢[PRAAx] ps 5 ≐ succ (pred (ps 5))) (hx : Γ ⊢[PRAAx] Nm s (ps 2) (ps 5) (ps 3) (ps 4)) :
    Γ ⊢[PRAAx] (ps 3 ≐ Xp (C (ps 4) ps) (p3 ps) * R (ps 4) ps + ps 2 * (Yp (C (ps 4) ps) (p3 ps) * T (ps 4) ps)) ⋏
      ((ps 4 ≐ Yp (C (ps 4) ps) (p3 ps) * R (ps 4) ps + Xp (C (ps 4) ps) (p3 ps) * T (ps 4) ps) ⋏
      (Nm s (ps 2) (ps 5) (R (ps 4) ps) (T (ps 4) ps) ⋏ (le (T (ps 4) ps) (ps 0 * ps 5) ⋏
      (le (R (ps 4) ps) (ps 2 * (ps 0 * ps 5) + ps 5) ⋏ le (C (ps 4) ps) (ps 4))))) := by
  have hall : Γ ⊢[PRAAx] Fm.all (Inv s (fun i => Syn.shift (ps i)) (var 0)) := by
    refine PRA.qfInd _ (by cases s <;> exact ⟨trivial, trivial, trivial, ⟨le_QF _ _, le_QF _ _⟩, le_QF _ _⟩) ?_ ?_
    · have e₁ : (fun i => Syn.subst (Syn.inst zero) (Syn.shift (ps i))) = ps := by
        funext i; simp [Syn.subst_inst_shift]
      rw [subst_Inv, e₁, show Syn.subst (Syn.inst zero) (var 0 : PTm (n + 1)) = zero by simp]
      refine invAt_congr (R_zero ps).eqSymm (T_zero ps).eqSymm (C_zero ps).eqSymm ?_
      refine .andI ?_ (.andI ?_ (.andI hx (.andI (.orI₂ (le_congr (add_zero _).eqSymm (.eqRefl _) (le_refl _))) (le_refl _))))
      · refine withEq (X_zero (Γ := Γ) ps) fun e₁ => withEq (Y_zero (Γ := Γ) ps) fun e₂ => ?_
        apply deriveNat; ipra_simps; rw [e₁, e₂]; ring
      · refine withEq (X_zero (Γ := Γ) ps) fun e₁ => withEq (Y_zero (Γ := Γ) ps) fun e₂ => ?_
        apply deriveNat; ipra_simps; rw [e₁, e₂]; ring
    · have e₁ : (fun i => Syn.subst (Syn.repl (succ (var 0))) (Syn.shift (ps i))) = fun i => Syn.shift (ps i) := by
        funext i; simp
      rw [subst_Inv, e₁, show Syn.subst (Syn.repl (succ (var 0))) (var 0 : PTm (n + 1)) = succ (var 0) by simp]
      have hA' := hA.shift
      have hB' := hB.shift
      have hD' := hD.shift
      have hK' := hK.shift
      simp only [Fm.shift, Fm.subst_eq, PTm.subst_mul, PTm.subst_add, PTm.subst_pred,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hA' hB' hD' hK'
      exact inv_step (ps := fun i => Syn.shift (ps i)) hA'.wk hB'.wk hD'.wk hK'.wk Prf.hyp0
  have h := Prf.allE (ps 4) hall
  have e₁ : (fun i => Syn.subst (Syn.inst (ps 4)) (Syn.shift (ps i))) = ps := by
    funext i; simp [Syn.subst_inst_shift]
  rw [subst_Inv, e₁, show Syn.subst (Syn.inst (ps 4)) (var 0 : PTm (n + 1)) = ps 4 by simp] at h
  -- The residual is in the box `t ≤ A K`.
  have ht : Γ ⊢[PRAAx] le (T (ps 4) ps) (ps 0 * ps 5) := by
    refine .orE (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))) Prf.hyp0 ?_
    have w := eq_add_of_le (Prf.hyp0 : (le (T (ps 4) ps + ps 4) (ps 4) :: Γ) ⊢[PRAAx] _)
    have z : (le (T (ps 4) ps + ps 4) (ps 4) :: Γ) ⊢[PRAAx] T (ps 4) ps ≐ zero := by
      refine add_eq_zero_left (y := monus (ps 4) (T (ps 4) ps + ps 4)) (add_right_cancel (c := ps 4) ?_)
      refine withEq w fun e => ?_
      ipra_lc -e
    exact le_congr z.eqSymm (.eqRefl _) (zero_le _)
  have hn := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))
  have hr : Γ ⊢[PRAAx] le (R (ps 4) ps) (ps 2 * (ps 0 * ps 5) + ps 5) := by
    refine le_of_sq_le (le_trans ?_ (seed_square hD hK))
    cases s
    · exact le_trans (le_add_right _ _) (le_congr hn.eqSymm (.eqRefl _) (le_trans (le_mul_mono (le_refl _) (le_mul_mono ht ht)) (le_add_right _ _)))
    · exact le_congr hn.eqSymm (.eqRefl _) (add_le_add_right _ (le_mul_mono (le_refl _) (le_mul_mono ht ht)))
  exact .andI (Prf.andE₁ h) (.andI (Prf.andE₁ (Prf.andE₂ h)) (.andI hn (.andI ht (.andI hr
    (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))))))

/-- `thm:general` (N > 0): `(x, y) = (r, t) uᶜ`, `c ≤ y`, with a seed of norm `N` in the box `t ≤ A K`,
`r ≤ D A K + K`. -/
theorem general_pos {ps : Fin 6 → PTm n} (hA : Γ ⊢[PRAAx] ps 0 * ps 0 ≐ one + ps 2 * (ps 1 * ps 1))
    (hB : Γ ⊢[PRAAx] ps 1 ≐ succ (pred (ps 1))) (hD : Γ ⊢[PRAAx] ps 2 ≐ succ (pred (ps 2)))
    (hK : Γ ⊢[PRAAx] ps 5 ≐ succ (pred (ps 5))) (hx : Γ ⊢[PRAAx] ps 3 * ps 3 ≐ ps 2 * (ps 4 * ps 4) + ps 5) :
    Γ ⊢[PRAAx] (ps 3 ≐ Xp (C (ps 4) ps) (p3 ps) * R (ps 4) ps + ps 2 * (Yp (C (ps 4) ps) (p3 ps) * T (ps 4) ps)) ⋏
      ((ps 4 ≐ Yp (C (ps 4) ps) (p3 ps) * R (ps 4) ps + Xp (C (ps 4) ps) (p3 ps) * T (ps 4) ps) ⋏
      ((R (ps 4) ps * R (ps 4) ps ≐ ps 2 * (T (ps 4) ps * T (ps 4) ps) + ps 5) ⋏ (le (T (ps 4) ps) (ps 0 * ps 5) ⋏
      (le (R (ps 4) ps) (ps 2 * (ps 0 * ps 5) + ps 5) ⋏ le (C (ps 4) ps) (ps 4))))) :=
  general (s := true) hA hB hD hK hx

/-- `thm:general` (N < 0): `(x, y) = (r, t) uᶜ`, `c ≤ y`, with a seed of norm `N` in the box `t ≤ A K`,
`r ≤ D A K + K`. -/
theorem general_neg {ps : Fin 6 → PTm n} (hA : Γ ⊢[PRAAx] ps 0 * ps 0 ≐ one + ps 2 * (ps 1 * ps 1))
    (hB : Γ ⊢[PRAAx] ps 1 ≐ succ (pred (ps 1))) (hD : Γ ⊢[PRAAx] ps 2 ≐ succ (pred (ps 2)))
    (hK : Γ ⊢[PRAAx] ps 5 ≐ succ (pred (ps 5))) (hx : Γ ⊢[PRAAx] ps 3 * ps 3 + ps 5 ≐ ps 2 * (ps 4 * ps 4)) :
    Γ ⊢[PRAAx] (ps 3 ≐ Xp (C (ps 4) ps) (p3 ps) * R (ps 4) ps + ps 2 * (Yp (C (ps 4) ps) (p3 ps) * T (ps 4) ps)) ⋏
      ((ps 4 ≐ Yp (C (ps 4) ps) (p3 ps) * R (ps 4) ps + Xp (C (ps 4) ps) (p3 ps) * T (ps 4) ps) ⋏
      ((R (ps 4) ps * R (ps 4) ps + ps 5 ≐ ps 2 * (T (ps 4) ps * T (ps 4) ps)) ⋏ (le (T (ps 4) ps) (ps 0 * ps 5) ⋏
      (le (R (ps 4) ps) (ps 2 * (ps 0 * ps 5) + ps 5) ⋏ le (C (ps 4) ps) (ps 4))))) :=
  general (s := false) hA hB hD hK hx

/-- `thm:general` (N > 0), converse: every seed of norm `N` times a power of `u` is a solution. -/
theorem seed_pos {A B D K r t : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B)) (hs : Γ ⊢[PRAAx] r * r ≐ D * (t * t) + K)
    (c : PTm n) :
    Γ ⊢[PRAAx] (Xp c ![A, B, D] * r + D * (Yp c ![A, B, D] * t)) * (Xp c ![A, B, D] * r + D * (Yp c ![A, B, D] * t)) ≐
      D * ((Yp c ![A, B, D] * r + Xp c ![A, B, D] * t) * (Yp c ![A, B, D] * r + Xp c ![A, B, D] * t)) + K := by
  have pw := Recurrences.pell_powers_at c ![A, B, D] (hA.eqTrans (add_comm _ _))
  ipra_lc (𝔞 r * 𝔞 r - 𝔞 D * 𝔞 t * 𝔞 t) * natEq pw + natEq hs

/-- `thm:general` (N < 0), converse: every seed of norm `N` times a power of `u` is a solution. -/
theorem seed_neg {A B D K r t : PTm n} (hA : Γ ⊢[PRAAx] A * A ≐ one + D * (B * B)) (hs : Γ ⊢[PRAAx] r * r + K ≐ D * (t * t))
    (c : PTm n) :
    Γ ⊢[PRAAx] (Xp c ![A, B, D] * r + D * (Yp c ![A, B, D] * t)) * (Xp c ![A, B, D] * r + D * (Yp c ![A, B, D] * t)) + K ≐
      D * ((Yp c ![A, B, D] * r + Xp c ![A, B, D] * t) * (Yp c ![A, B, D] * r + Xp c ![A, B, D] * t)) := by
  have pw := Recurrences.pell_powers_at c ![A, B, D] (hA.eqTrans (add_comm _ _))
  ipra_lc (𝔞 r * 𝔞 r - 𝔞 D * 𝔞 t * 𝔞 t) * natEq pw + natEq hs

end Signed

end LeanProofs.IPRA.DiophantineNumberTheory.PellGeneral
