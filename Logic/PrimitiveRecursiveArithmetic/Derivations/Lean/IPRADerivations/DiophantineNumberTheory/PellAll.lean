import IPRADerivations.DiophantineNumberTheory.PellDescent
import IPRADerivations.DiophantineNumberTheory.Recurrences
import IPRADerivations.AnalyticNumberTheory.Fermat
import IPRADerivations.Algebra.CubeRootTwo

/-!
# All solutions of Pell's equation

Packet: `diophantine-number-theory/pell_ipra_2026-11-15`, Theorem `thm:powers`.

Let `u = (A, B)` be a fundamental solution: `A² = 1 + D B²`, `B ≥ 1`, and `B ≤ y` for every
solution `x² = 1 + D y²` with `y ≥ 1` (`minimal D B`). Then every solution `(x, y)` equals
`(X_c, Y_c) = uᶜ` (the powers of `Recurrences`) for the exponent `c = C(y) ≤ y`, which is
an explicit PR term.

As in the paper, a state machine runs `y` stages. The state is the residual pair `(r, t)`
and a counter `c`, initially `(x, y)` and `0`. A stage with `t > 0` applies the unit descent
(`PellDescent.unit_descent`) and increments `c`; a stage with `t = 0` changes nothing. The
quantifier-free invariant `(x, y) = uᶜ (r, t)`, `r² = 1 + D t²`, `t = 0 ∨ t + k ≤ y`,
`c ≤ k` is proved by induction on the stage `k`. At stage `y` the residual is `(1, 0)`.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.PellAll

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.Coprime
open LeanProofs.IPRA.DiophantineNumberTheory.PellDescent
open LeanProofs.IPRA.Algebra.CubeRootTwo (sg sg_zero sg_succ)
open LeanProofs.IPRA.AnalyticNumberTheory.Fermat (subst_up_shift')

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-- The powers `uᵐ = (X_m, Y_m)` of `Recurrences`. -/
abbrev Xp (m : PTm n) (ps : Fin 3 → PTm n) : PTm n := Recurrences.X m ps
abbrev Yp (m : PTm n) (ps : Fin 3 → PTm n) : PTm n := Recurrences.Y m ps

/-! ## The state machine; step variables `0 = j`, `1 = r`, `2 = ⟨t, c⟩`, `3 = A`, `4 = B`,
`5 = D`, `6 = x`, `7 = y` -/

abbrev tW : PTm 8 := fstT (var 2)
abbrev rStep : PTm 8 := sg tW * monus (var 3 * var 1) (var 5 * (var 4 * tW)) + monus one (sg tW) * var 1
abbrev wStep : PTm 8 :=
  pairT (sg tW * monus (var 3 * tW) (var 4 * var 1) + monus one (sg tW) * tW) (sndT (var 2) + sg tW)

/-- The residual first coordinate, for parameters `ps = (A, B, D, x, y)`. -/
abbrev R (k : PTm n) (ps : Fin 5 → PTm n) : PTm n := sim₁ (var 3) (pairT (var 4) zero) rStep wStep k ps
abbrev W (k : PTm n) (ps : Fin 5 → PTm n) : PTm n := sim₂ (var 3) (pairT (var 4) zero) rStep wStep k ps
/-- The residual second coordinate and the counter. -/
abbrev T (k : PTm n) (ps : Fin 5 → PTm n) : PTm n := fstT (W k ps)
abbrev C (k : PTm n) (ps : Fin 5 → PTm n) : PTm n := sndT (W k ps)
/-- The parameters `(A, B, D)` of the powers. -/
abbrev p3 (ps : Fin 5 → PTm n) : Fin 3 → PTm n := fun i => ps (Fin.castLE (by omega) i)

section Equations

variable (ps : Fin 5 → PTm n)

theorem R_zero : Γ ⊢[PRAAx] R zero ps ≐ ps 3 := by
  simpa using sim₁_zero (Γ := Γ) (var 3 : PTm 5) (pairT (var 4) zero) rStep wStep ps

theorem W_zero : Γ ⊢[PRAAx] W zero ps ≐ pairT (ps 4) zero := by
  simpa using sim₂_zero (Γ := Γ) (var 3 : PTm 5) (pairT (var 4) zero) rStep wStep ps

theorem T_zero : Γ ⊢[PRAAx] T zero ps ≐ ps 4 := (W_zero ps).fstE
theorem C_zero : Γ ⊢[PRAAx] C zero ps ≐ zero := (W_zero ps).sndE

theorem R_succ (k : PTm n) : Γ ⊢[PRAAx] R (succ k) ps ≐
    sg (T k ps) * monus (ps 0 * R k ps) (ps 2 * (ps 1 * T k ps)) + monus one (sg (T k ps)) * R k ps := by
  simpa only [PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_fstT,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    Fin.cases_zero, finCases_one, finCases_two, finCases_three, finCases_four, finCases_five] using
    sim₁_succ (Γ := Γ) (var 3 : PTm 5) (pairT (var 4) zero) rStep wStep ps k

theorem W_succ (k : PTm n) : Γ ⊢[PRAAx] W (succ k) ps ≐
    pairT (sg (T k ps) * monus (ps 0 * T k ps) (ps 1 * R k ps) + monus one (sg (T k ps)) * T k ps)
      (C k ps + sg (T k ps)) := by
  simpa only [PTm.subst_add, PTm.subst_mul, PTm.subst_monus, subst_fstT, subst_sndT, subst_pairT,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var,
    Fin.cases_zero, finCases_one, finCases_two, finCases_three, finCases_four] using
    sim₂_succ (Γ := Γ) (var 3 : PTm 5) (pairT (var 4) zero) rStep wStep ps k

theorem T_succ (k : PTm n) : Γ ⊢[PRAAx] T (succ k) ps ≐
    sg (T k ps) * monus (ps 0 * T k ps) (ps 1 * R k ps) + monus one (sg (T k ps)) * T k ps :=
  (W_succ ps k).fstE

theorem C_succ (k : PTm n) : Γ ⊢[PRAAx] C (succ k) ps ≐ C k ps + sg (T k ps) :=
  (W_succ ps k).sndE

/-- The powers: `X_{m+1} = A X_m + D B Y_m`, `Y_{m+1} = B X_m + A Y_m`. -/
theorem X_succ (m : PTm n) : Γ ⊢[PRAAx] Xp (succ m) (p3 ps) ≐
    ps 0 * Xp m (p3 ps) + ps 2 * (ps 1 * Yp m (p3 ps)) :=
  Recurrences.X_succ m (p3 ps)

theorem Y_succ (m : PTm n) : Γ ⊢[PRAAx] Yp (succ m) (p3 ps) ≐
    ps 1 * Xp m (p3 ps) + ps 0 * Yp m (p3 ps) :=
  Recurrences.Y_succ m (p3 ps)

theorem X_zero : Γ ⊢[PRAAx] Xp zero (p3 ps) ≐ one :=
  Recurrences.X_zero (p3 ps)

theorem Y_zero : Γ ⊢[PRAAx] Yp zero (p3 ps) ≐ zero :=
  Recurrences.Y_zero (p3 ps)

theorem congrX {m m' : PTm n} (h : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] Xp m (p3 ps) ≐ Xp m' (p3 ps) :=
  Recurrences.congrX (p3 ps) h

theorem congrY {m m' : PTm n} (h : Γ ⊢[PRAAx] m ≐ m') : Γ ⊢[PRAAx] Yp m (p3 ps) ≐ Yp m' (p3 ps) :=
  Recurrences.congrY (p3 ps) h

end Equations

/-! ## Minimality -/

/-- `(A, B)` is minimal: every solution with `y ≥ 1` has `B ≤ y`. Under the binders,
`1 = x`, `0 = y`. -/
abbrev minimal (D B : PTm n) : Fm PTm n :=
  Fm.all (Fm.all ((var 1 * var 1 ≐ one + Syn.shift (Syn.shift D) * (var 0 * var 0)) ⟶
    (var 0 ≐ succ (pred (var 0))) ⟶ le (Syn.shift (Syn.shift B)) (var 0)))

ipra_subst minimal [subst_up_shift', Syn.up]

theorem minimal_at {D B : PTm n} (h : Γ ⊢[PRAAx] minimal D B) (x y : PTm n) :
    Γ ⊢[PRAAx] (x * x ≐ one + D * (y * y)) ⟶ (y ≐ succ (pred y)) ⟶ le B y := by
  have h₁ := Prf.allE y (Prf.allE x h)
  simpa [subst_up_shift', Syn.up] using h₁

/-! ## The invariant -/

/-- The invariant for a residual `(r, t)`, counter `c` and stage `k`. -/
abbrev InvAt (ps : Fin 5 → PTm n) (r t c k : PTm n) : Fm PTm n :=
  (ps 3 ≐ Xp c (p3 ps) * r + ps 2 * (Yp c (p3 ps) * t)) ⋏ (ps 4 ≐ Yp c (p3 ps) * r + Xp c (p3 ps) * t) ⋏
    (r * r ≐ one + ps 2 * (t * t)) ⋏ ((t ≐ zero) ⋎ le (t + k) (ps 4)) ⋏ le c k

abbrev Inv (ps : Fin 5 → PTm n) (k : PTm n) : Fm PTm n := InvAt ps (R k ps) (T k ps) (C k ps) k

theorem subst_Inv {m : ℕ} (σ : Fin n → PTm m) (ps : Fin 5 → PTm n) (k : PTm n) :
    (Inv ps k).subst σ = Inv (fun i => Syn.subst σ (ps i)) (Syn.subst σ k) := by
  simp [Inv, InvAt, p3]

theorem invAt_congr {ps : Fin 5 → PTm n} {r r' t t' c c' k : PTm n} (hr : Γ ⊢[PRAAx] r ≐ r')
    (ht : Γ ⊢[PRAAx] t ≐ t') (hc : Γ ⊢[PRAAx] c ≐ c') (h : Γ ⊢[PRAAx] InvAt ps r t c k) :
    Γ ⊢[PRAAx] InvAt ps r' t' c' k := by
  have hX := congrX ps hc
  have hY := congrY ps hc
  refine .andI ?_ (.andI ?_ (.andI ?_ (.andI ?_ ?_)))
  · exact (Prf.andE₁ h).eqTrans (congrAdd (congrMul hX hr) (congrMul (.eqRefl _) (congrMul hY ht)))
  · exact (Prf.andE₁ (Prf.andE₂ h)).eqTrans (congrAdd (congrMul hY hr) (congrMul hX ht))
  · exact (congrMul hr hr).eqSymm.eqTrans ((Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))).eqTrans
      (congrAdd (.eqRefl _) (congrMul (.eqRefl _) (congrMul ht ht))))
  · refine .orE (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))) ?_ ?_
    · exact .orI₁ (ht.wk.eqSymm.eqTrans Prf.hyp0)
    · exact .orI₂ (le_congr (congrAdd ht.wk (.eqRefl _)) (.eqRefl _) Prf.hyp0)
  · exact le_congr hc (.eqRefl _) (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h))))

theorem alg_x {x Xc Yc Xc' Yc' A B D R T r t : PTm n}
    (e₁ : Γ ⊢[PRAAx] x ≐ Xc * R + D * (Yc * T)) (hR : Γ ⊢[PRAAx] R ≐ A * r + D * (B * t))
    (hT : Γ ⊢[PRAAx] T ≐ B * r + A * t) (hX : Γ ⊢[PRAAx] Xc' ≐ A * Xc + D * (B * Yc))
    (hY : Γ ⊢[PRAAx] Yc' ≐ B * Xc + A * Yc) : Γ ⊢[PRAAx] x ≐ Xc' * r + D * (Yc' * t) := by
  ipra_lc natEq e₁ + Groth.ι (IPRA.Q.mk Γ Xc) * natEq hR +
    Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ Yc) * natEq hT - Groth.ι (IPRA.Q.mk Γ r) * natEq hX -
    Groth.ι (IPRA.Q.mk Γ D) * Groth.ι (IPRA.Q.mk Γ t) * natEq hY

theorem alg_y {y Xc Yc Xc' Yc' A B D R T r t : PTm n}
    (e₂ : Γ ⊢[PRAAx] y ≐ Yc * R + Xc * T) (hR : Γ ⊢[PRAAx] R ≐ A * r + D * (B * t))
    (hT : Γ ⊢[PRAAx] T ≐ B * r + A * t) (hX : Γ ⊢[PRAAx] Xc' ≐ A * Xc + D * (B * Yc))
    (hY : Γ ⊢[PRAAx] Yc' ≐ B * Xc + A * Yc) : Γ ⊢[PRAAx] y ≐ Yc' * r + Xc' * t := by
  ipra_lc natEq e₂ + Groth.ι (IPRA.Q.mk Γ Yc) * natEq hR + Groth.ι (IPRA.Q.mk Γ Xc) * natEq hT -
    Groth.ι (IPRA.Q.mk Γ t) * natEq hX - Groth.ι (IPRA.Q.mk Γ r) * natEq hY

/-- The zeroth Pell power reconstructs the original coordinates. -/
theorem reconstruct_zero (p : Fin 3 → PTm n) (x y : PTm n) :
    Γ ⊢[PRAAx] (x ≐ Xp zero p * x + p 2 * (Yp zero p * y)) ⋏
      (y ≐ Yp zero p * x + Xp zero p * y) := by
  have hX := Recurrences.X_zero (Γ := Γ) p
  have hY := Recurrences.Y_zero (Γ := Γ) p
  refine .andI ?_ ?_
  · exact ((congrAdd (congrMul hX (.eqRefl _)) (congrMul (.eqRefl _) (congrMul hY (.eqRefl _)))).eqTrans
      (by ipra_ring)).eqSymm
  · exact ((congrAdd (congrMul hY (.eqRefl _)) (congrMul hX (.eqRefl _))).eqTrans (by ipra_ring)).eqSymm

/-- A unit descent preserves reconstruction after one increase of the exponent. -/
theorem reconstruct_succ (p : Fin 3 → PTm n) {c x y R T r t : PTm n}
    (hx : Γ ⊢[PRAAx] x ≐ Xp c p * R + p 2 * (Yp c p * T))
    (hy : Γ ⊢[PRAAx] y ≐ Yp c p * R + Xp c p * T)
    (hr : Γ ⊢[PRAAx] R ≐ p 0 * r + p 2 * (p 1 * t))
    (ht : Γ ⊢[PRAAx] T ≐ p 1 * r + p 0 * t) :
    Γ ⊢[PRAAx] (x ≐ Xp (c + one) p * r + p 2 * (Yp (c + one) p * t)) ⋏
      (y ≐ Yp (c + one) p * r + Xp (c + one) p * t) := by
  have e := (succ_eq_add_one (Γ := Γ) c).eqSymm
  have hX := (Recurrences.congrX p e).eqTrans (Recurrences.X_succ c p)
  have hY := (Recurrences.congrY p e).eqTrans (Recurrences.Y_succ c p)
  exact .andI (alg_x hx hr ht hX hY) (alg_y hy hr ht hX hY)

/-- The residual drops by enough to pay for one additional descent stage. -/
theorem descent_index {t' t : PTm n} (k : PTm n) (h : Γ ⊢[PRAAx] lt t' t) :
    Γ ⊢[PRAAx] le (t' + succ k) (t + k) :=
  le_congr (by ipra_ring) (.eqRefl _) (add_le_add_right k h)

/-- When all stages are spent, a residual still bounded by the original index is zero. -/
theorem terminal_residual_zero {t y : PTm n} (h : Γ ⊢[PRAAx] le (t + y) y) :
    Γ ⊢[PRAAx] t ≐ zero := by
  apply add_eq_zero_left (y := monus y (t + y))
  ipra_lc -natEq (eq_add_of_le h)

/-- One stage preserves the invariant. -/
theorem inv_step {ps : Fin 5 → PTm n} {k : PTm n} (hA : Γ ⊢[PRAAx] ps 0 * ps 0 ≐ one + ps 2 * (ps 1 * ps 1))
    (hB : Γ ⊢[PRAAx] ps 1 ≐ succ (pred (ps 1))) (hmin : Γ ⊢[PRAAx] minimal (ps 2) (ps 1))
    (ih : Γ ⊢[PRAAx] Inv ps k) : Γ ⊢[PRAAx] Inv ps (succ k) := by
  have rs := R_succ (Γ := Γ) ps k
  have ts := T_succ (Γ := Γ) ps k
  have cs := C_succ (Γ := Γ) ps k
  refine .orE (zero_or_succ (T k ps)) ?_ ?_
  · -- `t = 0`: nothing changes.
    have hs : ((T k ps ≐ zero) :: Γ) ⊢[PRAAx] sg (T k ps) ≐ zero := (Common.congrSg Prf.hyp0).eqTrans sg_zero
    refine invAt_congr (r := R k ps) (t := T k ps) (c := C k ps) (rs.wk.eqTrans (Bezout.guard_zero Prf.hyp0)).eqSymm
      (ts.wk.eqTrans (Bezout.guard_zero Prf.hyp0)).eqSymm
      ((cs.wk.eqTrans ((congrAdd (.eqRefl _) hs).eqTrans (add_zero _))).eqSymm) ?_
    have i := ih.wk (ψ := T k ps ≐ zero)
    refine .andI (Prf.andE₁ i) (.andI (Prf.andE₁ (Prf.andE₂ i)) (.andI (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ i)))
      (.andI (.orI₁ Prf.hyp0) ?_)))
    exact le_trans (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ i)))) (le_succ_self _)
  · -- `t > 0`: one unit descent.
    have i := ih.wk (ψ := T k ps ≐ succ (pred (T k ps)))
    have hT : ((T k ps ≐ succ (pred (T k ps))) :: Γ) ⊢[PRAAx] T k ps ≐ succ (pred (T k ps)) := Prf.hyp0
    have e₃ := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ i))
    have hBT := Prf.impE (Prf.impE (minimal_at hmin.wk (R k ps) (T k ps)) e₃) hT
    have d := unit_descent hA.wk hB.wk e₃ hBT
    have hs := (Common.congrSg hT).eqTrans (sg_succ _)
    refine invAt_congr (rs.wk.eqTrans (Bezout.guard_succ hT)).eqSymm (ts.wk.eqTrans (Bezout.guard_succ hT)).eqSymm
      ((cs.wk.eqTrans (congrAdd (.eqRefl _) hs))).eqSymm ?_
    have hR := Prf.andE₁ (Prf.andE₂ (Prf.andE₂ d))
    have hT' := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ d))
    have xy := reconstruct_succ (p3 ps) i.andE₁ i.andE₂.andE₁ hR hT'
    refine .andI xy.andE₁ (.andI xy.andE₂ (.andI (Prf.andE₁ d) (.andI ?_ ?_)))
    · -- `t' + k + 1 ≤ t + k ≤ y`.
      refine .orE (Prf.andE₁ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ i)))) ?_ ?_
      · exact succ_ne_zero' _ (hT.wk.eqSymm.eqTrans Prf.hyp0)
      · exact .orI₂ (le_trans (descent_index k d.andE₂.andE₁.wk) Prf.hyp0)
    · have l := Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ i)))
      exact (succ_monus_succ _ _).eqTrans l |> fun h => le_congr (succ_eq_add_one _) (.eqRefl _) h

/-! ## The theorem -/

/-- At stage `y` the residual is `(1, 0)`, so `(x, y) = (X_c, Y_c)` with `c ≤ y`. -/
theorem pell_all_at {ps : Fin 5 → PTm n} (hA : Γ ⊢[PRAAx] ps 0 * ps 0 ≐ one + ps 2 * (ps 1 * ps 1))
    (hB : Γ ⊢[PRAAx] ps 1 ≐ succ (pred (ps 1))) (hmin : Γ ⊢[PRAAx] minimal (ps 2) (ps 1))
    (hx : Γ ⊢[PRAAx] ps 3 * ps 3 ≐ one + ps 2 * (ps 4 * ps 4)) :
    Γ ⊢[PRAAx] (ps 3 ≐ Xp (C (ps 4) ps) (p3 ps)) ⋏ (ps 4 ≐ Yp (C (ps 4) ps) (p3 ps)) ⋏ le (C (ps 4) ps) (ps 4) := by
  have hall : Γ ⊢[PRAAx] Fm.all (Inv (fun i => Syn.shift (ps i)) (var 0)) := by
    refine PRA.qfInd _ ⟨trivial, trivial, trivial, ⟨trivial, le_QF _ _⟩, le_QF _ _⟩ ?_ ?_
    · simp only [subst_Inv, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero]
      refine invAt_congr (R_zero ps).eqSymm (T_zero ps).eqSymm (C_zero ps).eqSymm ?_
      have xy := reconstruct_zero (Γ := Γ) (p3 ps) (ps 3) (ps 4)
      exact .andI xy.andE₁ (.andI xy.andE₂ (.andI hx
        (.andI (.orI₂ (le_congr (add_zero _).eqSymm (.eqRefl _) (le_refl _))) (le_refl _))))
    · simp only [subst_Inv, subst_repl_shift, Syn.subst_var, Syn.repl_zero]
      have hA' := hA.shift
      have hB' := hB.shift
      have hm' := hmin.shift
      simp only [Fm.shift, Fm.subst_eq, PTm.subst_mul, PTm.subst_add, PTm.subst_pred, subst_minimal,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at hA' hB' hm'
      exact inv_step (ps := fun i => Syn.shift (ps i)) hA'.wk hB'.wk hm'.wk Prf.hyp0
  have h := Prf.allE (ps 4) hall
  simp only [subst_Inv, Syn.subst_inst_shift, Syn.subst_var, Syn.inst_zero] at h
  -- The residual second coordinate is `0`, so the first is `1`.
  have ht : Γ ⊢[PRAAx] T (ps 4) ps ≐ zero := by
    exact .orE h.andE₂.andE₂.andE₂.andE₁ Prf.hyp0 (terminal_residual_zero Prf.hyp0)
  have hr : Γ ⊢[PRAAx] R (ps 4) ps ≐ one := by
    refine sq_inj ((Prf.andE₁ (Prf.andE₂ (Prf.andE₂ h))).eqTrans ?_)
    refine withEq ht fun e => ?_
    apply deriveNat; ipra_simps; rw [e]; ring
  refine .andI ?_ (.andI ?_ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ (Prf.andE₂ h)))))
  · refine (Prf.andE₁ h).eqTrans ?_
    refine withEq hr fun e₁ => withEq ht fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂]; ring
  · refine (Prf.andE₁ (Prf.andE₂ h)).eqTrans ?_
    refine withEq hr fun e₁ => withEq ht fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂]; ring

/-- Theorem `thm:powers`; variables `0 = A`, `1 = B`, `2 = D`, `3 = x`, `4 = y`. -/
abbrev pellAllFormula : Fm PTm 5 :=
  (var 0 * var 0 ≐ one + var 2 * (var 1 * var 1)) ⟶ (var 1 ≐ succ (pred (var 1))) ⟶
    minimal (var 2) (var 1) ⟶ (var 3 * var 3 ≐ one + var 2 * (var 4 * var 4)) ⟶
    (var 3 ≐ Xp (C (var 4) var) (p3 var)) ⋏ (var 4 ≐ Yp (C (var 4) var) (p3 var)) ⋏ le (C (var 4) var) (var 4)

theorem pell_all : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5 pellAllFormula :=
  closeUniv 5 (.impI (.impI (.impI (.impI (pell_all_at (ps := var) hyp3 hyp2 Prf.hyp1 Prf.hyp0)))))
where
  hyp3 {Δ : List (Fm PTm 5)} {a b c φ : Fm PTm 5} : (a :: b :: c :: φ :: Δ) ⊢[PRAAx] φ := Prf.hyp (by simp)

end LeanProofs.IPRA.DiophantineNumberTheory.PellAll

export_ipra DiophantineNumberTheory.PellAll (minimal)
