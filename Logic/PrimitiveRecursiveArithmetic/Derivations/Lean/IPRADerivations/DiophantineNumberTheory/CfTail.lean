import IPRADerivations.DiophantineNumberTheory.CfValue

/-!
# The nested fraction with a rational tail

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/diophantine.tex`, `dio:cf-error`:
"For a positive rational `t` and `n ≥ 0`, `[a_0; …, a_n, t] = (t p_n + p_{n−1})/(t q_n + q_{n−1})`."

For `t = u/v` the nested fraction `[a_0; …, a_m, u/v]` is evaluated from the inside out as a pair: `bt 0 = (u, v)`,
`bt (j+1) = (a_{m−j} X + Y, X)`; `ext m u v = bt (m+1)`. The coefficients are those of `CfReal`/`CfValue`.

* `bt_claim`: for `j < m`, `bt (j+1) = W · (u, v)` for the tail matrix `W = uv (j+1) (m−j−1)` of `a_{m−j}, …, a_m`;
* **`ext_value`**: `ext m u v = (u p_m + v p_{m−1}, u q_m + v q_{m−1})` exactly: the nested fraction is the
  matrix column, which `ContinuedFractionTail` (`err_even`, `err_odd`, …) takes as its value.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.CfTail

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.HurwitzLoop (sP sQ st)
open LeanProofs.IPRA.DiophantineNumberTheory.CfReal (nx proj_matrix proj_nx co cv uv cv_zero cv_succ uv_zero uv_succ lin_origin Lin4
  subst_cv subst_uv)
open LeanProofs.IPRA.DiophantineNumberTheory.CfValue (Pre Av congrSg' tail_step_data monus_one)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Algebra -/

theorem tb_base_alg {F S A Z s c u v P1 Q1 P1' Q1' x1 x2 x3 x4 : PTm n}
    (hF : Γ ⊢[PRAAx] F ≐ A * u + v) (hS : Γ ⊢[PRAAx] S ≐ u) (hA : Γ ⊢[PRAAx] A ≐ Z + s) (hs : Γ ⊢[PRAAx] s ≐ one)
    (hc : Γ ⊢[PRAAx] c ≐ succ Z)
    (h1 : Γ ⊢[PRAAx] P1 ≐ c * x1 + x3) (h2 : Γ ⊢[PRAAx] Q1 ≐ c * x2 + x4) (h3 : Γ ⊢[PRAAx] P1' ≐ x1)
    (h4 : Γ ⊢[PRAAx] Q1' ≐ x2)
    (e1 : Γ ⊢[PRAAx] x1 ≐ one) (e2 : Γ ⊢[PRAAx] x2 ≐ zero) (e3 : Γ ⊢[PRAAx] x3 ≐ zero) (e4 : Γ ⊢[PRAAx] x4 ≐ one) :
    Γ ⊢[PRAAx] (F ≐ P1 * u + P1' * v) ⋏ (S ≐ Q1 * u + Q1' * v) := by
  have f := natEq hF; have g := natEq hS; have a := natEq hA; have b := natEq hs; have k := natEq hc
  have k1 := natEq h1; have k2 := natEq h2; have k3 := natEq h3; have k4 := natEq h4
  have j1 := natEq e1; have j2 := natEq e2; have j3 := natEq e3; have j4 := natEq e4
  refine .andI ?_ ?_
  · ipra_lc f + 𝔞 u * a + 𝔞 u * b - 𝔞 u * k1 - 𝔞 u * 𝔞 c * j1 - 𝔞 u * j3 - 𝔞 u * k - 𝔞 v * k3 - 𝔞 v * j1
  · ipra_lc g - 𝔞 u * k2 - 𝔞 u * 𝔞 c * j2 - 𝔞 u * j4 - 𝔞 v * k4 - 𝔞 v * j2

theorem tb_step_alg {F S A X Y Z s c u v P Q P' Q' U1 V1 U1' V1' : PTm n}
    (hb1 : Γ ⊢[PRAAx] F ≐ A * X + Y) (hb2 : Γ ⊢[PRAAx] S ≐ X)
    (ihX : Γ ⊢[PRAAx] X ≐ P * u + P' * v) (ihY : Γ ⊢[PRAAx] Y ≐ Q * u + Q' * v)
    (r1 : Γ ⊢[PRAAx] U1 ≐ c * P + Q) (r2 : Γ ⊢[PRAAx] V1 ≐ P) (r3 : Γ ⊢[PRAAx] U1' ≐ c * P' + Q')
    (r4 : Γ ⊢[PRAAx] V1' ≐ P')
    (hA : Γ ⊢[PRAAx] A ≐ Z + s) (hs : Γ ⊢[PRAAx] s ≐ one) (hc : Γ ⊢[PRAAx] c ≐ succ Z) :
    Γ ⊢[PRAAx] (F ≐ U1 * u + U1' * v) ⋏ (S ≐ V1 * u + V1' * v) := by
  have b1 := natEq hb1; have b2 := natEq hb2; have x := natEq ihX; have y := natEq ihY
  have q1 := natEq r1; have q2 := natEq r2; have q3 := natEq r3; have q4 := natEq r4
  have a := natEq hA; have b := natEq hs; have k := natEq hc
  refine .andI ?_ ?_
  · ipra_lc b1 + 𝔞 X * a + 𝔞 X * b - 𝔞 u * q1 - 𝔞 v * q3 + 𝔞 c * x + y - 𝔞 X * k
  · ipra_lc b2 + x - 𝔞 u * q2 - 𝔞 v * q4

theorem tb_last_alg {F S A X Y a0 U V U' V' u v x1 x2 x3 x4 pm qm pm' qm' : PTm n}
    (hb1 : Γ ⊢[PRAAx] F ≐ A * X + Y) (hb2 : Γ ⊢[PRAAx] S ≐ X) (hA : Γ ⊢[PRAAx] A ≐ a0)
    (ihX : Γ ⊢[PRAAx] X ≐ U * u + U' * v) (ihY : Γ ⊢[PRAAx] Y ≐ V * u + V' * v)
    (l1 : Γ ⊢[PRAAx] pm ≐ U * x1 + V * x3) (l2 : Γ ⊢[PRAAx] qm ≐ U * x2 + V * x4)
    (l3 : Γ ⊢[PRAAx] pm' ≐ U' * x1 + V' * x3) (l4 : Γ ⊢[PRAAx] qm' ≐ U' * x2 + V' * x4)
    (e1 : Γ ⊢[PRAAx] x1 ≐ a0) (e2 : Γ ⊢[PRAAx] x2 ≐ one) (e3 : Γ ⊢[PRAAx] x3 ≐ one) (e4 : Γ ⊢[PRAAx] x4 ≐ zero) :
    Γ ⊢[PRAAx] (F ≐ u * pm + v * pm') ⋏ (S ≐ u * qm + v * qm') := by
  have b1 := natEq hb1; have b2 := natEq hb2; have a := natEq hA; have x := natEq ihX; have y := natEq ihY
  have m1 := natEq l1; have m2 := natEq l2; have m3 := natEq l3; have m4 := natEq l4
  have j1 := natEq e1; have j2 := natEq e2; have j3 := natEq e3; have j4 := natEq e4
  refine .andI ?_ ?_
  · ipra_lc b1 + 𝔞 X * a + 𝔞 a0 * x + y - 𝔞 u * m1 - 𝔞 u * 𝔞 U * j1 - 𝔞 u * 𝔞 V * j3 - 𝔞 v * m3 - 𝔞 v * 𝔞 U' * j1 -
      𝔞 v * 𝔞 V' * j3
  · ipra_lc b2 + x - 𝔞 u * m2 - 𝔞 u * 𝔞 U * j2 - 𝔞 u * 𝔞 V * j4 - 𝔞 v * m4 - 𝔞 v * 𝔞 U' * j2 - 𝔞 v * 𝔞 V' * j4

theorem tb_zero_alg {F S A X Y a0 u v pm qm pm' qm' : PTm n}
    (hb1 : Γ ⊢[PRAAx] F ≐ A * X + Y) (hb2 : Γ ⊢[PRAAx] S ≐ X) (hA : Γ ⊢[PRAAx] A ≐ a0)
    (hX : Γ ⊢[PRAAx] X ≐ u) (hY : Γ ⊢[PRAAx] Y ≐ v)
    (e1 : Γ ⊢[PRAAx] pm ≐ a0) (e2 : Γ ⊢[PRAAx] qm ≐ one) (e3 : Γ ⊢[PRAAx] pm' ≐ one) (e4 : Γ ⊢[PRAAx] qm' ≐ zero) :
    Γ ⊢[PRAAx] (F ≐ u * pm + v * pm') ⋏ (S ≐ u * qm + v * qm') := by
  have b1 := natEq hb1; have b2 := natEq hb2; have a := natEq hA; have x := natEq hX; have y := natEq hY
  have j1 := natEq e1; have j2 := natEq e2; have j3 := natEq e3; have j4 := natEq e4
  refine .andI ?_ ?_
  · ipra_lc b1 + 𝔞 X * a + 𝔞 a0 * x + y - 𝔞 u * j1 - 𝔞 v * j3
  · ipra_lc b2 + x - 𝔞 u * j2 - 𝔞 v * j4

/-! ## The evaluation -/

variable (a' : PR 1)

/-- The inward step over `0 = j`, `1 = (X, Y)`, `2 = ⟨m, ⟨u, v⟩⟩`: `(a_{m−j} X + Y, X)`. -/
abbrev btStep : PTm 3 := pairT (Av a' (monus (fstT (var 2)) (var 0)) * fstT (var 1) + sndT (var 1)) (fstT (var 1))

abbrev btInit : PTm 1 := sndT (var 0)

/-- `[a_{m−j+1}; …, a_m, u/v]` as a pair (for `j ≥ 1`), `bt 0 = (u, v)`. -/
abbrev bt (j m u v : PTm n) : PTm n := ap2 (rec2 btInit (btStep a')) j (pairT m (pairT u v))

/-- **The nested fraction `[a_0; …, a_m, u/v]`** as a pair. -/
abbrev ext (m u v : PTm n) : PTm n := bt a' (succ m) m u v

variable {a'}

@[simp] theorem subst_bt {k : ℕ} (σ : Fin n → PTm k) (j m u v : PTm n) :
    Syn.subst σ (bt a' j m u v) = bt a' (Syn.subst σ j) (Syn.subst σ m) (Syn.subst σ u) (Syn.subst σ v) := by
  simp [bt]

theorem congrAv {x y : PTm n} (h : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] Av a' x ≐ Av a' y :=
  congrAdd (congrAp1 a' h) (congrSg' h)

theorem bt_zero (m u v : PTm n) : Γ ⊢[PRAAx] bt a' zero m u v ≐ pairT u v := by
  have h := rec2_zero (Γ := Γ) btInit (btStep a') (pairT m (pairT u v))
  have e : Syn.subst ![pairT m (pairT u v)] (btInit : PTm 1) = sndT (pairT m (pairT u v)) := by simp
  rw [e] at h
  exact h.eqTrans (snd_pair _ _)

/-- One inward step, with the projections: `fst = a_{m−j} X + Y`, `snd = X`. -/
theorem bt_succ (j m u v : PTm n) :
    (Γ ⊢[PRAAx] fstT (bt a' (succ j) m u v) ≐
        Av a' (monus (fstT (pairT m (pairT u v))) j) * fstT (bt a' j m u v) + sndT (bt a' j m u v)) ∧
      (Γ ⊢[PRAAx] sndT (bt a' (succ j) m u v) ≐ fstT (bt a' j m u v)) := by
  have h := rec2_succ (Γ := Γ) btInit (btStep a') j (pairT m (pairT u v))
  have e : Syn.subst ![j, ap2 (rec2 btInit (btStep a')) j (pairT m (pairT u v)), pairT m (pairT u v)] (btStep a') =
      pairT (Av a' (monus (fstT (pairT m (pairT u v))) j) * fstT (ap2 (rec2 btInit (btStep a')) j (pairT m (pairT u v))) +
        sndT (ap2 (rec2 btInit (btStep a')) j (pairT m (pairT u v))))
        (fstT (ap2 (rec2 btInit (btStep a')) j (pairT m (pairT u v)))) := by
    simp [btStep, Av]
  rw [e] at h
  exact ⟨(congrFst h).eqTrans (fst_pair _ _), (congrSnd h).eqTrans (snd_pair _ _)⟩

theorem coef_eq {u v : PTm n} (m j : PTm n) : Γ ⊢[PRAAx] Av a' (monus (fstT (pairT m (pairT u v))) j) ≐ Av a' (monus m j) :=
  congrAv (congrMonus (fst_pair _ _) (.eqRefl _))

/-- The claim at stage `j`. -/
abbrev TailT (j m u v : PTm n) : Fm PTm n :=
  lt j m ⟶
    ((fstT (bt a' (succ j) m u v) ≐ sP (uv a' (succ j) (monus m (succ j))) * u +
        sP' (uv a' (succ j) (monus m (succ j))) * v) ⋏
      (sndT (bt a' (succ j) m u v) ≐ sQ (uv a' (succ j) (monus m (succ j))) * u +
        sQ' (uv a' (succ j) (monus m (succ j))) * v))

theorem claim_zero {m u v : PTm n} (hm : Γ ⊢[PRAAx] lt zero m) :
    Γ ⊢[PRAAx] (fstT (bt a' (succ zero) m u v) ≐ sP (uv a' (succ zero) (monus m (succ zero))) * u +
        sP' (uv a' (succ zero) (monus m (succ zero))) * v) ⋏
      (sndT (bt a' (succ zero) m u v) ≐ sQ (uv a' (succ zero) (monus m (succ zero))) * u +
        sQ' (uv a' (succ zero) (monus m (succ zero))) * v) := by
  have m1 := monus_one hm
  obtain ⟨b1, b2⟩ := bt_succ (Γ := Γ) (a' := a') zero m u v
  have z := bt_zero (Γ := Γ) (a' := a') m u v
  have hX : Γ ⊢[PRAAx] fstT (bt a' zero m u v) ≐ u := (congrFst z).eqTrans (fst_pair _ _)
  have hY : Γ ⊢[PRAAx] sndT (bt a' zero m u v) ≐ v := (congrSnd z).eqTrans (snd_pair _ _)
  have hF := b1.eqTrans (congrAdd (congrMul (coef_eq m zero) hX) hY)
  have hS := b2.eqTrans hX
  have e0 : Γ ⊢[PRAAx] monus m zero ≐ succ (monus m one) := (monus_zero m).eqTrans m1.eqSymm
  have hs : Γ ⊢[PRAAx] sg (monus m zero) ≐ one := (congrSg' e0).eqTrans (sg_succ _)
  have hc : Γ ⊢[PRAAx] co a' (succ (monus m one + zero)) ≐ succ (ap1 a' (monus m zero)) :=
    congrSucc (congrAp1 a' ((congrSucc (add_zero _)).eqTrans e0.eqSymm))
  obtain ⟨h1, h2, h3, h4⟩ := proj_nx (uv_succ (Γ := Γ) (a' := a') zero (monus m one))
  obtain ⟨p1, p2, p3, p4⟩ := proj_matrix (uv_zero (Γ := Γ) (a' := a') (monus m one))
  exact tb_base_alg hF hS (.eqRefl _) hs hc h1 h2 h3 h4 p1 p2 p3 p4

theorem claim_succ {j m u v : PTm n} (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (ih : Γ ⊢[PRAAx] (fstT (bt a' (succ j) m u v) ≐ sP (uv a' (succ j) (monus m (succ j))) * u +
        sP' (uv a' (succ j) (monus m (succ j))) * v) ⋏
      (sndT (bt a' (succ j) m u v) ≐ sQ (uv a' (succ j) (monus m (succ j))) * u +
        sQ' (uv a' (succ j) (monus m (succ j))) * v)) :
    Γ ⊢[PRAAx] (fstT (bt a' (succ (succ j)) m u v) ≐ sP (uv a' (succ (succ j)) (monus m (succ (succ j)))) * u +
        sP' (uv a' (succ (succ j)) (monus m (succ (succ j)))) * v) ⋏
      (sndT (bt a' (succ (succ j)) m u v) ≐ sQ (uv a' (succ (succ j)) (monus m (succ (succ j)))) * u +
        sQ' (uv a' (succ (succ j)) (monus m (succ (succ j)))) * v) := by
  obtain ⟨P, eUV, hs, hc⟩ := tail_step_data (a' := a') hj
  unfold Pre at P
  obtain ⟨b1, b2⟩ := bt_succ (Γ := Γ) (a' := a') (succ j) m u v
  have hb1 := b1.eqTrans (congrAdd (congrMul (coef_eq m (succ j)) (.eqRefl _)) (.eqRefl _))
  have mP := congrFst eUV
  have mQ := congrFst (congrSnd eUV)
  have mP' := congrFst (congrSnd (congrSnd eUV))
  have mQ' := congrSnd (congrSnd (congrSnd eUV))
  have ihX := (Prf.andE₁ ih).eqTrans (congrAdd (congrMul mP.eqSymm (.eqRefl _)) (congrMul mP'.eqSymm (.eqRefl _)))
  have ihY := (Prf.andE₂ ih).eqTrans (congrAdd (congrMul mQ.eqSymm (.eqRefl _)) (congrMul mQ'.eqSymm (.eqRefl _)))
  exact tb_step_alg hb1 b2 ihX ihY (Prf.andE₁ (Prf.andE₁ P)) (Prf.andE₂ (Prf.andE₁ P))
    (Prf.andE₁ (Prf.andE₂ P)) (Prf.andE₂ (Prf.andE₂ P)) (.eqRefl _) hs hc

theorem claim_all (m u v : PTm n) :
    Γ ⊢[PRAAx] Fm.all (TailT (a' := a') (var 0) (Syn.shift m) (Syn.shift u) (Syn.shift v)) := by
  refine PRA.qfInd _ ⟨lt_QF _ _, trivial, trivial⟩ ?_ ?_
  · simp only [TailT, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_lt, subst_le, subst_bt, subst_uv, subst_fstT,
      subst_sndT, subst_pairT, subst_ap2, PTm.subst_monus, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    exact .impI (claim_zero Prf.hyp0)
  · simp only [TailT, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_lt, subst_le, subst_bt, subst_uv, subst_fstT,
      subst_sndT, subst_pairT, subst_ap2, PTm.subst_monus, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.repl_zero,
      subst_repl_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
    refine .impI ?_
    let Θ : List (Fm PTm (n + 1)) := lt (succ (var 0)) (Syn.shift m) ::
      TailT (a' := a') (var 0) (Syn.shift m) (Syn.shift u) (Syn.shift v) :: Γ.map Fm.shift
    have hj : Θ ⊢[PRAAx] lt (succ (var 0)) (Syn.shift m) := Prf.hyp0
    have ih := Prf.impE (Prf.hyp1 : Θ ⊢[PRAAx] TailT (a' := a') (var 0) (Syn.shift m) (Syn.shift u) (Syn.shift v))
      (le_of_lt hj)
    exact claim_succ hj ih

theorem bt_claim {j m u v : PTm n} (h : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] (fstT (bt a' (succ j) m u v) ≐ sP (uv a' (succ j) (monus m (succ j))) * u +
        sP' (uv a' (succ j) (monus m (succ j))) * v) ⋏
      (sndT (bt a' (succ j) m u v) ≐ sQ (uv a' (succ j) (monus m (succ j))) * u +
        sQ' (uv a' (succ j) (monus m (succ j))) * v) := by
  have h2 := Prf.allE j (claim_all (Γ := Γ) (a' := a') m u v)
  simp only [TailT, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_lt, subst_le, subst_bt, subst_uv, subst_fstT,
    subst_sndT, subst_pairT, subst_ap2, PTm.subst_monus, PTm.subst_add, PTm.subst_mul, Syn.subst_var, Syn.inst_zero,
    Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 h

/-- **`dio:cf-error`, the identification**: `[a_0; …, a_m, u/v] = (u p_m + v p_{m−1}, u q_m + v q_{m−1})`. -/
theorem ext_value (m u v : PTm n) :
    Γ ⊢[PRAAx] (fstT (ext a' m u v) ≐ u * sP (cv a' m) + v * sP' (cv a' m)) ⋏
      (sndT (ext a' m u v) ≐ u * sQ (cv a' m) + v * sQ' (cv a' m)) := by
  refine .orE (zero_or_succ m) ?_ ?_
  · -- `m = 0`
    let Θ : List (Fm PTm n) := (m ≐ zero) :: Γ
    have hm : Θ ⊢[PRAAx] m ≐ zero := Prf.hyp0
    obtain ⟨b1, b2⟩ := bt_succ (Γ := Θ) (a' := a') zero m u v
    have z := bt_zero (Γ := Θ) (a' := a') m u v
    have hX : Θ ⊢[PRAAx] fstT (bt a' zero m u v) ≐ u := (congrFst z).eqTrans (fst_pair _ _)
    have hY : Θ ⊢[PRAAx] sndT (bt a' zero m u v) ≐ v := (congrSnd z).eqTrans (snd_pair _ _)
    have e0 : Θ ⊢[PRAAx] monus m zero ≐ zero := (monus_zero m).eqTrans hm
    have hA : Θ ⊢[PRAAx] Av a' (monus (fstT (pairT m (pairT u v))) zero) ≐ ap1 a' zero := by
      have x := natEq ((coef_eq (Γ := Θ) (a' := a') (u := u) (v := v) m zero).eqTrans (congrAv e0))
      ipra_lc x + natEq (sg_zero (Γ := Θ) (n := n))
    have ec : Θ ⊢[PRAAx] cv a' m ≐ st (ap1 a' zero) one one zero := (congrAp2 _ hm (.eqRefl _)).eqTrans cv_zero
    obtain ⟨c1, c2, c3, c4⟩ := proj_matrix ec
    have r := tb_zero_alg b1 b2 hA hX hY c1 c2 c3 c4
    have eb1 : Θ ⊢[PRAAx] fstT (ext a' m u v) ≐ fstT (bt a' (succ zero) m u v) :=
      congrFst (congrAp2 _ (congrSucc hm) (.eqRefl _))
    have eb2 : Θ ⊢[PRAAx] sndT (ext a' m u v) ≐ sndT (bt a' (succ zero) m u v) :=
      congrSnd (congrAp2 _ (congrSucc hm) (.eqRefl _))
    exact .andI (eb1.eqTrans (Prf.andE₁ r)) (eb2.eqTrans (Prf.andE₂ r))
  · -- `m = m' + 1`
    let Θ : List (Fm PTm n) := (m ≐ succ (pred m)) :: Γ
    have hm : Θ ⊢[PRAAx] m ≐ succ (pred m) := Prf.hyp0
    have hlt : Θ ⊢[PRAAx] lt (pred m) m := le_congr (.eqRefl _) hm.eqSymm (le_refl _)
    have T := bt_claim (a' := a') (u := u) (v := v) hlt
    have eb1 : Θ ⊢[PRAAx] fstT (ext a' m u v) ≐ fstT (bt a' (succ (succ (pred m))) m u v) :=
      congrFst (congrAp2 _ (congrSucc hm) (.eqRefl _))
    have eb2 : Θ ⊢[PRAAx] sndT (ext a' m u v) ≐ sndT (bt a' (succ (succ (pred m))) m u v) :=
      congrSnd (congrAp2 _ (congrSucc hm) (.eqRefl _))
    obtain ⟨b1, b2⟩ := bt_succ (Γ := Θ) (a' := a') (succ (pred m)) m u v
    have e0 : Θ ⊢[PRAAx] monus m (succ (pred m)) ≐ zero := (congrMonus (.eqRefl _) hm.eqSymm).eqTrans (monus_self _)
    have hA : Θ ⊢[PRAAx] Av a' (monus (fstT (pairT m (pairT u v))) (succ (pred m))) ≐ ap1 a' zero := by
      have x := natEq ((coef_eq (Γ := Θ) (a' := a') (u := u) (v := v) m (succ (pred m))).eqTrans (congrAv e0))
      ipra_lc x + natEq (sg_zero (Γ := Θ) (n := n))
    have eU : Θ ⊢[PRAAx] uv a' (succ (pred m)) (monus m (succ (pred m))) ≐ uv a' m zero :=
      congrAp2 _ hm.eqSymm e0
    have X := (Prf.andE₁ T).eqTrans (congrAdd (congrMul (congrFst eU) (.eqRefl _))
      (congrMul (congrFst (congrSnd (congrSnd eU))) (.eqRefl _)))
    have Y := (Prf.andE₂ T).eqTrans (congrAdd (congrMul (congrFst (congrSnd eU)) (.eqRefl _))
      (congrMul (congrSnd (congrSnd (congrSnd eU))) (.eqRefl _)))
    have L := lin_origin (Γ := Θ) (a' := a') m
    unfold Lin4 at L
    obtain ⟨c1, c2, c3, c4⟩ := proj_matrix (cv_zero (Γ := Θ) (a' := a'))
    have r := tb_last_alg b1 b2 hA X Y L.andE₁.andE₁ L.andE₁.andE₂ L.andE₂.andE₁ L.andE₂.andE₂ c1 c2 c3 c4
    exact .andI (eb1.eqTrans (Prf.andE₁ r)) (eb2.eqTrans (Prf.andE₂ r))

end LeanProofs.IPRA.DiophantineNumberTheory.CfTail
