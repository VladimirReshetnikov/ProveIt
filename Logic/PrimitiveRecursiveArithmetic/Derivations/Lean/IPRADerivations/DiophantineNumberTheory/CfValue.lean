import IPRADerivations.DiophantineNumberTheory.CfReal

/-!
# The value identity `[a_0; a_1, …, a_m] = p_m/q_m`

Packet: `diophantine-number-theory/number_theory_ipra_2026-11-22`, `chapters/diophantine.tex`, `dio:continuants`:
"For every valid finite coefficient list, `[a_0; …, a_n] = p_n/q_n`, `p_n q_{n−1} − p_{n−1} q_n = (−1)^{n+1}`."

The nested fraction is evaluated from the inside out, as a pair `(numerator, denominator)`: `bk 0 = (a_m, 1)`,
`bk (j+1) = (a_{m−j−1} X + Y, X)` for `bk j = (X, Y)`; `nest m = bk m m`. The coefficients are those of
`CfReal`, `a_i = a′(i) + [i ≥ 1]` (`Av`), for an arbitrary unary primitive recursive `a′`.

* `Pre`, **`pre`**: the tail matrix from index `N + 1` is the tail matrix from `N + 2` multiplied on the left by
  `[[a_{N+1}, 1], [1, 0]]`, that is, the forward continuant `K(a_{N+1}, …)` obeys the backward recursion
  `K(a_{N+1}, …) = a_{N+1} K(a_{N+2}, …) + K(a_{N+3}, …)`;
* `bk_tail`: for `j < m`, `bk j = (u, v)` for the tail matrix `uv (j+1) (m − j − 1)`;
* **`nest_value`**: `nest m = (p_m, q_m)` exactly.
-/

namespace LeanProofs.IPRA.DiophantineNumberTheory.CfValue

open_ipra exports
open LeanProofs.IPRA.DiophantineNumberTheory.HurwitzLoop (sP sQ st)
open LeanProofs.IPRA.DiophantineNumberTheory.CfReal (nx proj_matrix proj_nx co cv uv cv_zero cv_succ uv_zero uv_succ lin_origin Lin4
  subst_cv subst_uv)
open LeanProofs.IPRA.Signum (sg sg_zero sg_succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

alias congrSg' := Common.congrSg

/-! ## Prepending a coefficient -/

/-- `w₁ = [[c, 1], [1, 0]] · w` on both columns. -/
def Pre (w1 c w : PTm n) : Fm PTm n :=
  ((sP w1 ≐ c * sP w + sQ w) ⋏ (sQ w1 ≐ sP w)) ⋏ ((sP' w1 ≐ c * sP' w + sQ' w) ⋏ (sQ' w1 ≐ sP' w))

ipra_subst Pre

theorem pre_QF (w1 c w : PTm n) : (Pre w1 c w).QF := by
  simp [Pre, Fm.QF]

theorem pre_base_alg {c c' U V U' V' x1 x2 x3 x4 u v u' v' : PTm n} (ec : Γ ⊢[PRAAx] c' ≐ c)
    (h1 : Γ ⊢[PRAAx] U ≐ c' * x1 + x3) (h2 : Γ ⊢[PRAAx] V ≐ c' * x2 + x4) (h3 : Γ ⊢[PRAAx] U' ≐ x1)
    (h4 : Γ ⊢[PRAAx] V' ≐ x2)
    (e1 : Γ ⊢[PRAAx] x1 ≐ one) (e2 : Γ ⊢[PRAAx] x2 ≐ zero) (e3 : Γ ⊢[PRAAx] x3 ≐ zero) (e4 : Γ ⊢[PRAAx] x4 ≐ one)
    (f1 : Γ ⊢[PRAAx] u ≐ one) (f2 : Γ ⊢[PRAAx] v ≐ zero) (f3 : Γ ⊢[PRAAx] u' ≐ zero) (f4 : Γ ⊢[PRAAx] v' ≐ one) :
    Γ ⊢[PRAAx] ((U ≐ c * u + v) ⋏ (V ≐ u)) ⋏ ((U' ≐ c * u' + v') ⋏ (V' ≐ u')) := by
  have k1 := natEq h1; have k2 := natEq h2; have k3 := natEq h3; have k4 := natEq h4
  have j1 := natEq e1; have j2 := natEq e2; have j3 := natEq e3; have j4 := natEq e4
  have g1 := natEq f1; have g2 := natEq f2; have g3 := natEq f3; have g4 := natEq f4
  refine .andI (.andI ?_ ?_) (.andI ?_ ?_)
  · ipra_lc k1 + 𝔞 x1 * natEq ec + 𝔞 c * j1 + j3 - 𝔞 c * g1 - g2
  · ipra_lc k2 + 𝔞 x2 * natEq ec + 𝔞 c * j2 + j4 - g1
  · ipra_lc k3 + j1 - 𝔞 c * g3 - g4
  · ipra_lc k4 + j2 - g3

theorem pre_alg {c d d' U V U' V' U1 V1 U1' V1' u v u' v' u1 v1 u1' v1' : PTm n}
    (r1 : Γ ⊢[PRAAx] U ≐ c * u + v) (r2 : Γ ⊢[PRAAx] V ≐ u) (r3 : Γ ⊢[PRAAx] U' ≐ c * u' + v')
    (r4 : Γ ⊢[PRAAx] V' ≐ u')
    (h1 : Γ ⊢[PRAAx] U1 ≐ d * U + U') (h2 : Γ ⊢[PRAAx] V1 ≐ d * V + V') (h3 : Γ ⊢[PRAAx] U1' ≐ U)
    (h4 : Γ ⊢[PRAAx] V1' ≐ V)
    (ed : Γ ⊢[PRAAx] d' ≐ d)
    (g1 : Γ ⊢[PRAAx] u1 ≐ d' * u + u') (g2 : Γ ⊢[PRAAx] v1 ≐ d' * v + v') (g3 : Γ ⊢[PRAAx] u1' ≐ u)
    (g4 : Γ ⊢[PRAAx] v1' ≐ v) :
    Γ ⊢[PRAAx] ((U1 ≐ c * u1 + v1) ⋏ (V1 ≐ u1)) ⋏ ((U1' ≐ c * u1' + v1') ⋏ (V1' ≐ u1')) := by
  have s1 := natEq r1; have s2 := natEq r2; have s3 := natEq r3; have s4 := natEq r4
  have k1 := natEq h1; have k2 := natEq h2; have k3 := natEq h3; have k4 := natEq h4
  have t1 := natEq g1; have t2 := natEq g2; have t3 := natEq g3; have t4 := natEq g4
  refine .andI (.andI ?_ ?_) (.andI ?_ ?_)
  · ipra_lc k1 + 𝔞 d * s1 + s3 - 𝔞 c * (t1 + 𝔞 u * natEq ed) - (t2 + 𝔞 v * natEq ed)
  · ipra_lc k2 + 𝔞 d * s2 + s4 - (t1 + 𝔞 u * natEq ed)
  · ipra_lc k3 + s1 - 𝔞 c * t3 - t4
  · ipra_lc k4 + s2 - t3

variable {a' : PR 1}

theorem pre_base (N : PTm n) : Γ ⊢[PRAAx] Pre (uv a' (succ zero) N) (co a' (succ N)) (uv a' zero (succ N)) := by
  obtain ⟨h1, h2, h3, h4⟩ := proj_nx (uv_succ (Γ := Γ) (a' := a') zero N)
  obtain ⟨p1, p2, p3, p4⟩ := proj_matrix (uv_zero (Γ := Γ) (a' := a') N)
  obtain ⟨q1, q2, q3, q4⟩ := proj_matrix (uv_zero (Γ := Γ) (a' := a') (succ N))
  have ec : Γ ⊢[PRAAx] co a' (succ (N + zero)) ≐ co a' (succ N) := congrSucc (congrAp1 a' (congrSucc (add_zero N)))
  unfold Pre
  exact pre_base_alg ec h1 h2 h3 h4 p1 p2 p3 p4 q1 q2 q3 q4

theorem pre_step {N k : PTm n} (ih : Γ ⊢[PRAAx] Pre (uv a' (succ k) N) (co a' (succ N)) (uv a' k (succ N))) :
    Γ ⊢[PRAAx] Pre (uv a' (succ (succ k)) N) (co a' (succ N)) (uv a' (succ k) (succ N)) := by
  obtain ⟨h1, h2, h3, h4⟩ := proj_nx (uv_succ (Γ := Γ) (a' := a') (succ k) N)
  obtain ⟨g1, g2, g3, g4⟩ := proj_nx (uv_succ (Γ := Γ) (a' := a') k (succ N))
  have E : Γ ⊢[PRAAx] succ N + k ≐ N + succ k := by ipra_ring
  have ed : Γ ⊢[PRAAx] co a' (succ (succ N + k)) ≐ co a' (succ (N + succ k)) :=
    congrSucc (congrAp1 a' (congrSucc E))
  unfold Pre at ih ⊢
  exact pre_alg (Prf.andE₁ (Prf.andE₁ ih)) (Prf.andE₂ (Prf.andE₁ ih)) (Prf.andE₁ (Prf.andE₂ ih))
    (Prf.andE₂ (Prf.andE₂ ih)) h1 h2 h3 h4 ed g1 g2 g3 g4

/-- **Prepending a coefficient**: `uv (k+1) N = [[a_{N+1}, 1], [1, 0]] · uv k (N+1)`. -/
theorem pre (k N : PTm n) : Γ ⊢[PRAAx] Pre (uv a' (succ k) N) (co a' (succ N)) (uv a' k (succ N)) := by
  have hall : Γ ⊢[PRAAx] Fm.all (Pre (uv a' (succ (var 0)) (Syn.shift N)) (co a' (succ (Syn.shift N)))
      (uv a' (var 0) (succ (Syn.shift N)))) := by
    refine PRA.qfInd _ (pre_QF _ _ _) ?_ ?_
    · simp only [subst_Pre, subst_uv, subst_ap1, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact pre_base N
    · simp only [subst_Pre, subst_uv, subst_ap1, Syn.subst_var, Syn.repl_zero, subst_repl_shift,
        ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero]
      exact pre_step Prf.hyp0
  have h2 := Prf.allE k hall
  simp only [subst_Pre, subst_uv, subst_ap1, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at h2
  exact h2

/-! ## The nested fraction -/

variable (a')

/-- `a_i = a′(i) + [i ≥ 1]`. -/
abbrev Av (i : PTm n) : PTm n := ap1 a' i + sg i

/-- The inward step over `0 = j`, `1 = (X, Y)`, `2 = m`: `(a_{m−j−1} X + Y, X)`. -/
abbrev bkStep : PTm 3 := pairT (Av a' (monus (var 2) (succ (var 0))) * fstT (var 1) + sndT (var 1)) (fstT (var 1))

abbrev bkInit : PTm 1 := pairT (Av a' (var 0)) one

/-- `[a_{m−j}; …, a_m]` as a pair. -/
abbrev bk (j m : PTm n) : PTm n := ap2 (rec2 (bkInit a') (bkStep a')) j m

/-- **The nested fraction** `[a_0; a_1, …, a_m]` as a pair `(numerator, denominator)`. -/
abbrev nest (m : PTm n) : PTm n := bk a' m m

variable {a'}

@[simp] theorem subst_bk {k : ℕ} (σ : Fin n → PTm k) (j m : PTm n) :
    Syn.subst σ (bk a' j m) = bk a' (Syn.subst σ j) (Syn.subst σ m) := by
  simp [bk]

theorem bk_zero (m : PTm n) : Γ ⊢[PRAAx] bk a' zero m ≐ pairT (Av a' m) one := by
  simpa using rec2_zero (Γ := Γ) (bkInit a') (bkStep a') m

theorem bk_succ (j m : PTm n) : Γ ⊢[PRAAx] bk a' (succ j) m ≐
    pairT (Av a' (monus m (succ j)) * fstT (bk a' j m) + sndT (bk a' j m)) (fstT (bk a' j m)) := by
  have h := rec2_succ (Γ := Γ) (bkInit a') (bkStep a') j m
  have e : Syn.subst ![j, ap2 (rec2 (bkInit a') (bkStep a')) j m, m] (bkStep a') =
      pairT (Av a' (monus m (succ j)) * fstT (ap2 (rec2 (bkInit a') (bkStep a')) j m) +
        sndT (ap2 (rec2 (bkInit a') (bkStep a')) j m)) (fstT (ap2 (rec2 (bkInit a') (bkStep a')) j m)) := by
    simp [bkStep, Av]
  rw [e] at h; exact h

/-- `m ≥ j + 2` gives `(m − (j + 2)) + 1 = m − (j + 1)`. -/
theorem monus_step {j m : PTm n} (h : Γ ⊢[PRAAx] le (succ (succ j)) m) :
    Γ ⊢[PRAAx] succ (monus m (succ (succ j))) ≐ monus m (succ j) := by
  have e := eq_add_of_le h
  have e1 : Γ ⊢[PRAAx] m ≐ succ (monus m (succ (succ j))) + succ j := by
    ipra_lc natEq e
  have e2 : Γ ⊢[PRAAx] succ j ≐ zero + succ j := by apply deriveNat; ipra_simps; try ring
  exact ((congrMonus e1 e2).eqTrans ((monus_add_add _ _ _).eqTrans (monus_zero _))).eqSymm

/-- `m ≥ 1` gives `(m − 1) + 1 = m`. -/
theorem monus_one {m : PTm n} (h : Γ ⊢[PRAAx] le one m) : Γ ⊢[PRAAx] succ (monus m one) ≐ m := by
  ipra_lc -natEq (eq_add_of_le h)

/-- Reindex the shorter tail and its coefficient for one inward step. -/
theorem tail_step_data {j m : PTm n} (hj : Γ ⊢[PRAAx] lt (succ j) m) :
    let N := monus m (succ (succ j))
    let k := monus m (succ j)
    (Γ ⊢[PRAAx] Pre (uv a' (succ (succ j)) N) (co a' (succ N)) (uv a' (succ j) (succ N))) ∧
      (Γ ⊢[PRAAx] uv a' (succ j) (succ N) ≐ uv a' (succ j) k) ∧
      (Γ ⊢[PRAAx] sg k ≐ one) ∧
      (Γ ⊢[PRAAx] co a' (succ N) ≐ succ (ap1 a' k)) := by
  have h := monus_step hj
  exact ⟨pre _ _, congrAp2 _ (.eqRefl _) h, (congrSg' h.eqSymm).eqTrans (sg_succ _), congrSucc (congrAp1 a' h)⟩

theorem tail_base_alg {F S A Z s c U V x1 x2 x3 x4 : PTm n} (hF : Γ ⊢[PRAAx] F ≐ A) (hS : Γ ⊢[PRAAx] S ≐ one)
    (hA : Γ ⊢[PRAAx] A ≐ Z + s) (hs : Γ ⊢[PRAAx] s ≐ one) (hc : Γ ⊢[PRAAx] c ≐ succ Z)
    (h1 : Γ ⊢[PRAAx] U ≐ c * x1 + x3) (h2 : Γ ⊢[PRAAx] V ≐ c * x2 + x4)
    (e1 : Γ ⊢[PRAAx] x1 ≐ one) (e2 : Γ ⊢[PRAAx] x2 ≐ zero) (e3 : Γ ⊢[PRAAx] x3 ≐ zero) (e4 : Γ ⊢[PRAAx] x4 ≐ one) :
    Γ ⊢[PRAAx] (F ≐ U) ⋏ (S ≐ V) := by
  have f := natEq hF; have g := natEq hS; have a := natEq hA; have b := natEq hs; have k := natEq hc
  have k1 := natEq h1; have k2 := natEq h2
  have j1 := natEq e1; have j2 := natEq e2; have j3 := natEq e3; have j4 := natEq e4
  refine .andI ?_ ?_
  · ipra_lc f + a + b - k1 - 𝔞 c * j1 - j3 - k
  · ipra_lc g - k2 - 𝔞 c * j2 - j4

theorem tail_step_alg {F S A X Y Z s c U V P Q : PTm n} (hb1 : Γ ⊢[PRAAx] F ≐ A * X + Y) (hb2 : Γ ⊢[PRAAx] S ≐ X)
    (ihX : Γ ⊢[PRAAx] X ≐ P) (ihY : Γ ⊢[PRAAx] Y ≐ Q) (pr1 : Γ ⊢[PRAAx] U ≐ c * P + Q) (pr2 : Γ ⊢[PRAAx] V ≐ P)
    (hA : Γ ⊢[PRAAx] A ≐ Z + s) (hs : Γ ⊢[PRAAx] s ≐ one) (hc : Γ ⊢[PRAAx] c ≐ succ Z) :
    Γ ⊢[PRAAx] (F ≐ U) ⋏ (S ≐ V) := by
  have b1 := natEq hb1; have b2 := natEq hb2; have x := natEq ihX; have y := natEq ihY
  have q1 := natEq pr1; have q2 := natEq pr2; have a := natEq hA; have b := natEq hs; have k := natEq hc
  refine .andI ?_ ?_
  · ipra_lc b1 + 𝔞 X * a + 𝔞 X * b + (𝔞 Z + 1) * x + y - q1 - 𝔞 P * k
  · ipra_lc b2 + x - q2

/-- The claim at stage `j`: `bk j m` is the first column of `uv (j+1) (m − j − 1)`. -/
abbrev TailF (j m : PTm n) : Fm PTm n :=
  lt j m ⟶ ((fstT (bk a' j m) ≐ sP (uv a' (succ j) (monus m (succ j)))) ⋏
    (sndT (bk a' j m) ≐ sQ (uv a' (succ j) (monus m (succ j)))))

theorem tail_zero {m : PTm n} (hm : Γ ⊢[PRAAx] lt zero m) :
    Γ ⊢[PRAAx] (fstT (bk a' zero m) ≐ sP (uv a' (succ zero) (monus m (succ zero)))) ⋏
      (sndT (bk a' zero m) ≐ sQ (uv a' (succ zero) (monus m (succ zero)))) := by
  have m1 := monus_one hm
  obtain ⟨h1, h2, _, _⟩ := proj_nx (uv_succ (Γ := Γ) (a' := a') zero (monus m one))
  obtain ⟨p1, p2, p3, p4⟩ := proj_matrix (uv_zero (Γ := Γ) (a' := a') (monus m one))
  have b := bk_zero (Γ := Γ) (a' := a') m
  have hF : Γ ⊢[PRAAx] fstT (bk a' zero m) ≐ Av a' m := (congrFst b).eqTrans (fst_pair _ _)
  have hS : Γ ⊢[PRAAx] sndT (bk a' zero m) ≐ one := (congrSnd b).eqTrans (snd_pair _ _)
  have hs : Γ ⊢[PRAAx] sg m ≐ one := (congrSg' m1.eqSymm).eqTrans (sg_succ _)
  have hc : Γ ⊢[PRAAx] co a' (succ (monus m one + zero)) ≐ succ (ap1 a' m) :=
    congrSucc (congrAp1 a' ((congrSucc (add_zero _)).eqTrans m1))
  exact tail_base_alg hF hS (.eqRefl _) hs hc h1 h2 p1 p2 p3 p4

theorem tail_succ {j m : PTm n} (hj : Γ ⊢[PRAAx] lt (succ j) m)
    (ih : Γ ⊢[PRAAx] (fstT (bk a' j m) ≐ sP (uv a' (succ j) (monus m (succ j)))) ⋏
      (sndT (bk a' j m) ≐ sQ (uv a' (succ j) (monus m (succ j))))) :
    Γ ⊢[PRAAx] (fstT (bk a' (succ j) m) ≐ sP (uv a' (succ (succ j)) (monus m (succ (succ j))))) ⋏
      (sndT (bk a' (succ j) m) ≐ sQ (uv a' (succ (succ j)) (monus m (succ (succ j))))) := by
  obtain ⟨P, eUV, hs, hc⟩ := tail_step_data (a' := a') hj
  unfold Pre at P
  have b := bk_succ (Γ := Γ) (a' := a') j m
  have hb1 := (congrFst b).eqTrans (fst_pair _ _)
  have hb2 := (congrSnd b).eqTrans (snd_pair _ _)
  have ihX := (Prf.andE₁ ih).eqTrans (congrFst eUV).eqSymm
  have ihY := (Prf.andE₂ ih).eqTrans (congrFst (congrSnd eUV)).eqSymm
  exact tail_step_alg hb1 hb2 ihX ihY (Prf.andE₁ (Prf.andE₁ P)) (Prf.andE₂ (Prf.andE₁ P)) (.eqRefl _) hs hc

theorem tail_all (m : PTm n) : Γ ⊢[PRAAx] Fm.all (TailF (a' := a') (var 0) (Syn.shift m)) := by
  refine PRA.qfInd _ ⟨lt_QF _ _, trivial, trivial⟩ ?_ ?_
  · simp only [TailF, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_lt, subst_bk, subst_uv, subst_fstT,
      subst_sndT, subst_ap2, PTm.subst_monus, subst_le, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero]
    exact .impI (tail_zero Prf.hyp0)
  · simp only [TailF, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_lt, subst_bk, subst_uv, subst_fstT,
      subst_sndT, subst_ap2, PTm.subst_monus, subst_le, Syn.subst_var, Syn.repl_zero, subst_repl_shift, ConciseIPRA.PTm.subst_succ,
      ConciseIPRA.PTm.subst_zero]
    refine .impI ?_
    let Θ : List (Fm PTm (n + 1)) := lt (succ (var 0)) (Syn.shift m) ::
      TailF (a' := a') (var 0) (Syn.shift m) :: Γ.map Fm.shift
    have hj : Θ ⊢[PRAAx] lt (succ (var 0)) (Syn.shift m) := Prf.hyp0
    have ih := Prf.impE (Prf.hyp1 : Θ ⊢[PRAAx] TailF (a' := a') (var 0) (Syn.shift m))
      (le_of_lt hj)
    exact tail_succ hj ih

theorem bk_tail {j m : PTm n} (h : Γ ⊢[PRAAx] lt j m) :
    Γ ⊢[PRAAx] (fstT (bk a' j m) ≐ sP (uv a' (succ j) (monus m (succ j)))) ⋏
      (sndT (bk a' j m) ≐ sQ (uv a' (succ j) (monus m (succ j)))) := by
  have h2 := Prf.allE j (tail_all (Γ := Γ) (a' := a') m)
  simp only [TailF, Fm.subst_imp, Fm.subst_and, Fm.subst_eq, subst_lt, subst_bk, subst_uv, subst_fstT,
    subst_sndT, subst_ap2, PTm.subst_monus, subst_le, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ,
    ConciseIPRA.PTm.subst_zero] at h2
  exact .impE h2 h

theorem last_alg {F S A X Y U V a0 x1 x2 x3 x4 : PTm n} (hb1 : Γ ⊢[PRAAx] F ≐ A * X + Y) (hb2 : Γ ⊢[PRAAx] S ≐ X)
    (hA : Γ ⊢[PRAAx] A ≐ a0) (l1 : Γ ⊢[PRAAx] U ≐ X * x1 + Y * x3) (l2 : Γ ⊢[PRAAx] V ≐ X * x2 + Y * x4)
    (e1 : Γ ⊢[PRAAx] x1 ≐ a0) (e2 : Γ ⊢[PRAAx] x2 ≐ one) (e3 : Γ ⊢[PRAAx] x3 ≐ one) (e4 : Γ ⊢[PRAAx] x4 ≐ zero) :
    Γ ⊢[PRAAx] (F ≐ U) ⋏ (S ≐ V) := by
  have b1 := natEq hb1; have b2 := natEq hb2; have a := natEq hA; have q1 := natEq l1; have q2 := natEq l2
  have j1 := natEq e1; have j2 := natEq e2; have j3 := natEq e3; have j4 := natEq e4
  refine .andI ?_ ?_
  · ipra_lc b1 + 𝔞 X * a - q1 - 𝔞 X * j1 - 𝔞 Y * j3
  · ipra_lc b2 - q2 - 𝔞 X * j2 - 𝔞 Y * j4

/-- **`dio:continuants`, the value identity**: the nested fraction `[a_0; a_1, …, a_m]`, evaluated from the
inside out, is exactly `(p_m, q_m)`. -/
theorem nest_value (m : PTm n) :
    Γ ⊢[PRAAx] (fstT (nest a' m) ≐ sP (cv a' m)) ⋏ (sndT (nest a' m) ≐ sQ (cv a' m)) := by
  refine .orE (zero_or_succ m) ?_ ?_
  · -- `m = 0`
    have hm : ((m ≐ zero) :: Γ) ⊢[PRAAx] m ≐ zero := Prf.hyp0
    have eb : ((m ≐ zero) :: Γ) ⊢[PRAAx] nest a' m ≐ pairT (Av a' zero) one :=
      (congrAp2 _ hm hm).eqTrans (bk_zero zero)
    have ec : ((m ≐ zero) :: Γ) ⊢[PRAAx] cv a' m ≐ st (ap1 a' zero) one one zero :=
      (congrAp2 _ hm (.eqRefl _)).eqTrans cv_zero
    have F : ((m ≐ zero) :: Γ) ⊢[PRAAx] fstT (nest a' m) ≐ ap1 a' zero + sg zero :=
      (congrFst eb).eqTrans (fst_pair _ _)
    have S : ((m ≐ zero) :: Γ) ⊢[PRAAx] sndT (nest a' m) ≐ one := (congrSnd eb).eqTrans (snd_pair _ _)
    obtain ⟨P, Q, _, _⟩ := proj_matrix ec
    have f := natEq F; have p := natEq P
    refine .andI ?_ (S.eqTrans Q.eqSymm)
    ipra_lc f - p + natEq (sg_zero (Γ := ((m ≐ zero) :: Γ)) (n := n))
  · -- `m = m' + 1`
    let Θ : List (Fm PTm n) := (m ≐ succ (pred m)) :: Γ
    have hm : Θ ⊢[PRAAx] m ≐ succ (pred m) := Prf.hyp0
    have hlt : Θ ⊢[PRAAx] lt (pred m) m := le_congr (.eqRefl _) hm.eqSymm (le_refl _)
    have T := bk_tail (a' := a') hlt
    -- the last inward step
    have eb : Θ ⊢[PRAAx] nest a' m ≐ bk a' (succ (pred m)) m := congrAp2 _ hm (.eqRefl _)
    have b := eb.eqTrans (bk_succ (pred m) m)
    have hb1 := (congrFst b).eqTrans (fst_pair _ _)
    have hb2 := (congrSnd b).eqTrans (snd_pair _ _)
    have e0 : Θ ⊢[PRAAx] monus m (succ (pred m)) ≐ zero := (congrMonus (.eqRefl _) hm.eqSymm).eqTrans (monus_self _)
    have hA : Θ ⊢[PRAAx] Av a' (monus m (succ (pred m))) ≐ ap1 a' zero := by
      ipra_lc natEq (congrAp1 a' e0) + natEq ((congrSg' e0).eqTrans (sg_zero (n := n)))
    -- the tail matrix of `a_1, …, a_m` and `cv m = uv m 0 · cv 0`
    have eU : Θ ⊢[PRAAx] uv a' (succ (pred m)) (monus m (succ (pred m))) ≐ uv a' m zero :=
      congrAp2 _ hm.eqSymm e0
    have X := (Prf.andE₁ T).eqTrans (congrFst eU)
    have Y := (Prf.andE₂ T).eqTrans (congrFst (congrSnd eU))
    have L := lin_origin (Γ := Θ) (a' := a') m
    unfold Lin4 at L
    obtain ⟨c1, c2, c3, c4⟩ := proj_matrix (cv_zero (Γ := Θ) (a' := a'))
    exact last_alg hb1 hb2 hA
      (L.andE₁.andE₁.eqTrans (congrAdd (congrMul X.eqSymm (.eqRefl _)) (congrMul Y.eqSymm (.eqRefl _))))
      (L.andE₁.andE₂.eqTrans (congrAdd (congrMul X.eqSymm (.eqRefl _)) (congrMul Y.eqSymm (.eqRefl _)))) c1 c2 c3 c4

end LeanProofs.IPRA.DiophantineNumberTheory.CfValue
