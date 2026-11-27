import IPRADerivations.Combinatorics.Bell

/-!
# Stirling numbers of the second kind

Packet: `combinatorics/bell_numbers_ipra` (`prop:stirling`: `S(0, 0) = 1`,
`S(n + 1, k) = k S(n, k) + S(n, k − 1)`, with `S(n, k) = 0` outside `0 ≤ k ≤ n`).

The table is defined by primitive recursion on coded rows. Row `n` is the Cantor-coded list
`R_n = ⟨S(n, n), ⟨S(n, n − 1), … ⟨S(n, 0), 0⟩⟩⟩`, read with `nth` of `Combinatorics/Bell`, and
`R_{n+1}` is built from `R_n` by an inner recursion that conses the entries `0, 1, …, n + 1`.

* `build e m x`: the list `⟨e(m − 1, x), … ⟨e(0, x), 0⟩⟩`, by recursion on `m`;
* `nth_build`: `nth(build e (M + 1) x, j) = e(M − j, x)` for `j ≤ M`, by induction on `M` of the
  quantifier-free statement that the violation count over `j ≤ M` vanishes;
* `stir N K = [K ≤ N] · nth(R_N, N − K)`;
* `stir_zero`: `S(0, 0) = 1`; `stir_succ_zero`: `S(n + 1, 0) = 0`;
  `stir_above`: `S(n, k) = 0` for `k > n`;
* `stir_succ_succ`: `S(n + 1, k + 1) = (k + 1) S(n, k + 1) + S(n, k)` for `k ≤ n`.

The identity `X^n = ∑ S(n, k) (X)_k` is `Combinatorics/StirlingPowers`.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Combinatorics.Stirling

open_ipra
open LeanProofs.IPRA.Combinatorics.Bell (iS nth iS_zero nth_pair_zero nth_pair_succ monus_monus monus_le')
open LeanProofs.IPRA.AnalyticNumberTheory.EulerProduct (eq_of_viol viol_of_eq)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

theorem congrNth {L L' j j' : PTm n} (hL : Γ ⊢[PRAAx] L ≐ L') (hj : Γ ⊢[PRAAx] j ≐ j') :
    Γ ⊢[PRAAx] nth L j ≐ nth L' j' := congrFst (congrAp2 iS hj hL)

/-! ## Lists built by consing -/

section Build

variable (e : PTm 2)

/-- The step; variables `0 = m`, `1 = build m`, `2 = x`. -/
abbrev buildStep : PTm 3 := pairT (Syn.subst ![var 0, var 2] e) (var 1)
abbrev buildF : PR 2 := rec2 zero (buildStep e)
/-- `⟨e(m − 1, x), … ⟨e(0, x), 0⟩⟩`. -/
abbrev build (m x : PTm n) : PTm n := ap2 (buildF e) m x

theorem subst_e02 (a b c : PTm n) : Syn.subst ![a, b, c] (Syn.subst ![var 0, var 2] e) = inst2 e a c := by
  simp only [inst2, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

theorem build_succ (m x : PTm n) :
    Γ ⊢[PRAAx] build e (succ m) x ≐ pairT (inst2 e m x) (build e m x) := by
  have h := rec2_succ (Γ := Γ) zero (buildStep e) m x
  have e' : Syn.subst ![m, build e m x, x] (buildStep e) = pairT (inst2 e m x) (build e m x) := by
    simp only [buildStep, subst_pairT, subst_e02, Syn.subst_var]
    rfl
  rw [e'] at h
  exact h

/-- `e(fst y − j, snd y)`. -/
abbrev mB : PTm 2 := Syn.subst ![monus (fstT (var 1)) (var 0), sndT (var 1)] e

theorem subst_mB (j y : PTm n) :
    Syn.subst ![j, y] (mB e) = inst2 e (monus (fstT y) j) (sndT y) := by
  simp only [mB, inst2, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

/-- `1 ∸ [nth(build (fst y + 1) (snd y), j) = e(fst y − j, snd y)]`. -/
abbrev violB : PTm 2 :=
  monus one (eqb (nth (build e (succ (fstT (var 1))) (sndT (var 1))) (var 0)) (mB e))

theorem inst2_viol (j y : PTm n) : inst2 (violB e) j y =
    monus one (eqb (nth (build e (succ (fstT y)) (sndT y)) j) (inst2 e (monus (fstT y) j) (sndT y))) := by
  rw [← subst_mB]
  simp only [inst2, violB, PTm.subst_monus, subst_eqb, subst_fstT, subst_sndT, subst_ap2,
    ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

theorem viol_zero_term (y : PTm n) : Γ ⊢[PRAAx] inst2 (violB e) zero y ≐ zero := by
  rw [inst2_viol]
  refine viol_of_eq ?_
  exact (congrNth (build_succ e _ _) (.eqRefl _)).eqTrans ((nth_pair_zero _ _).eqTrans
    (congrInst2 e (monus_zero _).eqSymm (.eqRefl _)))

theorem viol_shift (j M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (violB e) (succ j) (pairT (succ M) x) ≐ inst2 (violB e) j (pairT M x) := by
  rw [inst2_viol, inst2_viol]
  refine congrMonus (.eqRefl _) (AnalyticNumberTheory.Euler.congrEqb ?_ ?_)
  · refine (congrNth (congrAp2 (buildF e) (congrSucc (fst_pair _ _)) (snd_pair _ _)) (.eqRefl _)).eqTrans ?_
    refine (congrNth (build_succ e _ _) (.eqRefl _)).eqTrans ((nth_pair_succ _ _ _).eqTrans ?_)
    exact congrNth (congrAp2 (buildF e) (congrSucc (fst_pair _ _)) (snd_pair _ _)).eqSymm (.eqRefl _)
  · refine (congrInst2 e (congrMonus (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqTrans ?_
    refine (congrInst2 e (succ_monus_succ _ _) (.eqRefl _)).eqTrans ?_
    exact (congrInst2 e (congrMonus (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)).eqSymm

theorem viol_base (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (violB e)) (succ zero) (pairT zero x) ≐ zero :=
  (sum_succ' _ _ _).eqTrans ((congrAdd (sum_zero _ _) (viol_zero_term e _)).eqTrans (add_zero _))

theorem viol_step {M x : PTm n} (ih : Γ ⊢[PRAAx] ap2 (sumF (violB e)) (succ M) (pairT M x) ≐ zero) :
    Γ ⊢[PRAAx] ap2 (sumF (violB e)) (succ (succ M)) (pairT (succ M) x) ≐ zero := by
  refine (sum_shift _ _ _).eqTrans ((congrAdd (viol_zero_term e _) ?_).eqTrans (zero_add _))
  refine (sum_congr_bounded (shiftBody (violB e)) (violB e) (pairT (succ M) x) (pairT M x) (succ M)
    (.allI (.impI ?_))).eqTrans ih
  rw [inst2_shiftBody]
  have e₁ : Syn.shift (pairT (succ M) x) = pairT (succ (Syn.shift M)) (Syn.shift x) := by simp [Syn.shift]
  have e₂ : Syn.shift (pairT M x) = pairT (Syn.shift M) (Syn.shift x) := by simp [Syn.shift]
  rw [e₁, e₂]
  exact viol_shift e _ _ _

/-- Variables: `0 = M` (induction), `1 = x`. -/
private abbrev violF : Fm PTm 2 := ap2 (sumF (violB e)) (succ (var 0)) (pairT (var 0) (var 1)) ≐ zero

private theorem viol₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] violF e := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact viol_base e _
  · exact viol_step e Prf.hyp0

/-- `nth(build e (M + 1) x, j) = e(M − j, x)` for `j ≤ M`. -/
theorem nth_build {j M : PTm n} (x : PTm n) (h : Γ ⊢[PRAAx] le j M) :
    Γ ⊢[PRAAx] nth (build e (succ M) x) j ≐ inst2 e (monus M j) x := by
  have v := inst (Γ := Γ) (viol₀ e) (![M, x] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, subst_ap2, subst_pairT, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] at v
  have z := sum_zero_elim (violB e) v ((succ_monus_succ _ _).eqTrans h)
  rw [inst2_viol] at z
  refine (congrNth (congrAp2 (buildF e) (congrSucc (fst_pair M x)) (snd_pair M x)) (.eqRefl j)).eqSymm.eqTrans ?_
  refine (eq_of_viol z).eqTrans ?_
  exact congrInst2 e (congrMonus (fst_pair _ _) (.eqRefl _)) (snd_pair _ _)

end Build

/-! ## Bits -/

/-- `[k ≤ N]`. -/
abbrev gle {n : ℕ} (k N : PTm n) : PTm n := monus one (monus k N)
/-- `[k ≥ 1]`. -/
abbrev sg {n : ℕ} (k : PTm n) : PTm n := monus one (monus one k)

theorem gle_of_le {k N : PTm n} (h : Γ ⊢[PRAAx] le k N) : Γ ⊢[PRAAx] gle k N ≐ one :=
  (congrMonus (.eqRefl _) h).eqTrans (monus_zero _)

theorem sg_zero : Γ ⊢[PRAAx] sg (zero : PTm n) ≐ zero :=
  (congrMonus (.eqRefl _) (monus_zero _)).eqTrans (monus_self _)

theorem sg_succ (k : PTm n) : Γ ⊢[PRAAx] sg (succ k) ≐ one :=
  (congrMonus (.eqRefl _) ((succ_monus_succ _ _).eqTrans (zero_monus _))).eqTrans (monus_zero _)

theorem gle_above {k N : PTm n} (h : Γ ⊢[PRAAx] le (succ N) k) : Γ ⊢[PRAAx] gle k N ≐ zero := by
  have m := Common.monus_succ_of_lt h
  exact (congrMonus (.eqRefl _) m).eqTrans ((succ_monus_succ _ _).eqTrans (zero_monus _))

/-! ## The Stirling table -/

/-- The entry `k S(n, k) + S(n, k − 1)` of row `n + 1`, over `0 = k`, `1 = ⟨n, R_n⟩`. -/
abbrev eS : PTm 2 :=
  var 0 * (gle (var 0) (fstT (var 1)) * nth (sndT (var 1)) (monus (fstT (var 1)) (var 0))) +
    sg (var 0) * nth (sndT (var 1)) (monus (fstT (var 1)) (pred (var 0)))

theorem inst2_eS (k y : PTm n) : inst2 eS k y =
    k * (gle k (fstT y) * nth (sndT y) (monus (fstT y) k)) + sg k * nth (sndT y) (monus (fstT y) (pred k)) := by
  simp [inst2]

/-- The row step; variables `0 = n`, `1 = R_n`. -/
abbrev rowStep : PTm 2 := build eS (succ (succ (var 0))) (pairT (var 0) (var 1))
abbrev RF : PR 1 := rec1 (pairT one zero) rowStep
/-- The coded row `R_N`. -/
abbrev row {n : ℕ} (N : PTm n) : PTm n := ap1 RF N

theorem row_zero : Γ ⊢[PRAAx] row (zero : PTm n) ≐ pairT one zero := by
  have h := rec1_zero (Γ := Γ) (pairT one zero) rowStep
  simpa using h

theorem row_succ (N : PTm n) : Γ ⊢[PRAAx] row (succ N) ≐ build eS (succ (succ N)) (pairT N (row N)) := by
  have h := rec1_succ (Γ := Γ) (pairT one zero) rowStep N
  simpa using h

/-- `S(N, K)`. -/
abbrev stir {n : ℕ} (N K : PTm n) : PTm n := gle K N * nth (row N) (monus N K)

/-- `S(0, 0) = 1`. -/
theorem stir_zero : Γ ⊢[PRAAx] stir (zero : PTm n) zero ≐ one := by
  have g := gle_of_le (Γ := Γ) (le_refl (zero : PTm n))
  have r : Γ ⊢[PRAAx] nth (row (zero : PTm n)) (monus zero zero) ≐ one :=
    (congrNth row_zero (monus_zero _)).eqTrans (nth_pair_zero _ _)
  exact (congrMul g r).eqTrans (one_mul _)

/-- `S(n, k) = 0` for `k > n`. -/
theorem stir_above {N K : PTm n} (h : Γ ⊢[PRAAx] le (succ N) K) : Γ ⊢[PRAAx] stir N K ≐ zero :=
  (congrMul (gle_above h) (.eqRefl _)).eqTrans (zero_mul _)

/-- `S(n + 1, 0) = 0`. -/
theorem stir_succ_zero (N : PTm n) : Γ ⊢[PRAAx] stir (succ N) zero ≐ zero := by
  have g := gle_of_le (Γ := Γ) (zero_le (succ N))
  have r : Γ ⊢[PRAAx] nth (row (succ N)) (monus (succ N) zero) ≐ inst2 eS zero (pairT N (row N)) :=
    (congrNth (row_succ N) (monus_zero _)).eqTrans
      ((nth_build eS _ (le_refl _)).eqTrans (congrInst2 eS (monus_self _) (.eqRefl _)))
  rw [inst2_eS] at r
  have r' : Γ ⊢[PRAAx] nth (row (succ N)) (monus (succ N) zero) ≐ zero :=
    r.eqTrans ((congrAdd (zero_mul _) (congrMul sg_zero (.eqRefl _))).eqTrans
      ((congrAdd (.eqRefl _) (zero_mul _)).eqTrans (add_zero _)))
  exact (congrMul g r').eqTrans (mul_zero _)

/-- `prop:stirling`: `S(n + 1, k + 1) = (k + 1) S(n, k + 1) + S(n, k)` for `k ≤ n`. -/
theorem stir_succ_succ {N K : PTm n} (h : Γ ⊢[PRAAx] le K N) :
    Γ ⊢[PRAAx] stir (succ N) (succ K) ≐ succ K * stir N (succ K) + stir N K := by
  have hs : Γ ⊢[PRAAx] le (succ K) (succ N) := (succ_monus_succ _ _).eqTrans h
  have g₁ := gle_of_le hs
  have n₁ : Γ ⊢[PRAAx] nth (row (succ N)) (monus (succ N) (succ K)) ≐ inst2 eS (succ K) (pairT N (row N)) :=
    (congrNth (row_succ N) (.eqRefl _)).eqTrans
      ((nth_build eS _ (monus_le' hs)).eqTrans (congrInst2 eS (monus_monus hs) (.eqRefl _)))
  rw [inst2_eS] at n₁
  have a₁ : Γ ⊢[PRAAx] gle (succ K) (fstT (pairT N (row N))) ≐ gle (succ K) N :=
    congrMonus (.eqRefl _) (congrMonus (.eqRefl _) (fst_pair _ _))
  have b₁ : Γ ⊢[PRAAx] nth (sndT (pairT N (row N))) (monus (fstT (pairT N (row N))) (succ K)) ≐
      nth (row N) (monus N (succ K)) :=
    congrNth (snd_pair _ _) (congrMonus (fst_pair _ _) (.eqRefl _))
  have d₁ : Γ ⊢[PRAAx] nth (sndT (pairT N (row N))) (monus (fstT (pairT N (row N))) (pred (succ K))) ≐
      nth (row N) (monus N K) :=
    congrNth (snd_pair _ _) (congrMonus (fst_pair _ _) (pred_succ _))
  have n₂ := n₁.eqTrans (congrAdd (congrMul (.eqRefl _) (congrMul a₁ b₁)) (congrMul (sg_succ K) d₁))
  refine (congrMul g₁ n₂).eqTrans ?_
  ipra_lc -(𝔞(nth (row N) (monus N K))) * natEq (gle_of_le h)

end LeanProofs.IPRA.Combinatorics.Stirling
