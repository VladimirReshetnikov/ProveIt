import IPRADerivations.Probability.Expectation
import IPRADerivations.Core.Fubini

/-!
# The finite law of the unconscious statistician

Packet: `probability/expected_value_ipra_2026-11-16`, Definition `def:pushforward` and Theorem
`thm:finite-lotus`. For a weight body `w(i, x)` on outcomes `i < M`, a map `σ(i, x) < N` and an
observable `g(j, x)` on `j < N`, with pushforward weights `v_j = ∑_{i<M} w_i [σ(i) = j]`:

* `lotus`: `∑_{i<M} w_i g(σ(i)) = ∑_{j<N} g(j) v_j`;
* `pushforward_total`: `∑_{j<N} v_j = ∑_{i<M} w_i` (the case `g = 1`).

The proof is the exchange of two finite sums (`Core/Fubini.fubini`) for
`a(i, j) = w_i [σ(i) = j] g(j)`: the row sums are `w_i g(σ(i))` (`sum_delta`) and the column sums are
`g(j) v_j`.

`sum_const_mul` (`∑_{j<N} K f(j) = K ∑_{j<N} f(j)` for an arbitrary term `K`) is reusable.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.Lotus

open_ipra
open LeanProofs.IPRA.Probability.Expectation (mul_one')
open LeanProofs.IPRA.AnalyticNumberTheory.Euler (congrEqb)

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Pulling a constant out of a sum -/

/-- `fst y · f(j, snd y)`. -/
def cmB (f : PTm 2) : PTm 2 := fstT (var 1) * Syn.subst ![var 0, sndT (var 1)] f

theorem inst2_cmB (f : PTm 2) (j y : PTm n) : inst2 (cmB f) j y = fstT y * inst2 f j (sndT y) := by
  simp only [inst2, cmB, PTm.subst_mul, Syn.subst_subst]
  congr 1
  · simp
  · congr 1; funext k; fin_cases k <;> simp

theorem cm_step (f : PTm 2) {N K x : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (sumF (cmB f)) N (pairT K x) ≐ K * ap2 (sumF f) N x) :
    Γ ⊢[PRAAx] ap2 (sumF (cmB f)) (succ N) (pairT K x) ≐ K * ap2 (sumF f) (succ N) x := by
  have e₁ := sum_succ' (Γ := Γ) (cmB f) N (pairT K x)
  rw [inst2_cmB] at e₁
  have t : Γ ⊢[PRAAx] fstT (pairT K x) * inst2 f N (sndT (pairT K x)) ≐ K * inst2 f N x :=
    congrMul (fst_pair _ _) (congrInst2 f (.eqRefl _) (snd_pair _ _))
  ipra_lc natEq (e₁.eqTrans (congrAdd ih t)) - Groth.ι (IPRA.Q.mk Γ K) * natEq (sum_succ' (Γ := Γ) f N x)

/-- Variables: `0 = N`, `1 = K`, `2 = x`. -/
private abbrev cmF (f : PTm 2) : Fm PTm 3 :=
  ap2 (sumF (cmB f)) (var 0) (pairT (var 1) (var 2)) ≐ var 1 * ap2 (sumF f) (var 0) (var 2)

private theorem cm₀ (f : PTm 2) : ([] : List (Fm PTm 3)) ⊢[PRAAx] cmF f := by
  ipra_ind [subst_ap2, subst_pairT]
  · exact (sum_zero _ _).eqTrans ((mul_zero _).eqSymm.eqTrans (congrMul (.eqRefl _) (sum_zero _ _).eqSymm))
  · exact cm_step f Prf.hyp0

/-- `∑_{j<N} K · f(j, x) = K · ∑_{j<N} f(j, x)`. -/
theorem sum_const_mul (f : PTm 2) (N K x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (cmB f)) N (pairT K x) ≐ K * ap2 (sumF f) N x := by
  have h := inst (Γ := Γ) (cm₀ f) (![N, K, x] : Fin 3 → PTm n)
  simpa using h

/-! ## The bodies -/

section Bodies

variable (w σ g : PTm 2)

/-- `a(i, j, x) = w(i, x) · ([σ(i, x) = j] · g(j, x))`. -/
def aB : PTm 3 :=
  Syn.subst ![var 0, var 2] w * (eqb (Syn.subst ![var 0, var 2] σ) (var 1) * Syn.subst ![var 1, var 2] g)

theorem inst3_aB (i j x : PTm n) :
    inst3 (aB w σ g) i j x = inst2 w i x * (eqb (inst2 σ i x) j * inst2 g j x) := by
  simp only [inst3, aB, inst2, PTm.subst_mul, subst_eqb, Syn.subst_subst, Syn.subst_var]
  congr 1
  · congr 1; funext k; fin_cases k <;> rfl
  · congr 1
    · congr 1; congr 1; funext k; fin_cases k <;> rfl
    · congr 1; funext k; fin_cases k <;> rfl

/-- `g(σ(i, x), x)`. -/
def gσ : PTm 2 := Syn.subst ![σ, var 1] g

theorem inst2_gσ (i x : PTm n) : inst2 (gσ σ g) i x = inst2 g (inst2 σ i x) x := by
  simp only [inst2, gσ, Syn.subst_subst]
  congr 1; funext k; fin_cases k <;> rfl

/-- `w(i, snd z) · [σ(i, snd z) = fst z]`: the pushforward summand for `j = fst z`. -/
def vB : PTm 2 :=
  Syn.subst ![var 0, sndT (var 1)] w * eqb (Syn.subst ![var 0, sndT (var 1)] σ) (fstT (var 1))

theorem inst2_vB (i z : PTm n) :
    inst2 (vB w σ) i z = inst2 w i (sndT z) * eqb (inst2 σ i (sndT z)) (fstT z) := by
  simp only [inst2, vB, PTm.subst_mul, subst_eqb, Syn.subst_subst, subst_fstT, subst_sndT, Syn.subst_var]
  congr 1
  · congr 1; funext k; fin_cases k <;> simp
  · congr 1; congr 1; funext k; fin_cases k <;> simp

/-- `g(j, snd y) · v_j`, with `v_j = ∑_{i < fst y} w_i [σ(i) = j]`. -/
def rB : PTm 2 :=
  Syn.subst ![var 0, sndT (var 1)] g * ap2 (sumF (vB w σ)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

theorem inst2_rB (j y : PTm n) :
    inst2 (rB w σ g) j y = inst2 g j (sndT y) * ap2 (sumF (vB w σ)) (fstT y) (pairT j (sndT y)) := by
  simp only [inst2, rB, PTm.subst_mul, subst_ap2, subst_pairT, subst_fstT, subst_sndT, Syn.subst_subst,
    Syn.subst_var]
  congr 1
  congr 1; funext k; fin_cases k <;> simp

end Bodies

/-! ## Row and column sums -/

section Eval

variable (w σ g : PTm 2)

theorem row_point (i j x : PTm n) :
    Γ ⊢[PRAAx] inst2 (rowB (aB w σ g)) j (pairT i x) ≐
      inst2 (cmB (dB g)) j (pairT (inst2 w i x) (pairT (inst2 σ i x) x)) := by
  rw [inst2_rowB, inst2_cmB, inst2_dB]
  refine (congrInst3 _ (fst_pair _ _) (.eqRefl _) (snd_pair _ _)).eqTrans ?_
  rw [inst3_aB]
  exact (congrMul (fst_pair _ _) (congrMul
    (congrEqb (snd_pair _ _).fstE (.eqRefl _))
    (congrInst2 g (.eqRefl _) (snd_pair _ _).sndE))).eqSymm

/-- The row sum: `∑_{j<N} a(i, j, x) = w_i g(σ(i))`. -/
theorem row_eval {i N x : PTm n} (h : Γ ⊢[PRAAx] lt (inst2 σ i x) N) :
    Γ ⊢[PRAAx] ap2 (sumF (rowB (aB w σ g))) N (pairT i x) ≐ inst2 w i x * inst2 g (inst2 σ i x) x := by
  refine (sum_congr_bounded (rowB (aB w σ g)) (cmB (dB g)) (pairT i x)
    (pairT (inst2 w i x) (pairT (inst2 σ i x) x)) N (.allI (.impI ?_))).eqTrans
    ((sum_const_mul (dB g) N _ _).eqTrans (congrMul (.eqRefl _) (sum_delta g h)))
  simp only [Syn.shift, subst_pairT, subst_inst2]
  exact row_point w σ g _ _ _

theorem col_point (i j x : PTm n) :
    Γ ⊢[PRAAx] inst2 (colB (aB w σ g)) i (pairT j x) ≐
      inst2 (cmB (vB w σ)) i (pairT (inst2 g j x) (pairT j x)) := by
  rw [inst2_colB, inst2_cmB, inst2_vB]
  refine (congrInst3 _ (.eqRefl _) (fst_pair _ _) (snd_pair _ _)).eqTrans ?_
  rw [inst3_aB]
  have e : Γ ⊢[PRAAx] fstT (pairT (inst2 g j x) (pairT j x)) *
      (inst2 w i (sndT (sndT (pairT (inst2 g j x) (pairT j x)))) *
        eqb (inst2 σ i (sndT (sndT (pairT (inst2 g j x) (pairT j x))))) (fstT (sndT (pairT (inst2 g j x) (pairT j x))))) ≐
      inst2 g j x * (inst2 w i x * eqb (inst2 σ i x) j) :=
    congrMul (fst_pair _ _) (congrMul
      (congrInst2 w (.eqRefl _) (snd_pair _ _).sndE)
      (congrEqb (congrInst2 σ (.eqRefl _) (snd_pair _ _).sndE)
        (snd_pair _ _).fstE))
  refine .eqTrans ?_ e.eqSymm
  ipra_ring

/-- The column sum: `∑_{i<M} a(i, j, x) = g(j) v_j`. -/
theorem col_eval (j M x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (colB (aB w σ g))) M (pairT j x) ≐
      inst2 g j x * ap2 (sumF (vB w σ)) M (pairT j x) := by
  refine (sum_congr_bounded (colB (aB w σ g)) (cmB (vB w σ)) (pairT j x)
    (pairT (inst2 g j x) (pairT j x)) M (.allI (.impI ?_))).eqTrans (sum_const_mul (vB w σ) M _ _)
  simp only [Syn.shift, subst_pairT, subst_inst2]
  exact col_point w σ g _ _ _

end Eval

/-! ## The theorem -/

/-- Finite LOTUS only requires the range hypothesis on the outcomes being summed. -/
theorem lotus_bounded (w σ g : PTm 2) {N x M : PTm n}
    (hr : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift M) ⟶ lt (inst2 σ (var 0) (Syn.shift x)) (Syn.shift N))) :
    Γ ⊢[PRAAx] ap2 (sumF (w * gσ σ g)) M x ≐ ap2 (sumF (rB w σ g)) N (pairT M x) := by
  have e₁ : Γ ⊢[PRAAx] ap2 (sumF (w * gσ σ g)) M x ≐ ap2 (sumF (oB (aB w σ g))) M (pairT N x) := by
    refine sum_congr_bounded (w * gσ σ g) (oB (aB w σ g)) x (pairT N x) M (.allI (.impI ?_))
    rw [Expectation.inst2_mul', inst2_gσ, shift_pairT]
    exact ((oB_at _ _ _ _).eqTrans (row_eval w σ g (Prf.impE hr.allOpen.wk Prf.hyp0))).eqSymm
  have e₂ : Γ ⊢[PRAAx] ap2 (sumF (pB (aB w σ g))) N (pairT M x) ≐ ap2 (sumF (rB w σ g)) N (pairT M x) := by
    refine sum_congr_bounded (pB (aB w σ g)) (rB w σ g) (pairT M x) (pairT M x) N (.allI (.impI ?_))
    rw [inst2_pB, inst2_rB, shift_pairT]
    exact (congrAp2 (sumF (colB (aB w σ g))) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqTrans
      ((col_eval w σ g _ _ _).eqTrans (congrMul (congrInst2 g (.eqRefl _) (snd_pair _ _)).eqSymm
        (congrAp2 (sumF (vB w σ)) (fst_pair _ _) (congrPairT (.eqRefl _) (snd_pair _ _))).eqSymm))
  exact e₁.eqTrans ((fubini (aB w σ g) M N x).eqTrans e₂)

/-- `thm:finite-lotus`: `∑_{i<M} w_i g(σ(i)) = ∑_{j<N} g(j) v_j`, for `σ < N`. -/
theorem lotus (w σ g : PTm 2) {N x : PTm n} (hr : Γ ⊢[PRAAx] Permutation.rangeAll σ N x) (M : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (w * gσ σ g)) M x ≐ ap2 (sumF (rB w σ g)) N (pairT M x) :=
  lotus_bounded w σ g (.allI (.impI hr.allOpen.wk))

/-- `v_j = ∑_{i < fst y} w_i [σ(i) = j]` as a body in `j`. -/
def pvB (w σ : PTm 2) : PTm 2 := ap2 (sumF (vB w σ)) (fstT (var 1)) (pairT (var 0) (sndT (var 1)))

theorem inst2_pvB (w σ : PTm 2) (j y : PTm n) :
    inst2 (pvB w σ) j y = ap2 (sumF (vB w σ)) (fstT y) (pairT j (sndT y)) := by
  simp [inst2, pvB]

/-- `def:pushforward`: the pushforward weights have the same total, `∑_{j<N} v_j = ∑_{i<M} w_i`. -/
theorem pushforward_total (w σ : PTm 2) {N x : PTm n} (hr : Γ ⊢[PRAAx] Permutation.rangeAll σ N x) (M : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (pvB w σ)) N (pairT M x) ≐ ap2 (sumF w) M x := by
  have l := lotus w σ (one : PTm 2) hr M
  have e₁ : Γ ⊢[PRAAx] ap2 (sumF (w * gσ σ (one : PTm 2))) M x ≐ ap2 (sumF w) M x := by
    refine sum_congr_bounded (w * gσ σ (one : PTm 2)) w x x M (.allI (.impI ?_))
    rw [Expectation.inst2_mul', inst2_gσ]
    have e : inst2 (one : PTm 2) (inst2 σ (var 0 : PTm (n + 1)) (Syn.shift x)) (Syn.shift x) = one := by
      simp [inst2]
    rw [e]
    exact mul_one' _
  have e₂ : Γ ⊢[PRAAx] ap2 (sumF (rB w σ (one : PTm 2))) N (pairT M x) ≐ ap2 (sumF (pvB w σ)) N (pairT M x) := by
    refine sum_congr_bounded (rB w σ (one : PTm 2)) (pvB w σ) (pairT M x) (pairT M x) N (.allI (.impI ?_))
    rw [inst2_rB, inst2_pvB]
    have e : inst2 (one : PTm 2) (var 0 : PTm (n + 1)) (sndT (Syn.shift (pairT M x))) = one := by
      simp [inst2]
    rw [e]
    exact one_mul _
  exact e₂.eqSymm.eqTrans (l.eqSymm.eqTrans e₁)

end LeanProofs.IPRA.Probability.Lotus
