import IPRADerivations.Probability.KolmogorovStep

/-!
# Summing the first-crossing steps of Kolmogorov's maximal inequality

Packet: `probability/expected_value_ipra_2026-11-16`, `paper/sections/08_samples_lln.tex`,
Theorem `thm:kolmogorov`, the last display of its proof: "Sum over the disjoint first-crossing events:
`a² P(max_k |S_k| ≥ a) ≤ E[S_n² ∑_k 1_{A_k}] ≤ E[S_n²]`."

On a finite sample space `t < T` with weight `p_t`, indicator bodies `I(k, t)` of the events `A_k`
(`k < n`), a threshold body `c_t` (`= a²`) and the natural body `Z_t` (`= S_n²`):

* `lift g`: a body of `(t, x)` read as a body of `(k, t, x)`;
* `col_scale`: `∑_{k<M} I(k, t) g(t) = g(t) ∑_{k<M} I(k, t)`;
* `assembly`: if `∑_t p c I(k, ·) ≤ ∑_t p I(k, ·) Z` for every `k < n` (the step of
  `Probability/KolmogorovStep`, `a² P(A_k) ≤ E[S_n² 1_{A_k}]`) and the events are disjoint,
  `∑_{k<n} I(k, t) ≤ 1` for `t < T`, then `∑_{k<n} ∑_t p c I(k, ·) ≤ ∑_t p Z`, i.e.
  `a² ∑_k P(A_k) = a² P(max_k |S_k| ≥ a) ≤ E[S_n²]`.

The proof exchanges the two finite sums (`Core/Fubini`) and uses disjointness pointwise. The step for
each `k` is supplied on the sample space itself; its derivation from the product decomposition at `k`
(`crossing_step`, through a coding of the `n`-fold product) and the identity `E[S_n²] = ∑ Var(X_j)` are
not derived here.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.KolmogorovAssembly

open_ipra
open LeanProofs.IPRA.Probability.Expectation (Ew Wt inst2_mul' inst2_add')
open LeanProofs.IPRA.Probability.Independence (dsum inst3_mul' shift_inst2 sum_scale)
open LeanProofs.IPRA.Analysis.PowerSums (sum_le)

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔟" t:max => Groth.ι (IPRA.Q.mk _ t)

/-- `g(t, x)` as a body of `(k, t, x)`. -/
def lift (g : PTm 2) : PTm 3 := Syn.subst ![var 1, var 2] g

theorem inst3_lift (g : PTm 2) (k t x : PTm n) : inst3 (lift g) k t x = inst2 g t x := by
  simp only [inst3, lift, inst2, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> rfl

/-- `g(t, snd y)`: a body of `(t, ⟨M, x⟩)` reading only `x`. -/
def gl (g : PTm 2) : PTm 2 := Syn.subst ![var 0, sndT (var 1)] g

theorem inst2_gl (g : PTm 2) (t y : PTm n) : inst2 (gl g) t y = inst2 g t (sndT y) := by
  simp only [inst2, gl, Syn.subst_subst]
  congr 1; funext i; fin_cases i <;> simp

/-- `∑_{k<M} I(k, t) g(t) = g(t) ∑_{k<M} I(k, t)`. -/
theorem col_scale (I : PTm 3) (g : PTm 2) (t M x : PTm n) :
    Γ ⊢[PRAAx] inst2 (pB (I * lift g)) t (pairT M x) ≐ inst2 g t x * inst2 (pB I) t (pairT M x) := by
  rw [inst2_pB, inst2_pB]
  refine sum_scale (colB (I * lift g)) (colB I) (fstT (pairT M x)) (inst2 g t x)
    (pairT t (sndT (pairT M x))) (pairT t (sndT (pairT M x))) (.allI (.impI ?_))
  rw [inst2_colB, inst2_colB, inst3_mul', inst3_lift, shift_inst2, shift_pairT]
  have hs : Syn.shift (sndT (pairT M x)) = sndT (pairT (Syn.shift M) (Syn.shift x)) := by
    simp [Syn.shift]
  rw [hs]
  have e₁ := fst_pair (Γ := lt (var 0) (Syn.shift (fstT (pairT M x))) :: Γ.map Fm.shift)
    (Syn.shift t) (sndT (pairT (Syn.shift M) (Syn.shift x)))
  have e₂ := (snd_pair (Γ := lt (var 0) (Syn.shift (fstT (pairT M x))) :: Γ.map Fm.shift)
    (Syn.shift t) (sndT (pairT (Syn.shift M) (Syn.shift x)))).eqTrans (snd_pair (Syn.shift M) (Syn.shift x))
  have c := congrInst2 g e₁ e₂
  apply deriveNat; ipra_simps
  rw [natEq c]; ring

/-- "Sum over the disjoint first-crossing events": `∑_{k<n} ∑_t p c I(k, ·) ≤ ∑_t p Z`. -/
theorem assembly (I : PTm 3) (p c Z : PTm 2) (nK T x : PTm n)
    (hstep : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift nK) ⟶
      le (inst2 (oB (I * lift (p * c))) (var 0) (Syn.shift (pairT T x)))
        (inst2 (oB (I * lift (p * Z))) (var 0) (Syn.shift (pairT T x)))))
    (hdis : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift T) ⟶
      le (inst2 (pB I) (var 0) (Syn.shift (pairT nK x))) one)) :
    Γ ⊢[PRAAx] le (dsum (I * lift (p * c)) nK T x) (Ew p Z T x) := by
  have s₁ := sum_le (oB (I * lift (p * c))) (oB (I * lift (p * Z))) (pairT T x) nK hstep
  have f₂ := fubini (Γ := Γ) (I * lift (p * Z)) nK T x
  have s₂ := sum_le (pB (I * lift (p * Z))) (gl (p * Z)) (pairT nK x) T (.allI (.impI (by
    have hd := Prf.impE hdis.allOpen.wk Prf.hyp0
    rw [shift_pairT] at hd ⊢
    have ce := natEq (col_scale (Γ := lt (var 0) (Syn.shift T) :: Γ.map Fm.shift) I (p * Z) (var 0)
      (Syn.shift nK) (Syn.shift x))
    rw [inst2_gl]
    have eg := natEq (congrInst2 (Γ := lt (var 0) (Syn.shift T) :: Γ.map Fm.shift) (p * Z)
      (.eqRefl (var 0)) (snd_pair (Syn.shift nK) (Syn.shift x)))
    ipra_le 𝔟 (inst2 (p * Z) (var 0) (Syn.shift x)) * sl hd using rw [ce, eg]; ring)))
  have e₃ := sum_congr_bounded (Γ := Γ) (gl (p * Z)) (p * Z) (pairT nK x) x T (.allI (.impI (by
    rw [inst2_gl, shift_pairT]
    exact congrInst2 (p * Z) (.eqRefl (var 0)) (snd_pair (Syn.shift nK) (Syn.shift x)))))
  exact le_trans s₁ (le_congr f₂.eqSymm e₃ s₂)

end LeanProofs.IPRA.Probability.KolmogorovAssembly
