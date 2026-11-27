import IPRADerivations.Core.SumOrder
import IPRADerivations.Core.ProdLemmas

/-!
# Replacing the factors of a product one at a time

Packet: `probability/central_limit_ipra_2026-11-15` (the finite product identity (6.8) in the proof
of `thm:bounded-normalized`, "proved by induction on the number of factors"). For factors
`a_k`, `g_k` put `A(N) = ∏_{k<N} a_k`, `G(N) = ∏_{k<N} g_k`. The sum
`∑_j (a_j − g_j) ∏_{k<j} a_k ∏_{j<k<N} g_k` satisfies the recursion
`H(N + 1) = H(N) g_N + A(N) (a_N − g_N)`; its positive and negative parts are

  `Hp (N + 1) = Hp N · g_N + A(N) a_N`,   `Hm (N + 1) = Hm N · g_N + A(N) g_N`.

* `replacement_identity`: `A(N) + Hm N = G(N) + Hp N`, i.e. `∏ a − ∏ g = H(N)`, identity (6.8);
* `replacement_bound`: if `a_k ≤ g_k + e_k`, `a_k ≤ R` and `g_k ≤ R` for `k < N`, then
  `G(N) ≤ R^N` and `R · A(N) ≤ R · G(N) + R^N ∑_{k<N} e_k`. With the factors scaled by `R` this is
  `∏ α_k ≤ ∏ γ_k + ∑ ε_k` for factors in `[0, 1]`: the one-sided form of
  `abs(∏ a_k − ∏ g_k) ≤ ∑ abs(a_k − g_k)`.

The characteristic functions, the damping estimates and the smoothing theorem are not formalized.
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Probability.ProductReplacement

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "𝔞" t:max => Groth.ι (IPRA.Q.mk _ t)

/-! ## The recursive sum -/

theorem sub3 (g : PTm 2) (N H x : PTm n) :
    Syn.subst ![N, H, x] (Syn.subst ![var 0, var 2] g) = inst2 g N x := by
  simp only [inst2, Syn.subst_subst]
  congr 1; funext j; fin_cases j <;> simp

/-- Steps; variables `0 = N`, `1 = H(N)`, `2 = x`. -/
abbrev hpStep (a g : PTm 2) : PTm 3 :=
  var 1 * Syn.subst ![var 0, var 2] g + ap2 (prodF a) (var 0) (var 2) * Syn.subst ![var 0, var 2] a
abbrev hmStep (a g : PTm 2) : PTm 3 :=
  var 1 * Syn.subst ![var 0, var 2] g + ap2 (prodF a) (var 0) (var 2) * Syn.subst ![var 0, var 2] g

/-- The positive part of `∑_j (a_j − g_j) ∏_{k<j} a_k ∏_{k>j} g_k`. -/
abbrev Hp (a g : PTm 2) (N x : PTm n) : PTm n := ap2 (rec2 zero (hpStep a g)) N x
/-- The negative part. -/
abbrev Hm (a g : PTm 2) (N x : PTm n) : PTm n := ap2 (rec2 zero (hmStep a g)) N x

theorem Hp_zero (a g : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] Hp a g zero x ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero (hpStep a g) x
  simpa using h

theorem Hm_zero (a g : PTm 2) (x : PTm n) : Γ ⊢[PRAAx] Hm a g zero x ≐ zero := by
  have h := rec2_zero (Γ := Γ) zero (hmStep a g) x
  simpa using h

theorem Hp_succ (a g : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] Hp a g (succ N) x ≐ Hp a g N x * inst2 g N x + ap2 (prodF a) N x * inst2 a N x := by
  have h := rec2_succ (Γ := Γ) zero (hpStep a g) N x
  have e : Syn.subst ![N, Hp a g N x, x] (hpStep a g) =
      Hp a g N x * inst2 g N x + ap2 (prodF a) N x * inst2 a N x := by
    simp only [PTm.subst_add, PTm.subst_mul, sub3, subst_ap2, Syn.subst_var]
    simp
  rw [e] at h
  exact h

theorem Hm_succ (a g : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] Hm a g (succ N) x ≐ Hm a g N x * inst2 g N x + ap2 (prodF a) N x * inst2 g N x := by
  have h := rec2_succ (Γ := Γ) zero (hmStep a g) N x
  have e : Syn.subst ![N, Hm a g N x, x] (hmStep a g) =
      Hm a g N x * inst2 g N x + ap2 (prodF a) N x * inst2 g N x := by
    simp only [PTm.subst_add, PTm.subst_mul, sub3, subst_ap2, Syn.subst_var]
    simp
  rw [e] at h
  exact h

/-! ## The identity -/

theorem prod_succ' (f : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF f) (succ N) x ≐ ap2 (prodF f) N x * inst2 f N x := prod_succ f N x

theorem id_base (a g : PTm 2) (x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF a) zero x + Hm a g zero x ≐ ap2 (prodF g) zero x + Hp a g zero x := by
  ipra_lc natEq (prod_zero (Γ := Γ) a x) - natEq (prod_zero (Γ := Γ) g x) + natEq (Hm_zero (Γ := Γ) a g x) -
    natEq (Hp_zero (Γ := Γ) a g x)

theorem id_step (a g : PTm 2) {N x : PTm n}
    (ih : Γ ⊢[PRAAx] ap2 (prodF a) N x + Hm a g N x ≐ ap2 (prodF g) N x + Hp a g N x) :
    Γ ⊢[PRAAx] ap2 (prodF a) (succ N) x + Hm a g (succ N) x ≐
      ap2 (prodF g) (succ N) x + Hp a g (succ N) x := by
  ipra_lc 𝔞(inst2 g N x) * natEq ih + natEq (prod_succ' (Γ := Γ) a N x) + natEq (Hm_succ (Γ := Γ) a g N x) -
    natEq (prod_succ' (Γ := Γ) g N x) - natEq (Hp_succ (Γ := Γ) a g N x)

/-- Variables: `0 = N` (induction), `1 = x`. -/
private abbrev idF (a g : PTm 2) : Fm PTm 2 :=
  ap2 (prodF a) (var 0) (var 1) + Hm a g (var 0) (var 1) ≐ ap2 (prodF g) (var 0) (var 1) + Hp a g (var 0) (var 1)

private theorem id₀ (a g : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] idF a g := by
  ipra_ind [subst_ap2]
  · exact id_base a g _
  · exact id_step a g Prf.hyp0

/-- Identity (6.8): `∏_{k<N} a_k + Hm N = ∏_{k<N} g_k + Hp N`. -/
theorem replacement_identity (a g : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (prodF a) N x + Hm a g N x ≐ ap2 (prodF g) N x + Hp a g N x := by
  have h := inst (Γ := Γ) (id₀ a g) (![N, x] : Fin 2 → PTm n)
  simpa using h

/-! ## The bound -/

theorem repl_step {A G E a g e R Rp : PTm n} (hG : Γ ⊢[PRAAx] le G Rp)
    (ih : Γ ⊢[PRAAx] le (R * A) (R * G + Rp * E)) (h₁ : Γ ⊢[PRAAx] le a (g + e))
    (h₂ : Γ ⊢[PRAAx] le a R) (h₃ : Γ ⊢[PRAAx] le g R) :
    Γ ⊢[PRAAx] le (G * g) (Rp * R) ⋏ le (R * (A * a)) (R * (G * g) + (Rp * R) * (E + e)) := by
  refine .andI (Common.mul_le_mul hG h₃) ?_
  have s1 := mul_le_mul_right a ih
  have s2 := add_le_add₂ (Common.mul_le_mul (le_refl (R * G)) h₁) (Common.mul_le_mul (le_refl (Rp * E)) h₂)
  have s3 := add_le_add₂ (le_refl (R * (G * g) + (Rp * E) * R)) (Common.mul_le_mul (le_refl (R * e)) hG)
  refine le_trans (le_congr ?_ ?_ s1) (le_trans s2 (le_congr ?_ ?_ s3))
  all_goals (ipra_ring)

/-- The induction formula; variable `0 = i`. -/
abbrev replF (a g e : PTm 2) (R N x : PTm n) : Fm PTm (n + 1) :=
  le (var 0) (Syn.shift N) ⟶
    (le (ap2 (prodF g) (var 0) (Syn.shift x)) (pw (Syn.shift R) (var 0)) ⋏
      le (Syn.shift R * ap2 (prodF a) (var 0) (Syn.shift x))
        (Syn.shift R * ap2 (prodF g) (var 0) (Syn.shift x) +
          pw (Syn.shift R) (var 0) * ap2 (sumF e) (var 0) (Syn.shift x)))

theorem replacement_all (a g e : PTm 2) (R N x : PTm n)
    (h₁ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 a (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift x) + inst2 e (var 0) (Syn.shift x))))
    (h₂ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 a (var 0) (Syn.shift x)) (Syn.shift R)))
    (h₃ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 g (var 0) (Syn.shift x)) (Syn.shift R))) :
    Γ ⊢[PRAAx] Fm.all (replF a g e R N x) := by
  ipra_qfind (⟨le_QF _ _, ⟨le_QF _ _, le_QF _ _⟩⟩) [subst_le, subst_ap2]
  · refine .impI (.andI ?_ ?_)
    · exact le_congr (prod_zero g x).eqSymm (pw_zero R).eqSymm (le_refl _)
    · exact le_trans (le_congr (congrMul (.eqRefl R) (prod_zero a x).eqSymm)
        (congrMul (.eqRefl R) (prod_zero g x).eqSymm) (le_refl _)) (le_add_right _ _)
  · have f₁ := h₁.allOpen; have f₂ := h₂.allOpen; have f₃ := h₃.allOpen
    refine .impI ?_
    have hle : (le (succ (var 0)) (Syn.shift N) :: replF a g e R N x :: Γ.map Fm.shift) ⊢[PRAAx]
        le (var 0) (Syn.shift N) := le_trans (le_succ_self _) Prf.hyp0
    have ih := Prf.impE Prf.hyp1 hle
    have st := repl_step (Prf.andE₁ ih) (Prf.andE₂ ih) (Prf.impE f₁.wk.wk Prf.hyp0)
      (Prf.impE f₂.wk.wk Prf.hyp0) (Prf.impE f₃.wk.wk Prf.hyp0)
    refine .andI ?_ ?_
    · exact le_congr (prod_succ g (var 0) _).eqSymm (pw_succ _ _).eqSymm (Prf.andE₁ st)
    · exact le_congr (congrMul (.eqRefl _) (prod_succ a (var 0) _).eqSymm)
        (congrAdd (congrMul (.eqRefl _) (prod_succ g (var 0) _).eqSymm)
          (congrMul (pw_succ _ _).eqSymm (sum_succ' e (var 0) _).eqSymm)) (Prf.andE₂ st)

/-- If `a_k ≤ g_k + e_k`, `a_k ≤ R`, `g_k ≤ R` for `k < N`, then `∏ g_k ≤ R^N` and
`R ∏ a_k ≤ R ∏ g_k + R^N ∑ e_k`. -/
theorem replacement_bound (a g e : PTm 2) (R N x : PTm n)
    (h₁ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 a (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift x) + inst2 e (var 0) (Syn.shift x))))
    (h₂ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 a (var 0) (Syn.shift x)) (Syn.shift R)))
    (h₃ : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶ le (inst2 g (var 0) (Syn.shift x)) (Syn.shift R))) :
    Γ ⊢[PRAAx] le (ap2 (prodF g) N x) (pw R N) ⋏
      le (R * ap2 (prodF a) N x) (R * ap2 (prodF g) N x + pw R N * ap2 (sumF e) N x) := by
  have h := Prf.allE N (replacement_all a g e R N x h₁ h₂ h₃)
  simp only [Fm.subst_imp, Fm.subst_and, subst_le, Fm.subst_eq, subst_ap2, PTm.subst_add, PTm.subst_mul,
    Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift, ConciseIPRA.PTm.subst_zero,
    ConciseIPRA.PTm.subst_succ] at h
  exact .impE h (le_refl N)

end LeanProofs.IPRA.Probability.ProductReplacement
