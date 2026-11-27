import IPRADerivations.Core.SumOrder

/-!
# Power-sum quadrature (`docs/proofs/analysis/basel_ipra`, Lemma `lem:moment`)

For `p ∈ ℕ` and `M ≥ 1` (with `0⁰ = 1`),
`0 ≤ 1/(p+1) − (1/M) ∑_{i<M} (i/M)ᵖ ≤ 1/M`. Cleared of denominators, with
`S = ∑_{i<M} iᵖ`:

`(p + 1) S ≤ M^{p+1} ≤ (p + 1) S + (p + 1) Mᵖ` (`power_sum_quadrature`; the case `M = 0` is
included).

As in the paper, the proof sums the two bounds
`i^{p+1} + (p+1) iᵖ ≤ (i+1)^{p+1} ≤ i^{p+1} + (p+1)(i+1)ᵖ` (each by induction on `p`) and
telescopes `∑_{i<M} ((i+1)^q − i^q) = M^q − 0^q`.

Also: `sum_le` (sums of pointwise smaller bodies are smaller) and `sum_mul_param` (a factor
depending only on the parameter comes out of a sum).
-/

set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.PowerSums

open_ipra

variable {n : ℕ} {Γ : List (Fm PTm n)}

/-! ## Sums -/

/-- Sums of pointwise smaller bodies are smaller. -/
theorem sum_le (f g : PTm 2) (x N : PTm n)
    (h : Γ ⊢[PRAAx] Fm.all (lt (var 0) (Syn.shift N) ⟶
      le (inst2 f (var 0) (Syn.shift x)) (inst2 g (var 0) (Syn.shift x)))) :
    Γ ⊢[PRAAx] le (ap2 (sumF f) N x) (ap2 (sumF g) N x) :=
  sum_le_params f g x x N h

/-- `c(x) · g(i, x)` as a body, for `c : PTm 1`. -/
def mulParam (c : PTm 1) (g : PTm 2) : PTm 2 := Syn.subst ![var 1] c * g

theorem inst2_mulParam (c : PTm 1) (g : PTm 2) (i x : PTm n) :
    inst2 (mulParam c g) i x = Syn.subst ![x] c * inst2 g i x := by
  simp only [inst2, mulParam, PTm.subst_mul, Syn.subst_subst]
  congr 2; funext j; fin_cases j; rfl

/-- Variables: `0 = N`, `1 = x`. -/
private abbrev mulParamF (c : PTm 1) (g : PTm 2) : Fm PTm 2 :=
  ap2 (sumF (mulParam c g)) (var 0) (var 1) ≐ Syn.subst ![var 1] c * ap2 (sumF g) (var 0) (var 1)

private theorem sum_mul_param₀ (c : PTm 1) (g : PTm 2) : ([] : List (Fm PTm 2)) ⊢[PRAAx] mulParamF c g := by
  ipra_ind [subst_ap2, Syn.subst_subst]
  · exact (sum_zero _ _).eqTrans ((mul_zero _).eqSymm.eqTrans (congrMul (.eqRefl _) (sum_zero _ _).eqSymm))
  · refine (sum_succ' _ (var 0) (var 1)).eqTrans ?_
    rw [inst2_mulParam]
    have e : (fun i => Syn.subst (Syn.repl (succ (var 0))) (![var 1] i) : Fin 1 → PTm 2) = ![var 1] := by
      funext i; fin_cases i; rfl
    rw [e]
    refine withEq Prf.hyp0 fun e₁ => withEq (sum_succ' g (var 0) (var 1)) fun e₂ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂]; ring

theorem sum_mul_param (c : PTm 1) (g : PTm 2) (N x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (mulParam c g)) N x ≐ Syn.subst ![x] c * ap2 (sumF g) N x := by
  have h := inst (Γ := Γ) (sum_mul_param₀ c g) (![N, x] : Fin 2 → PTm n)
  simp only [Fm.subst_eq, PTm.subst_mul, subst_ap2, Syn.subst_var, Syn.subst_subst,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at h
  have e : (fun i => Syn.subst ![N, x] (![var 1] i) : Fin 1 → PTm n) = ![x] := by
    funext i; fin_cases i; rfl
  rw [e] at h
  exact h

/-- Telescoping: `∑_{i<M} f(i+1) + f(0) = ∑_{i<M} f(i) + f(M)`. -/
theorem telescope' (f : PTm 2) (M x : PTm n) :
    Γ ⊢[PRAAx] ap2 (sumF (shiftBody f)) M x + inst2 f zero x ≐ ap2 (sumF f) M x + inst2 f M x :=
  (add_comm _ _).eqTrans ((sum_shift f M x).eqSymm.eqTrans (sum_succ' f M x))

/-! ## The two bounds -/

/-- Variables: `0 = p`, `1 = i`. `i^{p+1} + (p+1) iᵖ ≤ (i+1)^{p+1}`. -/
private abbrev lowerF : Fm PTm 2 :=
  le (pw (var 1) (succ (var 0)) + succ (var 0) * pw (var 1) (var 0)) (pw (succ (var 1)) (succ (var 0)))

private theorem lower₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] lowerF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · refine le_of_eq_add (d := zero) ?_
    refine withEq (pw_succ (Γ := []) (succ (var 0) : PTm 1) zero) fun e₁ =>
      withEq (pw_succ (Γ := []) (var 0 : PTm 1) zero) fun e₂ =>
      withEq (pw_zero (Γ := []) (succ (var 0) : PTm 1)) fun e₃ =>
      withEq (pw_zero (Γ := []) (var 0 : PTm 1)) fun e₄ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂, e₃, e₄]; ring
  · have w := eq_add_of_le (Prf.hyp0 : [lowerF] ⊢[PRAAx] lowerF)
    refine le_of_eq_add (d := succ (var 1) * monus (pw (succ (var 1)) (succ (var 0)))
      (pw (var 1) (succ (var 0)) + succ (var 0) * pw (var 1) (var 0)) + succ (var 0) * pw (var 1) (var 0)) ?_
    refine withEq w fun e₀ => withEq (pw_succ (Γ := [lowerF]) (succ (var 1) : PTm 2) (succ (var 0))) fun e₁ =>
      withEq (pw_succ (Γ := [lowerF]) (var 1 : PTm 2) (succ (var 0))) fun e₂ =>
      withEq (pw_succ (Γ := [lowerF]) (var 1 : PTm 2) (var 0)) fun e₃ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂, e₀, e₃]; ring

/-- Variables: `0 = p`, `1 = i`. `(i+1)^{p+1} ≤ i^{p+1} + (p+1)(i+1)ᵖ`. -/
private abbrev upperF : Fm PTm 2 :=
  le (pw (succ (var 1)) (succ (var 0))) (pw (var 1) (succ (var 0)) + succ (var 0) * pw (succ (var 1)) (var 0))

private theorem upper₀ : ([] : List (Fm PTm 2)) ⊢[PRAAx] upperF := by
  ipra_ind (le_QF _ _) [subst_le, subst_ap2]
  · refine le_of_eq_add (d := zero) ?_
    refine withEq (pw_succ (Γ := []) (succ (var 0) : PTm 1) zero) fun e₁ =>
      withEq (pw_succ (Γ := []) (var 0 : PTm 1) zero) fun e₂ =>
      withEq (pw_zero (Γ := []) (succ (var 0) : PTm 1)) fun e₃ =>
      withEq (pw_zero (Γ := []) (var 0 : PTm 1)) fun e₄ => ?_
    apply deriveNat; ipra_simps; rw [e₁, e₂, e₃, e₄]; ring
  · have w := eq_add_of_le (Prf.hyp0 : [upperF] ⊢[PRAAx] upperF)
    have m := eq_add_of_le (pw_le_pw (Γ := [upperF]) (succ (var 0)) (le_succ_self (var 1 : PTm 2)))
    refine le_of_eq_add (d := succ (var 1) * monus (pw (var 1) (succ (var 0)) + succ (var 0) *
      pw (succ (var 1)) (var 0)) (pw (succ (var 1)) (succ (var 0))) +
      monus (pw (succ (var 1)) (succ (var 0))) (pw (var 1) (succ (var 0)))) ?_
    refine withEq w fun e₀ => withEq m fun e₅ =>
      withEq (pw_succ (Γ := [upperF]) (succ (var 1) : PTm 2) (succ (var 0))) fun e₁ =>
      withEq (pw_succ (Γ := [upperF]) (var 1 : PTm 2) (succ (var 0))) fun e₂ =>
      withEq (pw_succ (Γ := [upperF]) (succ (var 1) : PTm 2) (var 0)) fun e₃ => ?_
    apply deriveNat; ipra_simps
    rw [e₁, e₂]
    linear_combination (Groth.ι (Q.mk [upperF] (var 1)) + 1) * e₀ + e₅ + (Groth.ι (Q.mk [upperF] (var 0)) + 1) * e₃

theorem lower (i p : PTm n) :
    Γ ⊢[PRAAx] le (pw i (succ p) + succ p * pw i p) (pw (succ i) (succ p)) := by
  have h := inst (Γ := Γ) lower₀ (![p, i] : Fin 2 → PTm n)
  simpa using h

theorem upper (i p : PTm n) :
    Γ ⊢[PRAAx] le (pw (succ i) (succ p)) (pw i (succ p) + succ p * pw (succ i) p) := by
  have h := inst (Γ := Γ) upper₀ (![p, i] : Fin 2 → PTm n)
  simpa using h

/-! ## The quadrature -/

/-- Bodies over `0 = i`, `1 = p`. -/
abbrev Aq : PTm 2 := pw (var 0) (succ (var 1))
abbrev Bq : PTm 2 := pw (var 0) (var 1)
abbrev cq : PTm 1 := succ (var 0)

theorem inst2_A (i x : PTm n) : inst2 Aq i x = pw i (succ x) := by simp [inst2]
theorem inst2_B (i x : PTm n) : inst2 Bq i x = pw i x := by simp [inst2]
theorem inst2_Ash (i x : PTm n) : inst2 (shiftBody Aq) i x = pw (succ i) (succ x) := by
  rw [inst2_shiftBody, inst2_A]
theorem inst2_Bsh (i x : PTm n) : inst2 (shiftBody Bq) i x = pw (succ i) x := by
  rw [inst2_shiftBody, inst2_B]
theorem inst2_lowerBody (i x : PTm n) :
    inst2 (addBody Aq (mulParam cq Bq)) i x = pw i (succ x) + succ x * pw i x := by
  rw [inst2_addBody, inst2_A, inst2_mulParam, inst2_B]; simp
theorem inst2_upperBody (i x : PTm n) :
    inst2 (addBody Aq (mulParam cq (shiftBody Bq))) i x = pw i (succ x) + succ x * pw (succ i) x := by
  rw [inst2_addBody, inst2_A, inst2_mulParam, inst2_Bsh]; simp

/-- `lem:moment`: `(p + 1) S ≤ M^{p+1} ≤ (p + 1) S + (p + 1) Mᵖ`, `S = ∑_{i<M} iᵖ`;
variables `0 = p`, `1 = M`. -/
abbrev quadratureFormula : Fm PTm 2 :=
  le (succ (var 0) * ap2 (sumF Bq) (var 1) (var 0)) (pw (var 1) (succ (var 0))) ⋏
    le (pw (var 1) (succ (var 0)))
      (succ (var 0) * ap2 (sumF Bq) (var 1) (var 0) + succ (var 0) * pw (var 1) (var 0))

theorem power_sum_open : ([] : List (Fm PTm 2)) ⊢[PRAAx] quadratureFormula := by
  -- Abbreviations: `p = var 0`, `M = var 1`.
  have tA := telescope' (Γ := ([] : List (Fm PTm 2))) Aq (var 1) (var 0)
  have tB := telescope' (Γ := ([] : List (Fm PTm 2))) Bq (var 1) (var 0)
  rw [inst2_A, inst2_A] at tA
  rw [inst2_B, inst2_B] at tB
  have z : ([] : List (Fm PTm 2)) ⊢[PRAAx] pw zero (succ (var 0)) ≐ zero :=
    (pw_succ _ _).eqTrans (mul_zero _)
  -- Summed lower bound.
  have sL := sum_le (Γ := ([] : List (Fm PTm 2))) (addBody Aq (mulParam cq Bq)) (shiftBody Aq) (var 0) (var 1)
    (.allI (by
      simp only [inst2_lowerBody, inst2_Ash]
      exact .impI (lower _ _)))
  have aL := sum_add (Γ := ([] : List (Fm PTm 2))) Aq (mulParam cq Bq) (var 1) (var 0)
  have mL := sum_mul_param (Γ := ([] : List (Fm PTm 2))) cq Bq (var 1) (var 0)
  -- Summed upper bound.
  have sU := sum_le (Γ := ([] : List (Fm PTm 2))) (shiftBody Aq) (addBody Aq (mulParam cq (shiftBody Bq)))
    (var 0) (var 1) (.allI (by
      simp only [inst2_upperBody, inst2_Ash]
      exact .impI (upper _ _)))
  have aU := sum_add (Γ := ([] : List (Fm PTm 2))) Aq (mulParam cq (shiftBody Bq)) (var 1) (var 0)
  have mU := sum_mul_param (Γ := ([] : List (Fm PTm 2))) cq (shiftBody Bq) (var 1) (var 0)
  simp only [Syn.subst_var, Matrix.cons_val_zero, ConciseIPRA.PTm.subst_succ] at mL mU
  have wL := eq_add_of_le sL
  have wU := eq_add_of_le sU
  refine .andI ?_ ?_
  · refine le_of_eq_add (d := monus (ap2 (sumF (shiftBody Aq)) (var 1) (var 0))
      (ap2 (sumF (addBody Aq (mulParam cq Bq))) (var 1) (var 0))) ?_
    have h₁ := natEq tA; have h₂ := natEq z; have h₃ := natEq wL; have h₄ := natEq aL; have h₅ := natEq mL
    apply deriveNat; ipra_simps
    linear_combination -h₁ + h₃ + h₄ + h₅ + h₂
  · refine le_of_eq_add (d := monus (ap2 (sumF (addBody Aq (mulParam cq (shiftBody Bq)))) (var 1) (var 0))
      (ap2 (sumF (shiftBody Aq)) (var 1) (var 0)) + succ (var 0) * pw zero (var 0)) ?_
    have h₁ := natEq tA; have h₂ := natEq z; have h₃ := natEq wU; have h₄ := natEq aU; have h₅ := natEq mU
    have h₆ := natEq tB
    apply deriveNat; ipra_simps
    linear_combination h₁ - h₂ + h₃ - h₄ - h₅ - (Groth.ι (Q.mk [] (var 0)) + 1) * h₆

theorem power_sum_quadrature : ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 2 quadratureFormula :=
  closeUniv 2 power_sum_open

/-- `lem:moment` at given `p`, `M`: `(p + 1) ∑_{i<M} iᵖ ≤ M^{p+1} ≤ (p + 1) ∑_{i<M} iᵖ + (p + 1) Mᵖ`. -/
theorem moment (p M : PTm n) :
    Γ ⊢[PRAAx] le (succ p * ap2 (sumF Bq) M p) (pw M (succ p)) ⋏
      le (pw M (succ p)) (succ p * ap2 (sumF Bq) M p + succ p * pw M p) := by
  have i := inst (Γ := Γ) power_sum_open (![p, M] : Fin 2 → PTm n)
  simpa using i

end LeanProofs.IPRA.Analysis.PowerSums
