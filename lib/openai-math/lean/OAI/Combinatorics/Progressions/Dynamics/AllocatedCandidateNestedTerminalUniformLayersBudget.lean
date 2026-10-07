import OAI.Combinatorics.Progressions.Estimates.AllocatedCandidateTerminalNextWork

namespace OAI

section

namespace Erdos3.VectorPolynomial

private noncomputable def uniformLayersAffinePolynomial : Polynomial ℕ :=
  let X : Polynomial ℕ := Polynomial.X
  let Q := X + ((X + 2) ^ 2 + 2) ^ 63
  2 * X + (Q + 2) ^ 10 + (Q + 2) ^ 8 + 1

private theorem uniformLayersAffinePolynomial_eval (x : ℝ) :
    uniformLayersAffinePolynomial.eval₂ (Nat.castRingHom ℝ) x =
      certifiedAffineCenterBudget x := by
  simp only [uniformLayersAffinePolynomial, certifiedAffineCenterBudget,
    Polynomial.eval₂_add, Polynomial.eval₂_mul, Polynomial.eval₂_pow,
    Polynomial.eval₂_X, Polynomial.eval₂_ofNat, Polynomial.eval₂_one]

private noncomputable def uniformLayersTerminalPolynomial (s Cprimitive : ℕ) : Polynomial ℕ :=
  (Polynomial.X + Polynomial.C Cprimitive) ^ Cprimitive + Polynomial.X + Polynomial.X +
    Polynomial.C s * Polynomial.X * uniformLayersAffinePolynomial +
    uniformLayersAffinePolynomial + Polynomial.C s + Polynomial.X + 10

private theorem uniformLayersTerminalPolynomial_eval (s Cprimitive : ℕ) (x : ℝ) :
    (uniformLayersTerminalPolynomial s Cprimitive).eval₂ (Nat.castRingHom ℝ) x =
      (x + Cprimitive) ^ Cprimitive + x + x +
        s * x * certifiedAffineCenterBudget x + certifiedAffineCenterBudget x + s + x + 10 := by
  simp only [uniformLayersTerminalPolynomial, Polynomial.eval₂_add, Polynomial.eval₂_mul,
    Polynomial.eval₂_pow, Polynomial.eval₂_C, Polynomial.eval₂_X, Polynomial.eval₂_ofNat,
    Nat.coe_castRingHom, uniformLayersAffinePolynomial_eval]

attribute [local irreducible] certifiedAffineCenterBudget
  preparedFiniteForwardParameter preparedFiniteForwardWork preparedFiniteForwardCap
  preparedFiniteForwardBranch preparedFiniteForwardCumulative

private theorem terminalFullInput_le_uniformLayers (s m Cprimitive : ℕ)
    {x work cumulative u : ℝ} (hx : 0 ≤ x) (hc : 0 ≤ cumulative)
    (hmx : (m : ℝ) ≤ x) (hxu : x ≤ u) (hwu : work ≤ u) (hcu : cumulative ≤ u) :
    allocatedCandidateTerminalFullInput s m Cprimitive x work cumulative ≤
      (uniformLayersTerminalPolynomial s Cprimitive).eval₂ (Nat.castRingHom ℝ) u := by
  have hmu : (m : ℝ) ≤ u := hmx.trans hxu
  have hu : 0 ≤ u := hx.trans hxu
  have hB : certifiedAffineCenterBudget cumulative ≤ certifiedAffineCenterBudget u := by
    simpa only [uniformLayersAffinePolynomial_eval] using
      natPolynomial_eval_mono_nonneg uniformLayersAffinePolynomial hc hcu
  have hB0 : 0 ≤ certifiedAffineCenterBudget cumulative := by
    simpa only [uniformLayersAffinePolynomial_eval] using
      natPolynomial_eval_nonneg uniformLayersAffinePolynomial hc
  have hBu0 : 0 ≤ certifiedAffineCenterBudget u := hB0.trans hB
  rw [uniformLayersTerminalPolynomial_eval]
  unfold allocatedCandidateTerminalFullInput
  gcongr

private theorem exists_terminalFullInput_uniformLayers_polynomial_next_work
    (s Cprimitive : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ (m A : ℕ) (constants : ℕ → ℕ) {x : ℝ},
      C ≤ A → 0 ≤ x → (m : ℝ) ≤ x →
      P.eval₂ (Nat.castRingHom ℝ)
        (allocatedCandidateTerminalFullInput s m Cprimitive x
          (preparedFiniteForwardWork A constants s x)
          (preparedFiniteForwardCumulative A constants s x)) ≤
        preparedFiniteForwardWork A constants (s + 1) x := by
  obtain ⟨C, hC, hcap⟩ := exists_preparedFiniteForward_polynomial_cap
    (P.comp (uniformLayersTerminalPolynomial s Cprimitive))
  refine ⟨C, hC, ?_⟩
  intro m A constants x hCA hx hmx
  have hA : 2 ≤ A := hC.trans hCA
  have hzero : (0 : ℝ) ∈ Set.Icc 0 x := ⟨le_rfl, hx⟩
  have hprec := preparedFiniteForward_model_precision_bounds A constants s hx hzero hzero
  have hprefix := preparedFiniteForward_prefix_bounds A constants s hx
  have hwork := preparedFiniteForward_model_scalar_bounds A constants s 0 hA hx
    (by simpa only [Nat.cast_zero] using hx)
  let u := preparedFiniteForwardSourcePrecision A constants s x 0 0 +
    preparedFiniteForwardWork A constants s x
  have hwu : preparedFiniteForwardWork A constants s x ≤ u :=
    le_add_of_nonneg_left hprec.2.1
  have hxu : x ≤ u :=
    (le_preparedFiniteForwardParameter A constants s hx).trans (hwork.2.1.trans hwu)
  have hcu : preparedFiniteForwardCumulative A constants s x ≤ u :=
    hprefix.1.2.trans (hwork.2.1.trans hwu)
  have hinput := terminalFullInput_le_uniformLayers s m Cprimitive hx hprefix.1.1
    hmx hxu hwu hcu
  have hinput0 :=
    (allocatedCandidateTerminalFullInput_bounds s m Cprimitive hx hwork.1 hprefix.1.1).1
  have hP := natPolynomial_eval_mono_nonneg P hinput0 hinput
  have hcapP : P.eval₂ (Nat.castRingHom ℝ)
      ((uniformLayersTerminalPolynomial s Cprimitive).eval₂ (Nat.castRingHom ℝ) u) ≤
        preparedFiniteForwardCap A constants s x := by
    simpa only [Polynomial.eval₂_comp, u] using hcap A constants s hCA hx hzero hzero
  have hnext := preparedFiniteForward_model_scalar_bounds A constants (s + 1) 0 hA hx
    (by simpa only [Nat.cast_zero] using hx)
  have hcapNext : preparedFiniteForwardCap A constants s x ≤
      preparedFiniteForwardParameter A constants (s + 1) x := by
    rw [preparedFiniteForwardParameter_succ]
    have hb := preparedFiniteForwardParameter_nonneg A constants s hx
    have hbranch := preparedFiniteForwardBranch_nonneg A constants s hx
    linarith only [hb, hbranch]
  exact (hP.trans hcapP).trans (hcapNext.trans hnext.2.1)

theorem exists_allocatedCandidateNestedTerminal_uniformLayers_polynomial_budget
    (s Cprimitive : ℕ) (P : Polynomial ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧
      ∀ (m A : ℕ) (constants : ℕ → ℕ) (innerDepth outer : ℕ) {x : ℝ},
        C ≤ A → s + 1 ≤ innerDepth → 0 ≤ x →
        (m : ℝ) ≤ candidateNestedForwardSeed A constants innerDepth outer x →
        let seed := candidateNestedForwardSeed A constants innerDepth outer x
        P.eval₂ (Nat.castRingHom ℝ)
          (allocatedCandidateTerminalFullInput s m Cprimitive seed
            (preparedFiniteForwardWork A constants s seed)
            (preparedFiniteForwardCumulative A constants s seed)) ≤
          candidateNestedForwardSeed A constants innerDepth (outer + 1) x := by
  obtain ⟨C, hC, hbound⟩ :=
    exists_terminalFullInput_uniformLayers_polynomial_next_work s Cprimitive P
  refine ⟨C, hC, ?_⟩
  intro m A constants innerDepth outer x hCA hdepth hx hm seed
  have hseed : 0 ≤ seed := candidateNestedForwardSeed_nonneg A constants innerDepth outer hx
  exact (hbound m A constants hCA hseed hm).trans
    (candidateNestedForwardWork_le_next_seed A constants innerDepth outer (s + 1) hx hdepth)

end Erdos3.VectorPolynomial

end

end OAI
