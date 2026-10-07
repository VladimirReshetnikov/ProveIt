import OAI.Combinatorics.Progressions.Estimates.NativeCorrelatedFactorFamily
import OAI.Combinatorics.Progressions.Polynomial.CommonAnchorPolynomialCorrections

namespace OAI

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

namespace NilpotentLieFiltration

theorem polynomialOrbitEval_zero_iff_coefficient_zero
    {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ) (g : F.PolynomialOrbit w) :
    F.polynomialOrbitEval w 0 g = 1 ↔ coefficients g.log 0 = 0 := by
  constructor
  · intro h
    have hc := congrArg NilpotentLieBCHGroup.coord h
    simpa only [F.polynomialOrbitEval_coord, Pi.zero_apply, Int.cast_zero,
      eval_zero_eq_coefficient, NilpotentLieBCHGroup.coord_one] using hc
  · intro h
    apply NilpotentLieBCHGroup.ext
    simpa only [F.polynomialOrbitEval_coord, Pi.zero_apply, Int.cast_zero,
      eval_zero_eq_coefficient, NilpotentLieBCHGroup.coord_one] using h

end NilpotentLieFiltration

theorem toAdd_hom_corrected_factor {G V : Type*} [Group G] [AddCommGroup V]
    (f : G →* Multiplicative V) (g₀ ε g γ : G) :
    Multiplicative.toAdd (f (g₀⁻¹ * ε⁻¹ * g * γ⁻¹)) =
      Multiplicative.toAdd (f g) - Multiplicative.toAdd (f g₀) -
        Multiplicative.toAdd (f ε) - Multiplicative.toAdd (f γ) := by
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
  abel

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_dependent_orbit_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors) (h₀ : ZMod N),
            h₀ ∈ A.shifts ∧ A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∀ h ∈ A.shifts, ∃ ε γ v : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                  (fun _ : Unit => 1) 0 ε = 1 ∧
                W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                  (fun _ : Unit => 1) 0 γ = 1 ∧
                W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                  (fun _ : Unit => 1) 0 v = 1 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) ε.log ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                ε * W.family.rank.orbitEquiv (fun _ : Unit => 1) (W.family.orbit h₀) * v * γ =
                  W.family.rank.orbitEquiv (fun _ : Unit => 1) (W.family.orbit h) ∧
                ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    hs c τ hG (fun _ : Unit => 1) (α d) v) ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ := by
  obtain ⟨C, hC, hfamily⟩ := exists_native_dependent_polynomial_corrections s hs
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPC, R, D, A, h₀,
      hh₀, hAW, hdensity, n, hn, hnC, hproj, hcorrection⟩ := hfamily W hF c τ hG hN
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPC, R, D, A, h₀,
    hh₀, hAW, hdensity, n, hn, hnC, hproj, ?_⟩
  intro h hh
  obtain ⟨E, Q, hE₀, hQ₀, hE, hQ, hres⟩ := hcorrection h hh
  let ε : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
    ⟨⟨E.val⟩, E.property⟩
  let γ : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
    ⟨⟨Q.val⟩, Q.property⟩
  let g := W.family.rank.orbitEquiv (fun _ : Unit => 1) (W.family.orbit h)
  let g₀ := W.family.rank.orbitEquiv (fun _ : Unit => 1) (W.family.orbit h₀)
  let v := g₀⁻¹ * ε⁻¹ * g * γ⁻¹
  have hε₀ : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 ε = 1 :=
    (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ ε).mpr hE₀
  have hγ₀ : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 γ = 1 :=
    (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ γ).mpr hQ₀
  have hg : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 g = 1 := W.family.orbit_rank_normalized h
  have hg₀ : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 g₀ = 1 := W.family.orbit_rank_normalized h₀
  refine ⟨ε, γ, v, hε₀, hγ₀, ?_, hE, hQ, ?_, ?_⟩
  · simp only [v, map_mul, map_inv, hg₀, hε₀, hg, hγ₀, inv_one, one_mul]
  · change ε * g₀ * v * γ = g
    dsimp only [v]
    group
  · intro d hd
    obtain ⟨e, u, he, hu, hdep⟩ := hres d hd
    have hε := W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
      hs c τ hG (fun _ : Unit => 1) (α d) ε e he.symm
    have hγ := W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
      hs c τ hG (fun _ : Unit => 1) (α d) γ u hu.symm
    have hv : Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
        hs c τ hG (fun _ : Unit => 1) (α d) v) =
        W.family.horizontalCoefficient hs c τ hG (α d) h -
          W.family.horizontalCoefficient hs c τ hG (α d) h₀ -
          W.family.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) e -
          W.family.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) u := by
      have hv := toAdd_hom_corrected_factor
        (W.family.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG
          (fun _ : Unit => 1) (α d)) g₀ ε g γ
      rw [hε, hγ] at hv
      exact hv
    rw [hv]
    exact hdep

end Erdos3

end

section

namespace Erdos3

open Module VectorPolynomial

namespace VectorPolynomial

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] [LieAlgebra ℝ L]

theorem CoefficientBound.add (b : Basis ι ℝ L) (T : σ → ℝ) {M N : ℝ}
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientBound b T M P) (hQ : CoefficientBound b T N Q) :
    CoefficientBound b T (M + N) (P + Q) := by
  intro α i
  simp only [map_add, Finsupp.add_apply]
  exact (abs_add_le _ _).trans ((add_le_add (hP α i) (hQ α i)).trans_eq (add_div _ _ _).symm)

theorem CoefficientGrid.add (b : Basis ι ℝ L) (l : ℕ)
    {P Q : VectorPolynomial σ ℚ L} (hP : CoefficientGrid b l P) (hQ : CoefficientGrid b l Q) :
    CoefficientGrid b l (P + Q) := by
  intro α
  obtain ⟨a, ha⟩ := hP α
  obtain ⟨c, hc⟩ := hQ α
  refine ⟨a + c, ?_⟩
  funext i
  simp only [Pi.add_apply, Int.cast_add, map_add, Finsupp.add_apply]
  change (a i : ℝ) + (c i : ℝ) =
    (l : ℝ) * (b.repr (coefficients P α) i + b.repr (coefficients Q α) i)
  exact (congrArg₂ (· + ·) (congrFun ha i) (congrFun hc i)).trans (mul_add _ _ _).symm

end VectorPolynomial

theorem toAdd_hom_corrected_reference {G V : Type*} [Group G] [AddCommGroup V]
    (f : G →* Multiplicative V) (ε g γ : G) :
    Multiplicative.toAdd (f (ε⁻¹ * g * γ⁻¹)) =
      Multiplicative.toAdd (f g) - Multiplicative.toAdd (f ε) - Multiplicative.toAdd (f γ) := by
  simp only [map_mul, map_inv, toAdd_mul, toAdd_inv]
  abel

theorem sub_corrected_reference_add_errors {V : Type*} [AddCommGroup V]
    (x y a b a₀ b₀ : V) :
    x - (y - a₀ - b₀) - (a + a₀) - (b + b₀) = x - y - a - b := by
  abel

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

theorem exists_native_periodic_factorization_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + a) ^ a ≤ (p + C) ^ C ∧
      ((p + a) ^ a + 1 + b) ^ b ≤ (p + C) ^ C := by
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B + (B + 1 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hB : 0 ≤ (p + a) ^ a := by positivity
  have hM : 0 ≤ ((p + a) ^ a + 1 + b) ^ b := by positivity
  have hsum : (p + a) ^ a + ((p + a) ^ a + 1 + b) ^ b ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hsum, hM], by linarith only [hsum, hB]⟩

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_periodic_dependent_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors) (h₀ : ZMod N),
            h₀ ∈ A.shifts ∧ A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n M : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∀ h ∈ A.shifts, ∃ ε γ v : W.family.model.filtration.realification.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 γ = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) ε.log ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                ε * W.family.orbit h₀ * v * γ = W.family.orbit h ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    hs c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) v)) ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ) : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)) ∧
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ)⁻¹ : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)⁻¹) := by
  obtain ⟨a, _, hfactor⟩ := exists_native_dependent_orbit_factorization s hs
  obtain ⟨b, _, hperiod⟩ := exists_native_orbit_rational_period s
  obtain ⟨C, hC, hbudget⟩ := exists_native_periodic_factorization_budget a b
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨hBC, hperiodC⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A, h₀,
      hh₀, hAW, hdensity, n, hn, hnB, hproj, hsplit⟩ :=
    hfactor W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B + 1 := (hpq.trans (hqP.trans hPB)).trans (by linarith)
  obtain ⟨M, hM, hMB, hMsolve⟩ := hperiod W.family.model (fun _ : Unit => 1)
    (fun _ => Nat.zero_lt_one) (B + 1) (by linarith)
    (RationalFilteredNilmanifold.GeometryComplexityLE.mono W.family.model W.family.complexity.1 hpB)
    (by simpa only [Fintype.card_unit, Nat.cast_one] using (show (1 : ℝ) ≤ B + 1 by linarith))
    n hn (hnB.trans (Real.exp_le_exp.mpr (by linarith)))
  have hlog (g : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1)) :
      ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g).log = g.log := by
    simpa only [MulEquiv.apply_symm_apply] using
      (W.family.rank.orbitEquiv_log (fun _ : Unit => 1)
        ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g)).symm
  have heval (g : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1))
      (x : Unit → ℤ) :
      W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x
          ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g) =
        W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval (fun _ : Unit => 1) x g := by
    simpa only [MulEquiv.apply_symm_apply] using
      (W.family.rank.orbitEquiv_eval (fun _ : Unit => 1)
        ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g) x).symm
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A, h₀,
    hh₀, hAW, ?_, n, M, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hM,
    hMB.trans (Real.exp_le_exp.mpr hperiodC), hproj, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro h hh
    obtain ⟨ε, γ, v, hε₀, hγ₀, hv₀, hε, hγ, heq, hdep⟩ := hsplit h hh
    let ε' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm ε
    let γ' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm γ
    let v' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm v
    have hgrid : CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ'.log := by
      simpa only [γ', hlog] using hγ
    refine ⟨ε', γ', v', (heval ε 0).trans hε₀, (heval γ 0).trans hγ₀,
      (heval v 0).trans hv₀, ?_, hgrid, ?_, ?_, hMsolve γ' hgrid⟩
    · apply CoefficientBound.mono (W.family.model.basis.baseChange ℝ)
        (fun _ : Unit => (N : ℝ)) (fun _ => by exact_mod_cast NeZero.pos N)
        (M := Real.exp B) _ (Real.exp_le_exp.mpr hBC)
      simpa only [ε', hlog] using hε
    · have hf := congrArg (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm heq
      simpa only [map_mul, MulEquiv.symm_apply_apply] using hf
    · intro d hd
      simpa only [v', MulEquiv.apply_symm_apply] using hdep d hd

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

theorem exists_common_reference_correction_budget (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      let B := (p + a) ^ a
      B ≤ (p + C) ^ C ∧ B + ((B + 3) ^ 2 + s * B) + 2 ≤ (p + C) ^ C := by
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B + ((B + 3) ^ 2 + Polynomial.C s * B) + 2)
  refine ⟨C, hC, ?_⟩
  intro p hp B'
  have hB : 0 ≤ B' := by dsimp only [B']; positivity
  have hrest : 0 ≤ (B' + 3) ^ 2 + s * B' := by positivity
  have hcost : B' + ((B' + 3) ^ 2 + s * B') + 2 ≤ (p + C) ^ C := by
    simpa [B, B', Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hcost, hrest], hcost⟩

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_common_dependent_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors), A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∃ ξ : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                  (fun _ : Unit => 1) 0 ξ = 1 ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    hs c τ hG (fun _ : Unit => 1) (α d) ξ) ∈
                    (fourFirstProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                ∀ h ∈ A.shifts, ∃ ε γ v : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit
                    (fun _ : Unit => 1),
                  W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                    (fun _ : Unit => 1) 0 ε = 1 ∧
                  W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                    (fun _ : Unit => 1) 0 γ = 1 ∧
                  W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
                    (fun _ : Unit => 1) 0 v = 1 ∧
                  CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                    (Real.exp ((p + C) ^ C)) ε.log ∧
                  CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                  ε * ξ * v * γ = W.family.rank.orbitEquiv (fun _ : Unit => 1) (W.family.orbit h) ∧
                  ∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                    Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                      hs c τ hG (fun _ : Unit => 1) (α d) v) ∈
                      (fourDependentProjection (D.horizontal
                        ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ := by
  obtain ⟨a, _, hfamily⟩ := exists_native_dependent_polynomial_corrections s hs
  obtain ⟨C, hC, hbudget⟩ := exists_common_reference_correction_budget s a
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨hBC, hcost⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A, h₀,
      hh₀, hAW, hdensity, n, hn, hnB, hproj, hcorrection⟩ :=
    hfamily W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hq : 0 ≤ q := hp.trans hpq
  have hP : 0 ≤ P := hq.trans hqP
  let S := (P + 3) ^ 2 + (s : ℝ) * q
  have hS : 0 ≤ S := by dsimp only [S]; positivity
  have hSB : S ≤ (B + 3) ^ 2 + s * B :=
    add_le_add (pow_le_pow_left₀ (by linarith) (add_le_add hPB (le_refl 3)) 2)
      (mul_le_mul_of_nonneg_left (hqP.trans hPB) (Nat.cast_nonneg s))
  have hsum : Real.exp B + Real.exp S ≤ Real.exp ((p + C) ^ C) := by
    calc
      _ ≤ Real.exp B + Real.exp B + Real.exp S := by linarith [Real.exp_nonneg B]
      _ ≤ Real.exp (B + S + 2) := exp_repeated_add_le hB hS
      _ ≤ _ := Real.exp_le_exp.mpr ((add_le_add (add_le_add (le_refl B) hSB) (le_refl 2)).trans hcost)
  obtain ⟨E₀, Q₀, hE₀zero, hQ₀zero, hE₀, hQ₀, href⟩ :=
    A.exists_anchor_polynomial_corrections h₀ hh₀ hs hq hP c τ hG n hproj
  have hd (d : Fin s) : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s := by
    simpa only [α, Finsupp.weight_single, smul_eq_mul, mul_one] using Nat.succ_le_of_lt d.isLt
  choose e₀ u₀ he₀ hu₀ hfirst using (fun d => href d (hd d))
  let ε₀ : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
    ⟨⟨E₀.val⟩, E₀.property⟩
  let γ₀ : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
    ⟨⟨Q₀.val⟩, Q₀.property⟩
  let g₀ := W.family.rank.orbitEquiv (fun _ : Unit => 1) (W.family.orbit h₀)
  let ξ := ε₀⁻¹ * g₀ * γ₀⁻¹
  have hε₀zero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 ε₀ = 1 :=
    (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ ε₀).mpr hE₀zero
  have hγ₀zero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 γ₀ = 1 :=
    (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ γ₀).mpr hQ₀zero
  have hg₀ : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 g₀ = 1 := W.family.orbit_rank_normalized h₀
  have hξzero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
      (fun _ : Unit => 1) 0 ξ = 1 := by
    simp only [ξ, map_mul, map_inv, hε₀zero, hγ₀zero, hg₀, inv_one, one_mul]
  have hξvalue (d : Fin s) :
      Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
        hs c τ hG (fun _ : Unit => 1) (α d) ξ) =
      W.family.horizontalCoefficient hs c τ hG (α d) h₀ -
        W.family.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) (e₀ d) -
        W.family.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d)) (u₀ d) := by
    have he := W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
      hs c τ hG (fun _ : Unit => 1) (α d) ε₀ (e₀ d) (he₀ d).symm
    have hu := W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
      hs c τ hG (fun _ : Unit => 1) (α d) γ₀ (u₀ d) (hu₀ d).symm
    have h := toAdd_hom_corrected_reference
      (W.family.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ : Unit => 1) (α d)) ε₀ g₀ γ₀
    rw [he, hu] at h
    exact h
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A,
    hAW, ?_, n, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hproj, ξ, hξzero, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro d hd'
    rw [hξvalue]
    exact hfirst d
  · intro h hh
    obtain ⟨E, Q, hEzero, hQzero, hE, hQ, hres⟩ := hcorrection h hh
    let ε : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
      ⟨⟨(E + E₀).val⟩, (E + E₀).property⟩
    let γ : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1) :=
      ⟨⟨(Q + Q₀).val⟩, (Q + Q₀).property⟩
    let g := W.family.rank.orbitEquiv (fun _ : Unit => 1) (W.family.orbit h)
    let v := ξ⁻¹ * ε⁻¹ * g * γ⁻¹
    have hεzero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
        (fun _ : Unit => 1) 0 ε = 1 := by
      apply (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ ε).mpr
      change coefficients (E.val + E₀.val) 0 = 0
      simp only [map_add, Finsupp.add_apply, hEzero, hE₀zero, add_zero]
    have hγzero : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
        (fun _ : Unit => 1) 0 γ = 1 := by
      apply (NilpotentLieFiltration.polynomialOrbitEval_zero_iff_coefficient_zero _ _ γ).mpr
      change coefficients (Q.val + Q₀.val) 0 = 0
      simp only [map_add, Finsupp.add_apply, hQzero, hQ₀zero, add_zero]
    have hg : W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval
        (fun _ : Unit => 1) 0 g = 1 := W.family.orbit_rank_normalized h
    refine ⟨ε, γ, v, hεzero, hγzero, ?_, ?_, ?_, ?_, ?_⟩
    · simp only [v, map_mul, map_inv, hξzero, hεzero, hg, hγzero, inv_one, one_mul]
    · exact CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N)
        (CoefficientBound.add _ _ hE hE₀) hsum
    · exact CoefficientGrid.add _ _ hQ hQ₀
    · change ε * ξ * v * γ = g
      dsimp only [v]
      group
    · intro d hd'
      obtain ⟨e, u, he, hu, hdep⟩ := hres d hd'
      let π := W.family.rank.filtration.realHorizontalMap (Finsupp.weight (fun _ : Unit => 1) (α d))
      have hεvalue : Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
          hs c τ hG (fun _ : Unit => 1) (α d) ε) = π e + π (e₀ d) := by
        apply (W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
          hs c τ hG (fun _ : Unit => 1) (α d) ε (e + e₀ d) ?_).trans (map_add π e (e₀ d))
        change e.val + (e₀ d).val = coefficients (E.val + E₀.val) (α d)
        rw [map_add, Finsupp.add_apply, he, he₀]
      have hγvalue : Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
          hs c τ hG (fun _ : Unit => 1) (α d) γ) = π u + π (u₀ d) := by
        apply (W.family.rank.filtration.nativeHorizontalCoefficientHom_eq_realHorizontalMap
          hs c τ hG (fun _ : Unit => 1) (α d) γ (u + u₀ d) ?_).trans (map_add π u (u₀ d))
        change u.val + (u₀ d).val = coefficients (Q.val + Q₀.val) (α d)
        rw [map_add, Finsupp.add_apply, hu, hu₀]
      have hv := toAdd_hom_corrected_factor
        (W.family.rank.filtration.nativeHorizontalCoefficientHom hs c τ hG (fun _ : Unit => 1) (α d)) ξ ε g γ
      rw [hξvalue d, hεvalue, hγvalue] at hv
      have hv' := hv.trans (sub_corrected_reference_add_errors
        (W.family.horizontalCoefficient hs c τ hG (α d) h)
        (W.family.horizontalCoefficient hs c τ hG (α d) h₀) (π e) (π u) (π (e₀ d)) (π (u₀ d)))
      exact (congrArg (fun z => z ∈ (fourDependentProjection (D.horizontal
        ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd'⟩)).baseChange ℝ) hv').mpr hdep

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_periodic_common_factorization (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors), A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n M : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∃ ξ : W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1 ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    hs c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) ξ)) ∈
                    (fourFirstProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
              ∀ h ∈ A.shifts, ∃ ε γ v : W.family.model.filtration.realification.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 γ = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) ε.log ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                ε * ξ * v * γ = W.family.orbit h ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    hs c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) v)) ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ) : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)) ∧
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ)⁻¹ : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)⁻¹) := by
  obtain ⟨a, _, hfactor⟩ := exists_native_common_dependent_factorization s hs
  obtain ⟨b, _, hperiod⟩ := exists_native_orbit_rational_period s
  obtain ⟨C, hC, hbudget⟩ := exists_native_periodic_factorization_budget a b
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨hBC, hperiodC⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A,
      hAW, hdensity, n, hn, hnB, hproj, ξ, hξ₀, hfirst, hsplit⟩ :=
    hfactor W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B + 1 := (hpq.trans (hqP.trans hPB)).trans (by linarith)
  obtain ⟨M, hM, hMB, hMsolve⟩ := hperiod W.family.model (fun _ : Unit => 1)
    (fun _ => Nat.zero_lt_one) (B + 1) (by linarith)
    (RationalFilteredNilmanifold.GeometryComplexityLE.mono W.family.model W.family.complexity.1 hpB)
    (by simpa only [Fintype.card_unit, Nat.cast_one] using (show (1 : ℝ) ≤ B + 1 by linarith))
    n hn (hnB.trans (Real.exp_le_exp.mpr (by linarith)))
  have hlog (g : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1)) :
      ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g).log = g.log := by
    simpa only [MulEquiv.apply_symm_apply] using
      (W.family.rank.orbitEquiv_log (fun _ : Unit => 1)
        ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g)).symm
  have heval (g : W.family.rank.filtration.realification.associatedDegree.PolynomialOrbit (fun _ : Unit => 1))
      (x : Unit → ℤ) :
      W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x
          ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g) =
        W.family.rank.filtration.realification.associatedDegree.polynomialOrbitEval (fun _ : Unit => 1) x g := by
    simpa only [MulEquiv.apply_symm_apply] using
      (W.family.rank.orbitEquiv_eval (fun _ : Unit => 1)
        ((W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm g) x).symm
  let ξ' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm ξ
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A,
    hAW, ?_, n, M, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hM,
    hMB.trans (Real.exp_le_exp.mpr hperiodC), hproj, ξ', (heval ξ 0).trans hξ₀, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro d hd
    simpa only [ξ', MulEquiv.apply_symm_apply] using hfirst d hd
  · intro h hh
    obtain ⟨ε, γ, v, hε₀, hγ₀, hv₀, hε, hγ, heq, hdep⟩ := hsplit h hh
    let ε' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm ε
    let γ' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm γ
    let v' := (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm v
    have hgrid : CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ'.log := by
      simpa only [γ', hlog] using hγ
    refine ⟨ε', γ', v', (heval ε 0).trans hε₀, (heval γ 0).trans hγ₀,
      (heval v 0).trans hv₀, ?_, hgrid, ?_, ?_, hMsolve γ' hgrid⟩
    · apply CoefficientBound.mono (W.family.model.basis.baseChange ℝ)
        (fun _ : Unit => (N : ℝ)) (fun _ => by exact_mod_cast NeZero.pos N)
        (M := Real.exp B) _ (Real.exp_le_exp.mpr hBC)
      simpa only [ε', hlog] using hε
    · have hf := congrArg (W.family.rank.orbitEquiv (fun _ : Unit => 1)).symm heq
      simpa only [map_mul, MulEquiv.symm_apply_apply] using hf
    · intro d hd
      simpa only [v', MulEquiv.apply_symm_apply] using hdep d hd

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

theorem exists_frozen_common_factorization_budget (a b : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ p : ℝ, 0 ≤ p →
      (p + a) ^ a ≤ (p + C) ^ C ∧
      ((p + a) ^ a + 2 + b) ^ b ≤ (p + C) ^ C := by
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    (B + (B + 2 + Polynomial.C b) ^ b)
  refine ⟨C, hC, ?_⟩
  intro p hp
  have hB : 0 ≤ (p + a) ^ a := by positivity
  have hF : 0 ≤ ((p + a) ^ a + 2 + b) ^ b := by positivity
  have hsum : (p + a) ^ a + ((p + a) ^ a + 2 + b) ^ b ≤ (p + C) ^ C := by
    simpa [B, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨by linarith only [hsum, hF], by linarith only [hsum, hB]⟩

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_frozen_common_factorization (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors), A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n M : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∃ ξ : W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1 ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) ξ)) ∈
                    (fourFirstProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
              ∀ h ∈ A.shifts, ∃ ε γ v : W.family.model.filtration.realification.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 γ = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) ε.log ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                ε * ξ * v * γ = W.family.orbit h ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) v)) ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                (∃ y : ZMod N,
                  (∀ x, ∑ i, ‖W.family.model.frozenCyclicOrbitValue
                    (W.family.vertical.observable i) ε (ξ * v) γ y x‖ ^ 2 = 1) ∧
                  Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
                    (W.replacedRankResidual h (fun i x => W.family.model.frozenCyclicOrbitValue
                      (W.family.vertical.observable i) ε (ξ * v) γ y x)))) ∧
                ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ) : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)) ∧
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ)⁻¹ : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)⁻¹) := by
  obtain ⟨a, _, hfactor⟩ := exists_native_periodic_common_factorization s (by omega)
  obtain ⟨b, _, hfreeze⟩ := exists_native_frozen_rank_correlation s 1 hs
  obtain ⟨C, hC, hbudget⟩ := exists_frozen_common_factorization_budget a b
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨hBC, hFC⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A,
      hAW, hdensity, n, M, hn, hnB, hM, hMB, hproj, ξ, hξ₀, hfirst, hsplit⟩ :=
    hfactor W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B + 2 := (hpq.trans (hqP.trans hPB)).trans (by linarith)
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A,
    hAW, ?_, n, M, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hM,
    hMB.trans (Real.exp_le_exp.mpr hBC), hproj, ξ, hξ₀, hfirst, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro h hh
    obtain ⟨ε, γ, v, hε₀, hγ₀, hv₀, hε, hγ, heq, hdep, hperiod⟩ := hsplit h hh
    have hε' : CoefficientBound (W.family.model.basis.baseChange ℝ)
        (fun _ : Unit => (N : ℝ)) (Real.exp (((B + 2) + 2) ^ 1)) ε.log :=
      CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) hε
        (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
    obtain ⟨y, hunit, V⟩ := hfreeze W hF ⟨h, hAW hh⟩ (B + 2) (by linarith) hpB M hM
      (hMB.trans (Real.exp_le_exp.mpr (by linarith))) ε ξ v γ heq hε'
      (fun x y hxy => (hperiod x y hxy).1) ((Real.exp_le_exp.mpr hFC).trans hN)
    refine ⟨ε, γ, v, hε₀, hγ₀, hv₀, ?_, hγ, heq, hdep,
      ⟨y, hunit, ⟨(Classical.choice V).mono hFC⟩⟩, hperiod⟩
    exact CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) hε
      (Real.exp_le_exp.mpr hBC)

end Erdos3

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold VectorPolynomial
open scoped TensorProduct BigOperators

attribute [local instance] NativeDegreeRankFamily.lie NativeDegreeRankFamily.algebra
  NativeDegreeRankFamily.topology NativeDegreeRankFamily.topologicalAdd
  NativeDegreeRankFamily.continuousSMul NativeDegreeRankFamily.hausdorff
  NativeIntegerExpansion.lie NativeIntegerExpansion.algebra
  NativeIntegerExpansion.topology NativeIntegerExpansion.topologicalAdd
  NativeIntegerExpansion.continuousSMul NativeIntegerExpansion.hausdorff

theorem exists_native_covered_common_factorization (s : ℕ) (hs : 2 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {κ : Type*} {r N : ℕ} [NeZero N] {p : ℝ} {F : ZMod N → ℂ}
      (W : NativeCorrelationStructure s r N p F), (∀ x, ‖F x‖ ≤ 1) →
      ∀ (c : Basis κ ℚ W.family.L) (τ : κ → ℕ)
        (hG : ∀ j, W.family.rank.filtration.associatedDegree.layer j =
          Submodule.span ℚ (c '' {i | j ≤ τ i})),
        Real.exp ((p + C) ^ C) ≤ N →
        let α : Fin s → Unit →₀ ℕ := fun d => Finsupp.single () (d.val + 1)
        ∃ (out : Fin W.family.outputDim) (H : Finset (ZMod N)) (q P : ℝ),
          H ⊆ W.shifts ∧ H.Nonempty ∧ CyclicShortShiftSet H ∧
          p ≤ q ∧ q ≤ P ∧ P ≤ (p + C) ^ C ∧
          ∃ (R : NativeRankRelation W.family out H q q) (D : R.CommonData P)
            (A : D.SparseAnchors), A.shifts ⊆ W.shifts ∧
            Real.exp (-((p + C) ^ C)) * Fintype.card (ZMod N) ≤ (A.shifts.card : ℝ) ∧
            ∃ n M : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              0 < M ∧ (M : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
              (∀ t (ht : t ∈ D.quadruples), (D.witness t ht).projectedDenominator ∣ n) ∧
              ∃ ξ : W.family.model.filtration.realification.PolynomialOrbit (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ξ = 1 ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) ξ)) ∈
                    (fourFirstProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
              ∃ Λ : Subgroup W.family.model.filtration.Group, Λ ≤ W.family.model.lattice ∧
                (Λ.subgroupOf W.family.model.lattice).Characteristic ∧
                (Λ.subgroupOf W.family.model.lattice).Normal ∧
                (Λ.subgroupOf W.family.model.lattice).FiniteIndex ∧
                (Λ.relIndex W.family.model.lattice : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
                ∃ (K : ℕ) (hK : 0 < K)
                  (hin : scaledIntegerGrid K ⊆ bchSubgroupCoordinates W.family.model.basis Λ)
                  (hout : bchSubgroupCoordinates W.family.model.basis Λ ⊆ denominatorGrid K),
                  (W.family.rank.withLattice Λ K hK hin hout).ComplexityLE ((p + C) ^ C) ∧
              ∀ h ∈ A.shifts, ∃ ε γ v : W.family.model.filtration.realification.PolynomialOrbit
                  (fun _ : Unit => 1),
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 ε = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 γ = 1 ∧
                W.family.model.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) 0 v = 1 ∧
                CoefficientBound (W.family.model.basis.baseChange ℝ) (fun _ : Unit => (N : ℝ))
                  (Real.exp ((p + C) ^ C)) ε.log ∧
                CoefficientGrid (W.family.model.basis.baseChange ℝ) n γ.log ∧
                ε * ξ * v * γ = W.family.orbit h ∧
                (∀ d (hd : Finsupp.weight (fun _ : Unit => 1) (α d) ≤ s),
                  Multiplicative.toAdd (W.family.rank.filtration.nativeHorizontalCoefficientHom
                    (by omega) c τ hG (fun _ : Unit => 1) (α d)
                    (W.family.rank.orbitEquiv (fun _ : Unit => 1) v)) ∈
                    (fourDependentProjection (D.horizontal
                      ⟨Finsupp.weight (fun _ : Unit => 1) (α d), Nat.lt_succ_of_le hd⟩)).baseChange ℝ) ∧
                (∃ y : ZMod N,
                  ∃ U : (W.family.model.withLattice Λ K hK hin hout).UnitVerticalObservable
                      ((W.family.rank.withLattice Λ K hK hin hout).realSubgroup s r)
                      (Fin W.family.outputDim) ((p + C) ^ C),
                    U.frequency = W.family.vertical.frequency ∧
                    (∀ (i : Fin W.family.outputDim) (x : ZMod N), U.observable i (QuotientGroup.mk
                      (W.family.model.filtration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v))) =
                      W.family.model.frozenCyclicOrbitValue
                        (W.family.vertical.observable i) ε (ξ * v) γ y x) ∧
                    Nonempty (NativeVectorCorrelation (s - 1) N ((p + C) ^ C)
                      (W.replacedRankResidual h (fun i x => U.observable i (QuotientGroup.mk
                        (W.family.model.filtration.realification.polynomialOrbitEval
                          (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v))))))) ∧
                ∀ x y : Unit → ℤ, (∀ j, (M : ℤ) ∣ x j - y j) →
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ) : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)) ∧
                  ((QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                    (fun _ : Unit => 1) x γ)⁻¹ : W.family.model.Space) =
                    QuotientGroup.mk (W.family.model.filtration.realification.polynomialOrbitEval
                      (fun _ : Unit => 1) y γ)⁻¹) := by
  obtain ⟨a, _, hfactor⟩ := exists_native_frozen_common_factorization s hs
  obtain ⟨b, _, hcover⟩ := exists_native_frozen_orbit_cover s 1
  obtain ⟨C, hC, hbudget⟩ := exists_frozen_common_factorization_budget a b
  refine ⟨C, hC, ?_⟩
  intro κ r N _ p F W hF c τ hG hN α
  have hp : 0 ≤ p := (Nat.cast_nonneg W.family.dim).trans W.family.complexity.1.1
  let B := (p + a) ^ a
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  obtain ⟨hBC, hCC⟩ := hbudget p hp
  obtain ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB, R, D, A,
      hAW, hdensity, n, M, hn, hnB, hM, hMB, hproj, ξ, hξ₀, hfirst, hsplit⟩ :=
    hfactor W hF c τ hG ((Real.exp_le_exp.mpr hBC).trans hN)
  have hpB : p ≤ B + 2 := (hpq.trans (hqP.trans hPB)).trans (by linarith)
  obtain ⟨Λ, hΛ, hchar, hnormal, hfinite, hindex, K, hK, hin, hout, hRank, hU⟩ :=
    hcover (I := Fin W.family.outputDim) (N := N) W.family.model W.family.rank
      (B + 2) (by linarith) (W.family.complexity.mono W.family.rank hpB)
      n hn (hnB.trans (Real.exp_le_exp.mpr (by linarith)))
  refine ⟨out, H, q, P, hHW, hH, hshort, hpq, hqP, hPB.trans hBC, R, D, A,
    hAW, ?_, n, M, hn, hnB.trans (Real.exp_le_exp.mpr hBC), hM,
    hMB.trans (Real.exp_le_exp.mpr hBC), hproj, ξ, hξ₀, hfirst,
    Λ, hΛ, hchar, hnormal, hfinite, hindex.trans (Real.exp_le_exp.mpr hCC),
    K, hK, hin, hout, hRank.mono _ hCC, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hBC))
      (Nat.cast_nonneg _)).trans hdensity
  · intro h hh
    obtain ⟨ε, γ, v, hε₀, hγ₀, hv₀, hε, hγ, heq, hdep, ⟨y, _, V⟩, hperiod⟩ := hsplit h hh
    have hε' : CoefficientBound (W.family.model.basis.baseChange ℝ)
        (fun _ : Unit => (N : ℝ)) (Real.exp (((B + 2) + 2) ^ 1)) ε.log :=
      CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) hε
        (Real.exp_le_exp.mpr (by simp only [pow_one]; linarith))
    obtain ⟨U, hfreq, hval⟩ := hU (W.family.vertical.mono hpB) ε γ hε' hγ y
    let U' := U.mono hCC
    have heval (i : Fin W.family.outputDim) (x : ZMod N) :
        U'.observable i (QuotientGroup.mk
          (W.family.model.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v))) =
        W.family.model.frozenCyclicOrbitValue (W.family.vertical.observable i) ε (ξ * v) γ y x :=
      hval i _
    have hfun : W.replacedRankResidual h (fun i x => U'.observable i (QuotientGroup.mk
          (W.family.model.filtration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) (ξ * v)))) =
        W.replacedRankResidual h (fun i x => W.family.model.frozenCyclicOrbitValue
          (W.family.vertical.observable i) ε (ξ * v) γ y x) := by
      apply congrArg (W.replacedRankResidual h)
      funext i x
      exact heval i x
    refine ⟨ε, γ, v, hε₀, hγ₀, hv₀, ?_, hγ, heq, hdep, ⟨y, U', hfreq, heval, ?_⟩, hperiod⟩
    · exact CoefficientBound.mono _ _ (fun _ => by exact_mod_cast NeZero.pos N) hε
        (Real.exp_le_exp.mpr hBC)
    · rw [hfun]
      exact ⟨(Classical.choice V).mono hBC⟩

end Erdos3

end

end OAI
