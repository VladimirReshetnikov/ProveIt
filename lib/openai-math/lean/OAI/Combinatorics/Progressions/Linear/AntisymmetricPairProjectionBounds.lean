import OAI.Combinatorics.Progressions.Estimates.AntisymmetricPairVerticalModel

namespace OAI

section

namespace Erdos3

open RationalFilteredNilmanifold
open scoped BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

theorem exists_antisymmetric_pair_projection_control :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p q r : ℝ}
      {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p}
      {N : ℕ} [NeZero N] {i j : Fin W.outputDim}
      {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
        Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
        (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
      (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
        V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
        (fun _ : Fin 2 => (N : ℝ)) r), 0 ≤ r →
      ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + q + r + C) ^ C) ∧
        ∀ k : Fin 2,
          W.model.filtration.PolynomialRationalGrid W.model.basis (fun _ : Fin 2 => 1) m
            (V.antisymmetricPairPolynomialMap k R.rational) ∧
          W.model.filtration.PolynomialSlowBound W.model.basis (fun _ : Fin 2 => 1)
            (fun _ => (N : ℝ)) (Real.exp ((p + q + r + C) ^ C))
              (V.antisymmetricPairPolynomialMap k R.slow) := by
  obtain ⟨a, _, hcontrol⟩ := exists_native_orbit_coefficient_control
  let X : Polynomial ℕ := Polynomial.X
  let B := X + (X + (X + 2) ^ 2 + 3) + 4
  let T := (B + 2) ^ 2 + B + (B + (B ^ 2 + B + 3) ^ 2) + B ^ 2 + 4 + X + 2
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((T + Polynomial.C a) ^ a)
  refine ⟨C, hC, ?_⟩
  intro p q r W N _ i j V R hr
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hq : 0 ≤ q := (Nat.cast_nonneg V.dim).trans V.complexity.1.1
  let u := p + q + r
  let b := u + raisedNiltestBudget u + 4
  let t := productNiltestBudget b + u + 2
  have hu : 0 ≤ u := by dsimp [u]; positivity
  have hpqu : p + q ≤ u := le_add_of_nonneg_right hr
  have hb : 0 ≤ b := by dsimp [b, raisedNiltestBudget]; positivity
  have hprod : 0 ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    positivity
  have ht : 0 ≤ t := by dsimp [t]; positivity
  have hrt : r ≤ t := by dsimp [t, u]; linarith
  have hBt : antisymmetricPairBudget p q ≤ b := by
    dsimp [antisymmetricPairBudget, b, raisedNiltestBudget]
    gcongr
  have hB0 : 0 ≤ antisymmetricPairBudget p q :=
    (by norm_num : (0 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le
  have hprodmono : productNiltestBudget (antisymmetricPairBudget p q) ≤ productNiltestBudget b := by
    unfold productNiltestBudget productObservableLipBudget
    gcongr
  have htest : productNiltestBudget (antisymmetricPairBudget p q) ≤ t :=
    hprodmono.trans (by dsimp [t]; linarith)
  let D := pi V.antisymmetricPairModels
  have hD : D.GeometryComplexityLE t := by
    apply (pi_geometry V.antisymmetricPairModels hB0
      (by simpa using (show (3 : ℝ) ≤ antisymmetricPairBudget p q from
        (by norm_num : (3 : ℝ) ≤ 4).trans V.antisymmetricPairBudget_four_le))
      (fun k => (V.antisymmetricPairTests_complexity k).1)).mono D
    exact (productNiltestBudget_geometry hB0).trans htest
  have hcost : (t + a) ^ a ≤ (p + q + r + C) ^ C := by
    simpa [X, B, T, t, b, u, raisedNiltestBudget, productNiltestBudget,
      productObservableLipBudget, Polynomial.eval₂_pow] using hbudget u hu
  have hN : ∀ _k : Fin 2, (0 : ℝ) < N := fun _ => Nat.cast_pos.mpr (NeZero.pos N)
  obtain ⟨m, hm, hmb, hrat, hslow⟩ := hcontrol (R.mono hrt hN) ht hD hN
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hcost), ?_⟩
  intro k
  have hs := NilpotentLieFiltration.realPolynomialGroupMap_slow D.basis W.model.basis
    (V.antisymmetricPairProjection k) (V.antisymmetricPairCoordinateIndex k)
    (V.antisymmetricPairProjection_repr k) D.filtration W.model.filtration
    (V.antisymmetricPairProjection_layers k) (fun _ : Fin 2 => 1)
    (fun _ => (N : ℝ)) (Real.exp ((t + a) ^ a)) R.slow hslow
  exact ⟨NilpotentLieFiltration.realPolynomialGroupMap_rational D.basis W.model.basis
      (V.antisymmetricPairProjection k) (V.antisymmetricPairCoordinateIndex k)
      (V.antisymmetricPairProjection_repr k) D.filtration W.model.filtration
      (V.antisymmetricPairProjection_layers k) (fun _ : Fin 2 => 1) m R.rational hrat,
    W.model.filtration.polynomialSlowBound_mono W.model.basis (fun _ : Fin 2 => 1)
      (fun _ => (N : ℝ)) hN (Real.exp_le_exp.mpr hcost) _ hs⟩

namespace NativePolynomialOrbitFactors

variable {p q r : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (mixedCorrelationDegree 1) p} {i j : Fin W.outputDim}
  {V : NativeSampleCorrelation (fun _ : Fin 2 => 1) 1 q
    Finset.univ (fun z : Fin 2 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => W.antisymmetricKernel i j ((z 0).val : ℤ) ((z 1).val : ℤ))}
  (R : NativePolynomialOrbitFactors (pi V.antisymmetricPairModels)
    V.antisymmetricPairPolynomial (piFrequency V.antisymmetricPairFrequencies)
    (fun _ : Fin 2 => (N : ℝ)) r)

def HasPairProjectionControl (b : ℝ) : Prop :=
  ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp b ∧ ∀ k : Fin 2,
    W.model.filtration.PolynomialRationalGrid W.model.basis (fun _ : Fin 2 => 1) m
      (V.antisymmetricPairPolynomialMap k R.rational) ∧
    W.model.filtration.PolynomialSlowBound W.model.basis (fun _ : Fin 2 => 1)
      (fun _ => (N : ℝ)) (Real.exp b) (V.antisymmetricPairPolynomialMap k R.slow)

theorem hasPairProjectionControl_mono {a b : ℝ} (h : R.HasPairProjectionControl a) (hab : a ≤ b) :
    R.HasPairProjectionControl b := by
  obtain ⟨m, hm, hmb, hproj⟩ := h
  refine ⟨m, hm, hmb.trans (Real.exp_le_exp.mpr hab), ?_⟩
  intro k
  exact ⟨(hproj k).1, W.model.filtration.polynomialSlowBound_mono W.model.basis
    (fun _ : Fin 2 => 1) (fun _ => (N : ℝ)) (fun _ => by exact_mod_cast NeZero.pos N)
    (Real.exp_le_exp.mpr hab) _ (hproj k).2⟩

end NativePolynomialOrbitFactors

end Erdos3

end

end OAI
