import OAI.Combinatorics.Progressions.Estimates.CanonicalEmptyLayerGeometry

namespace OAI

section

namespace Erdos3

theorem collision_error_of_exp_size_with_cap {F P C q ρ δ N : ℝ}
    (hC0 : 0 ≤ C) (hq0 : 0 ≤ q) (hρ : 0 < ρ) (hδ : 0 < δ)
    (hC : C ≤ Real.exp (P*(P+5))) (hq : q ≤ Real.exp P)
    (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P)) (hδP : δ⁻¹ ≤ Real.exp P)
    (hN : Real.exp (F + 2*P*(P+5) + spatialSamplingBudget P + 2*P + 4) ≤ N) :
    2*Real.exp F*(C^2*(2*q/(ρ*N))) ≤ δ := by
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have h4 : (4 : ℝ) ≤ Real.exp 4 := by linarith [Real.add_one_le_exp (4 : ℝ)]
  have hmain : (4*Real.exp F*C^2*q*(1/ρ))/δ ≤ N := by
    calc
      _ = 4*Real.exp F*C^2*q*(1/ρ)*δ⁻¹ := div_eq_mul_inv _ _
      _ ≤ Real.exp 4*Real.exp F*(Real.exp (P*(P+5)))^2*Real.exp P*
          Real.exp (spatialSamplingBudget P)*Real.exp P := by gcongr
      _ = Real.exp (F + 2*P*(P+5) + spatialSamplingBudget P + 2*P + 4) := by
        rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_add, ← Real.exp_add,
          ← Real.exp_add, ← Real.exp_add]
        congr 1
        norm_num
        ring
      _ ≤ N := hN
  have hnum := (div_le_iff₀ hδ).mp hmain
  calc
    _ = (4*Real.exp F*C^2*q*(1/ρ))/N := by ring
    _ ≤ δ := (div_le_iff₀ hN0).mpr (by simpa only [mul_comm N δ] using hnum)

noncomputable def allocatedFixedScaleCollisionLog (m : ℕ) (P : ℝ) : ℝ :=
  VectorPolynomial.allocatedFourierLogBudget m P + 2*P*(P+5) +
    spatialSamplingBudget P + 2*P + 4

theorem exists_allocatedFixedScaleCollisionLog_bound (m : ℕ) :
    ∃ A : ℕ, 2 ≤ A ∧ ∀ P : ℝ, 0 ≤ P → allocatedFixedScaleCollisionLog m P ≤ (P+A)^A := by
  obtain ⟨b, _, hb⟩ := VectorPolynomial.exists_allocatedFourierLogBudget_bound m
  let q : Polynomial ℕ := (Polynomial.X + Polynomial.C b)^b +
    2*Polynomial.X*(Polynomial.X+5) + (4*Polynomial.X+128) + 2*Polynomial.X + 4
  obtain ⟨A, hA, hbound⟩ := exists_natPolynomial_eval_budget q
  refine ⟨A, hA, ?_⟩
  intro P hP
  have hpoly : (P+b)^b + 2*P*(P+5) + spatialSamplingBudget P + 2*P + 4 ≤ (P+A)^A := by
    simpa [q, spatialSamplingBudget, Polynomial.eval₂_pow] using hbound P hP
  apply le_trans _ hpoly
  unfold allocatedFixedScaleCollisionLog
  gcongr
  exact hb P hP

namespace BooleanCubeKernel

open scoped BigOperators Classical

theorem selectedJointFiniteLaw_collision_small_with_cap {K X S : Type*}
    [Fintype K] [Fintype X] [DecidableEq X] [Fintype S] [DecidableEq S]
    (A : Finset (X → ℤ)) (hA : A.Nonempty)
    (site : S → K → ℤ) (hsite : Function.Injective site) (i : X)
    {F P δ : ℝ} (hP : 0 ≤ P) (hδ : 0 < δ) (hδP : δ⁻¹ ≤ Real.exp P)
    (hK : (Fintype.card K : ℝ) ≤ P) (hbound : ∀ s k, |(site s k : ℝ)| ≤ Real.exp P)
    (modulus : X → ℕ) (hmodulus : ∀ i, 0 < modulus i) (hmodP : (modulus i : ℝ) ≤ Real.exp P)
    (T : Finset (ColumnResiduePattern (Option K) X modulus)) (hT : T.Nonempty)
    (W : Option K × X → ℝ) (hW : ∀ z, 0 < W z)
    (hZ : 0 < ∑' z, selectedResidueSmoothWeight modulus T W z)
    (hscale : ∀ z, 8*(probabilityProfileLipschitz : ℝ) ≤ residueProfileWidth modulus W z)
    {ρ N : ℝ} (hρ : 0 < ρ) (hρP : 1/ρ ≤ Real.exp (spatialSamplingBudget P))
    (hN : Real.exp (F + 2*P*(P+5) + spatialSamplingBudget P + 2*P + 4) ≤ N)
    (hwidth : ∀ k, ρ*N ≤ W (some k,i))
    (D : (X → ℤ) → (Option K × X → ℤ) → ℝ) (hD0 : ∀ a z, 0 ≤ D a z)
    (hD : 0 < selectedJointDensityMass A modulus T W D)
    (hlower : 1/2 ≤ selectedJointDensityMass A modulus T W D)
    (hcap : ∀ a z, D a z ≤ Real.exp F) :
    (selectedJointFiniteLaw A hA modulus T W hW hZ D hD0 hD).mean
      (fun z => noninjectivityIndicator (fun s => jointIntegerPhysicalSite (site s) (z.1.val,z.2.val))) ≤ δ := by
  have hN0 : 0 < N := (Real.exp_pos _).trans_le hN
  have hcollision := selectedJointFiniteLaw_noninjectivity_le A hA site hsite i
    modulus hmodulus T hT W hW hZ hscale (mul_pos hρ hN0) hwidth D hD0 hD hlower
    (Real.exp_pos _).le hcap
  exact hcollision.trans (collision_error_of_exp_size_with_cap (Nat.cast_nonneg _)
    (Nat.cast_nonneg _) hρ hδ (integerSites_card_le_exp site hsite hP hK hbound)
    hmodP hρP hδP hN)

end BooleanCubeKernel

end Erdos3

end

end OAI
