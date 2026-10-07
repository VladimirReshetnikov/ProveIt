/- Modified for ProveIt: Use IsModuleTopology.topologicalAddGroup on Lean 4.32; statements unchanged. -/
import OAI.Combinatorics.Progressions.Dynamics.RefilteredExpansionErrorBudget
import OAI.Combinatorics.Progressions.Estimates.ControlledRefilteredRecoveredExpansion
import OAI.Combinatorics.Progressions.Estimates.PrescribedComplementInputPartition
import OAI.Combinatorics.Progressions.Polynomial.TrivialPolynomialData

namespace OAI

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup
open scoped TensorProduct BigOperators NNReal

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

noncomputable def SelectedRefilteredProductExpansionSpec (p : ℝ) (q r : ℕ) (cost : ℝ) : Prop :=
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  letI := realification_moduleTopology_t2 Q.basis
  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  letI := realification_moduleTopology_t2 Z₀.basis
  ∃ P : ℕ, 0 < P ∧ (P : ℝ) ≤ Real.exp cost ∧
    ∃ Q' : RationalFilteredNilmanifold (H ⧸ E.filtration.layerIdeal (s + 1)) s n,
      Q'.filtration = Q.filtration ∧ Q'.basis = Q.basis ∧ Q'.lattice ≤ Q.lattice ∧
      Q'.GeometryComplexityLE cost ∧
        ∃ Λ : Subgroup Z₀.filtration.Group, Λ ≤ Z₀.lattice ∧
          (Λ.subgroupOf Z₀.lattice).Characteristic ∧ (Λ.subgroupOf Z₀.lattice).Normal ∧
          (Λ.subgroupOf Z₀.lattice).FiniteIndex ∧ (Λ.relIndex Z₀.lattice : ℝ) ≤ Real.exp cost ∧
          ∃ (l : ℕ) (hl : 0 < l)
            (hin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates Z₀.basis Λ)
            (hout : bchSubgroupCoordinates Z₀.basis Λ ⊆ denominatorGrid l),
            let V := Z₀.withLattice Λ l hl hin hout
            V.GeometryComplexityLE cost ∧
            letI := V.metricSpace
            let w := fun _ : Unit => 1
            ∀ {J₀ : Type u} (freq : J₀ → ∀ i, L i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi D).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (N : ℕ) [NeZero N] {I J : Type u} [Fintype I] [Fintype J]
                (A : I → ZMod N → ℝ) (B : J → ZMod N → ℝ) (label : I → ZMod P) {ρ K : ℝ},
                0 < ρ → 0 ≤ K →
                (∀ i x, 0 ≤ A i x) → (∀ j x, 0 ≤ B j x) →
                (∀ x, ∑ i, A i x = 1) → (∀ x, ∑ j, B j x = 1) →
                (∀ i x, 0 < A i x → (x.val : ZMod P) = label i) →
                (∀ i x y, 0 < A i x → 0 < A i y →
                  dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ρ) →
                ∀ (S : ZMod N → (D a).Niltest w),
                  (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                  (∀ h z, z ∈ (D a).filtration.realification.subgroup (s + 1) →
                    (∀ j, realifyFunctional (freq j a) z.coord = 0) →
                    ∀ x, (S h).observable (z • x) = (S h).observable x) →
                  ∀ (Hsh : Set (ZMod N)) (g : ZMod N → ∀ i, (D i).filtration.realification.PolynomialOrbit w),
                    (∀ h ∈ Hsh, g h a = (S h).orbit) →
                    ∀ (slow middle rat : ZMod N → ((pi D).filtration.realification.adaptedPolynomialFiltration w).Group)
                      (κ : ZMod N → (pi D).RealGroup),
                      (∀ h ∈ Hsh, κ h ∈ (pi D).realLattice) →
                      (∀ h ∈ Hsh, slow h * middle h * rat h * (pi D).filtration.realification.adaptedConstantGroupHom w (κ h) =
                        ⟨⟨(NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (g h)).log,
                          (NilpotentLieFiltration.piRealOrbit (fun i => (D i).filtration) (g h)).property⟩⟩) →
                      (∀ h ∈ Hsh, (pi D).filtration.PolynomialSlowBound (pi D).basis w
                        (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                      (∀ h ∈ Hsh, (pi D).filtration.PolynomialRationalGrid (pi D).basis w q (rat h)) →
                      (∀ h ∈ Hsh, ∀ α, VectorPolynomial.coefficients
                        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
                          (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight w α)) →
                      (∀ h ∈ Hsh, VectorPolynomial.coefficients
                        ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0) →
                      (∀ i j h, h ∈ Hsh → ∀ x y, x ∉ cyclicWrapExceptional h ρ → y ∉ cyclicWrapExceptional h ρ →
                        0 < A i x * B j (x + h) → 0 < A i y * B j (y + h) →
                        dist (V.cyclicOrbitPoint
                          (NilpotentLieFiltration.piRealOrbit (fun i : I₀ => (D i.val).filtration)
                            (fun i : I₀ => g h i.val)) N (fun _ : Unit => x))
                          (V.cyclicOrbitPoint
                            (NilpotentLieFiltration.piRealOrbit (fun i : I₀ => (D i.val).filtration)
                              (fun i : I₀ => g h i.val)) N (fun _ : Unit => y)) ≤ K * ρ) →
                      ∃ U : I → J → ZMod N → Q'.Niltest w,
                        (∀ i j h, (U i j h).UnitIntervalValued) ∧
                        (∀ i j h, (U i j h).ComplexityLE (cost + 2)) ∧
                        (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ρ ∧ 0 < A i x * B j (x + h)) →
                          ∀ x, (U i j h).eval x = 0) ∧
                        ∃ err : ZMod N → ZMod N → ℝ,
                          (∀ h ∈ Hsh, ∀ x, ((S h).evalCyclic N (fun _ => x)).re =
                            (∑ i, ∑ j, A i x * B j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                          ∀ h, (𝔼 x, |err h x|) ≤ Real.exp cost * (K + 2) * ρ + 6 * ρ + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

section

universe u

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct BigOperators

variable {ι : Type u} [Fintype ι] [DecidableEq ι] {L : ι → Type u}
  [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {s : ℕ} {d : ι → ℕ}
  (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i)) (a : ι)
  (W : LieSubalgebra ℚ (pi D).filtration.AssociatedGraded) {e n : ℕ}
  (E : RationalFilteredNilmanifold ((pi D).filtration.gradedRefiltrationSubalgebra W) (s + 1) e)
  (Q : RationalFilteredNilmanifold
    (((pi D).filtration.gradedRefiltrationSubalgebra W) ⧸ E.filtration.layerIdeal (s + 1)) s n)
  [TopologicalSpace (ℝ ⊗[ℚ] L a)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L a)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L a)] [T2Space (ℝ ⊗[ℚ] L a)]

theorem selected_refiltered_product_expansion
    {p cost : ℝ} {q r : ℕ} (hbase : RefilteredProductExpansionSpec D a W E Q p q r cost) :
    SelectedRefilteredProductExpansionSpec D a W E Q p q r cost := by
  classical
  let H := (pi D).filtration.gradedRefiltrationSubalgebra W
  let I₀ := {i : ι // i ≠ a}
  let Z₀ := pi (fun i : I₀ => D i.val)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ E.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, L i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  obtain ⟨P, hP, hPb, Q', hQF, hQb, hQle, hQ, Λ, hΛ, hchar, hnormal,
    hfinite, hindex, l, hl, hin, hout, hV, hbase⟩ := hbase
  refine ⟨P, hP, hPb, Q', hQF, hQb, hQle, hQ, Λ, hΛ, hchar, hnormal,
    hfinite, hindex, l, hl, hin, hout, hV, ?_⟩
  let V := Z₀.withLattice Λ l hl hin hout
  let := V.metricSpace
  dsimp only
  intro J₀ freq hfreq N _ I J _ _ A B label ρ K hρ hK hA hB hAsum hBsum hres hcircle
    S hS hpositive hinvariant Hsh g horbit slow middle rat κ hκ hfactor hslow hrat hcoeff hzero hinput
  let w := fun _ : Unit => 1
  let S' := fun h => if h ∈ Hsh then S h else Niltest.const (D a) w 0
  let g' := fun h i => if h ∈ Hsh then g h i else (1 : (D i).filtration.realification.PolynomialOrbit w)
  let slow' := fun h => if h ∈ Hsh then slow h else 1
  let middle' := fun h => if h ∈ Hsh then middle h else 1
  let rat' := fun h => if h ∈ Hsh then rat h else 1
  let κ' := fun h => if h ∈ Hsh then κ h else 1
  have hS' (h) : (S' h).ComplexityLE p := by
    by_cases hh : h ∈ Hsh
    · simpa only [S', hh, ite_true] using hS h
    · simpa only [S', hh, ite_false] using Niltest.const_zero_complexity_of (hS h)
  have hpositive' (h) : (S' h).UnitIntervalValued := by
    by_cases hh : h ∈ Hsh
    · simpa only [S', hh, ite_true] using hpositive h
    · simpa only [S', hh, ite_false] using Niltest.const_zero_unit_interval (D a) w
  have hinvariant' (h : ZMod N) (z : (D a).RealGroup)
      (hz : z ∈ (D a).filtration.realification.subgroup (s + 1))
      (hfreqz : ∀ j, realifyFunctional (freq j a) z.coord = 0) (x : (D a).Space) :
      (S' h).observable (z • x) = (S' h).observable x := by
    by_cases hh : h ∈ Hsh
    · simpa only [S', hh, ite_true] using hinvariant h z hz hfreqz x
    · simp only [S', hh, ite_false, Niltest.const]
  have horbit' (h) : g' h a = (S' h).orbit := by
    by_cases hh : h ∈ Hsh
    · simpa only [g', S', hh, ite_true] using horbit h hh
    · simp only [g', S', hh, ite_false, Niltest.const]
  have hκ' (h) : κ' h ∈ (pi D).realLattice := by
    by_cases hh : h ∈ Hsh
    · simpa only [κ', hh, ite_true] using hκ h hh
    · simp only [κ', hh, ite_false, Subgroup.one_mem]
  have hfactor' (h) : slow' h * middle' h * rat' h *
      (pi D).filtration.realification.adaptedConstantGroupHom w (κ' h) =
        ⟨⟨(piRealOrbit (fun i => (D i).filtration) (g' h)).log,
          (piRealOrbit (fun i => (D i).filtration) (g' h)).property⟩⟩ := by
    by_cases hh : h ∈ Hsh
    · simpa only [slow', middle', rat', κ', g', hh, ite_true] using hfactor h hh
    · simp only [slow', middle', rat', κ', g', hh, ite_false, map_one, one_mul, piRealOrbit_one]
      rfl
  have hslow' (h) : (pi D).filtration.PolynomialSlowBound (pi D).basis w
      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow' h) := by
    by_cases hh : h ∈ Hsh
    · simpa only [slow', hh, ite_true] using hslow h hh
    · simpa only [slow', hh, ite_false] using
        (pi D).filtration.polynomialSlowBound_one (pi D).basis w (fun _ => (N : ℝ))
          (fun _ => Nat.cast_pos.mpr (NeZero.pos N)) (Real.exp_pos _).le
  have hrat' (h) : (pi D).filtration.PolynomialRationalGrid (pi D).basis w q (rat' h) := by
    by_cases hh : h ∈ Hsh
    · simpa only [rat', hh, ite_true] using hrat h hh
    · simpa only [rat', hh, ite_false] using
        (pi D).filtration.polynomialRationalGrid_one (pi D).basis w q
  have hcoeff' (h α) : coefficients
      ((middle' h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈
        (pi D).filtration.realGradedRefiltrationLayer W (Finsupp.weight w α) := by
    by_cases hh : h ∈ Hsh
    · simpa only [middle', hh, ite_true] using hcoeff h hh α
    · simp only [middle', hh, ite_false]
      change coefficients (0 : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) α ∈ _
      simp only [map_zero, Finsupp.zero_apply, Submodule.zero_mem]
  have hzero' (h) : coefficients
      ((middle' h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0 := by
    by_cases hh : h ∈ Hsh
    · simpa only [middle', hh, ite_true] using hzero h hh
    · simp only [middle', hh, ite_false]
      change coefficients (0 : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i, L i))) 0 = 0
      simp only [map_zero, Finsupp.zero_apply]
  have hinput' (i : I) (j : J) (h x y : ZMod N)
      (hx : x ∉ cyclicWrapExceptional h ρ) (hy : y ∉ cyclicWrapExceptional h ρ)
      (hAx : 0 < A i x * B j (x + h)) (hAy : 0 < A i y * B j (y + h)) :
      dist (V.cyclicOrbitPoint (piRealOrbit (fun i : I₀ => (D i.val).filtration)
        (fun i : I₀ => g' h i.val)) N (fun _ : Unit => x))
        (V.cyclicOrbitPoint (piRealOrbit (fun i : I₀ => (D i.val).filtration)
          (fun i : I₀ => g' h i.val)) N (fun _ : Unit => y)) ≤ K * ρ := by
    by_cases hh : h ∈ Hsh
    · simpa only [g', hh, ite_true] using hinput i j h hh x y hx hy hAx hAy
    · simp only [g', hh, ite_false, piRealOrbit_one]
      change dist (QuotientGroup.mk (V.filtration.realification.polynomialOrbitEval w
        (fun _ : Unit => (x.val : ℤ)) 1) : V.Space)
        (QuotientGroup.mk (V.filtration.realification.polynomialOrbitEval w
          (fun _ : Unit => (y.val : ℤ)) 1)) ≤ K * ρ
      rw [map_one, map_one, dist_self]
      exact mul_nonneg hK hρ.le
  obtain ⟨U, hU, hUc, hUempty, err, heval, hmean⟩ :=
    hbase freq hfreq N A B label hρ hK hA hB hAsum hBsum hres hcircle S' hS' hpositive'
      hinvariant' g' horbit' slow' middle' rat' κ' hκ' hfactor' hslow' hrat' hcoeff' hzero' hinput'
  refine ⟨U, hU, hUc, hUempty, err, ?_, hmean⟩
  intro h hh x
  simpa only [S', hh, ite_true] using heval h x

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

def PrescribedPartitionExpansionSpec (s r b₀ k₀ a B C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) ((s + 1) + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      (b : ∀ i, Basis (Fin (m i)) ℚ (L i)) (v : ∀ i, Fin (m i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ (b i '' {k | j ≤ v i k}))
      (M : ι → ℕ) (hM : ∀ i, 0 < M i)
      (hin : ∀ i, scaledIntegerGrid (M i) ⊆ bchSubgroupCoordinates
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) ((D i).filtration.squareLattice (D i).lattice))
      (hout : ∀ i, bchSubgroupCoordinates ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareLattice (D i).lattice) ⊆ denominatorGrid (M i)),
      let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      ∀ E : ∀ j, RationalFilteredNilmanifold (K j) (s + 1) (e j),
      let Z := sumFactors E Q
      ∀ {L₀ : Type} [LieRing L₀] [LieAlgebra ℚ L₀] {d₀ : ℕ}
        (D₀ : RationalFilteredNilmanifold L₀ (s + 1) d₀),
      let T := optionFactors D₀ Z
      ∀ (W : LieSubalgebra ℚ (pi T).filtration.AssociatedGraded) {dR dQ : ℕ}
        (R : RationalFilteredNilmanifold ((pi T).filtration.gradedRefiltrationSubalgebra W) (s + 1) dR)
        (Q₀ : RationalFilteredNilmanifold
          (((pi T).filtration.gradedRefiltrationSubalgebra W) ⧸ R.filtration.layerIdeal (s + 1)) s dQ)
        [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)] {p cost : ℝ} (q : ℕ),
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → 0 ≤ cost → cost ≤ (p + b₀) ^ b₀ →
      RefilteredProductExpansionSpec T none W R Q₀ p q r cost →
      let H := (pi T).filtration.gradedRefiltrationSubalgebra W
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
      letI := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
      letI := realification_moduleTopology_t2 Q₀.basis
      ∃ Q' : RationalFilteredNilmanifold (H ⧸ R.filtration.layerIdeal (s + 1)) s dQ,
        Q'.filtration = Q₀.filtration ∧ Q'.basis = Q₀.basis ∧ Q'.lattice ≤ Q₀.lattice ∧
        Q'.GeometryComplexityLE cost ∧
        ∀ (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (c : ι → ℤ) (N : ℕ) [NeZero N] {ε : ℝ},
        0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
        ∃ (I : Type) (inst : Fintype I), letI := inst;
          (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : I → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} (s + 1 + 1) N ((p + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            (∀ j x y, 0 < A j x → 0 < A j y →
              dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
            ∀ {J₀ : Type} (freq : J₀ → ∀ i, optionLieSpace L₀
              (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi T).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (S : ZMod N → (T none).Niltest (fun _ : Unit => 1)),
                (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                (∀ h z, z ∈ (T none).filtration.realification.subgroup (s + 1) →
                  (∀ j, realifyFunctional (freq j none) z.coord = 0) →
                  ∀ x, (S h).observable (z • x) = (S h).observable x) →
                ∀ (Hsh : Set (ZMod N))
                  (gT : ZMod N → ∀ i, (T i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
                  (branch : ZMod N → ι → Fin 2) (η γ : ZMod N → ∀ i, (D i).RealGroup)
                  (rSq : ZMod N → ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
                  (qSq : ZMod N → ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
                  (∀ h ∈ Hsh, gT h none = (S h).orbit) →
                  (∀ h ∈ Hsh, ∀ i, gT h (some i) = sumOrbits E Q g (qSq h) i) →
                  (∀ h ∈ Hsh, ∀ i, γ h i ∈ (D i).realLattice) →
                  (∀ h ∈ Hsh, ∀ i j, |((D i).basis.baseChange ℝ).repr (η h i).coord j| ≤
                    Real.exp ((p + 2) ^ k₀)) →
                  (∀ h ∈ Hsh, ∀ i (z : Unit → ℤ),
                    (D i).filtration.realSquareFstHom
                      ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) z (rSq h i)) =
                        (η h i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                          (z + fun _ => (h.val : ℤ) - ((branch h i).val : ℤ) * N) (g₀ i) * (γ h i)⁻¹ ∧
                    (D i).filtration.realSquareSndHom
                      ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) z (rSq h i)) =
                        (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                          (z + fun _ => c i) (g₀ i)) →
                  (∀ h ∈ Hsh, ∀ i, qSq h i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
                    ((D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)) (t := s + 1) le_rfl (rSq h i)) →
                  ∀ (slow middle rat : ZMod N →
                      ((pi T).filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group)
                    (δ : ZMod N → (pi T).RealGroup),
                    (∀ h ∈ Hsh, δ h ∈ (pi T).realLattice) →
                    (∀ h ∈ Hsh, slow h * middle h * rat h *
                      (pi T).filtration.realification.adaptedConstantGroupHom (fun _ : Unit => 1) (δ h) =
                        ⟨⟨(piRealOrbit (fun i => (T i).filtration) (gT h)).log,
                          (piRealOrbit (fun i => (T i).filtration) (gT h)).property⟩⟩) →
                    (∀ h ∈ Hsh, (pi T).filtration.PolynomialSlowBound (pi T).basis (fun _ : Unit => 1)
                      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                    (∀ h ∈ Hsh, (pi T).filtration.PolynomialRationalGrid (pi T).basis (fun _ : Unit => 1) q (rat h)) →
                    (∀ h ∈ Hsh, ∀ α, VectorPolynomial.coefficients
                      ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i,
                        optionLieSpace L₀ (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i))) α ∈
                        (pi T).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ : Unit => 1) α)) →
                    (∀ h ∈ Hsh, VectorPolynomial.coefficients
                      ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i,
                        optionLieSpace L₀ (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i))) 0 = 0) →
                    ∃ U : I → I → ZMod N → Q'.Niltest (fun _ : Unit => 1),
                      (∀ i j h, (U i j h).UnitIntervalValued) ∧
                      (∀ i j h, (U i j h).ComplexityLE ((p + C) ^ C)) ∧
                      (∀ i j h, (¬∃ x, x ∉ cyclicWrapExceptional h ε ∧ 0 < A i x * A j (x + h)) →
                        ∀ x, (U i j h).eval x = 0) ∧
                      ∃ err : ZMod N → ZMod N → ℝ,
                        (∀ h ∈ Hsh, ∀ x, ((S h).evalCyclic N (fun _ => x)).re =
                          (∑ i, ∑ j, A i x * A j (x + h) * ((U i j h).evalCyclic N (fun _ => x)).re) + err h x) ∧
                        ∀ h, (𝔼 x, |err h x|) ≤ Real.exp ((p + B) ^ B) * ε + 3 / N

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

def PreparedHigherShiftContradictionSpec (s r b₀ k₀ k Dexp : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) ((s + 1) + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal ((s + 1) + 1)))]
      (b : ∀ i, Basis (Fin (m i)) ℚ (L i)) (v : ∀ i, Fin (m i) → ℕ)
      (hF : ∀ i j, (D i).filtration.layer j = Submodule.span ℚ (b i '' {k | j ≤ v i k}))
      (M : ι → ℕ) (hM : ∀ i, 0 < M i)
      (hin : ∀ i, scaledIntegerGrid (M i) ⊆ bchSubgroupCoordinates
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) ((D i).filtration.squareLattice (D i).lattice))
      (hout : ∀ i, bchSubgroupCoordinates ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareLattice (D i).lattice) ⊆ denominatorGrid (M i)),
      let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
        ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
        ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
      ∀ E : ∀ j, RationalFilteredNilmanifold (K j) (s + 1) (e j),
      let Z := sumFactors E Q
      ∀ {L₀ : Type} [LieRing L₀] [LieAlgebra ℚ L₀] {d₀ : ℕ}
        (D₀ : RationalFilteredNilmanifold L₀ (s + 1) d₀),
      let T := optionFactors D₀ Z
      ∀ (W : LieSubalgebra ℚ (pi T).filtration.AssociatedGraded) {dR dQ : ℕ}
        (R : RationalFilteredNilmanifold ((pi T).filtration.gradedRefiltrationSubalgebra W) (s + 1) dR)
        (Q₀ : RationalFilteredNilmanifold
          (((pi T).filtration.gradedRefiltrationSubalgebra W) ⧸ R.filtration.layerIdeal (s + 1)) s dQ)
        [TopologicalSpace (ℝ ⊗[ℚ] L₀)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L₀)]
        [ContinuousSMul ℝ (ℝ ⊗[ℚ] L₀)] [T2Space (ℝ ⊗[ℚ] L₀)] {p cost : ℝ} (q : ℕ),
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → 0 ≤ cost → cost ≤ (p + b₀) ^ b₀ →
      RefilteredProductExpansionSpec T none W R Q₀ p q r cost →
        ∀ (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
          (c : ι → ℤ) (N : ℕ) [NeZero N],
        Odd N → Real.exp ((p + 2) ^ Dexp) ≤ N →
        ∀ (f₁ f₂ weight : ZMod N → ℝ) (sigma delta : ℝ),
          Real.exp (-((p + 2) ^ k)) ≤ sigma → Real.exp (-((p + 2) ^ k)) ≤ delta →
          (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
          (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
          (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
            ∀ {J₀ : Type} (freq : J₀ → ∀ i, optionLieSpace L₀
              (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i →ₗ[ℚ] ℚ),
              (∀ j x, x ∈ (pi T).filtration.realGradedRefiltrationLayer W (s + 1) →
                realifyFunctional (piFrequency (freq j)) x = 0) →
              ∀ (S : ZMod N → (T none).Niltest (fun _ : Unit => 1)),
                (∀ h, (S h).ComplexityLE p) → (∀ h, (S h).UnitIntervalValued) →
                (∀ h z, z ∈ (T none).filtration.realification.subgroup (s + 1) →
                  (∀ j, realifyFunctional (freq j none) z.coord = 0) →
                  ∀ x, (S h).observable (z • x) = (S h).observable x) →
                ∀ (Hsh : Finset (ZMod N))
                  (gT : ZMod N → ∀ i, (T i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
                  (branch : ZMod N → ι → Fin 2) (η γ : ZMod N → ∀ i, (D i).RealGroup)
                  (rSq : ZMod N → ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
                  (qSq : ZMod N → ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
                  (∀ h ∈ Hsh, gT h none = (S h).orbit) →
                  (∀ h ∈ Hsh, ∀ i, gT h (some i) = sumOrbits E Q g (qSq h) i) →
                  (∀ h ∈ Hsh, ∀ i, γ h i ∈ (D i).realLattice) →
                  (∀ h ∈ Hsh, ∀ i j, |((D i).basis.baseChange ℝ).repr (η h i).coord j| ≤
                    Real.exp ((p + 2) ^ k₀)) →
                  (∀ h ∈ Hsh, ∀ i (z : Unit → ℤ),
                    (D i).filtration.realSquareFstHom
                      ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) z (rSq h i)) =
                        (η h i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                          (z + fun _ => (h.val : ℤ) - ((branch h i).val : ℤ) * N) (g₀ i) * (γ h i)⁻¹ ∧
                    (D i).filtration.realSquareSndHom
                      ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                        (fun _ : Unit => 1) z (rSq h i)) =
                        (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                          (z + fun _ => c i) (g₀ i)) →
                  (∀ h ∈ Hsh, ∀ i, qSq h i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
                    ((D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)) (t := s + 1) le_rfl (rSq h i)) →
                  ∀ (slow middle rat : ZMod N →
                      ((pi T).filtration.realification.adaptedPolynomialFiltration (fun _ : Unit => 1)).Group)
                    (δ : ZMod N → (pi T).RealGroup),
                    (∀ h ∈ Hsh, δ h ∈ (pi T).realLattice) →
                    (∀ h ∈ Hsh, slow h * middle h * rat h *
                      (pi T).filtration.realification.adaptedConstantGroupHom (fun _ : Unit => 1) (δ h) =
                        ⟨⟨(piRealOrbit (fun i => (T i).filtration) (gT h)).log,
                          (piRealOrbit (fun i => (T i).filtration) (gT h)).property⟩⟩) →
                    (∀ h ∈ Hsh, (pi T).filtration.PolynomialSlowBound (pi T).basis (fun _ : Unit => 1)
                      (fun _ => (N : ℝ)) (Real.exp ((p + 2) ^ r)) (slow h)) →
                    (∀ h ∈ Hsh, (pi T).filtration.PolynomialRationalGrid (pi T).basis (fun _ : Unit => 1) q (rat h)) →
                    (∀ h ∈ Hsh, ∀ α, VectorPolynomial.coefficients
                      ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i,
                        optionLieSpace L₀ (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i))) α ∈
                        (pi T).filtration.realGradedRefiltrationLayer W (Finsupp.weight (fun _ : Unit => 1) α)) →
                    (∀ h ∈ Hsh, VectorPolynomial.coefficients
                      ((middle h).coord : VectorPolynomial Unit ℚ (ℝ ⊗[ℚ] (∀ i,
                        optionLieSpace L₀ (sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
                          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))) i))) 0 = 0) →
                    sigma * N ≤ (Hsh.card : ℝ) →
                    CyclicNiltestUpperComparison.{0} (s + 2) N ((p + 2) ^ Dexp)
                      (Real.exp (-((p + 2) ^ Dexp))) f₁ f₂ →
                    (∀ h ∈ Hsh, delta < 𝔼 n,
                      (f₁ n - (1 + epsilon) * f₂ n) * weight (n + h) *
                        ((S h).evalCyclic N (fun _ => n)).re) → False

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance_reducible] optionLieSpace

theorem prescribed_partition_expansion_from_partition (s r b₀ k₀ a B C B₀ J : ℕ)
    (hpartition : PrescribedComplementInputPartitionSpec (s + 1) k₀ a B₀ J)
    (hbudget : ∀ p : ℝ, 0 ≤ p →
      (p + (p + b₀) ^ b₀ + 2) + (p + (p + b₀) ^ b₀ + 2 + J) ^ J ≤ (p + C) ^ C)
    (hmetricBudget : ∀ p : ℝ, 0 ≤ p →
      (p + b₀) ^ b₀ + (p + (p + b₀) ^ b₀ + 2 + B₀) ^ B₀ + 10 ≤ (p + B) ^ B) :
    PrescribedPartitionExpansionSpec s r b₀ k₀ a B C := by
  dsimp only [PrescribedPartitionExpansionSpec]
  intro ι κ _ _ _ _ L _ _ d m _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    b v hF M hM hin hout E L₀ _ _ d₀ D₀ W dR dQ R Q₀ _ _ _ _ p cost q
    hp hι hκ hD hV hb hE hcost hcostb hbase
  classical
  let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Z := sumFactors E Q
  let T := optionFactors D₀ Z
  let H := (pi T).filtration.gradedRefiltrationSubalgebra W
  let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
    (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1))
  let I₀ := {i : Option (κ ⊕ ι) // i ≠ none}
  let Z₀ := pi (optionComplementFactors D₀ Z)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (H ⧸ R.filtration.layerIdeal (s + 1)))
  let := realification_moduleTopology_t2 Q₀.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i : I₀, optionLieSpace L₀ KL i.val))
  let := IsModuleTopology.topologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i : I₀, optionLieSpace L₀ KL i.val))
  let := realification_moduleTopology_t2 Z₀.basis
  have hselected : SelectedRefilteredProductExpansionSpec T none W R Q₀ p q r cost :=
    selected_refiltered_product_expansion T none W R Q₀ hbase
  obtain ⟨P, hP, hPb, Q', hQF, hQb, hQle, hQ, Λ, hΛ, hchar, hnormal,
      hfinite, hindex, l, hl, hlin, hlout, hV₀, hbase⟩ :=
    hselected
  refine ⟨Q', hQF, hQb, hQle, hQ, ?_⟩
  intro g g₀ c N _ ε hε hε1 hεinv
  let V₀ := Z₀.withLattice Λ l hl hlin hlout
  let := V₀.metricSpace
  let : NeZero P := ⟨Nat.ne_of_gt hP⟩
  let t := p + (p + b₀) ^ b₀ + 2
  have hp0 : 0 ≤ p := by linarith
  have hpt : p ≤ t := by
    dsimp [t]
    have hh : 0 ≤ (p + b₀) ^ b₀ := by positivity
    linarith
  have ht : 0 ≤ t := hp0.trans hpt
  have hcostt : cost + 2 ≤ t := by dsimp [t]; linarith
  have hcostt' : cost ≤ t := by linarith
  have htotal : t + (t + J) ^ J ≤ (p + C) ^ C := by
    exact hbudget p hp0
  have hcomplex : (t + J) ^ J ≤ (p + C) ^ C := by linarith
  have htC : t ≤ (p + C) ^ C := by
    have hh : 0 ≤ (t + J) ^ J := by positivity
    linarith
  have hmetric : cost + (t + B₀) ^ B₀ + 10 ≤ (p + B) ^ B := by
    have hh : (p + b₀) ^ b₀ + (t + B₀) ^ B₀ + 10 ≤ (p + B) ^ B := by
      exact hmetricBudget p hp0
    linarith
  have hpart := hpartition D b v hF M hM hin hout E D₀ Λ l hl hlin hlout g g₀ c P N
      (hp.trans hpt) (hι.trans hpt) (hκ.trans hpt) (fun i => (hD i).mono _ hpt)
      (fun i => (hV i).mono _ hpt) (fun i j k => (hb i j k).trans hpt)
      (fun j => (hE j).mono _ hpt) (hV₀.mono V₀ hcostt')
      (hPb.trans (Real.exp_le_exp.mpr hcostt')) hε hε1
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  let I : Type := Classical.choose hpart
  have hpartI := Classical.choose_spec hpart
  let inst : Fintype I := Classical.choose hpartI
  have hpartInst := Classical.choose_spec hpartI
  obtain ⟨hcount, A, label, hA, hsum, hres, hcircle, hshifts⟩ := hpartInst
  let := inst
  refine ⟨I, inst, hcount.trans (Real.exp_le_exp.mpr hcomplex), A,
    fun i => (hA i).mono le_rfl hcomplex, hsum, hcircle, ?_⟩
  intro J₀ freq hfreq S hS hpositive hinvariant Hsh gT branch η γ rSq qSq
    horbit hother hγ hη hnorm hqSq slow middle rat δ hδ hfactor hslow hrat hcoeff hzero
  have hinput (i j : I) (h : ZMod N) (hh : h ∈ Hsh) (x y : ZMod N)
      (hx : x ∉ cyclicWrapExceptional h ε) (hy : y ∉ cyclicWrapExceptional h ε)
      (hAx : 0 < A i x * A j (x + h)) (hAy : 0 < A i y * A j (y + h)) :
      dist (V₀.cyclicOrbitPoint (piRealOrbit (fun i : I₀ => (T i.val).filtration)
        (fun i : I₀ => gT h i.val)) N (fun _ : Unit => x))
        (V₀.cyclicOrbitPoint (piRealOrbit (fun i : I₀ => (T i.val).filtration)
          (fun i : I₀ => gT h i.val)) N (fun _ : Unit => y)) ≤ Real.exp ((t + B₀) ^ B₀) * ε := by
    have hgo : (fun i : I₀ => gT h i.val) = optionComplementOrbits D₀ Z (sumOrbits E Q g (qSq h)) := by
      funext i
      rcases i with ⟨i, hi⟩
      cases i with
      | none => exact False.elim (hi rfl)
      | some i => exact hother h hh i
    rw [hgo]
    apply hshifts h (branch h) (η h) (γ h) (rSq h) (qSq h) (hγ h hh) _
      (hnorm h hh) (hqSq h hh) i j x y hx hy hAx hAy
    intro i k
    exact (hη h hh i k).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) k₀))
  have hAnonneg (i x) : 0 ≤ A i x := ((hA i).unit_interval x).1
  have hexp := hbase (J₀ := J₀) freq hfreq N (I := I) (J := I) A A label
    (ρ := ε) (K := Real.exp ((t + B₀) ^ B₀)) hε (Real.exp_pos _).le hAnonneg hAnonneg hsum hsum hres hcircle
      S hS hpositive hinvariant Hsh gT horbit slow middle rat δ hδ hfactor hslow hrat hcoeff hzero hinput
  let U := Classical.choose hexp
  have hUdata := Classical.choose_spec hexp
  obtain ⟨hU, hUc, hUempty, err, heval, hmean⟩ := hUdata
  refine ⟨U, hU, fun i j h => (hUc i j h).mono (hcostt.trans htC), hUempty, err, heval, ?_⟩
  intro h
  have herr := refiltered_expansion_error_budget hcost
    (by positivity : 0 ≤ (t + B₀) ^ B₀) hε.le hmetric
  linarith [hmean h]

end Erdos3.RationalFilteredNilmanifold

end

end OAI
