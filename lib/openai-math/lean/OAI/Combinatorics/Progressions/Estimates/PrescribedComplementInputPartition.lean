import OAI.Combinatorics.Progressions.Estimates.PrescribedCoveredInputPartition

namespace OAI


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

def CoveredAnchoredInputPartitionSpec (s a C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
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
      ∀ (Λ : ∀ i, Subgroup (Q i).filtration.Group) (hΛ : ∀ i, Λ i ≤ (Q i).lattice)
        (l : ι → ℕ) (hl : ∀ i, 0 < l i)
        (hlin : ∀ i, scaledIntegerGrid (l i) ⊆ bchSubgroupCoordinates (Q i).basis (Λ i))
        (hlout : ∀ i, bchSubgroupCoordinates (Q i).basis (Λ i) ⊆ denominatorGrid (l i)),
      let Q' := fun i => (Q i).withLattice (Λ i) (l i) (hl i) (hlin i) (hlout i)
      ∀ (E : ∀ j, RationalFilteredNilmanifold (K j) s (e j))
        (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (T : ∀ i, (D i).Niltest (fun _ : Unit => 1)) (c : ι → ℤ)
        (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (T i).ComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i, (Q' i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → (q : ℝ) ≤ Real.exp p →
      0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ n k : ι → ℕ, (∀ i, 0 < n i ∧ 0 < k i) ∧
        ∃ r t : ℕ, 0 < r ∧ 0 < t ∧
          (Fintype.card ((((∀ i, (Fin (n i) × ZMod q) × Fin (k i)) × ZMod q) × Fin r) × Fin t) : ℝ)
            ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : ((((∀ i, (Fin (n i) × ZMod q) × Fin (k i)) × ZMod q) × Fin r) × Fin t) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            (∀ j x, 0 < A j x → (x.val : ZMod q) = j.1.1.2) ∧
            (∀ j x y, 0 < A j x → 0 < A j y →
              dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
            (∀ h : ZMod N, ((cyclicWrapExceptional h ε).card : ℝ) / N ≤ 6 * ε + 3 / N) ∧
            (pi (sumFactors E Q')).GeometryComplexityLE ((2 * p + 2) ^ 2) ∧
            letI : ∀ i, MetricSpace (Q' i).Space := fun i => (Q' i).metricSpace
            letI : ∀ j, MetricSpace (E j).Space := fun j => (E j).metricSpace
            (∀ j x y, 0 < A j x → 0 < A j y → ∀ z,
              dist ((E z).cyclicOrbitPoint (g z) N (fun _ : Unit => x))
                ((E z).cyclicOrbitPoint (g z) N (fun _ : Unit => y)) ≤ ε) ∧
            ∀ χ : ∀ i, (D i).RealGroup → CircleFourier.Circle,
              (∀ i, ∀ z ∈ (D i).filtration.realification.subgroup (s + 1), ∀ x,
                (T i).observable (z • x) = CircleFourier.character (χ i z) * (T i).observable x) →
              ∀ (h : ZMod N) (branch : ι → Fin 2),
                ∃ S : ∀ i, (Q i).Niltest (fun _ : Unit => 1),
                  (∀ i, (S i).normBound = (T i).normBound ^ 2) ∧
                  (∀ i, (S i).ComplexityLE ((p + C) ^ C)) ∧
                  (∀ i (z : Unit → ℤ), (S i).eval z =
                    (T i).eval (z + fun _ => (h.val : ℤ) - ((branch i).val : ℤ) * N) *
                      star ((T i).eval (z + fun _ => c i))) ∧
                  let S' := fun i => (S i).onSublattice (Λ i) (l i) (hl i) (hlin i) (hlout i) (hΛ i)
                  (∀ i, (S' i).ComplexityLE ((p + C) ^ C)) ∧
                  (∀ i z, (S' i).eval z = (S i).eval z) ∧
                  (∀ i j b x y,
                    x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
                    0 < A j x * A b (x + h) → 0 < A j y * A b (y + h) →
                    dist ((Q' i).cyclicOrbitPoint (S' i).orbit N (fun _ : Unit => x))
                      ((Q' i).cyclicOrbitPoint (S' i).orbit N (fun _ : Unit => y)) ≤ ε) ∧
                  let Z := sumFactors E Q'
                  letI : FiniteDimensional ℚ (∀ i, sumLieSpace K
                    (fun j => (D j).filtration.squareLieSubalgebra ⧸
                      (D j).filtration.squareFiltration.layerIdeal (s + 1)) i) :=
                    (productFinBasis Z).finiteDimensional_of_finite
                  letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, sumLieSpace K
                    (fun j => (D j).filtration.squareLieSubalgebra ⧸
                      (D j).filtration.squareFiltration.layerIdeal (s + 1)) i))
                  letI : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, sumLieSpace K
                    (fun j => (D j).filtration.squareLieSubalgebra ⧸
                      (D j).filtration.squareFiltration.layerIdeal (s + 1)) i)) :=
                    IsModuleTopology.isTopologicalAddGroup ℝ _
                  letI : T2Space (ℝ ⊗[ℚ] (∀ i, sumLieSpace K
                    (fun j => (D j).filtration.squareLieSubalgebra ⧸
                      (D j).filtration.squareFiltration.layerIdeal (s + 1)) i)) :=
                    realification_moduleTopology_t2 (productFinBasis Z)
                  letI := (pi Z).metricSpace
                  let G := piRealOrbit (fun i => (Z i).filtration)
                    (sumOrbits E Q' g (fun i => (S' i).orbit))
                  ∀ j b x y,
                    x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
                    0 < A j x * A b (x + h) → 0 < A j y * A b (y + h) →
                    dist ((pi Z).cyclicOrbitPoint G N (fun _ : Unit => x))
                      ((pi Z).cyclicOrbitPoint G N (fun _ : Unit => y)) ≤
                        Real.exp ((2 * p + 4) ^ 4) * ε ∧
                    ∀ (Γ : Subgroup (pi Z).filtration.Group) (mΓ : ℕ) (hmΓ : 0 < mΓ)
                      (hinΓ : scaledIntegerGrid mΓ ⊆ bchSubgroupCoordinates (pi Z).basis Γ)
                      (houtΓ : bchSubgroupCoordinates (pi Z).basis Γ ⊆ denominatorGrid mΓ),
                      (pi Z).lattice ≤ Γ →
                      let W := (pi Z).withLattice Γ mΓ hmΓ hinΓ houtΓ
                      letI := W.metricSpace
                      dist (W.cyclicOrbitPoint G N (fun _ : Unit => x))
                        (W.cyclicOrbitPoint G N (fun _ : Unit => y)) ≤
                          Real.exp ((2 * p + 4) ^ 4) * ε

end Erdos3.RationalFilteredNilmanifold


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem exists_covered_anchored_input_partition (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CoveredAnchoredInputPartitionSpec s a C := by
  obtain ⟨B, _, hsingle⟩ := exists_covered_anchored_square_niltests s a
  obtain ⟨R, _, hcommon⟩ := exists_common_positive_partition_refinement a
  obtain ⟨J, _, hrefine⟩ := exists_fixed_observation_refinement s a
  let X : Polynomial ℕ := Polynomial.X
  let P := 2 * X + (X + Polynomial.C B) ^ B + 2
  let U := P + (P + Polynomial.C R) ^ R
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + (U + Polynomial.C J) ^ J)
  refine ⟨C, hC, ?_⟩
  dsimp only [CoveredAnchoredInputPartitionSpec]
  intro ι κ _ _ _ _ L _ _ d m _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    b v hF M hM hin hout Λ hΛ l hl hlin hlout E g T c q N _ _ p ε
    hp hι hκ hT hV hQ' hb hE hq hε hε1 hεinv
  let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Q' := fun i => (Q i).withLattice (Λ i) (l i) (hl i) (hlin i) (hlout i)
  have hp0 : 0 ≤ p := by linarith
  let r := 2 * p + (p + B) ^ B + 2
  have hB0 : 0 ≤ (p + B) ^ B := by positivity
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp0.trans hpr
  have hBr : (p + B) ^ B ≤ r := by dsimp [r]; linarith
  let u := r + (r + R) ^ R
  have hru : r ≤ u := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hu : 0 ≤ u := hr.trans hru
  have hRu : (r + R) ^ R ≤ u := le_add_of_nonneg_left hr
  have hpu : p ≤ u := hpr.trans hru
  have htotal : u + (u + J) ^ J ≤ (p + C) ^ C := by
    simpa [X, P, U, r, u, Polynomial.eval₂_pow] using hbudget p hp0
  have huC : u ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans htotal
  have hBC : (p + B) ^ B ≤ (p + C) ^ C := hBr.trans (hru.trans huC)
  have hJC : (u + J) ^ J ≤ (p + C) ^ C := (le_add_of_nonneg_left hu).trans htotal
  choose δ _hδ hδε _hδinv n k hn hk hcount A hA hsum _hres _hcircle _hbad hblocks using
    fun i => hsingle (D i) (b i) (v i) (hF i) (M i) (hM i) (hin i) (hout i)
      (Λ i) (hΛ i) (l i) (hl i) (hlin i) (hlout i) (T i) (c i) q N
      hp (hT i) (hV i) (hQ' i) (hb i) hq hε hε1 hεinv
  obtain ⟨r₀, hr₀, hWcount, W, hW, hWsum, hWres, hWcircle, hWbad, _, hWsupport⟩ :=
    hcommon (q := q) A (by omega) hr (hι.trans hpr)
      (fun i => (hcount i).trans (Real.exp_le_exp.mpr hBr))
      (fun i j => (hA i j).mono le_rfl hBr) hsum
      (hq.trans (Real.exp_le_exp.mpr hpr)) hε
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2)
          (by linarith : p + 2 ≤ r + 2) a)))
  obtain ⟨t₀, ht₀, hUcount, U₀, hU, hUsum, hUsupport, hUpairs, hobs⟩ :=
    hrefine E g W (by omega) hu (hκ.trans hpu)
      (fun j => (hE j).mono (E j) hpu) (hWcount.trans (Real.exp_le_exp.mpr hRu))
      (fun j => (hW j).mono le_rfl hRu) hWsum hε
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2)
          (by linarith : p + 2 ≤ u + 2) a)))
  let Z := sumFactors E Q'
  have h2p : 0 ≤ 2 * p := by positivity
  have hp2p : p ≤ 2 * p := by linarith
  have hcardZ : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  have hZ : ∀ i, (Z i).GeometryComplexityLE (2 * p) := by
    intro i
    cases i with
    | inl i => exact (hE i).mono (E i) hp2p
    | inr i => exact (hQ' i).mono (Q' i) hp2p
  refine ⟨n, k, fun i => ⟨hn i, hk i⟩, r₀, t₀, hr₀, ht₀,
    hUcount.trans (Real.exp_le_exp.mpr hJC), U₀, fun j => (hU j).mono le_rfl hJC, hUsum,
    fun j x hx => hWres j.1 x (hUsupport j x hx),
    fun j x y hx hy => hWcircle j.1 x y (hUsupport j x hx) (hUsupport j y hy),
    hWbad, pi_geometry Z h2p hcardZ hZ, ?_⟩
  let : ∀ i, MetricSpace (Q' i).Space := fun i => (Q' i).metricSpace
  let : ∀ j, MetricSpace (E j).Space := fun j => (E j).metricSpace
  refine ⟨hobs, ?_⟩
  intro χ hvert h branch
  choose S hSnorm hScomplexity hSeval hS'complexity hS'eval hScell using
    fun i => hblocks i (χ i) (hvert i) h (branch i)
  let S' := fun i => (S i).onSublattice (Λ i) (l i) (hl i) (hlin i) (hlout i) (hΛ i)
  have hcell i j b x y (hx : x ∉ cyclicWrapExceptional h ε) (hy : y ∉ cyclicWrapExceptional h ε)
      (hUx : 0 < U₀ j x * U₀ b (x + h)) (hUy : 0 < U₀ j y * U₀ b (y + h)) :
      dist ((Q' i).cyclicOrbitPoint (S' i).orbit N (fun _ : Unit => x))
        ((Q' i).cyclicOrbitPoint (S' i).orbit N (fun _ : Unit => y)) ≤ ε :=
    hScell i (j.1.1.1 i) (b.1.1.1 i) x y
      (fun hbad => hx (cyclicWrapExceptional_mono h (hδε i) hbad))
      (fun hbad => hy (cyclicWrapExceptional_mono h (hδε i) hbad))
      (hWsupport h j.1 b.1 x (hUpairs h j b x hUx) i)
      (hWsupport h j.1 b.1 y (hUpairs h j b y hUy) i)
  refine ⟨S, hSnorm, fun i => (hScomplexity i).mono hBC, hSeval,
    fun i => (hS'complexity i).mono hBC, hS'eval, hcell, ?_⟩
  let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
    (D i).filtration.squareFiltration.layerIdeal (s + 1))
  let : FiniteDimensional ℚ (∀ i, KL i) := (productFinBasis Z).finiteDimensional_of_finite
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] (∀ i, KL i)) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] (∀ i, KL i)) := realification_moduleTopology_t2 (productFinBasis Z)
  let := (pi Z).metricSpace
  let : ∀ i, MetricSpace (Z i).Space := fun i => (Z i).metricSpace
  intro j b x y hx hy hUx hUy
  have hpositive j b x (hh : 0 < U₀ j x * U₀ b (x + h)) : 0 < U₀ j x := by
    rcases mul_pos_iff.mp hh with hh | hh
    · exact hh.1
    · linarith [((hU j).unit_interval x).1]
  have hinputs : ∀ i,
      dist ((Z i).cyclicOrbitPoint (sumOrbits E Q' g (fun j => (S' j).orbit) i) N (fun _ : Unit => x))
        ((Z i).cyclicOrbitPoint (sumOrbits E Q' g (fun j => (S' j).orbit) i) N (fun _ : Unit => y)) ≤ ε := by
    intro i
    cases i with
    | inl i => exact hobs j x y (hpositive j b x hUx) (hpositive j b y hUy) i
    | inr i => exact hcell i j b x y hx hy hUx hUy
  have hprod := pi_cyclicOrbitPoint_dist_le_exp Z (sumOrbits E Q' g (fun i => (S' i).orbit)) N
    (fun _ : Unit => x) (fun _ : Unit => y) h2p hcardZ (fun i => (hZ i).1) hε.le hinputs
  refine ⟨hprod, ?_⟩
  intro Γ mΓ hmΓ hinΓ houtΓ hΓ
  exact (largerLattice_cyclicOrbitPoint_dist_le (pi Z) Γ mΓ hmΓ hinΓ houtΓ hΓ
    (piRealOrbit (fun i => (Z i).filtration) (sumOrbits E Q' g (fun i => (S' i).orbit)))
    N (fun _ : Unit => x) (fun _ : Unit => y)).trans hprod

end Erdos3.RationalFilteredNilmanifold


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

def AmbientAnchoredInputPartitionSpec (s a B C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
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
      ∀ E : ∀ j, RationalFilteredNilmanifold (K j) s (e j),
      let Z := sumFactors E Q
      ∀ (Γ : Subgroup (pi Z).filtration.Group) (mΓ : ℕ) (hmΓ : 0 < mΓ)
        (hinΓ : scaledIntegerGrid mΓ ⊆ bchSubgroupCoordinates (pi Z).basis Γ)
        (houtΓ : bchSubgroupCoordinates (pi Z).basis Γ ⊆ denominatorGrid mΓ),
      let W := (pi Z).withLattice Γ mΓ hmΓ hinΓ houtΓ
      let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1))
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := realification_moduleTopology_t2 (pi Z).basis
      letI := W.metricSpace
      ∀ (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (T : ∀ i, (D i).Niltest (fun _ : Unit => 1)) (c : ι → ℤ)
        (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (T i).ComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → (mΓ : ℝ) ≤ Real.exp p → (q : ℝ) ≤ Real.exp p →
      0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ (I : Type) (inst : Fintype I), letI := inst;
        (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (A : I → ZMod N → ℝ) (label : I → ZMod q),
          (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = label j) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
          ∀ χ : ∀ i, (D i).RealGroup → CircleFourier.Circle,
            (∀ i, ∀ z ∈ (D i).filtration.realification.subgroup (s + 1), ∀ x,
              (T i).observable (z • x) = CircleFourier.character (χ i z) * (T i).observable x) →
            ∀ (h : ZMod N) (branch : ι → Fin 2),
              ∃ S : ∀ i, (Q i).Niltest (fun _ : Unit => 1),
                (∀ i, (S i).normBound = (T i).normBound ^ 2) ∧
                (∀ i, (S i).ComplexityLE ((p + C) ^ C)) ∧
                (∀ i (z : Unit → ℤ), (S i).eval z =
                  (T i).eval (z + fun _ => (h.val : ℤ) - ((branch i).val : ℤ) * N) *
                    star ((T i).eval (z + fun _ => c i))) ∧
                let G := piRealOrbit (fun i => (Z i).filtration)
                  (sumOrbits E Q g (fun i => (S i).orbit))
                ∀ j b x y,
                  x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
                  0 < A j x * A b (x + h) → 0 < A j y * A b (y + h) →
                  dist (W.cyclicOrbitPoint G N (fun _ : Unit => x))
                    (W.cyclicOrbitPoint G N (fun _ : Unit => y)) ≤
                      Real.exp ((p + B) ^ B) * ε

end Erdos3.RationalFilteredNilmanifold


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem exists_ambient_anchored_input_partition (s : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ a : ℕ, ∃ C : ℕ, 2 ≤ C ∧ AmbientAnchoredInputPartitionSpec s a B C := by
  obtain ⟨F, _, hcover⟩ := exists_native_factorwise_covers
  let X : Polynomial ℕ := Polynomial.X
  let T₀ := X + (2 * X + Polynomial.C F) ^ F
  obtain ⟨B, hB, hmetricBudget⟩ := exists_natPolynomial_eval_budget (T₀ + (2 * T₀ + 4) ^ 4)
  refine ⟨B, hB, ?_⟩
  intro a
  obtain ⟨J, _, hpartition⟩ := exists_covered_anchored_input_partition s a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T₀ + (T₀ + Polynomial.C J) ^ J)
  refine ⟨C, hC, ?_⟩
  dsimp only [AmbientAnchoredInputPartitionSpec]
  intro ι κ _ _ _ _ L _ _ d m _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    b v hF M hM hin hout E Γ mΓ hmΓ hinΓ houtΓ g T c q N _ _ p ε
    hp hι hκ hT hV hb hE hmΓb hq hε hε1 hεinv
  classical
  let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Z := sumFactors E Q
  let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
    (D i).filtration.squareFiltration.layerIdeal (s + 1))
  let W := (pi Z).withLattice Γ mΓ hmΓ hinΓ houtΓ
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := realification_moduleTopology_t2 (pi Z).basis
  let := W.metricSpace
  have hp0 : 0 ≤ p := by linarith
  have hp2p : p ≤ 2 * p := by linarith
  have hQ (i : ι) : (Q i).GeometryComplexityLE p :=
    (D i).filtration.squareFiltration.topQuotientModel_geometry _ _ _ _ _ _ _ _ hp0 (hV i)
  have hZ (i : κ ⊕ ι) : (Z i).GeometryComplexityLE (2 * p) := by
    cases i with
    | inl i => exact (hE i).mono _ hp2p
    | inr i => exact (hQ i).mono _ hp2p
  have hcard : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  obtain ⟨Δ, l, hl, hlin, hlout, hindex, hgeom, _, hsub⟩ :=
    hcover Z Γ mΓ hmΓ hinΓ (by positivity) hcard hZ
      (hmΓb.trans (Real.exp_le_exp.mpr hp2p))
  let E' := fun i => (E i).withLattice (Δ (.inl i)) (l (.inl i)) (hl (.inl i))
    (hlin (.inl i)) (hlout (.inl i))
  let Q' := fun i => (Q i).withLattice (Δ (.inr i)) (l (.inr i)) (hl (.inr i))
    (hlin (.inr i)) (hlout (.inr i))
  let Z' := sumFactors E' Q'
  have hZ' : Z' = fun i => (Z i).withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i) := by
    funext i
    cases i <;> rfl
  have hsub' : (pi Z').lattice ≤ Γ := by
    rw [hZ']
    exact hsub
  have hbase : (pi Z').basis = W.basis :=
    pi_basis_eq_of_basis_eq Z' Z (by intro i; cases i <;> rfl)
  let t := p + (2 * p + F) ^ F
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp0.trans hpt
  have hFt : (2 * p + F) ^ F ≤ t := le_add_of_nonneg_left hp0
  have hcomplex : (t + J) ^ J ≤ (p + C) ^ C := by
    have hh : t + (t + J) ^ J ≤ (p + C) ^ C := by
      simpa [T₀, X, t, Polynomial.eval₂_pow] using hbudget p hp0
    linarith
  have hmetric : (2 * t + 4) ^ 4 ≤ (p + B) ^ B := by
    have hh : t + (2 * t + 4) ^ 4 ≤ (p + B) ^ B := by
      simpa [T₀, X, t, Polynomial.eval₂_pow] using hmetricBudget p hp0
    linarith
  have hΛ (i : ι) : Δ (.inr i) ≤ (Q i).lattice := (hindex (.inr i)).1
  have hE' (i : κ) : (E' i).GeometryComplexityLE t := (hgeom (.inl i)).mono _ hFt
  have hQ' (i : ι) : (Q' i).GeometryComplexityLE t := (hgeom (.inr i)).mono _ hFt
  obtain ⟨n, k, _, r₀, t₁, _, _, hcount, A, hA, hsum, hres, hcircle, _, _, hfixed, hshifts⟩ :=
    hpartition D b v hF M hM hin hout (fun i => Δ (.inr i)) hΛ
      (fun i => l (.inr i)) (fun i => hl (.inr i))
      (fun i => hlin (.inr i)) (fun i => hlout (.inr i)) E' g T c q N
      (hp.trans hpt) (hι.trans hpt) (hκ.trans hpt) (fun i => (hT i).mono hpt)
      (fun i => (hV i).mono _ hpt) hQ' (fun i j k => (hb i j k).trans hpt)
      hE' (hq.trans (Real.exp_le_exp.mpr hpt)) hε hε1
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  let I := ((((∀ i, (Fin (n i) × ZMod q) × Fin (k i)) × ZMod q) × Fin r₀) × Fin t₁)
  refine ⟨I, inferInstance, hcount.trans (Real.exp_le_exp.mpr hcomplex), A,
    (fun j => j.1.1.2), fun j => (hA j).mono le_rfl hcomplex, hsum, hres, hcircle, ?_⟩
  intro χ hvert h branch
  obtain ⟨S, hSnorm, hScomplex, hSeval, _, _, _, hglobal⟩ := hshifts χ hvert h branch
  refine ⟨S, hSnorm, fun i => (hScomplex i).mono hcomplex, hSeval, ?_⟩
  let S' := fun i => (S i).onSublattice (Δ (.inr i)) (l (.inr i)) (hl (.inr i))
    (hlin (.inr i)) (hlout (.inr i)) (hΛ i)
  let G := piRealOrbit (fun i => (Z i).filtration) (sumOrbits E Q g (fun i => (S i).orbit))
  let G' := piRealOrbit (fun i => (Z' i).filtration) (sumOrbits E' Q' g (fun i => (S' i).orbit))
  let := (pi Z').metricSpace
  have heval (x : Unit → ℤ) :
      (pi Z).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x G =
        (pi Z').filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x G' :=
    piRealOrbit_eval_eq_of_log_eq (fun i => (Z i).filtration) (fun i => (Z' i).filtration)
      (sumOrbits E Q g (fun i => (S i).orbit)) (sumOrbits E' Q' g (fun i => (S' i).orbit))
      (by intro i; cases i <;> rfl) x
  have hpoint (x : ZMod N) : W.cyclicOrbitPoint G N (fun _ : Unit => x) =
      (QuotientGroup.mk ((pi Z').filtration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) G') : W.Space) :=
    congrArg (QuotientGroup.mk : W.RealGroup → W.Space) (heval (fun _ => (x.val : ℤ)))
  intro j b x y hx hy hAx hAy
  have hprod := (hglobal j b x y hx hy hAx hAy).1
  have hproject := (sublatticeProjection_lipschitz W (pi Z') hsub' hbase).dist_le_mul
    ((pi Z').cyclicOrbitPoint G' N (fun _ : Unit => x))
    ((pi Z').cyclicOrbitPoint G' N (fun _ : Unit => y))
  change dist (QuotientGroup.mk ((pi Z').filtration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) G') : W.Space)
    (QuotientGroup.mk ((pi Z').filtration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) G')) ≤
      (1 : ℝ) * dist ((pi Z').cyclicOrbitPoint G' N (fun _ : Unit => x))
        ((pi Z').cyclicOrbitPoint G' N (fun _ : Unit => y)) at hproject
  have hdist := congrArg₂ (dist : W.Space → W.Space → ℝ) (hpoint x) (hpoint y)
  exact ((hdist.le.trans (hproject.trans_eq (one_mul _))).trans hprod).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmetric) hε.le)

end Erdos3.RationalFilteredNilmanifold


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

def PrescribedAmbientInputPartitionSpec (s k₀ a B C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
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
      ∀ E : ∀ j, RationalFilteredNilmanifold (K j) s (e j),
      let Z := sumFactors E Q
      ∀ (Γ : Subgroup (pi Z).filtration.Group) (mΓ : ℕ) (hmΓ : 0 < mΓ)
        (hinΓ : scaledIntegerGrid mΓ ⊆ bchSubgroupCoordinates (pi Z).basis Γ)
        (houtΓ : bchSubgroupCoordinates (pi Z).basis Γ ⊆ denominatorGrid mΓ),
      let W := (pi Z).withLattice Γ mΓ hmΓ hinΓ houtΓ
      let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1))
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := realification_moduleTopology_t2 (pi Z).basis
      letI := W.metricSpace
      ∀ (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (c : ι → ℤ)
        (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → (mΓ : ℝ) ≤ Real.exp p → (q : ℝ) ≤ Real.exp p →
      0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ (I : Type) (inst : Fintype I), letI := inst;
        (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (A : I → ZMod N → ℝ) (label : I → ZMod q),
          (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = label j) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
          ∀ (h : ZMod N) (branch : ι → Fin 2) (η γ : ∀ i, (D i).RealGroup)
            (rSq : ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
            (qSq : ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ i, γ i ∈ (D i).realLattice) →
            (∀ i b, |((D i).basis.baseChange ℝ).repr (η i).coord b| ≤ Real.exp ((p + 2) ^ k₀)) →
            (∀ i (z : Unit → ℤ),
              (D i).filtration.realSquareFstHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (η i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => (h.val : ℤ) - ((branch i).val : ℤ) * N) (g₀ i) * (γ i)⁻¹ ∧
              (D i).filtration.realSquareSndHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => c i) (g₀ i)) →
            (∀ i, qSq i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
              ((D i).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq i)) →
            let G := piRealOrbit (fun i => (Z i).filtration) (sumOrbits E Q g qSq)
            ∀ j b x y,
              x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
              0 < A j x * A b (x + h) → 0 < A j y * A b (y + h) →
              dist (W.cyclicOrbitPoint G N (fun _ : Unit => x))
                (W.cyclicOrbitPoint G N (fun _ : Unit => y)) ≤
                  Real.exp ((p + B) ^ B) * ε

end Erdos3.RationalFilteredNilmanifold


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

theorem exists_prescribed_ambient_input_partition (s : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ k₀ a : ℕ, ∃ C : ℕ, 2 ≤ C ∧ PrescribedAmbientInputPartitionSpec s k₀ a B C := by
  obtain ⟨F, _, hcover⟩ := exists_native_factorwise_covers
  let X : Polynomial ℕ := Polynomial.X
  let T₀ := X + (2 * X + Polynomial.C F) ^ F
  obtain ⟨B, hB, hmetricBudget⟩ := exists_natPolynomial_eval_budget (T₀ + (2 * T₀ + 4) ^ 4)
  refine ⟨B, hB, ?_⟩
  intro k₀ a
  obtain ⟨J, _, hpartition⟩ := exists_prescribed_covered_input_partition s k₀ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (T₀ + (T₀ + Polynomial.C J) ^ J)
  refine ⟨C, hC, ?_⟩
  dsimp only [PrescribedAmbientInputPartitionSpec]
  intro ι κ _ _ _ _ L _ _ d m _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    b v hF M hM hin hout E Γ mΓ hmΓ hinΓ houtΓ g g₀ c q N _ _ p ε
    hp hι hκ hD hV hb hE hmΓb hq hε hε1 hεinv
  classical
  let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Z := sumFactors E Q
  let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
    (D i).filtration.squareFiltration.layerIdeal (s + 1))
  let W := (pi Z).withLattice Γ mΓ hmΓ hinΓ houtΓ
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := realification_moduleTopology_t2 (pi Z).basis
  let := W.metricSpace
  have hp0 : 0 ≤ p := by linarith
  have hp2p : p ≤ 2 * p := by linarith
  have hQ (i : ι) : (Q i).GeometryComplexityLE p :=
    (D i).filtration.squareFiltration.topQuotientModel_geometry _ _ _ _ _ _ _ _ hp0 (hV i)
  have hZ (i : κ ⊕ ι) : (Z i).GeometryComplexityLE (2 * p) := by
    cases i with
    | inl i => exact (hE i).mono _ hp2p
    | inr i => exact (hQ i).mono _ hp2p
  have hcard : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  obtain ⟨Δ, l, hl, hlin, hlout, hindex, hgeom, _, hsub⟩ :=
    hcover Z Γ mΓ hmΓ hinΓ (by positivity) hcard hZ
      (hmΓb.trans (Real.exp_le_exp.mpr hp2p))
  let E' := fun i => (E i).withLattice (Δ (.inl i)) (l (.inl i)) (hl (.inl i))
    (hlin (.inl i)) (hlout (.inl i))
  let Q' := fun i => (Q i).withLattice (Δ (.inr i)) (l (.inr i)) (hl (.inr i))
    (hlin (.inr i)) (hlout (.inr i))
  let Z' := sumFactors E' Q'
  have hZ' : Z' = fun i => (Z i).withLattice (Δ i) (l i) (hl i) (hlin i) (hlout i) := by
    funext i
    cases i <;> rfl
  have hsub' : (pi Z').lattice ≤ Γ := by
    rw [hZ']
    exact hsub
  have hbase : (pi Z').basis = W.basis :=
    pi_basis_eq_of_basis_eq Z' Z (by intro i; cases i <;> rfl)
  let t := p + (2 * p + F) ^ F
  have hpt : p ≤ t := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have ht : 0 ≤ t := hp0.trans hpt
  have hFt : (2 * p + F) ^ F ≤ t := le_add_of_nonneg_left hp0
  have hcomplex : (t + J) ^ J ≤ (p + C) ^ C := by
    have hh : t + (t + J) ^ J ≤ (p + C) ^ C := by
      simpa [T₀, X, t, Polynomial.eval₂_pow] using hbudget p hp0
    linarith
  have hmetric : (2 * t + 4) ^ 4 ≤ (p + B) ^ B := by
    have hh : t + (2 * t + 4) ^ 4 ≤ (p + B) ^ B := by
      simpa [T₀, X, t, Polynomial.eval₂_pow] using hmetricBudget p hp0
    linarith
  have hΛ (i : ι) : Δ (.inr i) ≤ (Q i).lattice := (hindex (.inr i)).1
  have hE' (i : κ) : (E' i).GeometryComplexityLE t := (hgeom (.inl i)).mono _ hFt
  have hQ' (i : ι) : (Q' i).GeometryComplexityLE t := (hgeom (.inr i)).mono _ hFt
  obtain ⟨I, inst, hcount, A, label, hA, hsum, hres, hcircle, hshifts⟩ :=
    hpartition D b v hF M hM hin hout (fun i => Δ (.inr i)) hΛ
      (fun i => l (.inr i)) (fun i => hl (.inr i))
      (fun i => hlin (.inr i)) (fun i => hlout (.inr i)) E' g g₀ c q N
      (hp.trans hpt) (hι.trans hpt) (hκ.trans hpt) (fun i => (hD i).mono _ hpt)
      (fun i => (hV i).mono _ hpt) hQ' (fun i j k => (hb i j k).trans hpt)
      hE' (hq.trans (Real.exp_le_exp.mpr hpt)) hε hε1
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  let := inst
  refine ⟨I, inst, hcount.trans (Real.exp_le_exp.mpr hcomplex), A,
    label, fun j => (hA j).mono le_rfl hcomplex, hsum, hres, hcircle, ?_⟩
  intro h branch η γ rSq qSq hγ hη hnorm hqSq
  have hηt (i : ι) (j) : |((D i).basis.baseChange ℝ).repr (η i).coord j| ≤
      Real.exp ((t + 2) ^ k₀) :=
    (hη i j).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) k₀))
  have hglobal := hshifts h branch η γ rSq qSq hγ hηt hnorm hqSq
  let G := piRealOrbit (fun i => (Z i).filtration) (sumOrbits E Q g qSq)
  let G' := piRealOrbit (fun i => (Z' i).filtration) (sumOrbits E' Q' g qSq)
  let := (pi Z').metricSpace
  have heval (x : Unit → ℤ) :
      (pi Z).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x G =
        (pi Z').filtration.realification.polynomialOrbitEval (fun _ : Unit => 1) x G' :=
    piRealOrbit_eval_eq_of_log_eq (fun i => (Z i).filtration) (fun i => (Z' i).filtration)
      (sumOrbits E Q g qSq) (sumOrbits E' Q' g qSq)
      (by intro i; cases i <;> rfl) x
  have hpoint (x : ZMod N) : W.cyclicOrbitPoint G N (fun _ : Unit => x) =
      (QuotientGroup.mk ((pi Z').filtration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) G') : W.Space) :=
    congrArg (QuotientGroup.mk : W.RealGroup → W.Space) (heval (fun _ => (x.val : ℤ)))
  intro j b x y hx hy hAx hAy
  have hprod := hglobal j b x y hx hy hAx hAy
  have hproject := (sublatticeProjection_lipschitz W (pi Z') hsub' hbase).dist_le_mul
    ((pi Z').cyclicOrbitPoint G' N (fun _ : Unit => x))
    ((pi Z').cyclicOrbitPoint G' N (fun _ : Unit => y))
  change dist (QuotientGroup.mk ((pi Z').filtration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) (fun _ => (x.val : ℤ)) G') : W.Space)
    (QuotientGroup.mk ((pi Z').filtration.realification.polynomialOrbitEval
      (fun _ : Unit => 1) (fun _ => (y.val : ℤ)) G')) ≤
      (1 : ℝ) * dist ((pi Z').cyclicOrbitPoint G' N (fun _ : Unit => x))
        ((pi Z').cyclicOrbitPoint G' N (fun _ : Unit => y)) at hproject
  have hdist := congrArg₂ (dist : W.Space → W.Space → ℝ) (hpoint x) (hpoint y)
  exact ((hdist.le.trans (hproject.trans_eq (one_mul _))).trans hprod).trans
    (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmetric) hε.le)

end Erdos3.RationalFilteredNilmanifold


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

def PrescribedComplementInputPartitionSpec (s k₀ a B C : ℕ) : Prop :=
    ∀ {ι κ : Type} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
      {L : ι → Type} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d m : ι → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
      {K : κ → Type} [∀ j, LieRing (K j)] [∀ j, LieAlgebra ℚ (K j)] {e : κ → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] K j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] K j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] K j)] [∀ j, T2Space (ℝ ⊗[ℚ] K j)]
      (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1) (d i))
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1)))]
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
      ∀ E : ∀ j, RationalFilteredNilmanifold (K j) s (e j),
      let Z := sumFactors E Q
      ∀ {L₀ : Type} [LieRing L₀] [LieAlgebra ℚ L₀] {d₀ : ℕ}
        (D₀ : RationalFilteredNilmanifold L₀ s d₀),
      let Z₀ := pi (optionComplementFactors D₀ Z)
      ∀ (Γ : Subgroup Z₀.filtration.Group) (mΓ : ℕ) (hmΓ : 0 < mΓ)
        (hinΓ : scaledIntegerGrid mΓ ⊆ bchSubgroupCoordinates Z₀.basis Γ)
        (houtΓ : bchSubgroupCoordinates Z₀.basis Γ ⊆ denominatorGrid mΓ),
      let W := Z₀.withLattice Γ mΓ hmΓ hinΓ houtΓ
      let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1))
      let KC := ∀ j : {j : Option (κ ⊕ ι) // j ≠ none}, optionLieSpace L₀ KL j.val
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] KC)
      letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] KC)
      letI := realification_moduleTopology_t2 Z₀.basis
      letI := W.metricSpace
      ∀ (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (c : ι → ℤ)
        (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → W.GeometryComplexityLE p → (q : ℝ) ≤ Real.exp p →
      0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ (I : Type) (inst : Fintype I), letI := inst;
        (Fintype.card I : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
        ∃ (A : I → ZMod N → ℝ) (label : I → ZMod q),
          (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (A j)) ∧
          (∀ x, ∑ j, A j x = 1) ∧
          (∀ j x, 0 < A j x → (x.val : ZMod q) = label j) ∧
          (∀ j x y, 0 < A j x → 0 < A j y →
            dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ ε) ∧
          ∀ (h : ZMod N) (branch : ι → Fin 2) (η γ : ∀ i, (D i).RealGroup)
            (rSq : ∀ i, (D i).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1))
            (qSq : ∀ i, (Q i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ i, γ i ∈ (D i).realLattice) →
            (∀ i b, |((D i).basis.baseChange ℝ).repr (η i).coord b| ≤ Real.exp ((p + 2) ^ k₀)) →
            (∀ i (z : Unit → ℤ),
              (D i).filtration.realSquareFstHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (η i)⁻¹ * (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => (h.val : ℤ) - ((branch i).val : ℤ) * N) (g₀ i) * (γ i)⁻¹ ∧
              (D i).filtration.realSquareSndHom
                ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
                  (fun _ : Unit => 1) z (rSq i)) =
                  (D i).filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
                    (z + fun _ => c i) (g₀ i)) →
            (∀ i, qSq i = (D i).filtration.squareFiltration.realQuotientPolynomialOrbit
              ((D i).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq i)) →
            let G := piRealOrbit (fun i => ((optionComplementFactors D₀ Z) i).filtration)
              (optionComplementOrbits D₀ Z (sumOrbits E Q g qSq))
            ∀ j b x y,
              x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
              0 < A j x * A b (x + h) → 0 < A j y * A b (y + h) →
              dist (W.cyclicOrbitPoint G N (fun _ : Unit => x))
                (W.cyclicOrbitPoint G N (fun _ : Unit => y)) ≤
                  Real.exp ((p + B) ^ B) * ε

end Erdos3.RationalFilteredNilmanifold


namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieBCHGroup NilpotentLieFiltration
open scoped TensorProduct

theorem exists_prescribed_complement_input_partition (s : ℕ) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ k₀ a : ℕ, ∃ C : ℕ, 2 ≤ C ∧
      PrescribedComplementInputPartitionSpec s k₀ a B C := by
  obtain ⟨F, _, hcover⟩ := exists_option_complement_cover
  obtain ⟨B₀, _, hpartition⟩ := exists_prescribed_ambient_input_partition s
  let X : Polynomial ℕ := Polynomial.X
  let T := X + (2 * X + 2) ^ 2
  let U := T + (T + Polynomial.C F) ^ F
  obtain ⟨B, hB, hmetricBudget⟩ :=
    exists_natPolynomial_eval_budget ((T + Polynomial.C F) ^ F + (U + Polynomial.C B₀) ^ B₀)
  refine ⟨B, hB, ?_⟩
  intro k₀ a
  obtain ⟨J, _, hpartition⟩ := hpartition k₀ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + (U + Polynomial.C J) ^ J)
  refine ⟨C, hC, ?_⟩
  dsimp only [PrescribedComplementInputPartitionSpec]
  intro ι κ _ _ _ _ L _ _ d m _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    b v hF M hM hin hout E L₀ _ _ d₀ D₀ Λ n hn hnin hnout g g₀ c q N _ _ p ε
    hp hι hκ hD hV hb hE htarget hq hε hε1 hεinv
  classical
  let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Z := sumFactors E Q
  let Z₀ := pi (optionComplementFactors D₀ Z)
  let W := Z₀.withLattice Λ n hn hnin hnout
  let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
    (D i).filtration.squareFiltration.layerIdeal (s + 1))
  let KC := ∀ j : {j : Option (κ ⊕ ι) // j ≠ none}, optionLieSpace L₀ KL j.val
  let := moduleTopology ℝ (ℝ ⊗[ℚ] KC)
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] KC)
  let := realification_moduleTopology_t2 Z₀.basis
  let := W.metricSpace
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := realification_moduleTopology_t2 (pi Z).basis
  have hp0 : 0 ≤ p := by linarith
  have hp2p : p ≤ 2 * p := by linarith
  have hQ (i : ι) : (Q i).GeometryComplexityLE p :=
    (D i).filtration.squareFiltration.topQuotientModel_geometry _ _ _ _ _ _ _ _ hp0 (hV i)
  have hZ (i : κ ⊕ ι) : (Z i).GeometryComplexityLE (2 * p) := by
    cases i with
    | inl i => exact (hE i).mono _ hp2p
    | inr i => exact (hQ i).mono _ hp2p
  have hcard : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  have hprod := pi_geometry Z (p := 2 * p) (by positivity) hcard hZ
  let t := p + (2 * p + 2) ^ 2
  have hpt : p ≤ t := le_add_of_nonneg_right (sq_nonneg _)
  have ht : 0 ≤ t := hp0.trans hpt
  have hprodT : (2 * p + 2) ^ 2 ≤ t := le_add_of_nonneg_left hp0
  obtain ⟨Γ, _, _, _, _, _, l, hl, hlin, hlout, hsource, _, htransfer⟩ :=
    hcover D₀ Z Λ n hn hnin hnout ht (hprod.mono _ hprodT) (htarget.mono W hpt)
  let V := (pi Z).withLattice Γ l hl hlin hlout
  let u := t + (t + F) ^ F
  have htu : t ≤ u := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hpu : p ≤ u := hpt.trans htu
  have hu : 0 ≤ u := hp0.trans hpu
  have hFu : (t + F) ^ F ≤ u := le_add_of_nonneg_left ht
  have hlbound : (l : ℝ) ≤ Real.exp u := hsource.2.1.trans (Real.exp_le_exp.mpr hFu)
  have hcomplex : (u + J) ^ J ≤ (p + C) ^ C := by
    have hh : u + (u + J) ^ J ≤ (p + C) ^ C := by
      simpa [T, U, X, t, u, Polynomial.eval₂_pow] using hbudget p hp0
    linarith
  have hmetric : (t + F) ^ F + (u + B₀) ^ B₀ ≤ (p + B) ^ B := by
    simpa [T, U, X, t, u, Polynomial.eval₂_pow] using hmetricBudget p hp0
  obtain ⟨I, inst, hcount, A, label, hA, hsum, hres, hcircle, hshifts⟩ :=
    hpartition D b v hF M hM hin hout E Γ l hl hlin hlout g g₀ c q N
      (hp.trans hpu) (hι.trans hpu) (hκ.trans hpu) (fun i => (hD i).mono _ hpu)
      (fun i => (hV i).mono _ hpu) (fun i j k => (hb i j k).trans hpu)
      (fun j => (hE j).mono _ hpu) hlbound (hq.trans (Real.exp_le_exp.mpr hpu))
      hε hε1 (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  let := inst
  refine ⟨I, inst, hcount.trans (Real.exp_le_exp.mpr hcomplex), A, label,
    fun j => (hA j).mono le_rfl hcomplex, hsum, hres, hcircle, ?_⟩
  intro h branch η γ rSq qSq hγ hη hnorm hqSq
  have hηu (i : ι) (j) : |((D i).basis.baseChange ℝ).repr (η i).coord j| ≤
      Real.exp ((u + 2) ^ k₀) :=
    (hη i j).trans (Real.exp_le_exp.mpr
      (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) k₀))
  have hglobal := hshifts h branch η γ rSq qSq hγ hηu hnorm hqSq
  let := V.metricSpace
  intro j k x y hx hy hAx hAy
  have hsmall := hglobal j k x y hx hy hAx hAy
  have hmap := htransfer (sumOrbits E Q g qSq)
    (fun _ : Unit => (x.val : ℤ)) (fun _ : Unit => (y.val : ℤ))
  calc
    _ ≤ Real.exp ((t + F) ^ F) *
        dist (V.cyclicOrbitPoint (piRealOrbit (fun i => (Z i).filtration)
          (sumOrbits E Q g qSq)) N (fun _ : Unit => x))
          (V.cyclicOrbitPoint (piRealOrbit (fun i => (Z i).filtration)
            (sumOrbits E Q g qSq)) N (fun _ : Unit => y)) := hmap
    _ ≤ Real.exp ((t + F) ^ F) * (Real.exp ((u + B₀) ^ B₀) * ε) :=
      mul_le_mul_of_nonneg_left hsmall (Real.exp_pos _).le
    _ = Real.exp ((t + F) ^ F + (u + B₀) ^ B₀) * ε := by rw [Real.exp_add, mul_assoc]
    _ ≤ Real.exp ((p + B) ^ B) * ε :=
      mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hmetric) hε.le

end Erdos3.RationalFilteredNilmanifold

end OAI
