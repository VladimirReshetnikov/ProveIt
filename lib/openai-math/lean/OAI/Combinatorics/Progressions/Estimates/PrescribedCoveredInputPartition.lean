import OAI.Combinatorics.Progressions.Geometry.SublatticeOrbitMetric
import OAI.Combinatorics.Progressions.Nilpotent.CoveredAnchoredSquareNiltests

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

def PrescribedCoveredInputPartitionSpec (s k₀ a C : ℕ) : Prop :=
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
      ∀ (Λ : ∀ i, Subgroup (Q i).filtration.Group) (_hΛ : ∀ i, Λ i ≤ (Q i).lattice)
        (l : ι → ℕ) (hl : ∀ i, 0 < l i)
        (hlin : ∀ i, scaledIntegerGrid (l i) ⊆ bchSubgroupCoordinates (Q i).basis (Λ i))
        (hlout : ∀ i, bchSubgroupCoordinates (Q i).basis (Λ i) ⊆ denominatorGrid (l i)),
      let Q' := fun i => (Q i).withLattice (Λ i) (l i) (hl i) (hlin i) (hlout i)
      ∀ (E : ∀ j, RationalFilteredNilmanifold (K j) s (e j))
        (g : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (g₀ : ∀ i, (D i).filtration.realification.PolynomialOrbit (fun _ : Unit => 1)) (c : ι → ℤ)
        (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → (Fintype.card ι : ℝ) ≤ p → (Fintype.card κ : ℝ) ≤ p →
      (∀ i, (D i).GeometryComplexityLE p) → (∀ i, (V i).GeometryComplexityLE p) →
      (∀ i, (Q' i).GeometryComplexityLE p) →
      (∀ i j k, rationalLogHeight ((D i).basis.repr (b i j) k) ≤ p) →
      (∀ j, (E j).GeometryComplexityLE p) → (q : ℝ) ≤ Real.exp p →
      0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      let Z := sumFactors E Q'
      let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
        (D i).filtration.squareFiltration.layerIdeal (s + 1))
      letI := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
      letI := realification_moduleTopology_t2 (pi Z).basis
      letI := (pi Z).metricSpace
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
            let G := piRealOrbit (fun i => (Z i).filtration) (sumOrbits E Q' g qSq)
            ∀ j b x y,
              x ∉ cyclicWrapExceptional h ε → y ∉ cyclicWrapExceptional h ε →
              0 < A j x * A b (x + h) → 0 < A j y * A b (y + h) →
              dist ((pi Z).cyclicOrbitPoint G N (fun _ : Unit => x))
                ((pi Z).cyclicOrbitPoint G N (fun _ : Unit => y)) ≤
                  Real.exp ((2 * p + 4) ^ 4) * ε

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_prescribed_covered_input_partition (s k₀ a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ PrescribedCoveredInputPartitionSpec s k₀ a C := by
  obtain ⟨J, _, hsingle⟩ := exists_prescribed_square_image_partition (s + 1) s k₀ a
  obtain ⟨R, _, hcommon⟩ := exists_common_positive_partition_refinement a
  obtain ⟨H, _, hrefine⟩ := exists_fixed_observation_refinement s a
  let X : Polynomial ℕ := Polynomial.X
  let R₀ := X + 2
  let U₀ := R₀ + (R₀ + Polynomial.C J) ^ J + 2
  let V₀ := U₀ + (U₀ + Polynomial.C R) ^ R
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (V₀ + (V₀ + Polynomial.C H) ^ H)
  refine ⟨C, hC, ?_⟩
  dsimp only [PrescribedCoveredInputPartitionSpec]
  intro ι κ _ _ _ _ L _ _ d m _ _ _ _ K _ _ e _ _ _ _ D _ _ _ _ _ _ _ _
    b v hF M hM hin hout Λ hΛ l hl hlin hlout E g g₀ c q N _ _ p ε
    hp hι hκ hD hV hQ' hb hE hq hε hε1 hεinv
  classical
  let V := fun i => (D i).filtration.squareFiltration.ofAdaptedBasis
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Q := fun i => (D i).filtration.squareFiltration.topQuotientModel
    ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2)) (squareFinWeight (v i))
    ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i))
    ((D i).filtration.squareLattice (D i).lattice) (M i) (hM i) (hin i) (hout i)
  let Q' := fun i => (Q i).withLattice (Λ i) (l i) (hl i) (hlin i) (hlout i)
  let Z := sumFactors E Q'
  let KL := sumLieSpace K (fun i => (D i).filtration.squareLieSubalgebra ⧸
    (D i).filtration.squareFiltration.layerIdeal (s + 1))
  let := moduleTopology ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := IsModuleTopology.isTopologicalAddGroup ℝ (ℝ ⊗[ℚ] (∀ i, KL i))
  let := realification_moduleTopology_t2 (pi Z).basis
  let := (pi Z).metricSpace
  have hp0 : 0 ≤ p := by linarith
  let r := p + 2
  let u := r + (r + J) ^ J + 2
  let w := u + (u + R) ^ R
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp0.trans hpr
  have hru : r ≤ u := by
    have hn : 0 ≤ (r + J) ^ J := by positivity
    dsimp [u]
    linarith
  have hJu : (r + J) ^ J ≤ u := by dsimp [u]; linarith
  have hu : 0 ≤ u := hr.trans hru
  have huw : u ≤ w := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hRw : (u + R) ^ R ≤ w := le_add_of_nonneg_left hu
  have hw : 0 ≤ w := hu.trans huw
  have hpu : p ≤ u := hpr.trans hru
  have hpw : p ≤ w := hpu.trans huw
  have hcomplex : (w + H) ^ H ≤ (p + C) ^ C := by
    have hh : w + (w + H) ^ H ≤ (p + C) ^ C := by
      simpa [V₀, U₀, R₀, X, r, u, w, Polynomial.eval₂_pow] using hbudget p hp0
    linarith
  let φ := fun i => lieQuotientMap ((D i).filtration.squareFiltration.layerIdeal (s + 1))
  have hpair (i : ι) : ∀ j k, rationalLogHeight ((pi (fun _ : Bool => D i)).basis.repr
      ((D i).filtration.squarePairMap ((V i).basis k)) j) ≤ r := by
    intro j k
    exact ((D i).squarePairMap_matrix_logHeight (b i) (v i) (hF i 2) hp0
      (fun j k => hb i k j) j k).trans (by dsimp [r]; linarith)
  have hφ (i : ι) : ∀ j k, rationalLogHeight ((Q' i).basis.repr (φ i ((V i).basis k)) j) ≤ r := by
    intro j k
    apply rationalLogHeight_le_of_height
      (quotientFinBasis_projection_height ((D i).filtration.squareFinBasis (b i) (v i) (hF i 2))
        ((D i).filtration.squareFiltration.layerIdeal (s + 1))
        {j | s + 1 ≤ squareFinWeight (v i) j}
        ((D i).filtration.squareFinBasis_layers (b i) (v i) (hF i) (s + 1)) k j)
    simpa only [Nat.cast_one] using Real.one_le_exp hr
  choose δ _ hδε _ n k _ _ hcount A₀ hA₀ hsum₀ _ _ _ hblocks using fun i =>
    hsingle (D i) (V i) (Q' i) (φ i) (g₀ i) (c i) q N (by omega) (hp.trans hpr)
      ((hD i).mono _ hpr) ((hV i).mono _ hpr) ((hQ' i).mono _ hpr) (hpair i) (hφ i)
      (hq.trans (Real.exp_le_exp.mpr hpr)) hε hε1
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  obtain ⟨r₀, _, hWcount, A₁, hA₁, hA₁sum, hA₁res, hA₁circle, _, _, hA₁support⟩ :=
    hcommon (q := q) A₀ (by omega) hu (hι.trans hpu)
      (fun i => (hcount i).trans (Real.exp_le_exp.mpr hJu))
      (fun i j => (hA₀ i j).mono le_rfl hJu) hsum₀
      (hq.trans (Real.exp_le_exp.mpr hpu)) hε
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  obtain ⟨t₁, _, hUcount, A, hA, hAsum, hAsupport, hApairs, hobs⟩ :=
    hrefine E g A₁ (by omega) hw (hκ.trans hpw)
      (fun i => (hE i).mono _ hpw) (hWcount.trans (Real.exp_le_exp.mpr hRw))
      (fun j => (hA₁ j).mono le_rfl hRw) hA₁sum hε
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) a)))
  let I := ((((∀ i, (Fin (n i) × ZMod q) × Fin (k i)) × ZMod q) × Fin r₀) × Fin t₁)
  refine ⟨I, inferInstance, hUcount.trans (Real.exp_le_exp.mpr hcomplex), A,
    (fun j => j.1.1.2), fun j => (hA j).mono le_rfl hcomplex, hAsum,
    fun j x hx => hA₁res j.1 x (hAsupport j x hx),
    fun j x y hx hy => hA₁circle j.1 x y (hAsupport j x hx) (hAsupport j y hy), ?_⟩
  let : ∀ i, MetricSpace (Q' i).Space := fun i => (Q' i).metricSpace
  let : ∀ i, MetricSpace (E i).Space := fun i => (E i).metricSpace
  intro h branch η γ rSq qSq hγ hη hnorm hqSq
  have hcell (i : ι) (j b : I) (x y : ZMod N)
      (hx : x ∉ cyclicWrapExceptional h ε) (hy : y ∉ cyclicWrapExceptional h ε)
      (hAx : 0 < A j x * A b (x + h)) (hAy : 0 < A j y * A b (y + h)) :
      dist ((Q' i).cyclicOrbitPoint (qSq i) N (fun _ : Unit => x))
        ((Q' i).cyclicOrbitPoint (qSq i) N (fun _ : Unit => y)) ≤ ε := by
    have hηr (b) : |((D i).basis.baseChange ℝ).repr (η i).coord b| ≤ Real.exp ((r + 2) ^ k₀) :=
      (hη i b).trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2) (by linarith) k₀))
    have hbound := hblocks i h (branch i) (η i) (γ i) (rSq i) (hγ i) hηr (hnorm i)
      (j.1.1.1 i) (b.1.1.1 i) x y
      (fun hbad => hx (cyclicWrapExceptional_mono h (hδε i) hbad))
      (fun hbad => hy (cyclicWrapExceptional_mono h (hδε i) hbad))
      (hA₁support h j.1 b.1 x (hApairs h j b x hAx) i)
      (hA₁support h j.1 b.1 y (hApairs h j b y hAy) i)
    have hpoint (z : ZMod N) : (Q' i).cyclicOrbitPoint (qSq i) N (fun _ : Unit => z) =
        QuotientGroup.mk (realificationMap
          (hnil := (D i).filtration.squareFiltration.lowerCentralSeries_eq_bot)
          (hM := (Q' i).filtration.lowerCentralSeries_eq_bot) (φ i)
          ((D i).filtration.squareFiltration.realification.polynomialOrbitEval
            (fun _ : Unit => 1) (fun _ => (z.val : ℤ)) (rSq i))) := by
      apply (congrArg (fun g => (Q' i).cyclicOrbitPoint g N (fun _ : Unit => z)) (hqSq i)).trans
      exact congrArg (QuotientGroup.mk : (Q' i).RealGroup → (Q' i).Space)
        ((D i).filtration.squareFiltration.realQuotientPolynomialOrbit_eval
          ((D i).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq i)
          (fun _ => (z.val : ℤ)))
    exact (congrArg₂ (fun x y : (Q' i).Space => dist x y) (hpoint x) (hpoint y)).trans_le hbound
  intro j b x y hx hy hAx hAy
  have hpositive (z : ZMod N) (hz : 0 < A j z * A b (z + h)) : 0 < A j z := by
    rcases mul_pos_iff.mp hz with hz | hz
    · exact hz.1
    · linarith [((hA j).unit_interval z).1]
  let : ∀ i, MetricSpace (Z i).Space := fun i => (Z i).metricSpace
  have hinputs : ∀ i, dist ((Z i).cyclicOrbitPoint (sumOrbits E Q' g qSq i) N (fun _ : Unit => x))
      ((Z i).cyclicOrbitPoint (sumOrbits E Q' g qSq i) N (fun _ : Unit => y)) ≤ ε := by
    intro i
    cases i with
    | inl i => exact hobs j x y (hpositive x hAx) (hpositive y hAy) i
    | inr i => exact hcell i j b x y hx hy hAx hAy
  have hcountZ : (Fintype.card (κ ⊕ ι) : ℝ) ≤ 2 * p := by
    simp only [Fintype.card_sum, Nat.cast_add]
    linarith
  have hZgeom (i : κ ⊕ ι) : (Z i).GeometryComplexityLE (2 * p) := by
    cases i with
    | inl i => exact (hE i).mono _ (by linarith)
    | inr i => exact (hQ' i).mono _ (by linarith)
  exact pi_cyclicOrbitPoint_dist_le_exp Z (sumOrbits E Q' g qSq) N
    (fun _ : Unit => x) (fun _ : Unit => y) (by positivity : (0 : ℝ) ≤ 2 * p)
    hcountZ (fun i => (hZgeom i).1) hε.le hinputs

end Erdos3.RationalFilteredNilmanifold

end

end OAI
