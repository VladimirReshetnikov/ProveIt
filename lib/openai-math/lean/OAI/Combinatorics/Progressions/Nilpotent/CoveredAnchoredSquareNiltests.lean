import OAI.Combinatorics.Progressions.Estimates.AnchoredSquareImagePartition
import OAI.Combinatorics.Progressions.Nilpotent.NativeSquareNiltest

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration
open scoped TensorProduct

def CoveredAnchoredSquareNiltestsSpec (s a C : ℕ) : Prop :=
    ∀ {L : Type} [LieRing L] [LieAlgebra ℚ L] {d m : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      (D : RationalFilteredNilmanifold L (s + 1) d)
      [TopologicalSpace (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [T2Space (ℝ ⊗[ℚ] D.filtration.squareLieSubalgebra)]
      [TopologicalSpace (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      [T2Space (ℝ ⊗[ℚ] (D.filtration.squareLieSubalgebra ⧸
        D.filtration.squareFiltration.layerIdeal (s + 1)))]
      (b : Basis (Fin m) ℚ L) (v : Fin m → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ v i}))
      (M : ℕ) (hM : 0 < M)
      (hin : scaledIntegerGrid M ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis b v (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b v (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid M),
      let V := D.filtration.squareFiltration.ofAdaptedBasis
        (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
        (D.filtration.squareFinBasis_layers b v hF)
        (D.filtration.squareLattice D.lattice) M hM hin hout
      let Q := D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
        (D.filtration.squareFinBasis_layers b v hF)
        (D.filtration.squareLattice D.lattice) M hM hin hout
      ∀ (Λ : Subgroup Q.filtration.Group) (hΛ : Λ ≤ Q.lattice) (l : ℕ) (hl : 0 < l)
        (hlin : scaledIntegerGrid l ⊆ bchSubgroupCoordinates Q.basis Λ)
        (hlout : bchSubgroupCoordinates Q.basis Λ ⊆ denominatorGrid l),
      let Q' := Q.withLattice Λ l hl hlin hlout
      ∀ (T : D.Niltest (fun _ : Unit => 1)) (c : ℤ) (q N : ℕ) [NeZero q] [NeZero N] {p ε : ℝ},
      2 ≤ p → T.ComplexityLE p → V.GeometryComplexityLE p → Q'.GeometryComplexityLE p →
      (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ p) →
      (q : ℝ) ≤ Real.exp p → 0 < ε → ε ≤ 1 → 1 / ε ≤ Real.exp ((p + 2) ^ a) →
      ∃ δ : ℝ, 0 < δ ∧ δ ≤ ε ∧ 1 / δ ≤ Real.exp ((p + C) ^ C) ∧
        ∃ n k : ℕ, 0 < n ∧ 0 < k ∧
          (Fintype.card ((Fin n × ZMod q) × Fin k) : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          ∃ A : ((Fin n × ZMod q) × Fin k) → ZMod N → ℝ,
            (∀ j, PositiveCyclicNiltest.{0} (s + 1) N ((p + C) ^ C) (A j)) ∧
            (∀ x, ∑ j, A j x = 1) ∧
            (∀ j x, 0 < A j x → (x.val : ZMod q) = j.1.2) ∧
            (∀ j x y, 0 < A j x → 0 < A j y →
              dist (ZMod.toAddCircle x) (ZMod.toAddCircle y) ≤ δ) ∧
            (∀ h : ZMod N, ((cyclicWrapExceptional h δ).card : ℝ) / N ≤ 6 * δ + 3 / N) ∧
            letI := Q'.metricSpace
            ∀ χ : D.RealGroup → CircleFourier.Circle,
              (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
                T.observable (z • x) = CircleFourier.character (χ z) * T.observable x) →
              ∀ (h : ZMod N) (branch : Fin 2), ∃ S : Q.Niltest (fun _ : Unit => 1),
                S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
                (∀ z : Unit → ℤ, S.eval z =
                  T.eval (z + fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) *
                    star (T.eval (z + fun _ => c))) ∧
                let S' := S.onSublattice Λ l hl hlin hlout hΛ
                S'.ComplexityLE ((p + C) ^ C) ∧
                (∀ z : Unit → ℤ, S'.eval z = S.eval z) ∧
                ∀ i j x y,
                  x ∉ cyclicWrapExceptional h δ → y ∉ cyclicWrapExceptional h δ →
                  0 < A i x * A j (x + h) → 0 < A i y * A j (y + h) →
                  dist (Q'.cyclicOrbitPoint S'.orbit N (fun _ : Unit => x))
                    (Q'.cyclicOrbitPoint S'.orbit N (fun _ : Unit => y)) ≤ ε

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup
open scoped TensorProduct

theorem exists_covered_anchored_square_niltests (s a : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ CoveredAnchoredSquareNiltestsSpec s a C := by
  obtain ⟨B, _, hpartition⟩ := exists_anchored_square_image_partition (s + 1) s a
  let R : ℕ := Classical.choose (exists_specified_square_niltest.{0, 0} s)
  have hconstruct := @(Classical.choose_spec (exists_specified_square_niltest.{0, 0} s)).2
  let X : Polynomial ℕ := Polynomial.X
  let P := X + 2
  let U := P + (P + Polynomial.C B) ^ B
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (U + (U + Polynomial.C R) ^ R)
  refine ⟨C, hC, ?_⟩
  dsimp only [CoveredAnchoredSquareNiltestsSpec]
  intro L _ _ d m _ _ _ _ D _ _ _ _ _ _ _ _ b v hF M hM hin hout
    Λ hΛ l hl hlin hlout T c q N _ _ p ε hp hT hV hQ' hb hq hε hε1 hεinv
  let bs := D.filtration.squareFinBasis b v (hF 2)
  let vs := squareFinWeight v
  let hls := D.filtration.squareFinBasis_layers b v hF
  let V := D.filtration.squareFiltration.ofAdaptedBasis bs vs hls
    (D.filtration.squareLattice D.lattice) M hM hin hout
  let Q := D.filtration.squareFiltration.topQuotientModel bs vs hls
    (D.filtration.squareLattice D.lattice) M hM hin hout
  let Q' := Q.withLattice Λ l hl hlin hlout
  let φ := lieQuotientMap (D.filtration.squareFiltration.layerIdeal (s + 1))
  have hp0 : 0 ≤ p := by linarith
  let r := p + 2
  have hpr : p ≤ r := by dsimp [r]; linarith
  have hr : 0 ≤ r := hp0.trans hpr
  have hpair : ∀ i j, rationalLogHeight ((pi (fun _ : Bool => D)).basis.repr
      (D.filtration.squarePairMap (V.basis j)) i) ≤ r := by
    intro i j
    exact (D.squarePairMap_matrix_logHeight b v (hF 2) hp0 (fun i j => hb j i) i j).trans
      (by dsimp [r]; linarith)
  have hφ : ∀ i j, rationalLogHeight (Q'.basis.repr (φ (V.basis j)) i) ≤ r := by
    intro i j
    apply rationalLogHeight_le_of_height
      (quotientFinBasis_projection_height bs (D.filtration.squareFiltration.layerIdeal (s + 1))
        {i | s + 1 ≤ vs i} (hls (s + 1)) j i)
    simpa only [Nat.cast_one] using Real.one_le_exp hr
  obtain ⟨δ, hδ, hδε, hδinv, n, k, hn, hk, hcount, A, hA, hsum, hres, hcircle,
      hexception, hblocks⟩ :=
    hpartition D V Q' φ T.orbit c q N (by omega) (hp.trans hpr)
      (hT.1.mono D hpr) (hV.mono V hpr) (hQ'.mono Q' hpr) hpair hφ
      (hq.trans (Real.exp_le_exp.mpr hpr)) hε hε1
      (hεinv.trans (Real.exp_le_exp.mpr
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ p + 2)
          (by linarith : p + 2 ≤ r + 2) a)))
  let u := r + (r + B) ^ B
  have hru : r ≤ u := le_add_of_nonneg_right (pow_nonneg (by positivity) _)
  have hu : 0 ≤ u := hr.trans hru
  have hBu : (r + B) ^ B ≤ u := le_add_of_nonneg_left hr
  have htotal : u + (u + R) ^ R ≤ (p + C) ^ C := by
    simpa [X, P, U, r, u, Polynomial.eval₂_pow] using hbudget p hp0
  have huC : u ≤ (p + C) ^ C :=
    (le_add_of_nonneg_right (pow_nonneg (by positivity) _)).trans htotal
  have hBC : (r + B) ^ B ≤ (p + C) ^ C := hBu.trans huC
  have hRC : (u + R) ^ R ≤ (p + C) ^ C := (le_add_of_nonneg_left hu).trans htotal
  have hpu : p ≤ u := hpr.trans hru
  refine ⟨δ, hδ, hδε, hδinv.trans (Real.exp_le_exp.mpr hBC), n, k, hn, hk,
    hcount.trans (Real.exp_le_exp.mpr hBC), A, fun j => (hA j).mono le_rfl hBC,
    hsum, hres, hcircle, hexception, ?_⟩
  let := Q'.metricSpace
  intro χ hvert h branch
  obtain ⟨η, γ, rSq, hγ, hη, hnorm, hcell⟩ := hblocks h branch
  obtain ⟨S, horbit, _, hSNorm, hSComplexity, hSval⟩ :=
    hconstruct D b v hF M hM hin hout T hu (hT.mono hpu) (hV.mono V hpu)
      (fun i j => (hb i j).trans hpu) η
      (fun i => (hη i).trans (Real.exp_le_exp.mpr hBu)) rSq χ hvert
  have hSC : S.ComplexityLE ((p + C) ^ C) := hSComplexity.mono hRC
  refine ⟨S, hSNorm, hSC, ?_,
    S.onSublattice_complexity Λ l hl hlin hlout hΛ hSC (hQ'.mono Q' (hpu.trans huC)),
    S.onSublattice_eval Λ l hl hlin hlout hΛ, ?_⟩
  · intro z
    exact (hSval z).trans (D.filtration.realSquareObservable_recovers_product D.lattice η γ
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (z + fun _ => (h.val : ℤ) - (branch.val : ℤ) * N) T.orbit)
      (D.filtration.realification.polynomialOrbitEval (fun _ : Unit => 1)
        (z + fun _ => c) T.orbit) hγ T.observable
      (D.filtration.squareFiltration.realification.polynomialOrbitEval
        (fun _ : Unit => 1) z rSq) (hnorm z).1 (hnorm z).2)
  · intro i j x y hx hy hxy hyy
    have hpoint (z : ZMod N) :
        Q'.cyclicOrbitPoint (S.onSublattice Λ l hl hlin hlout hΛ).orbit N (fun _ : Unit => z) =
          QuotientGroup.mk (realificationMap
            (hnil := D.filtration.squareFiltration.lowerCentralSeries_eq_bot)
            (hM := Q'.filtration.lowerCentralSeries_eq_bot) φ
            (D.filtration.squareFiltration.realification.polynomialOrbitEval
              (fun _ : Unit => 1) (fun _ => (z.val : ℤ)) rSq)) := by
      apply (congrArg (fun g => Q'.cyclicOrbitPoint g N (fun _ : Unit => z)) horbit).trans
      exact congrArg (fun g : Q'.RealGroup => (QuotientGroup.mk g : Q'.Space))
        (D.filtration.squareFiltration.realQuotientPolynomialOrbit_eval
          (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl rSq
          (fun _ : Unit => (z.val : ℤ)))
    exact (congrArg₂ (fun u v : Q'.Space => dist u v) (hpoint x) (hpoint y)).trans_le
      (hcell i j x y hx hy hxy hyy)

end Erdos3.RationalFilteredNilmanifold

end

end OAI
