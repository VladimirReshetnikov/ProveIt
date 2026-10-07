import OAI.Combinatorics.Progressions.Estimates.NativeCommonModelQuadruples
import OAI.Combinatorics.Progressions.Estimates.PositiveShiftNativePartners
import OAI.Combinatorics.Progressions.Estimates.PositiveShiftRefilteredExpansionSpec
import OAI.Combinatorics.Progressions.Estimates.PrescribedPartitionExpansionCore
import OAI.Combinatorics.Progressions.Lattices.AnchoredIntegerIntervalsPower

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct NNReal

theorem exists_controlled_prescribed_square_model (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
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
      {p : ℝ}, 0 ≤ p → D.GeometryComplexityLE p →
      ∃ (b : Basis (Fin (finrank ℚ L)) ℚ L) (v : Fin (finrank ℚ L) → ℕ)
        (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ v i}))
        (M : ℕ) (hM : 0 < M)
        (hin : scaledIntegerGrid M ⊆ bchSubgroupCoordinates
          (D.filtration.squareFinBasis b v (hF 2)) (D.filtration.squareLattice D.lattice))
        (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b v (hF 2))
          (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid M),
        (∀ i j, rationalLogHeight (D.basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        (D.filtration.squareFiltration.ofAdaptedBasis
          (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
          (D.filtration.squareFinBasis_layers b v hF)
          (D.filtration.squareLattice D.lattice) M hM hin hout).GeometryComplexityLE ((p + C) ^ C) ∧
        let Q := D.filtration.squareFiltration.topQuotientModel
          (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
          (D.filtration.squareFinBasis_layers b v hF)
          (D.filtration.squareLattice D.lattice) M hM hin hout
        Q.GeometryComplexityLE ((p + C) ^ C) ∧
        ∀ (w : σ → ℕ), (∀ i, 0 < w i) → ∀ T : D.Niltest w, T.ComplexityLE p →
        ∀ χ : D.RealGroup → CircleFourier.Circle,
          (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
            T.observable (z • x) = character (χ z) * T.observable x) →
        ∀ a b₀ : σ → ℤ, ∃ η γ : D.RealGroup, γ ∈ D.realLattice ∧
          (∀ i, |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp ((p + C) ^ C)) ∧
          ∃ (rSq : D.filtration.squareFiltration.realification.PolynomialOrbit w) (S : Q.Niltest w),
            (∀ x : σ → ℤ,
              D.filtration.realSquareFstHom
                (D.filtration.squareFiltration.realification.polynomialOrbitEval w x rSq) =
                  η⁻¹ * D.filtration.realification.polynomialOrbitEval w (x + a) T.orbit * γ⁻¹ ∧
              D.filtration.realSquareSndHom
                (D.filtration.squareFiltration.realification.polynomialOrbitEval w x rSq) =
                  D.filtration.realification.polynomialOrbitEval w (x + b₀) T.orbit) ∧
            S.orbit = D.filtration.squareFiltration.realQuotientPolynomialOrbit
              (D.filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl rSq ∧
            S.normBound = T.normBound ^ 2 ∧ S.ComplexityLE ((p + C) ^ C) ∧
            ∀ x : σ → ℤ, S.eval x = T.eval (x + a) * star (T.eval (x + b₀)) := by
  obtain ⟨a, _, hnormalize⟩ := exists_native_two_shift_normalization (s + 1)
  obtain ⟨g, _, hgeometry⟩ := squareGeometryBudget_polynomial
  obtain ⟨k, _, htest⟩ := exists_specified_square_niltest s
  let X : Polynomial ℕ := Polynomial.X
  let P := X + 1 + (X + Polynomial.C g) ^ g + (X + 1 + Polynomial.C a) ^ a
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget (P + (P + Polynomial.C k) ^ k)
  refine ⟨C, hC, ?_⟩
  intro σ L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp hD
  let q := p + 1 + (p + g) ^ g + (p + 1 + a) ^ a
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hgp : 0 ≤ (p + g) ^ g := by positivity
  have hap : 0 ≤ (p + 1 + a) ^ a := by positivity
  have hpq : p ≤ q := by dsimp [q]; linarith
  have hp1q : p + 1 ≤ q := by dsimp [q]; linarith
  have hgeomq : squareGeometryBudget p ≤ q := by
    have hg := hgeometry p hp
    dsimp [q]
    linarith
  have hnormq : (p + 1 + a) ^ a ≤ q := by dsimp [q]; linarith
  have hbud : q + (q + k) ^ k ≤ (p + C) ^ C := by
    simpa [P, X, q, Polynomial.eval₂_pow] using hbudget p hp
  have hqC : q ≤ (p + C) ^ C := by
    have hnonneg : 0 ≤ (q + k) ^ k := by positivity
    linarith
  have htestC : (q + k) ^ k ≤ (p + C) ^ C := by linarith
  obtain ⟨b, v, hF, M, hM, hin, hout, hb, hV⟩ := D.exists_controlled_square_geometry hp hD
  let V := D.filtration.squareFiltration.ofAdaptedBasis
    (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
    (D.filtration.squareFinBasis_layers b v hF) (D.filtration.squareLattice D.lattice) M hM hin hout
  let Q := D.filtration.squareFiltration.topQuotientModel
    (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
    (D.filtration.squareFinBasis_layers b v hF) (D.filtration.squareLattice D.lattice) M hM hin hout
  have hVq : V.GeometryComplexityLE q := hV.mono V hgeomq
  have hQq : Q.GeometryComplexityLE q :=
    D.filtration.squareFiltration.topQuotientModel_geometry
      (D.filtration.squareFinBasis b v (hF 2)) (squareFinWeight v)
      (D.filtration.squareFinBasis_layers b v hF) (D.filtration.squareLattice D.lattice)
      M hM hin hout hq hVq
  refine ⟨b, v, hF, M, hM, hin, hout, (fun i j => (hb i j).trans (hp1q.trans hqC)),
    hVq.mono V hqC, hQq.mono Q hqC, ?_⟩
  intro w hw T hT χ hvert left right
  obtain ⟨η, γ, hγ, hη, rSq, hnorm⟩ := hnormalize D hp hD w hw left right T.orbit
  have hηq (i) : |(D.basis.baseChange ℝ).repr η.coord i| ≤ Real.exp q :=
    (hη i).trans (Real.exp_le_exp.mpr hnormq)
  obtain ⟨S, hSo, _, hSn, hSc, hSeval⟩ := htest D b v hF M hM hin hout T hq
    (hT.mono hpq) hVq (fun i j => (hb i j).trans hp1q) η hηq rSq χ hvert
  refine ⟨η, γ, hγ, (fun i => (hηq i).trans (Real.exp_le_exp.mpr hqC)), rSq, S,
    hnorm, hSo, hSn, hSc.mono htestC, ?_⟩
  intro x
  exact (hSeval x).trans (D.filtration.realSquareObservable_recovers_product D.lattice η γ
    (D.filtration.realification.polynomialOrbitEval w (x + left) T.orbit)
    (D.filtration.realification.polynomialOrbitEval w (x + right) T.orbit) hγ T.observable
    (D.filtration.squareFiltration.realification.polynomialOrbitEval w x rSq)
    (hnorm x).1 (hnorm x).2)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct NNReal

theorem exists_controlled_prescribed_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {G J σ : Type*} {L : J → Type*}
      [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)] {d : J → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
      (D : ∀ j, RationalFilteredNilmanifold (L j) (s + 1) (d j))
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] (D j).filtration.squareLieSubalgebra)]
      [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D j).filtration.squareLieSubalgebra)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D j).filtration.squareLieSubalgebra)]
      [∀ j, T2Space (ℝ ⊗[ℚ] (D j).filtration.squareLieSubalgebra)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] ((D j).filtration.squareLieSubalgebra ⧸
        (D j).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D j).filtration.squareLieSubalgebra ⧸
        (D j).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D j).filtration.squareLieSubalgebra ⧸
        (D j).filtration.squareFiltration.layerIdeal (s + 1)))]
      [∀ j, T2Space (ℝ ⊗[ℚ] ((D j).filtration.squareLieSubalgebra ⧸
        (D j).filtration.squareFiltration.layerIdeal (s + 1)))]
      {p : ℝ}, 0 ≤ p → (∀ j, (D j).GeometryComplexityLE p) →
      ∃ (b : ∀ j, Basis (Fin (finrank ℚ (L j))) ℚ (L j))
        (v : ∀ j, Fin (finrank ℚ (L j)) → ℕ)
        (hF : ∀ j i, (D j).filtration.layer i = Submodule.span ℚ (b j '' {k | i ≤ v j k}))
        (M : J → ℕ) (hM : ∀ j, 0 < M j)
        (hin : ∀ j, scaledIntegerGrid (M j) ⊆ bchSubgroupCoordinates
          ((D j).filtration.squareFinBasis (b j) (v j) (hF j 2)) ((D j).filtration.squareLattice (D j).lattice))
        (hout : ∀ j, bchSubgroupCoordinates ((D j).filtration.squareFinBasis (b j) (v j) (hF j 2))
          ((D j).filtration.squareLattice (D j).lattice) ⊆ denominatorGrid (M j)),
        (∀ j i k, rationalLogHeight ((D j).basis.repr (b j i) k) ≤ (p + C) ^ C) ∧
        (∀ j, ((D j).filtration.squareFiltration.ofAdaptedBasis
          ((D j).filtration.squareFinBasis (b j) (v j) (hF j 2)) (squareFinWeight (v j))
          ((D j).filtration.squareFinBasis_layers (b j) (v j) (hF j))
          ((D j).filtration.squareLattice (D j).lattice) (M j) (hM j) (hin j) (hout j)).GeometryComplexityLE ((p + C) ^ C)) ∧
        let Q := fun j => (D j).filtration.squareFiltration.topQuotientModel
          ((D j).filtration.squareFinBasis (b j) (v j) (hF j 2)) (squareFinWeight (v j))
          ((D j).filtration.squareFinBasis_layers (b j) (v j) (hF j))
          ((D j).filtration.squareLattice (D j).lattice) (M j) (hM j) (hin j) (hout j)
        (∀ j, (Q j).GeometryComplexityLE ((p + C) ^ C)) ∧
        ∀ (w : σ → ℕ), (∀ i, 0 < w i) →
        ∀ T : ∀ j, (D j).Niltest w, (∀ j, (T j).ComplexityLE p) →
        ∀ χ : ∀ j, (D j).RealGroup → CircleFourier.Circle,
          (∀ j z, z ∈ (D j).filtration.realification.subgroup (s + 1) → ∀ x,
            (T j).observable (z • x) = character (χ j z) * (T j).observable x) →
        ∀ left right : G → J → σ → ℤ,
        ∃ (η γ : G → ∀ j, (D j).RealGroup)
          (rSq : G → ∀ j, (D j).filtration.squareFiltration.realification.PolynomialOrbit w)
          (S : G → ∀ j, (Q j).Niltest w),
          ∀ h j, γ h j ∈ (D j).realLattice ∧
            (∀ i, |((D j).basis.baseChange ℝ).repr (η h j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
            (∀ x : σ → ℤ,
              (D j).filtration.realSquareFstHom
                ((D j).filtration.squareFiltration.realification.polynomialOrbitEval w x (rSq h j)) =
                  (η h j)⁻¹ * (D j).filtration.realification.polynomialOrbitEval w (x + left h j) (T j).orbit * (γ h j)⁻¹ ∧
              (D j).filtration.realSquareSndHom
                ((D j).filtration.squareFiltration.realification.polynomialOrbitEval w x (rSq h j)) =
                  (D j).filtration.realification.polynomialOrbitEval w (x + right h j) (T j).orbit) ∧
            (S h j).orbit = (D j).filtration.squareFiltration.realQuotientPolynomialOrbit
              ((D j).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq h j) ∧
            (S h j).normBound = (T j).normBound ^ 2 ∧ (S h j).ComplexityLE ((p + C) ^ C) ∧
            ∀ x : σ → ℤ, (S h j).eval x = (T j).eval (x + left h j) * star ((T j).eval (x + right h j)) := by
  classical
  obtain ⟨C, hC, hmodel⟩ := exists_controlled_prescribed_square_model s
  refine ⟨C, hC, ?_⟩
  intro G J σ L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp hD
  have hmodels (j : J) := hmodel (σ := σ) (D j) hp (hD j)
  choose b v hF M hM hin hout hb hV hQ hbuild using hmodels
  refine ⟨b, v, hF, M, hM, hin, hout, hb, hV, hQ, ?_⟩
  intro w hw T hT χ hvert left right
  have hchoices (h : G) (j : J) := hbuild j w hw (T j) (hT j) (χ j) (hvert j) (left h j) (right h j)
  choose η γ hγ hη rSq S hnorm hSo hSn hSc hSval using hchoices
  exact ⟨η, γ, rSq, S, fun h j => ⟨hγ h j, hη h j, hnorm h j, hSo h j, hSn h j, hSc h j, hSval h j⟩⟩

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.PositiveShiftBasis

open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_native_partner_intervals {s N : ℕ} [NeZero N] {q : ℝ}
    {a J : ZMod N → ℝ} (B : PositiveShiftBasis s N q a J)
    {L M : Fin B.count → Type*}
    [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
    [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
    [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
    [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
    {d e : Fin B.count → ℕ}
    (D : ∀ j, RationalFilteredNilmanifold (L j) (s + 1) (d j))
    (E : ∀ j, RationalFilteredNilmanifold (M j) (s + 1) (e j))
    (Q : ∀ j, (D j).Niltest (fun _ : Unit => 1))
    (R : ∀ j, (E j).Niltest (fun _ : Unit => 1))
    (H : Finset (ZMod N)) (hsub : H ⊆ B.shifts) {p : ℝ} (hp : 2 ≤ p) (hqp : q ≤ p)
    (hsize : Real.exp (-p) * N ≤ (H.card : ℝ))
    (hQ : ∀ j, (Q j).normBound ≤ 1) (hR : ∀ j, (R j).normBound ≤ 1)
    (hcorr : ∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
      (B.mode h j).evalCyclic N (fun _ => n) * (Q j).evalCyclic N (fun _ => n) *
        (R j).evalCyclic N (fun _ => n + h)‖) :
    ∃ h₀ ∈ H, ∃ (branches : Fin B.count → Bool × Bool) (S : Finset (ZMod N)),
      S ⊆ H ∧ S.Nonempty ∧ Real.exp (-((p + 2) ^ 3)) * N ≤ (S.card : ℝ) ∧
      ∀ h ∈ S, ∀ j, ∃ start len : ℕ, 0 < len ∧ start + len ≤ N ∧
        2 * ((len : ℤ) - 1) < N ∧ Real.exp (-((p + 2) ^ 3)) * N ≤ (len : ℝ) ∧
        Real.exp (-((p + 2) ^ 3)) ≤
          ‖𝔼 x ∈ translatedIntegerBox (fun _ : Unit => (start : ℤ)) (fun _ => len),
            (B.mode h j).eval x * star ((B.mode h₀ j).eval x) *
              ((Q j).eval x * star ((Q j).eval x)) *
              ((R j).eval (x + fun _ => cyclicBranchOffset h (branches j).1) *
                star ((R j).eval (x + fun _ => cyclicBranchOffset h₀ (branches j).2)))‖ := by
  have hm : (Fintype.card (Fin B.count) : ℝ) ≤ p := by
    rw [Fintype.card_fin]
    exact (Nat.cast_le.mpr B.count_le_dim).trans (B.geometry.1.trans hqp)
  obtain ⟨h₀, hh₀, branches, S, hSH, hSn, hlarge, hinterval⟩ :=
    exists_anchored_integer_intervals_power H
      (fun h j n => (B.mode h j).eval (fun _ => n))
      (fun j n => (Q j).eval (fun _ => n)) (fun j n => (R j).eval (fun _ => n))
      hp hm le_rfl hsize
      (fun h hh j n => ((B.mode h j).norm_eval_le _).trans (B.mode_norm h (hsub hh) j))
      (fun j n => ((Q j).norm_eval_le _).trans (hQ j))
      (fun j n => ((R j).norm_eval_le _).trans (hR j)) hcorr
  refine ⟨h₀, hh₀, branches, S, hSH, hSn, hlarge, ?_⟩
  intro h hh j
  obtain ⟨start, len, hlen, hbound, hshort, hbias, hvol⟩ := hinterval h hh j
  have hN : (0 : ℝ) < N := by exact_mod_cast NeZero.pos N
  refine ⟨start, len, hlen, hbound, hshort, (le_div_iff₀ hN).mp hvol, ?_⟩
  rw [unitIntervalBox_expect]
  have hshift (n c : ℤ) : ((fun _ : Unit => n) + fun _ => c) = (fun _ => n + c) := rfl
  simpa only [hshift, partnerAnchorWeight, mul_assoc] using hbias

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration

variable {L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}

structure SquareModelData (D : RationalFilteredNilmanifold L (s + 1) d) where
  basis : Basis (Fin (finrank ℚ L)) ℚ L
  weight : Fin (finrank ℚ L) → ℕ
  layers : ∀ i, D.filtration.layer i = Submodule.span ℚ (basis '' {j | i ≤ weight j})
  grid : ℕ
  grid_pos : 0 < grid
  inner : scaledIntegerGrid grid ⊆ bchSubgroupCoordinates
    (D.filtration.squareFinBasis basis weight (layers 2)) (D.filtration.squareLattice D.lattice)
  outer : bchSubgroupCoordinates (D.filtration.squareFinBasis basis weight (layers 2))
    (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid grid

namespace SquareModelData

variable {D : RationalFilteredNilmanifold L (s + 1) d}

noncomputable def fullModel (F : D.SquareModelData) :=
  D.filtration.squareFiltration.ofAdaptedBasis
    (D.filtration.squareFinBasis F.basis F.weight (F.layers 2)) (squareFinWeight F.weight)
    (D.filtration.squareFinBasis_layers F.basis F.weight F.layers)
    (D.filtration.squareLattice D.lattice) F.grid F.grid_pos F.inner F.outer

noncomputable def quotientModel (F : D.SquareModelData) :=
  D.filtration.squareFiltration.topQuotientModel
    (D.filtration.squareFinBasis F.basis F.weight (F.layers 2)) (squareFinWeight F.weight)
    (D.filtration.squareFinBasis_layers F.basis F.weight F.layers)
    (D.filtration.squareLattice D.lattice) F.grid F.grid_pos F.inner F.outer

theorem quotientModel_adapted (F : D.SquareModelData) :
    ∃ w : _ → ℕ, ∀ j, F.quotientModel.filtration.layer j =
      Submodule.span ℚ (F.quotientModel.basis '' {i | j ≤ w i}) := by
  classical
  refine ⟨quotientFinWeight (squareFinWeight F.weight)
    {i | s + 1 ≤ squareFinWeight F.weight i}, ?_⟩
  exact D.filtration.squareFiltration.topQuotientModel_basis_layers
    (D.filtration.squareFinBasis F.basis F.weight (F.layers 2)) (squareFinWeight F.weight)
    (D.filtration.squareFinBasis_layers F.basis F.weight F.layers)
    (D.filtration.squareLattice D.lattice) F.grid F.grid_pos F.inner F.outer

end SquareModelData
end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.PositiveShiftBasis

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators NNReal

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

theorem exists_prescribed_lower_inputs (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis s N q a J) {L : (Fin B.count × Bool) → Type*}
      [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Fin B.count × Bool) → ℕ}
      [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
      [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
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
      (T : ∀ i, (D i).Niltest (fun _ : Unit => 1))
      (H : Finset (ZMod N)), H ⊆ B.shifts →
      ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ i, (T i).ComplexityLE p) → (∀ i, (T i).normBound ≤ 1) →
      ∀ χ : ∀ i, (D i).RealGroup → CircleFourier.Circle,
      (∀ i z, z ∈ (D i).filtration.realification.subgroup (s + 1) → ∀ x,
        (T i).observable (z • x) = character (χ i z) * (T i).observable x) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
        (B.mode h j).evalCyclic N (fun _ => n) * (T (j, true)).evalCyclic N (fun _ => n) *
          (T (j, false)).evalCyclic N (fun _ => n + h)‖) →
      ∃ F : ∀ i, (D i).SquareModelData,
        (∀ i, (F i).fullModel.GeometryComplexityLE ((p + C) ^ C)) ∧
        (∀ i, (F i).quotientModel.GeometryComplexityLE ((p + C) ^ C)) ∧
        (∀ i j k, rationalLogHeight ((D i).basis.repr ((F i).basis j) k) ≤ (p + C) ^ C) ∧
        ∃ h₀ ∈ H, ∃ (branches : Fin B.count → Bool × Bool) (S : Finset (ZMod N)),
          S ⊆ H ∧ S.Nonempty ∧ Real.exp (-((p + C) ^ C)) * N ≤ (S.card : ℝ) ∧
          ∃ (A : ∀ j, (F (j, true)).quotientModel.Niltest (fun _ : Unit => 1))
            (R : ZMod N → ∀ j, (F (j, false)).quotientModel.Niltest (fun _ : Unit => 1))
            (η γ : ZMod N → ∀ j, (D (j, false)).RealGroup)
            (rSq : ZMod N → ∀ j,
              (D (j, false)).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ j, (A j).normBound ≤ 1 ∧ (A j).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (A j).eval x = (T (j, true)).eval x * star ((T (j, true)).eval x)) ∧
            (∀ h j, γ h j ∈ (D (j, false)).realLattice ∧
              (∀ i, |((D (j, false)).basis.baseChange ℝ).repr (η h j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (∀ x : Unit → ℤ,
                (D (j, false)).filtration.realSquareFstHom
                  ((D (j, false)).filtration.squareFiltration.realification.polynomialOrbitEval
                    (fun _ => 1) x (rSq h j)) =
                    (η h j)⁻¹ * (D (j, false)).filtration.realification.polynomialOrbitEval (fun _ => 1)
                      (x + fun _ => cyclicBranchOffset h (branches j).1) (T (j, false)).orbit * (γ h j)⁻¹ ∧
                (D (j, false)).filtration.realSquareSndHom
                  ((D (j, false)).filtration.squareFiltration.realification.polynomialOrbitEval
                    (fun _ => 1) x (rSq h j)) =
                    (D (j, false)).filtration.realification.polynomialOrbitEval (fun _ => 1)
                      (x + fun _ => cyclicBranchOffset h₀ (branches j).2) (T (j, false)).orbit) ∧
              (R h j).orbit = (D (j, false)).filtration.squareFiltration.realQuotientPolynomialOrbit
                ((D (j, false)).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq h j) ∧
              (R h j).normBound ≤ 1 ∧ (R h j).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (R h j).eval x =
                (T (j, false)).eval (x + fun _ => cyclicBranchOffset h (branches j).1) *
                  star ((T (j, false)).eval (x + fun _ => cyclicBranchOffset h₀ (branches j).2))) ∧
            ∀ h ∈ S, ∀ j, ∃ start len : ℕ, 0 < len ∧ start + len ≤ N ∧
              2 * ((len : ℤ) - 1) < N ∧ Real.exp (-((p + C) ^ C)) * N ≤ (len : ℝ) ∧
              Real.exp (-((p + C) ^ C)) ≤
                ‖𝔼 x ∈ translatedIntegerBox (fun _ : Unit => (start : ℤ)) (fun _ => len),
                  (B.mode h j).eval x * star ((B.mode h₀ j).eval x) * (A j).eval x * (R h j).eval x‖ := by
  classical
  obtain ⟨c, _, hfamily⟩ := RationalFilteredNilmanifold.exists_controlled_prescribed_square_family s
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget ((X + Polynomial.C c) ^ c + (X + 2) ^ 3 + X + 2)
  refine ⟨C, hC, ?_⟩
  intro N _ q a J B L _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ T H hH p hp hqp hsize hTc hTn χ hvert hcorr
  have hp0 : 0 ≤ p := by linarith
  have hbud : (p + c) ^ c + (p + 2) ^ 3 + p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp0
  have hc0 : 0 ≤ (p + c) ^ c := by positivity
  have hi0 : 0 ≤ (p + 2) ^ 3 := by positivity
  have hcC : (p + c) ^ c ≤ (p + C) ^ C := by linarith
  have hiC : (p + 2) ^ 3 ≤ (p + C) ^ C := by linarith
  obtain ⟨b, v, hF, M, hM, hin, hout, hb, hV, hQ, hbuild⟩ :=
    hfamily (G := Option (ZMod N)) (σ := Unit) D hp0 (fun i => (hTc i).1)
  let F : ∀ i, (D i).SquareModelData := fun i =>
    { basis := b i, weight := v i, layers := hF i, grid := M i,
      grid_pos := hM i, inner := hin i, outer := hout i }
  obtain ⟨h₀, hh₀, branches, S, hSH, hSn, hlarge, hinterval⟩ := B.exists_native_partner_intervals
    (fun j => D (j, true)) (fun j => D (j, false))
    (fun j => T (j, true)) (fun j => T (j, false)) H hH hp hqp hsize
    (fun j => hTn (j, true)) (fun j => hTn (j, false)) hcorr
  let left : Option (ZMod N) → (Fin B.count × Bool) → Unit → ℤ := fun h i =>
    match h with
    | none => 0
    | some h => if i.2 then 0 else fun _ => cyclicBranchOffset h (branches i.1).1
  let right : Option (ZMod N) → (Fin B.count × Bool) → Unit → ℤ := fun h i =>
    match h with
    | none => 0
    | some _ => if i.2 then 0 else fun _ => cyclicBranchOffset h₀ (branches i.1).2
  obtain ⟨η, γ, rSq, U, hdata⟩ := hbuild (fun _ => 1) (fun _ => by norm_num) T hTc χ hvert left right
  let A : ∀ j, (F (j, true)).quotientModel.Niltest (fun _ : Unit => 1) := fun j => U none (j, true)
  let R : ZMod N → ∀ j, (F (j, false)).quotientModel.Niltest (fun _ : Unit => 1) :=
    fun h j => U (some h) (j, false)
  have hAval (j) (x) : (A j).eval x = (T (j, true)).eval x * star ((T (j, true)).eval x) := by
    change (U none (j, true)).eval x = _
    simpa only [left, right, add_zero] using (hdata none (j, true)).2.2.2.2.2.2 x
  have hRval (h j) (x) : (R h j).eval x =
      (T (j, false)).eval (x + fun _ => cyclicBranchOffset h (branches j).1) *
        star ((T (j, false)).eval (x + fun _ => cyclicBranchOffset h₀ (branches j).2)) := by
    change (U (some h) (j, false)).eval x = _
    simpa only [left, right, Bool.false_eq_true, ↓reduceIte] using
      (hdata (some h) (j, false)).2.2.2.2.2.2 x
  refine ⟨F, ?_, ?_, (fun i j k => (hb i j k).trans hcC), h₀, hh₀, branches, S, hSH, hSn, ?_,
    A, R, (fun h j => η (some h) (j, false)), (fun h j => γ (some h) (j, false)),
    (fun h j => rSq (some h) (j, false)), ?_, ?_, ?_⟩
  · exact fun i => (hV i).mono (F i).fullModel hcC
  · exact fun i => (hQ i).mono (F i).quotientModel hcC
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hiC))
      (Nat.cast_nonneg N)).trans hlarge
  · intro j
    obtain ⟨_, _, _, _, hn, hc, _⟩ := hdata none (j, true)
    refine ⟨?_, hc.mono hcC, hAval j⟩
    change (U none (j, true)).normBound ≤ 1
    rw [hn]
    exact pow_le_one₀ (by positivity) (hTn (j, true))
  · intro h j
    obtain ⟨hγ, hη, hnorm, hOrbit, hn, hc, _⟩ := hdata (some h) (j, false)
    refine ⟨hγ, (fun i => (hη i).trans (Real.exp_le_exp.mpr hcC)), ?_, hOrbit, ?_, hc.mono hcC, hRval h j⟩
    · simpa only [left, right, Bool.false_eq_true, ↓reduceIte] using hnorm
    · change (U (some h) (j, false)).normBound ≤ 1
      rw [hn]
      exact pow_le_one₀ (by positivity) (hTn (j, false))
  · intro h hh j
    obtain ⟨start, len, hlen, hbound, hshort, hvol, hbias⟩ := hinterval h hh j
    refine ⟨start, len, hlen, hbound, hshort, ?_, ?_⟩
    · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hiC))
        (Nat.cast_nonneg N)).trans hvol
    · simp only [hAval, hRval]
      exact (Real.exp_le_exp.mpr (neg_le_neg hiC)).trans hbias

end Erdos3.PositiveShiftBasis

end

section

universe u

namespace Erdos3.PositiveShiftBasis

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def PrescribedCommonFactorizationSpec (s C : ℕ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {a J : ZMod N → ℝ}
      (B : PositiveShiftBasis.{u} s N q a J) (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {L : (Fin B.count × Bool) → Type u}
        [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Fin B.count × Bool) → ℕ}
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
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
        (T : ∀ i, (D i).Niltest (fun _ : Unit => 1)) (H : Finset (ZMod N)),
      H ⊆ B.shifts → ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ i, (T i).ComplexityLE p) → (∀ i, (T i).normBound ≤ 1) →
      ∀ χ : ∀ i, (D i).RealGroup → CircleFourier.Circle,
      (∀ i z, z ∈ (D i).filtration.realification.subgroup (s + 1) → ∀ x,
        (T i).observable (z • x) = character (χ i z) * (T i).observable x) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
        (B.mode h j).evalCyclic N (fun _ => n) * (T (j, true)).evalCyclic N (fun _ => n) *
          (T (j, false)).evalCyclic N (fun _ => n + h)‖) →
      Real.exp ((p + C) ^ C) ≤ N →
      ∃ F : ∀ i, (D i).SquareModelData,
        (∀ i, (F i).fullModel.GeometryComplexityLE ((p + C) ^ C)) ∧
        (∀ i, (F i).quotientModel.GeometryComplexityLE ((p + C) ^ C)) ∧
        (∀ i j k, rationalLogHeight ((D i).basis.repr ((F i).basis j) k) ≤ (p + C) ^ C) ∧
        ∃ h₀ ∈ H, ∃ branches : Fin B.count → Bool × Bool,
          ∃ (A : ∀ j, (F (j, true)).quotientModel.Niltest (fun _ : Unit => 1))
            (R : ZMod N → ∀ j, (F (j, false)).quotientModel.Niltest (fun _ : Unit => 1))
            (η γ : ZMod N → ∀ j, (D (j, false)).RealGroup)
            (rSq : ZMod N → ∀ j,
              (D (j, false)).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
            (∀ j, (A j).normBound ≤ 1 ∧ (A j).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (A j).eval x = (T (j, true)).eval x * star ((T (j, true)).eval x)) ∧
            (∀ h j, γ h j ∈ (D (j, false)).realLattice ∧
              (∀ i, |((D (j, false)).basis.baseChange ℝ).repr (η h j).coord i| ≤ Real.exp ((p + C) ^ C)) ∧
              (∀ x : Unit → ℤ,
                (D (j, false)).filtration.realSquareFstHom
                  ((D (j, false)).filtration.squareFiltration.realification.polynomialOrbitEval
                    (fun _ => 1) x (rSq h j)) =
                    (η h j)⁻¹ * (D (j, false)).filtration.realification.polynomialOrbitEval (fun _ => 1)
                      (x + fun _ => cyclicBranchOffset h (branches j).1) (T (j, false)).orbit * (γ h j)⁻¹ ∧
                (D (j, false)).filtration.realSquareSndHom
                  ((D (j, false)).filtration.squareFiltration.realification.polynomialOrbitEval
                    (fun _ => 1) x (rSq h j)) =
                    (D (j, false)).filtration.realification.polynomialOrbitEval (fun _ => 1)
                      (x + fun _ => cyclicBranchOffset h₀ (branches j).2) (T (j, false)).orbit) ∧
              (R h j).orbit = (D (j, false)).filtration.squareFiltration.realQuotientPolynomialOrbit
                ((D (j, false)).filtration.squareFiltration.layerIdeal (s + 1)) (t := s) le_rfl (rSq h j) ∧
              (R h j).normBound ≤ 1 ∧ (R h j).ComplexityLE ((p + C) ^ C) ∧
              ∀ x, (R h j).eval x =
                (T (j, false)).eval (x + fun _ => cyclicBranchOffset h (branches j).1) *
                  star ((T (j, false)).eval (x + fun _ => cyclicBranchOffset h₀ (branches j).2))) ∧
            Nonempty (B.CommonFactorization (fun j => (F (j, true)).quotientModel)
              (fun j => (F (j, false)).quotientModel) A R h₀ H ((p + C) ^ C))

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module RationalFilteredNilmanifold NilpotentLieFiltration
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff
attribute [local instance_reducible] optionLieSpace

def FactoredPositiveShiftContradictionSpec (s Dexp : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight)
      {L M : Fin B.count → Type}
      [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
      [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
      (D : ∀ j, RationalFilteredNilmanifold (L j) (s + 1) (d j))
      (E : ∀ j, RationalFilteredNilmanifold (M j) (s + 1 + 1) (e j))
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] (E j).filtration.squareLieSubalgebra)]
      [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] (E j).filtration.squareLieSubalgebra)]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] (E j).filtration.squareLieSubalgebra)]
      [∀ j, T2Space (ℝ ⊗[ℚ] (E j).filtration.squareLieSubalgebra)]
      [∀ j, TopologicalSpace (ℝ ⊗[ℚ] ((E j).filtration.squareLieSubalgebra ⧸
        (E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
      [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((E j).filtration.squareLieSubalgebra ⧸
        (E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
      [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((E j).filtration.squareLieSubalgebra ⧸
        (E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
      [∀ j, T2Space (ℝ ⊗[ℚ] ((E j).filtration.squareLieSubalgebra ⧸
        (E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
      (Y : ∀ j, (E j).SquareModelData)
      (A : ∀ j, (D j).Niltest (fun _ : Unit => 1))
      (R : ZMod N → ∀ j, (Y j).quotientModel.Niltest (fun _ : Unit => 1))
      (anchor : ZMod N) (H : Finset (ZMod N)) {p : ℝ}
      (F : B.CommonFactorization D (fun j => (Y j).quotientModel) A R anchor H p),
      H ⊆ B.shifts → 2 ≤ p → q ≤ p →
      (∀ j, (D j).GeometryComplexityLE p) → (∀ j, (E j).GeometryComplexityLE p) →
      (∀ j, (Y j).fullModel.GeometryComplexityLE p) →
      (∀ j, (Y j).quotientModel.GeometryComplexityLE p) →
      (∀ j i k, rationalLogHeight ((E j).basis.repr ((Y j).basis i) k) ≤ p) →
      ∀ (g₀ : ∀ j, (E j).filtration.realification.PolynomialOrbit (fun _ : Unit => 1))
        (branches : Fin B.count → Bool × Bool)
        (η γ : ZMod N → ∀ j, (E j).RealGroup)
        (rSq : ZMod N → ∀ j,
          (E j).filtration.squareFiltration.realification.PolynomialOrbit (fun _ : Unit => 1)),
        (∀ h ∈ F.shifts, ∀ j, γ h j ∈ (E j).realLattice) →
        (∀ h ∈ F.shifts, ∀ j i, |((E j).basis.baseChange ℝ).repr (η h j).coord i| ≤ Real.exp p) →
        (∀ h ∈ F.shifts, ∀ j (x : Unit → ℤ),
          (E j).filtration.realSquareFstHom
            ((E j).filtration.squareFiltration.realification.polynomialOrbitEval
              (fun _ => 1) x (rSq h j)) =
              (η h j)⁻¹ * (E j).filtration.realification.polynomialOrbitEval (fun _ => 1)
                (x + fun _ => cyclicBranchOffset h (branches j).1) (g₀ j) * (γ h j)⁻¹ ∧
          (E j).filtration.realSquareSndHom
            ((E j).filtration.squareFiltration.realification.polynomialOrbitEval
              (fun _ => 1) x (rSq h j)) =
              (E j).filtration.realification.polynomialOrbitEval (fun _ => 1)
                (x + fun _ => cyclicBranchOffset anchor (branches j).2) (g₀ j)) →
        (∀ h ∈ F.shifts, ∀ j, (R h j).orbit =
          (E j).filtration.squareFiltration.realQuotientPolynomialOrbit
            ((E j).filtration.squareFiltration.layerIdeal (s + 1 + 1)) (t := s + 1) le_rfl (rSq h j)) →
        Odd N → Real.exp ((productExpansionBudget p + 2) ^ Dexp) ≤ N →
        (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
        (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
        (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
        CyclicNiltestUpperComparison.{0} (s + 2) N ((productExpansionBudget p + 2) ^ Dexp)
          (Real.exp (-((productExpansionBudget p + 2) ^ Dexp))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def NativePartnerContradictionSpec (s C : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight) (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {L : (Fin B.count × Bool) → Type}
        [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)] {d : (Fin B.count × Bool) → ℕ}
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
        (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1 + 1) (d i))
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, T2Space (ℝ ⊗[ℚ] (D i).filtration.squareLieSubalgebra)]
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
        [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
        [∀ i, T2Space (ℝ ⊗[ℚ] ((D i).filtration.squareLieSubalgebra ⧸
          (D i).filtration.squareFiltration.layerIdeal (s + 1 + 1)))]
        (T : ∀ i, (D i).Niltest (fun _ : Unit => 1)) (H : Finset (ZMod N)),
      H ⊆ B.shifts → ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ i, (T i).ComplexityLE p) → (∀ i, (T i).normBound ≤ 1) →
      ∀ χ : ∀ i, (D i).RealGroup → CircleFourier.Circle,
      (∀ i z, z ∈ (D i).filtration.realification.subgroup (s + 1 + 1) → ∀ x,
        (T i).observable (z • x) = character (χ i z) * (T i).observable x) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
        (B.mode h j).evalCyclic N (fun _ => n) * (T (j, true)).evalCyclic N (fun _ => n) *
          (T (j, false)).evalCyclic N (fun _ => n + h)‖) →
      Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
      (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module NilpotentLieFiltration CircleFourier
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def NativePartnerPairContradictionSpec (s C : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight)
      (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {L M : Fin B.count → Type}
        [∀ j, LieRing (L j)] [∀ j, LieAlgebra ℚ (L j)]
        [∀ j, LieRing (M j)] [∀ j, LieAlgebra ℚ (M j)] {d e : Fin B.count → ℕ}
        [∀ j, TopologicalSpace (ℝ ⊗[ℚ] L j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] L j)]
        [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] L j)] [∀ j, T2Space (ℝ ⊗[ℚ] L j)]
        [∀ j, TopologicalSpace (ℝ ⊗[ℚ] M j)] [∀ j, IsTopologicalAddGroup (ℝ ⊗[ℚ] M j)]
        [∀ j, ContinuousSMul ℝ (ℝ ⊗[ℚ] M j)] [∀ j, T2Space (ℝ ⊗[ℚ] M j)]
        (D : ∀ j, RationalFilteredNilmanifold (L j) (s + 1 + 1) (d j))
        (E : ∀ j, RationalFilteredNilmanifold (M j) (s + 1 + 1) (e j))
        (V : ∀ j, (D j).Niltest (fun _ : Unit => 1))
        (W : ∀ j, (E j).Niltest (fun _ : Unit => 1)) (H : Finset (ZMod N)),
      H ⊆ B.shifts → ∀ {p : ℝ}, 2 ≤ p → q ≤ p → Real.exp (-p) * N ≤ (H.card : ℝ) →
      (∀ j, (V j).ComplexityLE p) → (∀ j, (W j).ComplexityLE p) →
      (∀ j, (V j).normBound ≤ 1) → (∀ j, (W j).normBound ≤ 1) →
      ∀ (χ : ∀ j, (D j).RealGroup → CircleFourier.Circle)
        (χ' : ∀ j, (E j).RealGroup → CircleFourier.Circle),
      (∀ j z, z ∈ (D j).filtration.realification.subgroup (s + 1 + 1) → ∀ x,
        (V j).observable (z • x) = character (χ j z) * (V j).observable x) →
      (∀ j z, z ∈ (E j).filtration.realification.subgroup (s + 1 + 1) → ∀ x,
        (W j).observable (z • x) = character (χ' j z) * (W j).observable x) →
      (∀ h ∈ H, ∀ j, Real.exp (-p) ≤ ‖𝔼 n,
        (B.mode h j).evalCyclic N (fun _ => n) * (V j).evalCyclic N (fun _ => n) *
          (W j).evalCyclic N (fun _ => n + h)‖) →
      Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
      (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def TwoSiteModelContradictionSpec (s C : ℕ) (epsilon : ℝ) : Prop :=
    ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
      (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight)
      (w : Fin B.dim → ℕ),
      (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
      ∀ {I : Type} {K : I → Type} [Fintype I] [∀ i, Fintype (K i)]
        {L : I → Type} {M : ∀ i, K i → Type}
        [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
        [∀ i k, LieRing (M i k)] [∀ i k, LieAlgebra ℚ (M i k)]
        [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
        [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
        [∀ i k, TopologicalSpace (ℝ ⊗[ℚ] M i k)] [∀ i k, IsTopologicalAddGroup (ℝ ⊗[ℚ] M i k)]
        [∀ i k, ContinuousSMul ℝ (ℝ ⊗[ℚ] M i k)] [∀ i k, T2Space (ℝ ⊗[ℚ] M i k)]
        {d : I → ℕ} {e : ∀ i, K i → ℕ}
        (D : ∀ i, RationalFilteredNilmanifold (L i) (s + 1 + 1) (d i))
        (E : ∀ i k, RationalFilteredNilmanifold (M i k) (s + 1 + 1) (e i k))
        (Q : ∀ i, (D i).Niltest (fun _ : Unit => 1))
        (R : ∀ i k, (E i k).Niltest (fun _ : Unit => 1))
        (ea : ZMod N → ℂ) (eb : I → ZMod N → ℂ) (c : I → ℂ) (b : ∀ i, K i → ℂ),
      (∀ n, ((f₁ n - (1 + epsilon) * f₂ n : ℝ) : ℂ) =
        (∑ i, c i * (Q i).evalCyclic N (fun _ => n)) + ea n) →
      (∀ i n, (weight n : ℂ) = (∑ k, b i k * (R i k).evalCyclic N (fun _ => n)) + eb i n) →
      ∀ {p : ℝ}, 2 ≤ p → q ≤ p →
      (∑ i, ‖c i‖) ≤ Real.exp p → (∀ i, (∑ k, ‖b i k‖) ≤ Real.exp p) →
      (∀ i, (Q i).ComplexityLE p) → (∀ i k, (R i k).ComplexityLE p) →
      (∀ i, (Q i).normBound ≤ 1) → (∀ i k, (R i k).normBound ≤ 1) →
      (shiftTestingSeminorm (fun n => (weight n : ℂ)) B.testingFamily ea +
        ∑ i, ‖c i‖ * shiftTestingSeminorm (fun n => (Q i).evalCyclic N (fun _ => n))
          (translatedTestFamily B.testingFamily) (eb i) ≤ Real.exp (-(2 * q + 2))) →
      (Fintype.card (Sigma K) : ℝ) ≤ Real.exp p →
      Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
      (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

section

namespace Erdos3.PositiveShiftBasis

open Module
open scoped TensorProduct BigOperators

attribute [local instance] PositiveShiftBasis.lie PositiveShiftBasis.algebra
  PositiveShiftBasis.topology PositiveShiftBasis.topologicalAdd
  PositiveShiftBasis.continuousSMul PositiveShiftBasis.hausdorff

def NativeDetectorContradictionSpec (s C : ℕ) (epsilon : ℝ) : Prop :=
  ∀ {N : ℕ} [NeZero N] {q : ℝ} {f₁ f₂ weight : ZMod N → ℝ}
    (B : PositiveShiftBasis.{0} (s + 1) N q (fun n => f₁ n - (1 + epsilon) * f₂ n) weight)
    (w : Fin B.dim → ℕ),
    (∀ k, B.model.filtration.layer k = Submodule.span ℚ (B.model.basis '' {i | k ≤ w i})) →
    ∀ {p p₁ p₂ K M beta₁ beta₂ : ℝ},
      2 ≤ p → 2 ≤ p₁ → 2 ≤ p₂ → q ≤ p → p₁ ≤ p → p₂ ≤ p →
      0 < K → 0 < M → 0 < beta₁ → 0 < beta₂ →
      (∀ n, ‖((f₁ n - (1 + epsilon) * f₂ n : ℝ) : ℂ)‖ ≤ M) →
      (∀ n, ‖(weight n : ℂ)‖ ≤ K) →
      2 / beta₁ ≤ Real.exp p → 2 / beta₂ ≤ Real.exp p →
      let eta := Real.exp (-(2 * q + 2))
      (1 + 4 * K ^ 2 / (beta₁ ^ 2 * (eta / 4) ^ 2)) *
        (1 + 4 / (beta₂ ^ 2 * (eta * beta₁ / 8) ^ 2)) ≤ Real.exp p →
      NativeModelDetector (s + 1 + 1) N p₁
        (shiftTestingSeminorm (fun n => (weight n : ℂ)) B.testingFamily) K M beta₁ (eta / 4) →
      (∀ f ∈ nativeCyclicFunctions (s + 1 + 1) N p₁,
        NativeModelDetector (s + 1 + 1) N p₂
          (shiftTestingSeminorm f (translatedTestFamily B.testingFamily))
          1 K beta₂ (eta * beta₁ / 8)) →
      Odd N → Real.exp ((p + C) ^ C) ≤ N →
      (∀ n, 0 ≤ f₁ n ∧ f₁ n ≤ Real.exp p) →
      (∀ n, 0 ≤ f₂ n ∧ f₂ n ≤ Real.exp p) →
      (∀ n, 0 ≤ weight n ∧ weight n ≤ Real.exp p) →
      CyclicNiltestUpperComparison.{0} (s + 2) N ((p + C) ^ C)
        (Real.exp (-((p + C) ^ C))) f₁ f₂ → False

end Erdos3.PositiveShiftBasis

end

end OAI
