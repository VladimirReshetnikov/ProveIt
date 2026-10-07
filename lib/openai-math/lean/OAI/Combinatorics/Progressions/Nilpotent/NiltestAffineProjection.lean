import OAI.Combinatorics.Progressions.Estimates.PositiveCyclicCorrelation
import OAI.Combinatorics.Progressions.Geometry.NestedBoxReindex
import OAI.Combinatorics.Progressions.Geometry.SymbolFactorizationTransport
import OAI.Combinatorics.Progressions.Nilpotent.NiltestProbabilityProjection
import OAI.Combinatorics.Progressions.Polynomial.PolynomialSymbolBounds

namespace OAI

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ τ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ} {v : τ → ℕ}

noncomputable def substitute (T : D.Niltest w) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) : D.Niltest v :=
  { T with orbit := D.filtration.realification.polynomialOrbitSubstitute f hf T.orbit }

theorem eval_substitute (T : D.Niltest w) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) (x : τ → ℤ) (y : σ → ℤ)
    (hxy : ∀ i, MvPolynomial.aeval (R := ℚ) (fun j => (x j : ℚ)) (f i) = (y i : ℚ)) :
    (T.substitute f hf).eval x = T.eval y := by
  exact congrArg (fun z : D.RealGroup => T.observable (QuotientGroup.mk z))
    (D.filtration.realification.polynomialOrbitSubstitute_eval f hf T.orbit x y hxy)

@[simp] theorem substitute_complexityLE (T : D.Niltest w) (f : σ → MvPolynomial τ ℚ)
    (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) (p : ℝ) :
    (T.substitute f hf).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

noncomputable def affinePullback [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (A : σ → τ → ℤ) (b : σ → ℤ) : D.Niltest (fun _ : τ => 1) :=
  T.substitute (integerAffinePolynomial A b) (integerAffinePolynomial_support A b)

theorem eval_affinePullback [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (A : σ → τ → ℤ) (b : σ → ℤ) (x : τ → ℤ) :
    (T.affinePullback A b).eval x = T.eval (integerAffineMap A b x) :=
  T.eval_substitute (integerAffinePolynomial A b) (integerAffinePolynomial_support A b)
    x (integerAffineMap A b x) (integerAffinePolynomial_eval A b x)

@[simp] theorem affinePullback_complexityLE [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (A : σ → τ → ℤ) (b : σ → ℤ) (p : ℝ) :
    (T.affinePullback A b).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

noncomputable def linearPullbackHom [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (f : σ → ((τ → ℤ) →+ ℤ)) : D.Niltest (fun _ : τ => 1) := by
  classical
  exact T.affinePullback (fun i j => f i (Pi.single j 1)) 0

theorem eval_linearPullbackHom [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (f : σ → ((τ → ℤ) →+ ℤ)) (x : τ → ℤ) :
    (T.linearPullbackHom f).eval x = T.eval (fun i => f i x) := by
  classical
  change (T.affinePullback (fun i j => f i (Pi.single j 1)) 0).eval x = _
  rw [eval_affinePullback]
  congr 1
  funext i
  simpa only [integerAffineMap, Pi.zero_apply, zero_add] using (integerLinearForm_eq_sum (f i) x).symm

@[simp] theorem linearPullbackHom_complexityLE [Fintype τ] (T : D.Niltest (fun _ : σ => 1))
    (f : σ → ((τ → ℤ) →+ ℤ)) (p : ℝ) :
    (T.linearPullbackHom f).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def translate (T : D.Niltest w) (hw : ∀ i, 0 < w i) (h : σ → ℤ) : D.Niltest w :=
  { T with
    orbit := NilpotentLieFiltration.polynomialOrbitOfLog
      (VectorPolynomial.translate (fun i => (h i : ℚ)) T.orbit.log)
      (D.filtration.realification.adapted_translate w hw (fun i => (h i : ℚ)) T.orbit.adapted) }

@[simp] theorem eval_translate (T : D.Niltest w) (hw : ∀ i, 0 < w i) (h x : σ → ℤ) :
    (T.translate hw h).eval x = T.eval (x + h) := by
  apply congrArg T.observable
  apply congrArg QuotientGroup.mk
  apply NilpotentLieBCHGroup.ext
  change VectorPolynomial.eval (fun i => (x i : ℚ))
      (VectorPolynomial.translate (fun i => (h i : ℚ)) T.orbit.log) =
    VectorPolynomial.eval (fun i => ((x + h) i : ℚ)) T.orbit.log
  rw [VectorPolynomial.eval_translate]
  simp only [Pi.add_apply, Int.cast_add]

@[simp] theorem translate_complexityLE (T : D.Niltest w) (hw : ∀ i, 0 < w i)
    (h : σ → ℤ) (p : ℝ) : (T.translate hw h).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {I L : Type*} [Fintype I] [DecidableEq I] [LieRing L] [LieAlgebra ℚ L] {s dim : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s dim}

theorem exists_nested_box_restriction (T : D.Niltest (fun _ : I => 1))
    (c b : I → ℤ) {m d : ℕ} (hm : 0 < m) (hd : 0 < d)
    (H K : I → ℕ) (hK : ∀ i, 0 < K i)
    (hsub : commonStrideBox b d K ⊆ commonStrideBox c m H) :
    ∃ U : D.Niltest (fun _ : I => 1),
      (∀ p, U.ComplexityLE p ↔ T.ComplexityLE p) ∧
      ∀ x ∈ integerBox K, U.eval x = T.eval (commonStrideIndex c m (commonStridePoint b d x)) := by
  obtain ⟨A, a, hA⟩ := exists_nested_box_affine c b hm hd H K hK hsub
  refine ⟨T.affinePullback A a, fun p => affinePullback_complexityLE T A a p, ?_⟩
  intro x hx
  rw [eval_affinePullback, (hA x hx).2, commonStrideIndex_point c hm]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open scoped TensorProduct

variable {K K' L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

noncomputable def coordinateEquiv (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K') :
    D.Niltest (fun _ : K' => 1) :=
  T.substitute (fun i => MvPolynomial.X (e i))
    (fun i => weightedSupportLE_X (fun _ : K' => 1) (e i))

@[simp] theorem eval_coordinateEquiv (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K')
    (x : K' → ℤ) :
    (T.coordinateEquiv e).eval x = T.eval (fun i => x (e i)) := by
  exact T.eval_substitute (fun i => MvPolynomial.X (e i))
    (fun i => weightedSupportLE_X (fun _ : K' => 1) (e i))
    x (fun i => x (e i)) (fun _ => by simp)

@[simp] theorem eval_coordinateEquiv_symm (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K')
    (x : K → ℤ) :
    (T.coordinateEquiv e).eval (fun j => x (e.symm j)) = T.eval x := by
  simp only [eval_coordinateEquiv, Equiv.symm_apply_apply]

@[simp] theorem coordinateEquiv_observable (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K') :
    (T.coordinateEquiv e).observable = T.observable := rfl

@[simp] theorem coordinateEquiv_normBound (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K') :
    (T.coordinateEquiv e).normBound = T.normBound := rfl

@[simp] theorem coordinateEquiv_lipBound (T : D.Niltest (fun _ : K => 1)) (e : K ≃ K') :
    (T.coordinateEquiv e).lipBound = T.lipBound := rfl

@[simp] theorem coordinateEquiv_complexityLE (T : D.Niltest (fun _ : K => 1))
    (e : K ≃ K') (p : ℝ) :
    (T.coordinateEquiv e).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

open scoped TensorProduct BigOperators

namespace Erdos3

theorem exists_correlating_niltest_product_piece {ι : Type*} [Fintype ι]
    {L : ι → Type*} [∀ i, LieRing (L i)] [∀ i, LieAlgebra ℚ (L i)]
    {s : ℕ} {d : ι → ℕ}
    [∀ i, TopologicalSpace (ℝ ⊗[ℚ] L i)] [∀ i, IsTopologicalAddGroup (ℝ ⊗[ℚ] L i)]
    [∀ i, ContinuousSMul ℝ (ℝ ⊗[ℚ] L i)] [∀ i, T2Space (ℝ ⊗[ℚ] L i)]
    (D : ∀ i, RationalFilteredNilmanifold (L i) s (d i))
    (w : Fin 1 → ℕ) (hw : ∀ j, 0 < w j) (T : ∀ i, (D i).Niltest w)
    {p : ℝ} (hT : ∀ i, (T i).ComplexityLE p) {N : ℕ} [NeZero N]
    (h : ι → ZMod N) (f : ZMod N → ℂ) (hf : ∀ x, ‖f x‖ ≤ 1)
    (hc : Real.exp (-p) ≤ ‖finiteCorrelation Finset.univ f
      (translatedCyclicProduct h (fun i n => (T i).eval (fun _ => n)))‖) :
    ∃ a : commonCyclicCuts h,
      let len := intervalCutUpper (commonCyclicCuts h) N a - a
      let S := fun i => (T i).translate hw (fun _ => cyclicTranslationOffset (h i) a)
      0 < len ∧ a.val + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      (∀ i, (S i).ComplexityLE p) ∧
      Real.exp (-p) / (2 * ((Fintype.card ι : ℝ) + 8)) ≤
        ‖finiteCorrelation (Finset.Ico (a.val : ℤ) (a.val + len)) (fun x => f (x : ZMod N))
          (fun x => ∏ i, (S i).eval (fun _ => x))‖ ∧
      Real.exp (-p) / (2 * ((Fintype.card ι : ℝ) + 8) * Real.exp ((Fintype.card ι : ℝ) * p)) ≤
        (len : ℝ) / N := by
  have hu (x : ZMod N) :
      ‖translatedCyclicProduct h (fun i n => (T i).eval (fun _ => n)) x‖ ≤
        Real.exp ((Fintype.card ι : ℝ) * p) :=
    translatedCyclicProduct_norm_bound h _ (fun i n => (T i).eval_budget (hT i) _) x
  obtain ⟨a, hpos, hbound, hshort, hcorr, hvol⟩ := exists_correlating_integer_product_interval
    h (fun i n => (T i).eval (fun _ => n)) f (Real.exp_pos (-p))
      (Real.exp_pos ((Fintype.card ι : ℝ) * p)) hf hu hc
  refine ⟨a, hpos, hbound, hshort, ?_, ?_, hvol⟩
  · intro i
    exact hT i
  · have he (x : ℤ) :
        (∏ i, ((T i).translate hw (fun _ => cyclicTranslationOffset (h i) a)).eval (fun _ => x)) =
          ∏ i, (T i).eval (fun _ => x + cyclicTranslationOffset (h i) a) := by
      apply Finset.prod_congr rfl
      intro i _
      rw [RationalFilteredNilmanifold.Niltest.eval_translate]
      rfl
    simpa only [he] using hcorr

end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct BigOperators

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

noncomputable def symbol (T : D.Niltest w) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    D.filtration.RealPolynomialSymbolGroup w :=
  D.filtration.realPolynomialSymbolHom b ω hF w ⟨⟨T.orbit.log, T.orbit.property⟩⟩

theorem symbol_translate (T : D.Niltest w) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (hw : ∀ i, 0 < w i) (h : σ → ℤ) :
    (T.translate hw h).symbol b ω hF = T.symbol b ω hF := by
  apply D.filtration.realPolynomialSymbolHom_eq_of_quotient_eq b ω hF w
  apply NilpotentLieBCHGroup.ext
  exact D.filtration.realification.polynomialSymbolMap_translate w hw
    (fun i => (h i : ℚ)) ⟨T.orbit.log, T.orbit.property⟩

theorem mean_translate_box [Fintype σ] [DecidableEq σ]
    (T : D.Niltest w) (hw : ∀ i, 0 < w i) (a : σ → ℤ) (N : σ → ℕ) :
    (𝔼 x ∈ integerBox N, (T.translate hw a).eval x) =
      𝔼 x ∈ translatedIntegerBox a N, T.eval x := by
  rw [translatedIntegerBox, translateSupport,
    Finset.expect_image (add_right_injective a).injOn]
  apply Finset.expect_congr rfl
  intro x _
  rw [T.eval_translate, add_comm]

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

noncomputable def scalarAffinePolynomial {σ : Type*} (r : ℚ) (shift : σ → ℚ) (i : σ) :
    MvPolynomial σ ℚ := MvPolynomial.C (shift i) + MvPolynomial.C r * MvPolynomial.X i

theorem scalarAffinePolynomial_support {σ : Type*} (r : ℚ) (shift : σ → ℚ) (i : σ) :
    scalarAffinePolynomial r shift i ∈ weightedSupportLE (fun _ : σ => 1) 1 := by
  apply Submodule.add_mem
  · exact weightedSupportLE_C _ 1 (shift i)
  · simpa only [zero_add] using
      weightedSupportLE_mul (weightedSupportLE_C (fun _ : σ => 1) 0 r)
        (weightedSupportLE_X (fun _ : σ => 1) i)

namespace VectorPolynomial

theorem substitute_scalarAffinePolynomial {σ V : Type*} [AddCommGroup V] [Module ℚ V]
    (r : ℚ) (shift : σ → ℚ) (p : VectorPolynomial σ ℚ V) :
    substitute (scalarAffinePolynomial r shift) p =
      weightedDilation (fun _ => 1) r (translate shift p) := by
  apply sub_eq_zero.mp
  apply eq_zero_of_eval_zero
  intro x
  rw [map_sub, eval_substitute, eval_weightedDilation, eval_translate]
  simp [scalarAffinePolynomial, add_comm]

end VectorPolynomial

namespace RationalFilteredNilmanifold.Niltest

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d}

noncomputable def scalarAffinePullback (T : D.Niltest (fun _ : σ => 1))
    (r : ℚ) (shift : σ → ℚ) : D.Niltest (fun _ : σ => 1) :=
  T.substitute (scalarAffinePolynomial r shift) (scalarAffinePolynomial_support r shift)

@[simp] theorem scalarAffinePullback_complexityLE (T : D.Niltest (fun _ : σ => 1))
    (r : ℚ) (shift : σ → ℚ) (p : ℝ) :
    (T.scalarAffinePullback r shift).ComplexityLE p ↔ T.ComplexityLE p := Iff.rfl

theorem scalarAffinePullback_log (T : D.Niltest (fun _ : σ => 1)) (r : ℚ) (shift : σ → ℚ) :
    (T.scalarAffinePullback r shift).orbit.log =
      weightedDilation (fun _ => 1) r (VectorPolynomial.translate shift T.orbit.log) :=
  substitute_scalarAffinePolynomial r shift T.orbit.log

theorem scalarAffinePullback_eval_integer (T : D.Niltest (fun _ : σ => 1))
    (a : ℤ) (shift x : σ → ℤ) :
    (T.scalarAffinePullback a (fun i => (shift i : ℚ))).eval x =
      T.eval (fun i => a * x i + shift i) := by
  apply T.eval_substitute (scalarAffinePolynomial (a : ℚ) (fun i => (shift i : ℚ)))
    (scalarAffinePolynomial_support _ _) x (fun i => a * x i + shift i)
  intro i
  simp [scalarAffinePolynomial, add_comm]

theorem scalarAffinePullback_symbol (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (r : ℚ) (shift : σ → ℚ) :
    (T.scalarAffinePullback r shift).symbol b ω hF =
      D.filtration.realPolynomialSymbolDilationHom (fun _ => 1) r (T.symbol b ω hF) := by
  apply NilpotentLieBCHGroup.ext
  change D.filtration.realSymbolOfPolynomial b ω hF (fun _ => 1)
      (T.scalarAffinePullback r shift).orbit.log =
    D.filtration.realPolynomialSymbolDilation (fun _ => 1) r
      (D.filtration.realSymbolOfPolynomial b ω hF (fun _ => 1) T.orbit.log)
  rw [T.scalarAffinePullback_log]
  apply NilpotentLieFiltration.realSymbolOfPolynomial_affine
  · exact fun _ => Nat.zero_lt_one
  · exact T.orbit.adapted

theorem scalarAffinePullback_factorization (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {S H : σ → ℝ} {p q : ℝ} {M : ℕ} {U : LieSubalgebra ℚ D.filtration.AssociatedGraded}
    (h : D.filtration.SymbolFactorizationIn b ω hF S (T.symbol b ω hF) p M U)
    (a : ℤ) (m : ℕ) (ha : a ≠ 0) (hm : 0 < m) (shift : σ → ℚ)
    (hS : ∀ i, 0 < S i) (hH : ∀ i, 0 < H i) (hq : 0 ≤ q)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / m : ℚ) : ℝ)| * H i) ≤ S i) :
    D.filtration.SymbolFactorizationIn b ω hF H
      ((T.scalarAffinePullback ((a : ℚ) / m) shift).symbol b ω hF)
      (p + (s : ℝ) * q) (M * m ^ s) U := by
  rw [T.scalarAffinePullback_symbol]
  exact NilpotentLieFiltration.SymbolFactorizationIn.dilate_ratio D.filtration b ω hF
    h a m ha hm hS hH hq hphysical

end RationalFilteredNilmanifold.Niltest
end Erdos3

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

theorem scalarAffinePullback_symbol_inverse_stride
    (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (Q : ℕ) (hQ : 0 < Q) (shift : σ → ℚ) :
    D.filtration.realPolynomialSymbolDilationHom (fun _ : σ => 1) ((Q : ℚ)⁻¹)
      ((T.scalarAffinePullback Q shift).symbol b ω hF) = T.symbol b ω hF := by
  rw [T.scalarAffinePullback_symbol]
  apply NilpotentLieBCHGroup.ext
  simp only [NilpotentLieFiltration.realPolynomialSymbolDilationHom_coord,
    ← NilpotentLieFiltration.realPolynomialSymbolDilation_mul,
    inv_mul_cancel₀ (show (Q : ℚ) ≠ 0 by exact_mod_cast hQ.ne'),
    NilpotentLieFiltration.realPolynomialSymbolDilation_one]

theorem scalarAffineCell_factorization_to_original
    (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (Q : ℕ) (hQ : 0 < Q) (shift : σ → ℚ)
    {S H : σ → ℝ} {p q : ℝ} {denom : ℕ}
    {U : LieSubalgebra ℚ D.filtration.AssociatedGraded}
    (h : D.filtration.SymbolFactorizationIn b ω hF S
      ((T.scalarAffinePullback Q shift).symbol b ω hF) p denom U)
    (hS : ∀ i, 0 < S i) (hH : ∀ i, 0 < H i) (hq : 0 ≤ q)
    (hphysical : ∀ i, Real.exp (-q) * (H i / (Q : ℝ)) ≤ S i) :
    D.filtration.SymbolFactorizationIn b ω hF H (T.symbol b ω hF)
      (p + (s : ℝ) * q) (denom * Q ^ s) U := by
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hratio (i : σ) :
      Real.exp (-q) * (|(((1 : ℚ) / Q : ℚ) : ℝ)| * H i) ≤ S i := by
    convert hphysical i using 1
    push_cast
    rw [abs_div, abs_one, abs_of_pos hQreal]
    ring
  have htransport := NilpotentLieFiltration.SymbolFactorizationIn.dilate_ratio
    D.filtration b ω hF h 1 Q (by norm_num) hQ hS hH hq hratio
  rw [Int.cast_one, one_div,
    T.scalarAffinePullback_symbol_inverse_stride b ω hF Q hQ shift] at htransport
  exact htransport

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open CircleFourier
open scoped TensorProduct BigOperators

variable {σ τ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
    [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    {D : RationalFilteredNilmanifold L s d} {w : σ → ℕ}

theorem symbol_eq_of_orbit_eq (T U : D.Niltest w) (h : T.orbit = U.orbit)
    (b : Module.Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i})) :
    T.symbol b ω hF = U.symbol b ω hF := by
  unfold symbol
  apply congrArg (D.filtration.realPolynomialSymbolHom b ω hF w)
  apply NilpotentLieBCHGroup.ext
  apply Subtype.ext
  exact congrArg (fun o : D.filtration.realification.PolynomialOrbit w => o.log) h

theorem affinePullback_orbit_eq_of_orbit_eq [Fintype τ]
    (T U : D.Niltest (fun _ : σ => 1)) (h : T.orbit = U.orbit)
    (A : σ → τ → ℤ) (b : σ → ℤ) :
    (T.affinePullback A b).orbit = (U.affinePullback A b).orbit := by
  change D.filtration.realification.polynomialOrbitSubstitute _ _ T.orbit =
    D.filtration.realification.polynomialOrbitSubstitute _ _ U.orbit
  rw [h]

theorem exists_affine_finset_kernel_projection_family [Fintype τ]
    (T : D.Niltest (fun _ : σ => 1)) (hT : T.UnitIntervalValued)
    {p : ℝ} (hTc : T.ComplexityLE p) (K : Submodule ℚ L) (hK : K ≤ D.filtration.layer s)
    {J β : Type*} [Fintype J]
    (eta : J → L →ₗ[ℚ] ℚ) (U : J → D.Niltest (fun _ : σ => 1))
    (horbit : ∀ j, (U j).orbit = T.orbit)
    (hvertical : ∀ j (z : D.RealGroup), z ∈ D.filtration.realification.subgroup s → ∀ x,
      (U j).observable (z • x) =
        character ((realifyFunctional (eta j) z.coord : ℝ) : CircleFourier.Circle) * (U j).observable x)
    (A : β → σ → τ → ℤ) (b : β → σ → ℤ)
    (boxes : β → Finset (τ → ℤ)) (hboxes : ∀ a, (boxes a).Nonempty)
    (threshold : β → ℝ) {rho : ℝ} (hrho : 0 ≤ rho) (hthreshold : ∀ a, 0 ≤ threshold a)
    (happrox : ∀ x, ‖T.observable x - ∑ j, (U j).observable x‖ ≤ rho)
    (hkill : ∀ j, (∃ a, threshold a <
      ‖𝔼 x ∈ boxes a, ((U j).affinePullback (A a) (b a)).eval x‖) →
      ∀ v ∈ K, eta j v = 0) :
    ∃ S : D.Niltest (fun _ : σ => 1),
      S.UnitIntervalValued ∧ S.ComplexityLE p ∧ S.orbit = T.orbit ∧
      (∀ z : D.RealGroup, z.coord ∈ K.baseChange ℝ →
        ∀ x, S.observable (z • x) = S.observable x) ∧
      ∀ a, ‖(𝔼 x ∈ boxes a, (T.affinePullback (A a) (b a)).eval x) -
        (𝔼 x ∈ boxes a, (S.affinePullback (A a) (b a)).eval x)‖ ≤
          2 * rho + Fintype.card J * threshold a := by
  let law (a : β) := FiniteProbabilityWeights.uniformFinset (boxes a) (hboxes a)
  let path (a : β) (x : ↥(boxes a)) := integerAffineMap (A a) (b a) x.val
  have hmean (a : β) (F : D.Niltest (fun _ : σ => 1)) :
      (law a).complexMean (fun x => F.eval (path a x)) =
        𝔼 x ∈ boxes a, (F.affinePullback (A a) (b a)).eval x := by
    simpa only [law, path, eval_affinePullback] using
      FiniteProbabilityWeights.uniformFinset_complexMean (boxes a) (hboxes a)
        (fun x => F.eval (integerAffineMap (A a) (b a) x))
  have hkill' : ∀ j, (∃ a, threshold a <
      ‖(law a).complexMean (fun x => (U j).eval (path a x))‖) →
      ∀ v ∈ K, eta j v = 0 := by
    intro j ⟨a, ha⟩ v hv
    apply hkill j ⟨a, ?_⟩ v hv
    simpa only [hmean] using ha
  obtain ⟨S, hS, hSc, hSo, hinv, herr⟩ :=
    T.exists_probability_kernel_projection_family hT hTc K hK eta U horbit hvertical
      law path threshold hrho hthreshold happrox hkill'
  exact ⟨S, hS, hSc, hSo, hinv, fun a => by simpa only [hmean] using herr a⟩

end Erdos3.RationalFilteredNilmanifold.Niltest

end

end OAI
