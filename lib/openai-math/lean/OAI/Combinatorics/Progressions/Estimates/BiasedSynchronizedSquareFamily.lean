import OAI.Combinatorics.Progressions.Dynamics.CompatibleReducedFastReset
import OAI.Combinatorics.Progressions.Estimates.CommonFixedNativeSquareFamily
import OAI.Combinatorics.Progressions.Fourier.SquareModeGradedFrequency
import OAI.Combinatorics.Progressions.Geometry.SquareQuotientHeightTransport

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {α σ ι L : Type*} [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ) (hw : ∀ i, 0 < w i)

include hw in
theorem exists_common_real_reduced_fast_relative
    (e : Basis ι ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (S : Finset α) (hS : S.Nonempty)
    (K : α → LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : α → F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : ∀ a ∈ S, (g a).coord ∈ realificationLieSubalgebra (K a))
    (x : F.quotientTop.RealPolynomialSymbolGroup w)
    (hdiag : ∀ a ∈ S, F.reducedSquareRealSymbolHom w (g a) = x)
    (m : ℕ) {p : ℝ} (hp : 0 ≤ p) (hm : (m : ℝ) ≤ p) (hd : (Fintype.card ι : ℝ) ≤ p)
    (hK : ∀ a ∈ S, ∃ v : Fin m → F.squareFiltration.quotientTop.PolynomialSymbol w,
      Submodule.span ℚ (Set.range v) = (K a).toSubmodule ∧
        ∀ i j, rationalLogHeight (e.repr (v i) j) ≤ p) :
    ∃ a₀ ∈ S, ∃ T : Finset α, T ⊆ S ∧ a₀ ∈ T ∧ (∀ a ∈ T, K a = K a₀) ∧
      (∀ a ∈ T, (F.reducedSquareRealRelativePart w (g a)).coord -
        (F.reducedSquareRealRelativePart w (g a₀)).coord ∈
          (F.reducedSquareFastRelativeSubmodule w (K a₀)).baseChange ℝ) ∧
      Real.exp (-((p + 2) ^ 5)) * S.card ≤ (T.card : ℝ) := by
  have hcommonExists := exists_common_fast_subalgebra e S hS K m hp hm hd hK
  obtain ⟨a₀, ha₀, T, hTS, haT, hcommon, hlarge⟩ := hcommonExists
  refine ⟨a₀, ha₀, T, hTS, haT, hcommon, ?_, hlarge⟩
  intro a ha
  have hga : (g a).coord ∈ realificationLieSubalgebra (K a₀) := by
    rw [← hcommon a ha]
    exact hg a (hTS ha)
  exact F.reducedSquareRealRelative_same_diagonal_mod_kernel w hw (K a₀)
    hga (hg a₀ ha₀) ((hdiag a (hTS ha)).trans (hdiag a₀ ha₀).symm)

include hw in
theorem synchronized_real_reduced_fast_relative
    (W : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (E P R c d Z : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (A D : F.quotientTop.RealPolynomialSymbolGroup w)
    (hP : P.coord ∈ realificationLieSubalgebra W)
    (hc : c.coord ∈ realificationLieSubalgebra W)
    (hd : d.coord ∈ realificationLieSubalgebra W)
    (hZ : Z.coord ∈ realificationLieSubalgebra W)
    (hcq : F.reducedSquareRealSymbolHom w c = A⁻¹ * F.reducedSquareRealSymbolHom w E)
    (hdq : F.reducedSquareRealSymbolHom w d = F.reducedSquareRealSymbolHom w R * D⁻¹)
    (hZq : F.reducedSquareRealSymbolHom w Z =
      A⁻¹ * F.reducedSquareRealSymbolHom w (E * P * R) * D⁻¹) :
    (F.reducedSquareRealRelativePart w (c * P * d)).coord -
      (F.reducedSquareRealRelativePart w Z).coord ∈
        (F.reducedSquareFastRelativeSubmodule w W).baseChange ℝ := by
  have hreset := synchronize_splitting_projection (F.reducedSquareRealSymbolHom w)
    (NilpotentLieBCHGroup.realificationSubgroup
      (hnil := F.squareFiltration.quotientTop.polynomialSymbol_lowerCentralSeries_eq_bot w) W)
    E P R c d A D hP hc hd hcq hdq
  exact F.reducedSquareRealRelative_same_diagonal_mod_kernel w hw W hreset.2.1 hZ
    (hreset.2.2.2.2.trans hZq.symm)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

def ReducedSquareRelativeCongruent {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (P Q : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w) : Prop :=
  (F.reducedSquareRealRelativePart w P).coord - (F.reducedSquareRealRelativePart w Q).coord ∈
    (F.reducedSquareFastRelativeSubmodule w U).baseChange ℝ

theorem symbolFastIn_reducedSquareRealSymbolHom {σ L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L (s + 1)) (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (g : F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
    (hg : F.squareFiltration.quotientTop.SymbolFastIn w U g) :
    F.quotientTop.SymbolFastIn w (U.map (F.reducedSquareSndSymbolMap w))
      (F.reducedSquareRealSymbolHom w g) := F.reducedSquareRealSymbolHom_fast w U g hg

def SynchronizedReducedSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (_hw : ∀ i, 0 < w i)
    (U : LieSubalgebra ℚ (F.squareFiltration.quotientTop.PolynomialSymbol w))
    (v : κ → F.squareFiltration.quotientTop.PolynomialSymbol w)
    (_hv : Submodule.span ℚ (Set.range v) = U.toSubmodule)
    (_hU : BasisBlockInvariant (F.reducedSquareSymbolBasis b ω hF w) (fun z => z.val.1) U.toSubmodule)
    (H l : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hh : ∀ i j, RationalHeightLE ((F.reducedSquareSymbolBasis b ω hF w).repr (v i) j) H),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ {α : Type*} (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
        (S : Finset α) (a₀ : α) (_ha₀ : a₀ ∈ S)
        (E P R : α → F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
        (_hP : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolFastIn w U (P a))
        (_hE : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w T (Real.exp p) (E a))
        (_hR : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w l (R a))
        (_hprojection : ∀ a ∈ S, F.reducedSquareRealSymbolHom w (E a * P a * R a) =
          F.reducedSquareRealSymbolHom w (E a₀ * P a₀ * R a₀)),
        ∃ E' P' R' : α → F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w,
          (∀ a ∈ S, E' a * P' a * R' a = E a * P a * R a ∧
            F.squareFiltration.quotientTop.SymbolFastIn w U (P' a) ∧
            F.reducedSquareRealSymbolHom w (E' a) = F.reducedSquareRealSymbolHom w (E a₀) ∧
            F.reducedSquareRealSymbolHom w (R' a) = F.reducedSquareRealSymbolHom w (R a₀) ∧
            F.reducedSquareRealSymbolHom w (P' a) = F.reducedSquareRealSymbolHom w (P a₀) ∧
            F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
              (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
              w T (Real.exp ((p + C) ^ C)) (E' a) ∧
            F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
              (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w m (R' a)) ∧
          ∀ a ∈ S, F.ReducedSquareRelativeCongruent w U (P' a) (P' a₀)

theorem exists_synchronized_reduced_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedReducedSquareFamilySpec s C := by
  obtain ⟨C, hC, hreset⟩ := exists_compatible_reduced_fast_reset s 1
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw U v hv hU H l p hH hl hp hι hσ hκ hHp hlp hc hh
  obtain ⟨sectionMap, m, hm, hmp, hlm, hsync⟩ :=
    hreset F b ω hF w hw U v hv hU H l p hH hl hp hι hσ hκ hHp hlp hc hh
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro α T hT S a₀ ha₀ E P R hP hE hR hprojection
  let π := F.reducedSquareRealSymbolHom w
  let A := π (E a₀)
  let B := π (P a₀)
  let D := π (R a₀)
  let c := fun a => F.reducedSquareRealLinearLift w sectionMap (A⁻¹ * π (E a))
  let d := fun a => F.reducedSquareRealLinearLift w sectionMap (π (R a) * D⁻¹)
  let E' := fun a => E a * (c a)⁻¹
  let P' := fun a => c a * P a * d a
  let R' := fun a => (d a)⁻¹ * R a
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hEin : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w T
      (Real.exp ((p + 2) ^ 1)) (E a) := by
    intro a ha
    exact F.squareFiltration.quotientTop.symbolSlowBound_mono (F.reducedSquareBasis b ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w T hTpos
      (Real.exp_le_exp.mpr (by norm_num)) (E a) (hE a ha)
  have hA := F.reducedSquareRealSymbolHom_slow b ω hF w T (Real.exp ((p + 2) ^ 1)) (E a₀) (hEin a₀ ha₀)
  have hD := F.reducedSquareRealSymbolHom_grid b ω hF w l (R a₀) (hR a₀ ha₀)
  have hB := F.reducedSquareRealSymbolHom_fast w U (P a₀) (hP a₀ ha₀)
  have hresult : ∀ a ∈ S, E' a * P' a * R' a = E a * P a * R a ∧
      F.squareFiltration.quotientTop.SymbolFastIn w U (P' a) ∧
      π (E' a) = A ∧ π (R' a) = D ∧ π (P' a) = B ∧
      F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
        w T (Real.exp ((p + C) ^ C)) (E' a) ∧
      F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w m (R' a) := by
    intro a ha
    have heq : A * B * D = π (E a * P a * R a) := by
      simpa only [A, B, D, π, map_mul] using (hprojection a ha).symm
    exact hsync T hT (E a) (P a) (R a) A B D (hP a ha) hB heq
      (hEin a ha) (hR a ha) hA hD
  refine ⟨E', P', R', hresult, ?_⟩
  intro a ha
  exact F.reducedSquareRealRelative_same_diagonal_mod_kernel w hw U
    (hresult a ha).2.1 (hresult a₀ ha₀).2.1
    ((hresult a ha).2.2.2.2.1.trans (hresult a₀ ha₀).2.2.2.2.1.symm)

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module
open scoped TensorProduct

def PointwiseSynchronizedSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L (s + 1)) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (_hw : ∀ i, 0 < w i)
    (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hW : BasisGradedSubmodule
      (F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF))
      (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (H l : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hp : 0 ≤ p)
    (_hι : 2 * (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hh : ∀ i j, RationalHeightLE
      ((F.squareFiltration.quotientTop.associatedGradedBasis (F.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)).repr (v i) j) H),
    let U := F.squareFiltration.quotientTop.symbolPointwiseSubalgebra (F.reducedSquareBasis b ω hF)
      (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w W
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ {α : Type*} (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
        (S : Finset α) (a₀ : α) (_ha₀ : a₀ ∈ S)
        (E P R : α → F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w)
        (_hP : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolFastIn w U (P a))
        (_hE : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w T (Real.exp p) (E a))
        (_hR : ∀ a ∈ S, F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
          (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w l (R a))
        (_hprojection : ∀ a ∈ S, F.reducedSquareRealSymbolHom w (E a * P a * R a) =
          F.reducedSquareRealSymbolHom w (E a₀ * P a₀ * R a₀)),
        ∃ E' P' R' : α → F.squareFiltration.quotientTop.RealPolynomialSymbolGroup w,
          (∀ a ∈ S, E' a * P' a * R' a = E a * P a * R a ∧
            F.squareFiltration.quotientTop.SymbolFastIn w U (P' a) ∧
            F.reducedSquareRealSymbolHom w (E' a) = F.reducedSquareRealSymbolHom w (E a₀) ∧
            F.reducedSquareRealSymbolHom w (R' a) = F.reducedSquareRealSymbolHom w (R a₀) ∧
            F.reducedSquareRealSymbolHom w (P' a) = F.reducedSquareRealSymbolHom w (P a₀) ∧
            F.squareFiltration.quotientTop.SymbolSlowBound (F.reducedSquareBasis b ω hF)
              (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF)
              w T (Real.exp ((p + C) ^ C)) (E' a) ∧
            F.squareFiltration.quotientTop.SymbolRationalGrid (F.reducedSquareBasis b ω hF)
              (fun i => squareBasisWeight ω i.val) (F.reducedSquareBasis_layers b ω hF) w m (R' a)) ∧
          ∀ a ∈ S, F.ReducedSquareRelativeCongruent w U (P' a) (P' a₀)

theorem exists_pointwise_synchronized_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ PointwiseSynchronizedSquareFamilySpec s C := by
  obtain ⟨a, _, hfamily⟩ := exists_synchronized_reduced_square_family s
  let Q : Polynomial ℕ := (Polynomial.X + Polynomial.C (s + 3)) ^ (s + 3)
  let B : Polynomial ℕ := (Q + Polynomial.C a) ^ a
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget B
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ F b ω hF w hw W v hv hW H l p hH hl hp hι hσ hκ hHp hlp hc hh
  let bq := F.reducedSquareBasis b ω hF
  let ωq := fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω i.val
  let hq := F.reducedSquareBasis_layers b ω hF
  let U := F.squareFiltration.quotientTop.symbolPointwiseSubalgebra bq ωq hq w W
  let v' := F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily bq ωq hq w v
  let : Fintype (ReducedSquareSymbolIndex s w ω) :=
    symbolBasisIndexFintype w ωq s hw
      (F.squareFiltration.quotientTop.adaptedBasis_weight_le_step bq ωq hq)
  let q : ℝ := (p + (s + 3)) ^ (s + 3)
  have hqpos : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := symbol_spanning_parameter_ge s hp
  have hιp : (Fintype.card ι : ℝ) ≤ p := by
    have hi := Nat.cast_nonneg (α := ℝ) (Fintype.card ι)
    linarith
  have hdim : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ p := by
    have hnat : Fintype.card (ReducedSquareBasisIndex s ω) ≤ 2 * Fintype.card ι :=
      (Fintype.card_subtype_le _).trans (card_squareBasis_index_le ω)
    have hreal : (Fintype.card (ReducedSquareBasisIndex s ω) : ℝ) ≤ 2 * (Fintype.card ι : ℝ) := by
      exact_mod_cast hnat
    exact hreal.trans hι
  have hcount : (Fintype.card (ReducedSquareSymbolIndex s w ω × κ) : ℝ) ≤ q := by
    have hnat : Fintype.card (ReducedSquareSymbolIndex s w ω × κ) ≤
        Fintype.card (ReducedSquareBasisIndex s ω) * (s + 1) * (Fintype.card σ + 1) ^ s *
          Fintype.card κ := by
      rw [Fintype.card_prod]
      exact Nat.mul_le_mul_right _ (symbolBasisIndex_card_le w ωq s hw
        (F.squareFiltration.quotientTop.adaptedBasis_weight_le_step bq ωq hq))
    exact (Nat.cast_le.mpr hnat).trans (symbol_spanning_count_bound s _ _ _ hp hdim hσ hκ)
  have hbound : (q + a) ^ a ≤ (p + C) ^ C := by
    simpa [B, Q, q, Polynomial.eval₂_pow] using hfinal p hp
  obtain ⟨m, hm, hmp, hlm, hsync⟩ := hfamily F b ω hF w hw U v'
    (F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily_span bq ωq hq w W hW v hv)
    (F.squareFiltration.quotientTop.symbolPointwiseSubalgebra_blockInvariant bq ωq hq w W)
    H l q hH hl hqpos (hιp.trans hpq) (hσ.trans hpq) hcount
    (hHp.trans (Real.exp_le_exp.mpr hpq)) (hlp.trans (Real.exp_le_exp.mpr hpq)) hc
    (F.squareFiltration.quotientTop.pointwiseSymbolSpanningFamily_height bq ωq hq w v hH hh)
  refine ⟨m, hm, hmp.trans (Real.exp_le_exp.mpr hbound), hlm, ?_⟩
  intro α T hT S a₀ ha₀ E P R hP hE hR hprojection
  have hTpos : ∀ i, 0 < T i := fun i => (Real.exp_pos _).trans_le (hT i)
  have hEin : ∀ x ∈ S, F.squareFiltration.quotientTop.SymbolSlowBound bq ωq hq w T
      (Real.exp q) (E x) := fun x hx =>
    F.squareFiltration.quotientTop.symbolSlowBound_mono bq ωq hq w T hTpos
      (Real.exp_le_exp.mpr hpq) (E x) (hE x hx)
  have hchosen := hsync T
    (fun i => (Real.exp_le_exp.mpr hbound).trans (hT i)) S a₀ ha₀ E P R
  obtain ⟨E', P', R', hgood, hrelative⟩ := hchosen hP hEin hR hprojection
  refine ⟨E', P', R', ?_, hrelative⟩
  intro x hx
  obtain ⟨heq, hfast, hleft, hright, hmiddle, hslow, hrat⟩ := hgood x hx
  exact ⟨heq, hfast, hleft, hright, hmiddle,
    F.squareFiltration.quotientTop.symbolSlowBound_mono bq ωq hq w T hTpos
      (Real.exp_le_exp.mpr hbound) (E' x) hslow, hrat⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
  (N : ℕ) (hN : 0 < N)
  (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
    (D.filtration.squareFinBasis b ω (hF 2)) (D.filtration.squareLattice D.lattice))
  (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b ω (hF 2))
    (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)

local notation "Q" => D.filtration.squareFiltration.topQuotientModel
  (D.filtration.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
  (D.filtration.squareFinBasis_layers b ω hF) (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "hQ" => D.filtration.squareFiltration.topQuotientModel_basis_layers
  (D.filtration.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
  (D.filtration.squareFinBasis_layers b ω hF) (D.filtration.squareLattice D.lattice) N hN hin hout
local notation "bq" => D.filtration.reducedSquareBasis b ω hF
local notation "ωq" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "hq" => D.filtration.reducedSquareBasis_layers b ω hF

theorem HasFixedNativeSquareFactors.canonical_factors {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)} {η : L →ₗ[ℚ] ℚ}
    {T : σ → ℝ} {h : σ → ℤ} {p : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded}
    (hdata : D.HasFixedNativeSquareFactors (D.filtration.squareFinBasis b ω (hF 2))
      (squareFinWeight ω) (D.filtration.squareFinBasis_layers b ω hF)
      N hN hin hout hs g η T h p l W) :
    ∃ ε γ : D.RealGroup, γ ∈ D.realLattice ∧
      (∀ i, |(D.basis.baseChange ℝ).repr ε.coord i| ≤ Real.exp p) ∧
      ∃ r : D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1),
        D.filtration.realAdaptedPolynomialMap (fun _ => 1)
            (D.filtration.realSquareFstPolynomialHom (fun _ => 1) r).coord =
          normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-ε.coord) (-γ.coord)
            (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
        D.filtration.realSquareSndPolynomialHom (fun _ => 1) r = g ∧
        D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
            D.filtration.realFirstCoefficientConstant (fun _ => 1) ε.coord -
            D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
              (D.filtration.realFirstCoefficientConstant (fun _ => 1) γ.coord) =
          D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
            (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) ∧
        D.filtration.squareFiltration.quotientTop.SymbolFactorizationIn bq ωq hq T
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) r) p l W := by
  obtain ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ξ, _, _, _, hfixed⟩ := hdata
  refine ⟨ε, γ, hγ, hε, r, hf, hsecond, hderivative, ?_⟩
  exact (D.filtration.squareTopQuotientModel_factorization_iff b ω hF
    (D.filtration.squareLattice D.lattice) N hN hin hout T _ p l W).mp hfixed

theorem HasFixedNativeSquareFactors.fullFast_top_frequency {hs : 1 ≤ s}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)} {η : L →ₗ[ℚ] ℚ}
    {T : σ → ℝ} {h : σ → ℤ} {p : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded}
    (hdata : D.HasFixedNativeSquareFactors (D.filtration.squareFinBasis b ω (hF 2))
      (squareFinWeight ω) (D.filtration.squareFinBasis_layers b ω hF)
      N hN hin hout hs g η T h p l W)
    (hW : BasisGradedSubmodule ((Q).filtration.associatedGradedBasis (Q).basis
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) hQ)
        (quotientFinWeight (squareFinWeight ω) {i | s + 1 ≤ squareFinWeight ω i}) W.toSubmodule) :
    ∀ x ∈ D.filtration.fullFastGradedRelative b ω hF W,
      basisGradeProjection (D.filtration.associatedGradedBasis b ω hF) ω (s + 1) x = x →
        D.filtration.gradedFrequency b ω hF η x = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, ξ, _, hrestriction, hξ, _⟩ := hdata
  exact D.filtration.square_mode_fullFast_top_frequency b ω hF hs η ξ hrestriction W
    ((D.filtration.squareTopQuotientModel_graded_iff b ω hF
      (D.filtration.squareLattice D.lattice) N hN hin hout W.toSubmodule).mp hW)
    ((D.filtration.squareTopQuotientModel_top_annihilation_iff b ω hF
      (D.filtration.squareLattice D.lattice) N hN hin hout ξ W).mp hξ)

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.RationalFilteredNilmanifold

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  (D : RationalFilteredNilmanifold L (s + 1) d) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

def SynchronizedNativeSquareData (T : σ → ℝ)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (S : Finset (σ → ℤ)) (h₀ : σ → ℤ)
    (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (p q : ℝ) (l m : ℕ) : Prop :=
  let U := D.filtration.fastPointwiseSquare b ω hF (fun _ : σ => 1) W
  ∃ (ε γ : (σ → ℤ) → D.RealGroup)
    (r : (σ → ℤ) → D.filtration.squareFiltration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (E P R : (σ → ℤ) → D.filtration.squareFiltration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (A B D₀ : D.filtration.quotientTop.RealPolynomialSymbolGroup (fun _ : σ => 1)),
    A * B * D₀ = D.filtration.adaptedReducedRealSymbolHom (fun _ => 1) g ∧
    D.filtration.quotientTop.SymbolSlowBound (D.filtration.quotientTopBasis b ω hF)
      (fun i => ω i.val) (D.filtration.quotientTopBasis_layers b ω hF)
      (fun _ => 1) T (Real.exp p) A ∧
    D.filtration.quotientTop.SymbolRationalGrid (D.filtration.quotientTopBasis b ω hF)
      (fun i => ω i.val) (D.filtration.quotientTopBasis_layers b ω hF) (fun _ => 1) l D₀ ∧
    D.filtration.quotientTop.SymbolFastIn (fun _ => 1)
      (U.map (D.filtration.reducedSquareSndSymbolMap (fun _ => 1))) B ∧
    (∀ h ∈ S, γ h ∈ D.realLattice ∧
      (∀ i, |(D.basis.baseChange ℝ).repr (ε h).coord i| ≤ Real.exp p) ∧
      D.filtration.realAdaptedPolynomialMap (fun _ => 1)
          (D.filtration.realSquareFstPolynomialHom (fun _ => 1) (r h)).coord =
        normalizedShiftLog (s + 1) (fun i => (h i : ℚ)) (-(ε h).coord) (-(γ h).coord)
          (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) ∧
      D.filtration.realSquareSndPolynomialHom (fun _ => 1) (r h) = g ∧
      D.filtration.realFirstCoefficientDirectionMap g.coord (fun i => (h i : ℝ)) -
          D.filtration.realFirstCoefficientConstant (fun _ => 1) (ε h).coord -
          D.filtration.realFirstCoefficientAdjoint (fun _ => 1) g
            (D.filtration.realFirstCoefficientConstant (fun _ => 1) (γ h).coord) =
        D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one)
          (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) (r h)) ∧
      E h * P h * R h = D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) (r h) ∧
      D.filtration.squareFiltration.quotientTop.SymbolFastIn (fun _ => 1) U (P h) ∧
      D.filtration.reducedSquareRealSymbolHom (fun _ => 1) (E h) = A ∧
      D.filtration.reducedSquareRealSymbolHom (fun _ => 1) (R h) = D₀ ∧
      D.filtration.reducedSquareRealSymbolHom (fun _ => 1) (P h) = B ∧
      D.filtration.squareFiltration.quotientTop.SymbolSlowBound
        (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) T (Real.exp q) (E h) ∧
      D.filtration.squareFiltration.quotientTop.SymbolRationalGrid
        (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) m (R h)) ∧
    ∀ h ∈ S, D.filtration.ReducedSquareRelativeCongruent (fun _ => 1) U (P h) (P h₀)

omit [Fintype ι] in
theorem SynchronizedNativeSquareData.mono {T : σ → ℝ}
    {g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)}
    {S : Finset (σ → ℤ)} {h₀ : σ → ℤ}
    {W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded}
    {p q p' q' : ℝ} {l m : ℕ}
    (hdata : D.SynchronizedNativeSquareData b ω hF T g S h₀ W p q l m)
    (hp : p ≤ p') (hq : q ≤ q') (hT : ∀ i, 0 < T i) :
    D.SynchronizedNativeSquareData b ω hF T g S h₀ W p' q' l m := by
  obtain ⟨ε, γ, r, E, P, R, A, B, D₀, hprod, hA, hD, hB, hgood, hrelative⟩ := hdata
  refine ⟨ε, γ, r, E, P, R, A, B, D₀, hprod, ?_, hD, hB, ?_, hrelative⟩
  · exact D.filtration.quotientTop.symbolSlowBound_mono
      (D.filtration.quotientTopBasis b ω hF) (fun i => ω i.val)
      (D.filtration.quotientTopBasis_layers b ω hF) (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hp) A hA
  · intro h hh
    obtain ⟨hγ, hε, hf, hs, hderivative, hfactor, hfast, hleft, hright, hmiddle, hslow, hrat⟩ := hgood h hh
    refine ⟨hγ, (fun i => (hε i).trans (Real.exp_le_exp.mpr hp)), hf, hs, hderivative,
      hfactor, hfast, hleft, hright, hmiddle, ?_, hrat⟩
    exact D.filtration.squareFiltration.quotientTop.symbolSlowBound_mono
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hq) (E h) hslow

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

def SynchronizedNativeCommonCoefficientSpec (s C : ℕ) : Prop :=
  ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H l m : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hm : 0 < m) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p) (_hd : (d : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p) (_hmp : (m : ℝ) ≤ Real.exp p)
    (_hgrid : (D.grid : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hb : ∀ i j, RationalHeightLE (b.repr (D.basis j) i) H)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i)
    (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
    (S : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ S)
    (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (_hbox : ∀ h ∈ S, ∀ i, |(h i : ℝ)| ≤ T i)
    (_hdata : D.SynchronizedNativeSquareData b ω hF T g S h₀ W p p l m),
    let q := (p + 2) ^ 3 + 3 * p + 1
    let U := D.filtration.fastPointwiseSquare b ω hF (fun _ : σ => 1) W
    ∃ n : ℕ, 0 < n ∧ (n : ℝ) ≤ Real.exp ((q + C) ^ C) ∧ l ∣ n ∧ m ∣ n ∧
      ∃ (A B R : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (small rational : (σ → ℤ) → D.filtration.RealFirstCoefficientModule (fun _ : σ => 1))
        (Z : D.filtration.RealFirstCoefficientModule (fun _ : σ => 1)),
        A * B * R = g ∧ B ∈ D.filtration.realFastDiagonalSubgroup (fun _ => 1) U ∧
        D.filtration.RealAdaptedCoefficientBound b ω hF (fun _ => 1) T (Real.exp p) A.coord ∧
        D.filtration.RealAdaptedCoefficientGrid b ω hF (fun _ => 1) l R.coord ∧
        coefficients (D.filtration.realAdaptedPolynomialMap (fun _ => 1) A.coord) 0 = 0 ∧
        coefficients (D.filtration.realAdaptedPolynomialMap (fun _ => 1) R.coord) 0 = 0 ∧
        coefficients (D.filtration.realAdaptedPolynomialMap (fun _ => 1) B.coord) 0 =
          coefficients (D.filtration.realAdaptedPolynomialMap (fun _ => 1) g.coord) 0 ∧
        ∀ h ∈ S,
          (D.filtration.realFirstCoefficientDirectionMap B.coord (fun i => (h i : ℝ)) -
            (small h + D.filtration.realFirstCoefficientAdjoint (fun _ => 1) B (rational h) + Z) ∈
              D.filtration.realFirstCoefficientFastSubmodule (fun _ => 1) (fun _ => Nat.zero_lt_one)
                (D.filtration.reducedSquareFastRelativeSubmodule (fun _ => 1) U)) ∧
          D.filtration.FirstCoefficientSlowBound b ω hF (fun _ => 1) T
            (Real.exp ((q + C) ^ C)) (small h) ∧
          D.filtration.FirstCoefficientGrid b ω hF (fun _ => 1) n (rational h)

theorem exists_synchronized_native_common_coefficients (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedNativeCommonCoefficientSpec s C := by
  obtain ⟨C, hC, hfamily⟩ := exists_normalized_common_family s
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ d D b ω hF H l m p hH hl hm hp hι hσ hd hHp hlp hmp hgrid hc hb
    T hT g S h₀ hh₀ W hbox hdata
  let U := D.filtration.fastPointwiseSquare b ω hF (fun _ : σ => 1) W
  let δ := matrixDenominator (fun i j => b.repr (D.basis j) i)
  let k := δ * D.grid * l * m
  let q := (p + 2) ^ 3 + 3 * p + 1
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hpq : p ≤ q := by
    have h3 : 0 ≤ (p + 2) ^ 3 := by positivity
    dsimp [q]
    linarith
  have h2q : (p + 2) ^ 2 ≤ q := by
    have h23 : (p + 2) ^ 2 ≤ (p + 2) ^ 3 := pow_le_pow_right₀ (by linarith) (by decide)
    dsimp [q]
    linarith
  have hd' : (Fintype.card (Fin d) : ℝ) ≤ p := by simpa only [Fintype.card_fin] using hd
  have hδ : 0 < δ := matrixDenominator_pos _
  have hk : 0 < k := Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hδ D.grid_pos) hl) hm
  have hδp : (δ : ℝ) ≤ Real.exp ((p + 2) ^ 3) :=
    real_basis_transfer_denominator D.basis b hp hd' hι hHp hb
  have hkq : (k : ℝ) ≤ Real.exp q := by
    dsimp only [k]
    rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_mul]
    calc
      _ ≤ Real.exp ((p + 2) ^ 3) * Real.exp p * Real.exp p * Real.exp p :=
        mul_le_mul (mul_le_mul (mul_le_mul hδp hgrid (Nat.cast_nonneg _) (Real.exp_nonneg _))
          hlp (Nat.cast_nonneg _) (by positivity)) hmp (Nat.cast_nonneg _) (by positivity)
      _ = Real.exp ((p + 2) ^ 3 + 3 * p) := by
        rw [← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp q := Real.exp_le_exp.mpr (by dsimp [q]; linarith)
  have hlk : l ∣ k := dvd_mul_of_dvd_left (dvd_mul_left l (δ * D.grid)) m
  have hmk : m ∣ k := dvd_mul_left m (δ * D.grid * l)
  have hδk : δ * D.grid ∣ k :=
    (dvd_mul_right (δ * D.grid) l).trans (dvd_mul_right (δ * D.grid * l) m)
  obtain ⟨ε, γ, r, E, P, R, A₀, B₀, R₀, hproduct, hA₀, hR₀, hB₀, hgood, _⟩ := hdata
  obtain ⟨A, B, D₀, hABD, hA, hB, hD, hAslow, hDgrid, hAzero, hDzero, hBzero⟩ :=
    D.filtration.exists_reduced_native_factorization b ω hF (fun _ : σ => 1)
      T hT (Real.exp_nonneg p) l g A₀ B₀ R₀ hproduct hA₀ hR₀
  have hBfast : B ∈ D.filtration.realFastDiagonalSubgroup (fun _ => 1) U := by
    change (D.filtration.adaptedReducedRealSymbolHom (fun _ => 1) B).coord ∈
      realificationLieSubalgebra (U.map (D.filtration.reducedSquareSndSymbolMap (fun _ => 1)))
    rw [hB]
    exact hB₀
  obtain ⟨n, hn, hnq, hkn, hcoeff⟩ := hfamily D.filtration b ω hF U H q hH hq
    (hι.trans hpq) (hσ.trans hpq) (hHp.trans (Real.exp_le_exp.mpr hpq)) hc k hk hkq
  have hE : ∀ h ∈ S, D.filtration.squareFiltration.quotientTop.SymbolSlowBound
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) T (Real.exp q) (E h) := by
    intro h hh
    exact D.filtration.squareFiltration.quotientTop.symbolSlowBound_mono
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hpq) (E h) (hgood h hh).2.2.2.2.2.2.2.2.2.2.1
  have hR : ∀ h ∈ S, D.filtration.squareFiltration.quotientTop.SymbolRationalGrid
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) k (R h) := by
    intro h hh
    exact D.filtration.squareFiltration.quotientTop.symbolRationalGrid_mono
      (D.filtration.reducedSquareBasis b ω hF) (fun i => squareBasisWeight ω i.val)
      (D.filtration.reducedSquareBasis_layers b ω hF) (fun _ => 1) hm hmk (R h)
      (hgood h hh).2.2.2.2.2.2.2.2.2.2.2
  have hε : ∀ h ∈ S, ∀ i, |(b.baseChange ℝ).repr (ε h).coord i| ≤ Real.exp q := by
    intro h hh i
    exact (real_basis_coordinates_exp_bound D.basis b hp hd' hHp hb (ε h).coord
      (hgood h hh).2.1 i).trans (Real.exp_le_exp.mpr h2q)
  have hγ : ∀ h ∈ S, (fun i => (b.baseChange ℝ).repr (γ h).coord i) ∈ realDenominatorGrid k := by
    intro h hh
    have hdeclared := realification_subgroup_grid D.basis D.lattice D.grid D.outer_grid
      (γ h) (hgood h hh).1
    exact realDenominatorGrid_subset_of_dvd (Nat.mul_pos hδ D.grid_pos) hδk
      (real_basis_coordinates_grid D.basis b D.grid (γ h).coord hdeclared)
  obtain ⟨small, rational, hcommon⟩ := hcoeff T hT A B D₀
    (D.filtration.realAdaptedCoefficientBound_mono b ω hF (fun _ => 1) T hT
      (Real.exp_le_exp.mpr hpq) A.coord hAslow)
    (D.filtration.realAdaptedCoefficientGrid_mono b ω hF (fun _ => 1) hl hlk D₀.coord hDgrid)
    S r E P R (P h₀) (fun h => (ε h).coord) (fun h => (γ h).coord) hbox
    (by intro h hh; rw [hABD]; exact (hgood h hh).2.2.1)
    (by intro h hh; rw [hABD, (hgood h hh).2.2.2.1])
    (fun h hh => (hgood h hh).2.2.2.2.2.1.symm)
    (fun h hh => hA.trans (hgood h hh).2.2.2.2.2.2.2.1.symm)
    (fun h hh => hB.trans (hgood h hh).2.2.2.2.2.2.2.2.2.1.symm)
    (fun h hh => (hgood h hh).2.2.2.2.2.2.1)
    (hgood h₀ hh₀).2.2.2.2.2.2.1
    (fun h hh => (hgood h hh).2.2.2.2.2.2.2.2.2.1.trans
      (hgood h₀ hh₀).2.2.2.2.2.2.2.2.2.1.symm) hE hR hε hγ
  exact ⟨n, hn, hnq, hlk.trans hkn, hmk.trans hkn, A, B, D₀, small, rational,
    D.filtration.realReducedRelativeCoefficient (fun _ => 1) (fun _ => Nat.zero_lt_one) (P h₀),
    hABD, hBfast, hAslow, hDgrid, hAzero, hDzero, hBzero, hcommon⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial
open scoped TensorProduct

def SynchronizedNativeSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ {σ ι κ L : Type*} [Fintype σ] [Fintype ι] [Fintype κ] [LieRing L] [LieAlgebra ℚ L]
    {d : ℕ} (D : RationalFilteredNilmanifold L (s + 1) d)
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (N : ℕ) (hN : 0 < N)
    (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
      (D.filtration.squareFinBasis b ω (hF 2)) (D.filtration.squareLattice D.lattice))
    (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis b ω (hF 2))
      (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N)
    (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (v : κ → D.filtration.squareFiltration.quotientTop.AssociatedGraded)
    (_hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (_hW : BasisGradedSubmodule
      (D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (D.filtration.reducedSquareBasis_layers b ω hF))
      (fun i => squareBasisWeight ω i.val) W.toSubmodule)
    (H l : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hl : 0 < l) (_hp : 0 ≤ p)
    (_hι : 2 * (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hκ : (Fintype.card κ : ℝ) ≤ p) (_hHp : (H : ℝ) ≤ Real.exp p) (_hlp : (l : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (_hh : ∀ i j, RationalHeightLE
      ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis b ω hF)
        (fun i => squareBasisWeight ω i.val) (D.filtration.reducedSquareBasis_layers b ω hF)).repr
          (v i) j) H),
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
      ∀ (T : σ → ℝ) (_hT : ∀ i, Real.exp ((p + C) ^ C) ≤ T i)
        (hs : 1 ≤ s) (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1))
        (η : L →ₗ[ℚ] ℚ) (S : Finset (σ → ℤ)) (h₀ : σ → ℤ) (_hh₀ : h₀ ∈ S)
        (_hdata : ∀ h ∈ S, D.HasFixedNativeSquareFactors
          (D.filtration.squareFinBasis b ω (hF 2)) (squareFinWeight ω)
          (D.filtration.squareFinBasis_layers b ω hF) N hN hin hout hs g η T h p l W),
        D.SynchronizedNativeSquareData b ω hF T g S h₀ W p ((p + C) ^ C) l m

theorem exists_synchronized_native_square_family (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ SynchronizedNativeSquareFamilySpec s C := by
  obtain ⟨C, hC, hfamily⟩ := exists_pointwise_synchronized_square_family s
  refine ⟨C, hC, ?_⟩
  intro σ ι κ L _ _ _ _ _ d D b ω hF N hN hin hout W v hv hW H l p hH hl hp hι hσ hκ hHp hlp hc hh
  obtain ⟨m, hm, hmp, hlm, hsync⟩ := hfamily D.filtration b ω hF (fun _ : σ => 1)
    (fun _ => Nat.zero_lt_one) W v hv hW H l p hH hl hp hι hσ hκ hHp hlp hc hh
  refine ⟨m, hm, hmp, hlm, ?_⟩
  intro T hT hs g η S h₀ hh₀ hdata
  have hcanonical := fun h hh =>
    RationalFilteredNilmanifold.HasFixedNativeSquareFactors.canonical_factors D b ω hF
      N hN hin hout (hdata h hh)
  choose! ε γ hγ hε r hf hsecond hderivative hfactor using hcanonical
  have hfastFactors := fun h hh => SymbolFactorizationIn.exists_fast_factors
    D.filtration.squareFiltration.quotientTop (D.filtration.reducedSquareBasis b ω hF)
    (fun i => squareBasisWeight ω i.val) (D.filtration.reducedSquareBasis_layers b ω hF) (hfactor h hh)
  choose! E P R hprod hE hR hP using hfastFactors
  let π := D.filtration.reducedSquareRealSymbolHom (fun _ : σ => 1)
  have hprojection : ∀ h ∈ S, π (E h * P h * R h) = D.filtration.adaptedReducedRealSymbolHom (fun _ => 1) g := by
    intro h hh
    rw [hprod h hh]
    change D.filtration.reducedSquareRealSymbolHom (fun _ => 1)
      (D.filtration.squareFiltration.adaptedReducedRealSymbolHom (fun _ => 1) (r h)) = _
    rw [D.filtration.adaptedReducedRealSymbolHom_square_projection, hsecond h hh]
  obtain ⟨E', P', R', hgood, hrelative⟩ := hsync T hT S h₀ hh₀ E P R hP hE hR
    (fun h hh => (hprojection h hh).trans (hprojection h₀ hh₀).symm)
  refine ⟨ε, γ, r, E', P', R', π (E h₀), π (P h₀), π (R h₀), ?_, ?_, ?_, ?_, ?_, hrelative⟩
  · rw [← map_mul, ← map_mul]
    exact hprojection h₀ hh₀
  · exact D.filtration.reducedSquareRealSymbolHom_slow b ω hF (fun _ => 1) T (Real.exp p) (E h₀) (hE h₀ hh₀)
  · exact D.filtration.reducedSquareRealSymbolHom_grid b ω hF (fun _ => 1) l (R h₀) (hR h₀ hh₀)
  · exact D.filtration.symbolFastIn_reducedSquareRealSymbolHom (fun _ => 1) _ (P h₀) (hP h₀ hh₀)
  · intro h hh
    obtain ⟨heq, hfast, hleft, hright, hmiddle, hslow, hrat⟩ := hgood h hh
    exact ⟨hγ h hh, hε h hh, hf h hh, hsecond h hh, hderivative h hh,
      heq.trans (hprod h hh), hfast, hleft, hright, hmiddle, hslow, hrat⟩

end Erdos3

end

section

namespace Erdos3

open Module NilpotentLieFiltration NilpotentLieBCHGroup VectorPolynomial CircleFourier
open scoped TensorProduct BigOperators

universe uσ uL

def BiasedSynchronizedSquareFamilySpec (s C : ℕ) : Prop :=
  ∀ (_hs : 1 ≤ s) {σ : Type uσ} {L : Type uL}
    [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L] {d : ℕ}
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
    (p : ℝ) (_hp : 0 ≤ p) (T : D.Niltest (fun _ : σ => 1)) (_hT : T.ComplexityLE p),
    ∃ (e : Basis (Fin (finrank ℚ L)) ℚ L) (ω : Fin (finrank ℚ L) → ℕ)
      (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
      (N : ℕ) (hN : 0 < N)
      (hin : scaledIntegerGrid N ⊆ bchSubgroupCoordinates
        (D.filtration.squareFinBasis e ω (hF 2)) (D.filtration.squareLattice D.lattice))
      (hout : bchSubgroupCoordinates (D.filtration.squareFinBasis e ω (hF 2))
        (D.filtration.squareLattice D.lattice) ⊆ denominatorGrid N),
      (∀ i j, rationalLogHeight (D.basis.repr (e i) j) ≤ p + 1) ∧
      (D.filtration.squareFiltration.topQuotientModel
        (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
        (D.filtration.squareFinBasis_layers e ω hF)
        (D.filtration.squareLattice D.lattice) N hN hin hout).GeometryComplexityLE (squareGeometryBudget p) ∧
      ∀ (g : D.filtration.RealAdaptedPolynomialGroup (fun _ : σ => 1)),
        D.filtration.nativePolynomialOrbit (fun _ => 1) g = T.orbit →
      ∀ (η : L →ₗ[ℚ] ℚ),
        (∀ z ∈ D.filtration.realification.subgroup (s + 1), ∀ x,
          T.observable (z • x) = character ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) *
            T.observable x) →
      ∀ (origin : σ → ℤ) (lengths : σ → ℕ), (∀ i, 0 < lengths i) →
        (Fintype.card σ : ℝ) ≤ p →
        (∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ)) →
        Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths, T.eval x‖ →
        ∃ (S : Finset (σ → ℤ)) (h₀ : σ → ℤ) (l m : ℕ)
          (W : LieSubalgebra ℚ D.filtration.squareFiltration.quotientTop.AssociatedGraded)
          (u : Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i}) →
            D.filtration.squareFiltration.quotientTop.AssociatedGraded),
          h₀ ∈ S ∧ Real.exp (-((p + C) ^ C)) * (∏ i, (lengths i : ℝ)) ≤ S.card ∧
          0 < l ∧ (l : ℝ) ≤ Real.exp ((p + C) ^ C) ∧
          0 < m ∧ (m : ℝ) ≤ Real.exp ((p + C) ^ C) ∧ l ∣ m ∧
          Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
          BasisGradedSubmodule
            (D.filtration.squareFiltration.quotientTop.associatedGradedBasis
              (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
              (D.filtration.reducedSquareBasis_layers e ω hF))
            (fun i => squareBasisWeight ω i.val) W.toSubmodule ∧
          (∀ i j, rationalLogHeight
            ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
              (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
              (D.filtration.reducedSquareBasis_layers e ω hF)).repr (u i) j) ≤ (p + C) ^ C) ∧
          (∀ x ∈ D.filtration.fullFastGradedRelative e ω hF W,
            basisGradeProjection (D.filtration.associatedGradedBasis e ω hF) ω (s + 1) x = x →
              D.filtration.gradedFrequency e ω hF η x = 0) ∧
          (∀ h ∈ S, (∀ i, |(h i : ℝ)| ≤ lengths i) ∧
            ∀ i, Real.exp (-((p + C) ^ C)) * lengths i <
              (((lengths i : ℤ) - |h i|).toNat : ℝ)) ∧
          D.SynchronizedNativeSquareData e ω hF (fun i => (lengths i : ℝ)) g S h₀ W
            ((p + C) ^ C) ((p + C) ^ C) l m

theorem exists_biased_synchronized_square_family (s c : ℕ)
    (hI : TranslatedStepDropSpec.{uσ, uL} s c) :
    ∃ C : ℕ, 2 ≤ C ∧ BiasedSynchronizedSquareFamilySpec.{uσ, uL} s C := by
  obtain ⟨a, _, hfamily⟩ := exists_common_fixed_native_square_family s c hI
  obtain ⟨b, _, hsynchronize⟩ := exists_synchronized_native_square_family s
  let B : Polynomial ℕ := (Polynomial.X + Polynomial.C a) ^ a
  let G : Polynomial ℕ := ((Polynomial.X + 3) ^ 11 + 2 * Polynomial.X + 5) ^ 11
  let Q : Polynomial ℕ := B + (Polynomial.X + 4) ^ 11 + G + 2 * Polynomial.X + 2
  let P : Polynomial ℕ := B + (Q + 1) + (Q + 1 + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro hs σ L _ _ _ _ d _ _ _ _ D _ _ _ _ _ _ _ _ p hp T hT
  let k : ℝ := (p + a) ^ a
  let q : ℝ := k + (p + 4) ^ 11 + squareGeometryBudget p + 2 * p + 2
  have hk : 0 ≤ k := by dsimp [k]; positivity
  have hbracket : 0 ≤ (p + 4) ^ 11 := by positivity
  have hgeompos := squareGeometryBudget_nonneg hp
  have hq : 0 ≤ q := by dsimp [q]; positivity
  have hkq : k ≤ q := by dsimp [q]; linarith
  have hbracketq : (p + 4) ^ 11 ≤ q := by dsimp [q]; linarith
  have hgeomq : squareGeometryBudget p ≤ q := by dsimp [q]; linarith
  have h2pq : 2 * p ≤ q := by dsimp [q]; linarith
  have hpq : p ≤ q := by linarith
  have hq1 : 0 ≤ q + 1 := by linarith
  have hbq : 0 ≤ (q + 1 + b) ^ b := by positivity
  have hbound : k + (q + 1) + (q + 1 + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Q, B, G, k, q, squareGeometryBudget, Polynomial.eval₂_pow] using hfinal p hp
  have hkC : k ≤ (p + C) ^ C := by linarith
  have hqC : q + 1 ≤ (p + C) ^ C := by linarith
  have hbC : (q + 1 + b) ^ b ≤ (p + C) ^ C := by linarith
  obtain ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, hconstruct⟩ := hfamily hs D p hp T hT
  obtain ⟨hdim, _, hstructure⟩ := D.basis_geometry_of_forward_height e hp hT.1 he
  refine ⟨e, ω, hF, N, hN, hin, hout, he, hgeometry, ?_⟩
  intro g hgOrbit η hvert origin lengths hlengths hσ hlarge hbias
  have hTpos : ∀ i, 0 < (lengths i : ℝ) := fun i => by exact_mod_cast hlengths i
  obtain ⟨S, l, W, u, hS, hcount, hl, hlk, hu, hW, hheight, hgood⟩ :=
    hconstruct g hgOrbit η hvert origin lengths hlengths hσ
      (fun i => (Real.exp_le_exp.mpr hkC).trans (hlarge i)) hbias
  obtain ⟨h₀, hh₀⟩ := hS
  have hWcanonical := (D.filtration.squareTopQuotientModel_graded_iff e ω hF
    (D.filtration.squareLattice D.lattice) N hN hin hout W.toSubmodule).mp hW
  have hcanonicalHeight : BasisFamilyLogHeight
      (D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers e ω hF)) u k :=
    D.filtration.squareTopQuotientModel_graded_logHeight e ω hF
      (D.filtration.squareLattice D.lattice) N hN hin hout u hheight
  let H := ⌈Real.exp q⌉₊
  have hH : 1 ≤ H := one_le_ceil_exp q
  have hHq : (H : ℝ) ≤ Real.exp (q + 1) := ceil_exp_le_exp_add_one hq
  have hdimq : 2 * (Fintype.card (Fin (finrank ℚ L)) : ℝ) ≤ q + 1 := by
    have := mul_le_mul_of_nonneg_left hdim (by norm_num : (0 : ℝ) ≤ 2)
    linarith
  have hκq : (Fintype.card (Fin (Fintype.card {i // ¬ s + 1 ≤ squareFinWeight ω i})) : ℝ) ≤ q + 1 := by
    rw [Fintype.card_fin]
    exact hgeometry.1.trans (hgeomq.trans (by linarith))
  have hσq : (Fintype.card σ : ℝ) ≤ q + 1 := hσ.trans (hpq.trans (by linarith))
  have hlq : (l : ℝ) ≤ Real.exp (q + 1) :=
    hlk.trans (Real.exp_le_exp.mpr (hkq.trans (by linarith)))
  have hc : ∀ i j k, RationalHeightLE (e.repr ⁅e i, e j⁆ k) H :=
    fun i j k => rationalHeightLE_ceil_exp ((hstructure i j k).trans hbracketq)
  have hh : ∀ i j, RationalHeightLE
      ((D.filtration.squareFiltration.quotientTop.associatedGradedBasis
        (D.filtration.reducedSquareBasis e ω hF) (fun i => squareBasisWeight ω i.val)
        (D.filtration.reducedSquareBasis_layers e ω hF)).repr (u i) j) H :=
    fun i j => rationalHeightLE_ceil_exp ((hcanonicalHeight i j).trans hkq)
  obtain ⟨m, hm, hmb, hlm, hsync⟩ := hsynchronize D e ω hF N hN hin hout W u hu hWcanonical
    H l (q + 1) hH hl hq1 hdimq hσq hκq hHq hlq hc hh
  have hfixed : ∀ h ∈ S, D.HasFixedNativeSquareFactors
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout hs g η
      (fun i => (lengths i : ℝ)) h (q + 1) l W := by
    intro h hh
    exact RationalFilteredNilmanifold.HasFixedNativeSquareFactors.mono D
      (D.filtration.squareFinBasis e ω (hF 2)) (squareFinWeight ω)
      (D.filtration.squareFinBasis_layers e ω hF) N hN hin hout
      (hgood h hh).2.2 (hkq.trans (by linarith)) hTpos
  have hdata := hsync (fun i => (lengths i : ℝ))
    (fun i => (Real.exp_le_exp.mpr hbC).trans (hlarge i)) hs g η S h₀ hh₀ hfixed
  refine ⟨S, h₀, l, m, W, u, hh₀, ?_, hl, hlk.trans (Real.exp_le_exp.mpr hkC),
    hm, hmb.trans (Real.exp_le_exp.mpr hbC), hlm, hu, hWcanonical, ?_, ?_, ?_, ?_⟩
  · exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hkC))
      (Finset.prod_nonneg (fun i _ => Nat.cast_nonneg (lengths i)))).trans hcount
  · exact fun i j => (hcanonicalHeight i j).trans hkC
  · exact RationalFilteredNilmanifold.HasFixedNativeSquareFactors.fullFast_top_frequency
      D e ω hF N hN hin hout (hgood h₀ hh₀).2.2 hW
  · intro h hh
    exact ⟨(hgood h hh).1, fun i =>
      (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (neg_le_neg hkC))
        (Nat.cast_nonneg (lengths i))).trans_lt ((hgood h hh).2.1 i)⟩
  · exact RationalFilteredNilmanifold.SynchronizedNativeSquareData.mono
      D e ω hF hdata hqC hbC hTpos

theorem exists_stepTwo_biased_synchronized_square_family :
    ∃ C : ℕ, 2 ≤ C ∧ BiasedSynchronizedSquareFamilySpec.{uσ, uL} 1 C :=
  exists_biased_synchronized_square_family 1 4 translatedStepDropSpec_one

end Erdos3

end

end OAI
