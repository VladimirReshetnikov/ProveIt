import OAI.Combinatorics.Progressions.Geometry.HorizontalSeparationTransport
import OAI.Combinatorics.Progressions.Linear.FullFastHorizontalSpanning

namespace OAI

section

namespace Erdos3

theorem exists_controlled_derivative_absorption {H E V ι κ ν τ σ : Type*}
    [AddCommGroup H] [Module ℝ H] [AddCommGroup E] [Module ℝ E]
    [SeminormedAddCommGroup V] [NormedSpace ℝ V]
    [Fintype ι] [Fintype κ] [Fintype ν]
    (e : H ≃ₗ[ℝ] (ι → ℝ)) (U K : Submodule ℝ H)
    (A : Matrix ι κ ℚ) (B : Matrix ι ν ℚ)
    (hAspan : Submodule.span ℝ (Set.range (A.map (Rat.castHom ℝ)).col) = U.map e.toLinearMap)
    (hBspan : Submodule.span ℝ (Set.range (B.map (Rat.castHom ℝ)).col) = K.map e.toLinearMap)
    (b : ν → K) (hb : ∀ j, e (b j).val = (B.map (Rat.castHom ℝ)).col j)
    (P : E →ₗ[ℝ] H) (f : E →ₗ[ℝ] E) (hf : P.comp f = P)
    (S R : K →ₗ[ℝ] E) (hSR : S = f.comp R)
    (hS : P.comp S = K.subtype) (hR : P.comp R = K.subtype)
    (c : E →ₗ[ℝ] (τ → ℝ)) (N : E →ₗ[ℝ] V)
    (n rden : ℕ) (hRgrid : ∀ j, c (R (b j)) ∈ realDenominatorGrid n)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hA : ∀ i j, RationalHeightLE (A i j) J) (hB : ∀ i j, RationalHeightLE (B i j) J)
    {p : ℝ} (hp : 0 ≤ p) (hι : (Fintype.card ι : ℝ) ≤ p)
    (hcols : (Fintype.card (κ ⊕ ν) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (M C : ℝ) (hC : 0 ≤ C) (hSbound : ∀ x, ‖N (S x)‖ ≤ C * ‖e x.val‖)
    (y small rational : σ → E) (k : σ → K)
    (hsystem : ∀ i, y i = small i + f (rational i) + S (k i))
    (hy : ∀ i, P (y i) ∈ U)
    (hsmall : ∀ i, ‖e (P (small i))‖ ≤ Real.exp p / T i)
    (hNsmall : ∀ i, ‖N (small i)‖ ≤ M / T i)
    (hrational : ∀ i, e (P (rational i)) ∈ realDenominatorGrid l)
    (hrgrid : ∀ i, c (rational i) ∈ realDenominatorGrid rden) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ ks kr : σ → K, ∀ i,
        P (small i - S (ks i)) ∈ U ∧
        P (rational i - R (kr i)) ∈ U ∧
        (k i + ks i + kr i).val ∈ U ∧
        y i = (small i - S (ks i)) + f (rational i - R (kr i)) + S (k i + ks i + kr i) ∧
        ‖e (ks i).val‖ ≤ Real.exp ((p + 2) ^ 19) * Real.exp p / T i ∧
        ‖N (small i - S (ks i))‖ ≤ (M + C * Real.exp ((p + 2) ^ 19) * Real.exp p) / T i ∧
        ‖e (P (small i - S (ks i)))‖ ≤ (1 + Real.exp ((p + 2) ^ 19)) * Real.exp p / T i ∧
        c (rational i - R (kr i)) ∈ realDenominatorGrid (rden * (n * m)) := by
  obtain ⟨m, hm, hmp, split, hsplit, hnorm, hgrid⟩ :=
    exists_controlled_kernel_split_equiv e U K A B hAspan hBspan b hb (c.comp R) n hRgrid
      hJ hl hA hB hp hι hcols hJp hlp
  let ks : σ → K := fun i => split (P (small i))
  let kr : σ → K := fun i => split (P (rational i))
  have hks (i : σ) : ‖e (ks i).val‖ ≤ Real.exp ((p + 2) ^ 19) * Real.exp p / T i := by
    calc
      _ ≤ Real.exp ((p + 2) ^ 19) * ‖e (P (small i))‖ := hnorm _
      _ ≤ Real.exp ((p + 2) ^ 19) * (Real.exp p / T i) :=
        mul_le_mul_of_nonneg_left (hsmall i) (Real.exp_nonneg _)
      _ = _ := by ring
  refine ⟨m, hm, hmp, ks, kr, fun i => ?_⟩
  have hproj : P (y i) = P (small i) + P (rational i) + (k i).val := by
    rw [hsystem i, map_add, map_add,
      show P (f (rational i)) = P (rational i) from DFunLike.congr_fun hf _,
      show P (S (k i)) = (k i).val from DFunLike.congr_fun hS _]
  have hparts := horizontal_parts_separation_equiv e U K A B hAspan hBspan
    hJ hl hA hB hp hι hcols hJp hlp T hT i
    (P (y i)) (P (small i)) (P (rational i)) (k i) hproj (hy i) (hsmall i) (hrational i)
  have habsorb := horizontal_absorption_with_split U K P f hf S R hSR hS hR split hsplit
    (y i) (small i) (rational i) (k i) (hsystem i) (hy i) hparts.1 hparts.2
  refine ⟨habsorb.1, habsorb.2.1, habsorb.2.2.1, habsorb.2.2.2, hks i, ?_, ?_, ?_⟩
  · calc
      _ ≤ ‖N (small i)‖ + ‖N (S (ks i))‖ := by rw [map_sub]; exact norm_sub_le _ _
      _ ≤ M / T i + C * (Real.exp ((p + 2) ^ 19) * Real.exp p / T i) :=
        add_le_add (hNsmall i) ((hSbound _).trans (mul_le_mul_of_nonneg_left (hks i) hC))
      _ = _ := by ring
  · rw [map_sub, map_sub, show P (S (ks i)) = (ks i).val from DFunLike.congr_fun hS _]
    calc
      _ ≤ ‖e (P (small i))‖ + ‖e (ks i).val‖ := norm_sub_le _ _
      _ ≤ Real.exp p / T i + Real.exp ((p + 2) ^ 19) * Real.exp p / T i :=
        add_le_add (hsmall i) (hks i)
      _ = _ := by ring
  · rw [map_sub]
    exact realDenominatorGrid_sub_product rden (n * m) _ _ (hrgrid i) (hgrid _ (hrational i))

end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ ν τ L V : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype ι] [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) Wf)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W))
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))

theorem exists_fullFast_derivative_absorption
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (g : 𝓖) (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g.val.coord) 0 = 0)
    (K : Submodule ℝ 𝓗) (Q : Matrix (LayerOneBasisIndex ω) ν ℚ)
    (hQspan : Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col) = K.map (cH).toLinearMap)
    (b : ν → K) (hb : ∀ j, cH (b j).val = (Q.map (Rat.castHom ℝ)).col j)
    (S R : K →ₗ[ℝ] 𝓔) (hSR : S = (ρ g).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (c : 𝓔 →ₗ[ℝ] (τ → ℝ)) (N : 𝓔 →ₗ[ℝ] V)
    (n rden : ℕ) (hRgrid : ∀ j, c (R (b j)) ∈ realDenominatorGrid n)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) J)
    (hQ : ∀ i j, RationalHeightLE (Q i j) J)
    {p : ℝ} (hp : 0 ≤ p)
    (hsize : ((Fintype.card κ + Fintype.card ι + Fintype.card ν : ℕ) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (M C : ℝ) (hC : 0 ≤ C) (hSbound : ∀ x, ‖N (S x)‖ ≤ C * ‖cH x.val‖)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, Y g i = small i + ρ g (rational i) + S (k i))
    (hsmall : ∀ i, ‖cH (𝓟 (small i))‖ ≤ Real.exp p / T i)
    (hNsmall : ∀ i, ‖N (small i)‖ ≤ M / T i)
    (hrational : ∀ i, cH (𝓟 (rational i)) ∈ realDenominatorGrid l)
    (hrgrid : ∀ i, c (rational i) ∈ realDenominatorGrid rden) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ ks kr : σ → K, ∀ i,
        𝓟 (small i - S (ks i)) ∈ 𝓤 ∧
        𝓟 (rational i - R (kr i)) ∈ 𝓤 ∧
        (k i + ks i + kr i).val ∈ 𝓤 ∧
        Y g i = (small i - S (ks i)) + ρ g (rational i - R (kr i)) + S (k i + ks i + kr i) ∧
        ‖cH (ks i).val‖ ≤ Real.exp ((p + 2) ^ 19) * Real.exp p / T i ∧
        ‖N (small i - S (ks i))‖ ≤ (M + C * Real.exp ((p + 2) ^ 19) * Real.exp p) / T i ∧
        ‖cH (𝓟 (small i - S (ks i)))‖ ≤ (1 + Real.exp ((p + 2) ^ 19)) * Real.exp p / T i ∧
        c (rational i - R (kr i)) ∈ realDenominatorGrid (rden * (n * m)) := by
  have hrow : Fintype.card (LayerOneBasisIndex ω) ≤ Fintype.card ι :=
    Fintype.card_le_of_injective Subtype.val Subtype.val_injective
  have hrows : (Fintype.card (LayerOneBasisIndex ω) : ℝ) ≤ p := by
    have hle : Fintype.card (LayerOneBasisIndex ω) ≤
        Fintype.card κ + Fintype.card ι + Fintype.card ν := by omega
    exact (Nat.cast_le.mpr hle).trans hsize
  have hcol : Fintype.card ((κ ⊕ TopGradedBasisIndex s ω) ⊕ ν) ≤
      Fintype.card κ + Fintype.card ι + Fintype.card ν := by
    rw [Fintype.card_sum]
    exact Nat.add_le_add_right (fullFastDiagonalGenerators_card (κ := κ) (s := s) (ω := ω)) _
  have hf : (𝓟).comp (ρ g).toLinearMap = 𝓟 := by
    apply LinearMap.ext
    intro x
    exact F.realFastCoefficientAction_horizontal (fun _ => 1) (fun _ => Nat.zero_lt_one)
      Wf e ω hF g x
  exact exists_controlled_derivative_absorption cH 𝓤 K (F.fullFastHorizontalMatrix e ω hF v) Q
    (F.fullFastHorizontalMatrix_span e ω hF W hW v hv) hQspan b hb 𝓟 (ρ g).toLinearMap hf
    S R hSR hS hR c N n rden hRgrid hJ hl (F.fullFastHorizontalMatrix_height e ω hF v hJ hheight)
    hQ hp hrows ((Nat.cast_le.mpr hcol).trans hsize) hJp hlp T hT M C hC hSbound
    (Y g) small rational k hsystem
    (fun i => F.fullFast_horizontal_derivative_mem e ω hF W hW g.val g.property hzero i)
    hsmall hNsmall hrational hrgrid

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι κ ν τ L V : Type*} [Fintype σ] [DecidableEq σ]
  [Fintype ι] [Fintype κ] [Fintype ν] [LieRing L] [LieAlgebra ℚ L]
  [SeminormedAddCommGroup V] [NormedSpace ℝ V] {s : ℕ}
  (F : NilpotentLieFiltration L (s + 1)) (e : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (e '' {i | j ≤ ω i}))
  (W : LieSubalgebra ℚ F.squareFiltration.quotientTop.AssociatedGraded)

local notation "ωW" => (fun i : ReducedSquareBasisIndex s ω => squareBasisWeight ω (Subtype.val i))
local notation "bW" => F.squareFiltration.quotientTop.associatedGradedBasis
  (F.reducedSquareBasis e ω hF) ωW (F.reducedSquareBasis_layers e ω hF)
local notation "Wf" => F.fastPointwiseSquare e ω hF (fun _ : σ => 1) W
local notation "𝓗" => ℝ ⊗[ℚ] (L ⧸ F.layer 2)
local notation "𝓔" => F.RealFastCoefficientModule (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "𝓖" => F.realFastDiagonalSubgroup (fun _ : σ => 1) Wf
local notation "𝓟" => F.realFastCoefficientHorizontal (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
  (F.reducedSquareFastRelativeSubmodule (fun _ => 1) Wf)
local notation "𝓤" => Submodule.baseChange ℝ (F.layerOneGradedSubmodule e ω hF (F.fullFastGradedDiagonal W))
local notation "cH" => Basis.equivFun (Basis.baseChange ℝ (F.layerOneBasis e ω hF))
local notation "ρ" => F.realFastCoefficientAction (fun _ : σ => 1) (fun _ => Nat.zero_lt_one) Wf
local notation "Y" => (fun (g : 𝓖) i => F.realFastCoefficientDirectionMap Wf (Subtype.val g) (Pi.single i 1))

theorem exists_fullFast_horizontal_normalization
    (hW : BasisGradedSubmodule bW ωW W.toSubmodule)
    (v : κ → F.squareFiltration.quotientTop.AssociatedGraded)
    (hv : Submodule.span ℚ (Set.range v) = W.toSubmodule)
    (g : 𝓖) (hzero : coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g.val.coord) 0 = 0)
    (K : Submodule ℝ 𝓗) (Q : Matrix (LayerOneBasisIndex ω) ν ℚ)
    (hQspan : Submodule.span ℝ (Set.range (Q.map (Rat.castHom ℝ)).col) = K.map (cH).toLinearMap)
    (b : ν → K) (hb : ∀ j, cH (b j).val = (Q.map (Rat.castHom ℝ)).col j)
    (S R : K →ₗ[ℝ] 𝓔) (hSR : S = (ρ g).toLinearMap.comp R)
    (hS : (𝓟).comp S = K.subtype) (hR : (𝓟).comp R = K.subtype)
    (c : 𝓔 →ₗ[ℝ] (τ → ℝ)) (N : 𝓔 →ₗ[ℝ] V)
    (n rden : ℕ) (hRgrid : ∀ j, c (R (b j)) ∈ realDenominatorGrid n)
    {J l : ℕ} (hJ : 1 ≤ J) (hl : 0 < l)
    (hheight : ∀ j i, RationalHeightLE ((bW).repr (v j) i) J)
    (hQ : ∀ i j, RationalHeightLE (Q i j) J)
    {p : ℝ} (hp : 0 ≤ p)
    (hsize : ((Fintype.card κ + Fintype.card ι + Fintype.card ν : ℕ) : ℝ) ≤ p)
    (hJp : (J : ℝ) ≤ Real.exp p) (hlp : (l : ℝ) ≤ Real.exp p)
    (T : σ → ℝ) (hT : ∀ i, Real.exp (separationBudget p) ≤ T i)
    (M C : ℝ) (hC : 0 ≤ C) (hSbound : ∀ x, ‖N (S x)‖ ≤ C * ‖cH x.val‖)
    (small rational : σ → 𝓔) (k : σ → K)
    (hsystem : ∀ i, Y g i = small i + ρ g (rational i) + S (k i))
    (hsmall : ∀ i, ‖cH (𝓟 (small i))‖ ≤ Real.exp p / T i)
    (hNsmall : ∀ i, ‖N (small i)‖ ≤ M / T i)
    (hrational : ∀ i, cH (𝓟 (rational i)) ∈ realDenominatorGrid l)
    (hrgrid : ∀ i, c (rational i) ∈ realDenominatorGrid rden)
    (dproj : ℕ) (hprojgrid : ∀ l x, c x ∈ realDenominatorGrid l →
      cH (𝓟 x) ∈ realDenominatorGrid (dproj * l)) :
    ∃ m : ℕ, 0 < m ∧ (m : ℝ) ≤ Real.exp ((p + 2) ^ 36) ∧
      ∃ ks kr : σ → K,
        (∀ i, ‖N (small i - S (ks i))‖ ≤ (M + C * Real.exp ((p + 2) ^ 19) * Real.exp p) / T i ∧
          c (rational i - R (kr i)) ∈ realDenominatorGrid (rden * (n * m))) ∧
        ∃ a g' q : 𝓖,
          a.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (small i - S (ks i))) ∧
          q.val = F.realLayerOneCorrection e ω hF (fun i => 𝓟 (rational i - R (kr i))) ∧
          F.RealAdaptedCoefficientBound e ω hF (fun _ => 1) T
            ((1 + Real.exp ((p + 2) ^ 19)) * Real.exp p) a.val.coord ∧
          F.RealAdaptedCoefficientGrid e ω hF (fun _ => 1) (dproj * (rden * (n * m))) q.val.coord ∧
          coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g'.val.coord) 0 = 0 ∧
          (∀ i, (F.layer 2).mkQ.baseChange ℝ
            (coefficients (F.realAdaptedPolynomialMap (fun _ => 1) g'.val.coord) (Finsupp.single i 1)) =
              (k i + ks i + kr i).val) ∧
          let S' := (ρ a).symm.toLinearMap.comp S
          let R' := (ρ q).toLinearMap.comp R
          let small' := fun i => (ρ a).symm ((small i - S (ks i)) - Y a i)
          let rational' := fun i => ρ q (rational i - R (kr i)) - Y q i
          a * g' * q = g ∧ S' = (ρ g').toLinearMap.comp R' ∧
            (𝓟).comp S' = K.subtype ∧ (𝓟).comp R' = K.subtype ∧
            ∀ i, Y g' i = small' i + ρ g' (rational' i) + S' (k i + ks i + kr i) ∧
              𝓟 (small' i) = 0 ∧ 𝓟 (rational' i) = 0 ∧ 𝓟 (Y g' i) = (k i + ks i + kr i).val ∧
              𝓟 (Y g' i) ∈ 𝓤 ⊓ K := by
  classical
  have h := F.exists_fullFast_derivative_absorption
    (σ := σ) (ι := ι) (κ := κ) (ν := ν) (τ := τ) (V := V) e ω hF W hW v hv
    g hzero K Q hQspan b hb S R hSR hS hR c N n rden hRgrid hJ hl hheight hQ hp hsize hJp hlp
    T hT M C hC hSbound small rational k hsystem hsmall hNsmall hrational hrgrid
  obtain ⟨m, hm, hmp, ks, kr, habs⟩ := h
  let small0 : σ → 𝓔 := fun i => small i - S (ks i)
  let rational0 : σ → 𝓔 := fun i => rational i - R (kr i)
  let k0 : σ → K := fun i => k i + ks i + kr i
  have hs0 : ∀ i, 𝓟 (small0 i) ∈ 𝓤 := fun i => (habs i).1
  have hr0 : ∀ i, 𝓟 (rational0 i) ∈ 𝓤 := fun i => (habs i).2.1
  have hk0 : ∀ i, (k0 i).val ∈ 𝓤 := fun i => (habs i).2.2.1
  have hsys0 : ∀ i, Y g i = small0 i + ρ g (rational0 i) + S (k0 i) :=
    fun i => (habs i).2.2.2.1
  have hN0 : ∀ i, ‖N (small0 i)‖ ≤ (M + C * Real.exp ((p + 2) ^ 19) * Real.exp p) / T i := by
    intro i
    rcases habs i with ⟨_, _, _, _, _, hn, _, _⟩
    exact hn
  have hP0 : ∀ i, ‖cH (𝓟 (small0 i))‖ ≤ (1 + Real.exp ((p + 2) ^ 19)) * Real.exp p / T i := by
    intro i
    rcases habs i with ⟨_, _, _, _, _, _, hp, _⟩
    exact hp
  have hgrid0 : ∀ i, c (rational0 i) ∈ realDenominatorGrid (rden * (n * m)) := by
    intro i
    rcases habs i with ⟨_, _, _, _, _, _, _, hg⟩
    exact hg
  refine ⟨m, hm, hmp, ks, kr, fun i => ⟨hN0 i, hgrid0 i⟩, ?_⟩
  exact F.realFast_bounded_horizontal_normalization e ω hF (F.fullFastGradedDiagonal W) Wf
    (F.fullFastPointwise_image_le e ω hF (fun _ => 1) (fun _ => Nat.zero_lt_one) W hW)
    g hzero K S R hSR hS hR small0 rational0 k0 hsys0 hs0 hr0 hk0
    T (fun i => (Real.exp_pos _).trans_le (hT i))
    ((1 + Real.exp ((p + 2) ^ 19)) * Real.exp p) (by positivity) hP0
    (dproj * (rden * (n * m))) (fun i => hprojgrid _ _ (hgrid0 i))

end Erdos3.NilpotentLieFiltration

end

end OAI
