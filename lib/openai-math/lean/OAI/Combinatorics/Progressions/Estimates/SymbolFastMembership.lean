/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Compat.TensorProduct
import OAI.Combinatorics.Progressions.Fourier.HomogeneousGradedProjectionFrequency
import OAI.Combinatorics.Progressions.Sampling.RationalPowerGrid

namespace OAI

section

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s)

@[simp] theorem adaptedWeightedDilation_coe (w : σ → ℕ) (r : ℚ)
    (p : F.adaptedLieSubalgebra w) :
    (F.adaptedWeightedDilation w r p : VectorPolynomial σ ℚ L) =
      weightedDilation w r (p : VectorPolynomial σ ℚ L) := rfl

theorem polynomialSymbolDilation_repr (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (r : ℚ) (x : F.PolynomialSymbol w) (z : SymbolBasisIndex w ω) :
    (F.polynomialSymbolBasis b ω hF w).repr (F.polynomialSymbolDilation w r x) z =
      r ^ Finsupp.weight w z.val.1 * (F.polynomialSymbolBasis b ω hF w).repr x z := by
  obtain ⟨p, rfl⟩ := F.polynomialSymbolMap_surjective w x
  rw [F.polynomialSymbolDilation_map, F.polynomialSymbolBasis_repr_map,
    F.polynomialSymbolBasis_repr_map]
  change b.repr (coefficients (weightedDilation w r (p : VectorPolynomial σ ℚ L)) z.val.1) z.val.2 = _
  rw [coefficients_weightedDilation, map_smul, Finsupp.smul_apply, smul_eq_mul]

noncomputable def realPolynomialSymbolDilation (w : σ → ℕ) (r : ℚ) :
    F.RealPolynomialSymbol w →ₗ⁅ℚ⁆ F.RealPolynomialSymbol w :=
  LieAlgebra.ExtendScalars.map (AlgHom.id ℚ ℝ) (F.polynomialSymbolDilation w r)

@[simp] theorem realPolynomialSymbolDilation_tmul (w : σ → ℕ) (r : ℚ)
    (a : ℝ) (x : F.PolynomialSymbol w) :
    F.realPolynomialSymbolDilation w r (a ⊗ₜ[ℚ] x) =
      a ⊗ₜ[ℚ] F.polynomialSymbolDilation w r x := by
  simp only [realPolynomialSymbolDilation, LieAlgebra.ExtendScalars.map_apply_tmul, AlgHom.id_apply]

theorem realPolynomialSymbolDilation_repr (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (r : ℚ) (x : F.RealPolynomialSymbol w) (z : SymbolBasisIndex w ω) :
    ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr (F.realPolynomialSymbolDilation w r x) z =
      (r : ℝ) ^ Finsupp.weight w z.val.1 * ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr x z := by
  induction x using TensorProduct.inductionOn with
  | tmul a x =>
    rw [F.realPolynomialSymbolDilation_tmul, Basis.baseChange_repr_tmul,
      Basis.baseChange_repr_tmul, F.polynomialSymbolDilation_repr]
    simp only [Rat.smul_def, Rat.cast_mul, Rat.cast_pow]
    ring
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy, mul_add]

@[simp] theorem realPolynomialSymbolDilation_one (w : σ → ℕ) (x : F.RealPolynomialSymbol w) :
    F.realPolynomialSymbolDilation w 1 x = x := by
  induction x using TensorProduct.inductionOn with
  | tmul a x => simp only [F.realPolynomialSymbolDilation_tmul, F.polynomialSymbolDilation_one]
  | add x y hx hy => simp only [map_add, hx, hy]

theorem realPolynomialSymbolDilation_mul (w : σ → ℕ) (a b : ℚ) (x : F.RealPolynomialSymbol w) :
    F.realPolynomialSymbolDilation w (a * b) x =
      F.realPolynomialSymbolDilation w a (F.realPolynomialSymbolDilation w b x) := by
  induction x using TensorProduct.inductionOn with
  | tmul c x => simp only [F.realPolynomialSymbolDilation_tmul, F.polynomialSymbolDilation_mul]
  | add x y hx hy => simp only [map_add, hx, hy]

noncomputable def realPolynomialSymbolDilationHom (w : σ → ℕ) (r : ℚ) :
    F.RealPolynomialSymbolGroup w →* F.RealPolynomialSymbolGroup w :=
  NilpotentLieBCHGroup.map (F.realPolynomialSymbolDilation w r)

@[simp] theorem realPolynomialSymbolDilationHom_coord (w : σ → ℕ) (r : ℚ)
    (g : F.RealPolynomialSymbolGroup w) :
    (F.realPolynomialSymbolDilationHom w r g).coord = F.realPolynomialSymbolDilation w r g.coord := rfl

theorem realSymbolOfPolynomial_dilation (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (r : ℚ) (p : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) :
    F.realSymbolOfPolynomial b ω hF w (weightedDilation w r p) =
      F.realPolynomialSymbolDilation w r (F.realSymbolOfPolynomial b ω hF w p) := by
  apply ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr.injective
  ext z
  rw [F.realPolynomialSymbolDilation_repr, F.realSymbolOfPolynomial_coordinate,
    F.realSymbolOfPolynomial_coordinate]
  simp only [coefficients_weightedDilation, map_rat_smul, Finsupp.smul_apply,
    Rat.smul_def, Rat.cast_pow]

theorem realPolynomialSymbolHom_dilation (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (w : σ → ℕ) (r : ℚ) (g : (F.realification.adaptedPolynomialFiltration w).Group) :
    F.realPolynomialSymbolHom b ω hF w
      (NilpotentLieBCHGroup.map (F.realification.adaptedWeightedDilation w r) g) =
      F.realPolynomialSymbolDilationHom w r (F.realPolynomialSymbolHom b ω hF w g) := by
  have hmap : (NilpotentLieBCHGroup.map (F.realification.adaptedWeightedDilation w r) g :
      (F.realification.adaptedPolynomialFiltration w).Group).coord =
      F.realification.adaptedWeightedDilation w r g.coord := rfl
  apply NilpotentLieBCHGroup.ext
  rw [F.realPolynomialSymbolHom_coord, F.realPolynomialSymbolDilationHom_coord,
    F.realPolynomialSymbolHom_coord, hmap]
  simp only [F.realPolynomialSymbolMap_apply, F.realification.adaptedWeightedDilation_coe]
  apply realSymbolOfPolynomial_dilation

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

def ControlledSymbolFactorization (η : L →ₗ[ℚ] ℚ) (T : σ → ℝ)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) : Prop :=
  ∃ (m : ℕ) (E P R : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (W : LieSubalgebra ℚ F.AssociatedGraded) (v : ι → F.AssociatedGraded),
    0 < m ∧ (m : ℝ) ≤ Real.exp p ∧ E * P * R = X ∧
    F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) E ∧
    F.SymbolRationalGrid b ω hF (fun _ => 1) m R ∧
    Submodule.span ℚ (Set.range v) = W.toSubmodule ∧
    BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule ∧
    (∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (v i) j) ≤ p) ∧
    (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
      F.gradedFrequency b ω hF η x = 0) ∧
    P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) W)

theorem ControlledSymbolFactorization.mono {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF η T X p) (hpq : p ≤ q)
    (hT : ∀ i, 0 < T i) : F.ControlledSymbolFactorization b ω hF η T X q := by
  obtain ⟨m, E, P, R, W, v, hm, hmp, hprod, hE, hR, hv, hW, hh, hη, hP⟩ := h
  exact ⟨m, E, P, R, W, v, hm, hmp.trans (Real.exp_le_exp.mpr hpq), hprod,
    F.symbolSlowBound_mono b ω hF (fun _ => 1) T hT (Real.exp_le_exp.mpr hpq) E hE,
    hR, hv, hW, (fun i j => (hh i j).trans hpq), hη, hP⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def ControlledSymbolCompositionSpec (s C : ℕ) : Prop :=
  ∀ {σ ι L : Type*} [Fintype σ] [Fintype ι] [LieRing L] [LieAlgebra ℚ L]
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (H : ℕ) (p : ℝ) (_hH : 1 ≤ H) (_hp : 0 ≤ p)
    (_hι : (Fintype.card ι : ℝ) ≤ p) (_hσ : (Fintype.card σ : ℝ) ≤ p)
    (_hHp : (H : ℝ) ≤ Real.exp p)
    (_hc : ∀ i j k, RationalHeightLE (b.repr ⁅b i, b j⁆ k) H)
    (T : σ → ℝ) (_hT : ∀ i, 0 < T i) (η : L →ₗ[ℚ] ℚ)
    (l : ℕ) (_hl : 0 < l) (_hlp : (l : ℝ) ≤ Real.exp p)
    (A X R : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (_hA : F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) A)
    (_hR : F.SymbolRationalGrid b ω hF (fun _ => 1) l R)
    (_hX : F.ControlledSymbolFactorization b ω hF η T X p),
    F.ControlledSymbolFactorization b ω hF η T (A * X * R) ((p + C) ^ C)

theorem exists_controlled_symbol_composition (s : ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ControlledSymbolCompositionSpec s C := by
  obtain ⟨a, _, hslow⟩ := exists_symbol_slow_product_bound s 1 2
  obtain ⟨b, _, hgrid⟩ := exists_symbol_rational_product_bound s 2
  let P : Polynomial ℕ := Polynomial.X + (2 * Polynomial.X + Polynomial.C a) ^ a +
    (2 * Polynomial.X + Polynomial.C b) ^ b
  obtain ⟨C, hC, hfinal⟩ := exists_natPolynomial_eval_budget P
  refine ⟨C, hC, ?_⟩
  intro σ ι L _ _ _ _ F e ω hF H p hH hp hι hσ hHp hc T hT η l hl hlp A X R hA hR hX
  have hpa : 0 ≤ (2 * p + a) ^ a := by positivity
  have hpb : 0 ≤ (2 * p + b) ^ b := by positivity
  have hbound : p + (2 * p + a) ^ a + (2 * p + b) ^ b ≤ (p + C) ^ C := by
    simpa [P, Polynomial.eval₂_pow] using hfinal p hp
  have hpC : p ≤ (p + C) ^ C := by linarith
  have haC : (2 * p + a) ^ a ≤ (p + C) ^ C := by linarith
  have hbC : (2 * p + b) ^ b ≤ (p + C) ^ C := by linarith
  have h2p : 0 ≤ 2 * p := by positivity
  have hp2 : p ≤ 2 * p := by linarith
  have he2 := Real.exp_le_exp.mpr hp2
  have he : Real.exp p ≤ Real.exp ((2 * p + 2) ^ 1) := Real.exp_le_exp.mpr (by rw [pow_one]; linarith)
  obtain ⟨m, E, Q, B, Z, v, hm, hmp, hprod, hE, hB, hv, hZ, hh, hη, hQ⟩ := hX
  have hleft := hslow F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H (2 * p) hH h2p (hι.trans hp2) (hσ.trans hp2) (hHp.trans he2) hc T hT [A, E] (by simp) (by
      intro x hx
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
      rcases hx with rfl | rfl
      · exact F.symbolSlowBound_mono e ω hF (fun _ => 1) T hT he _ hA
      · exact F.symbolSlowBound_mono e ω hF (fun _ => 1) T hT he _ hE)
  have hleft' : F.SymbolSlowBound e ω hF (fun _ => 1) T (Real.exp ((2 * p + a) ^ a)) (A * E) := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hleft
  have hdenom : ((l * m : ℕ) : ℝ) ≤ Real.exp (2 * p) := by
    rw [Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p := mul_le_mul hlp hmp (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = _ := by rw [← Real.exp_add]; congr 1; ring
  obtain ⟨n, hn, hnp, _, hproducts⟩ := hgrid F e ω hF (fun _ : σ => 1) (fun _ => Nat.zero_lt_one)
    H (2 * p) hH h2p (hι.trans hp2) (hσ.trans hp2) (hHp.trans he2) hc (l * m) (Nat.mul_pos hl hm) hdenom
  have hright := hproducts [B, R] (by simp) (by
    intro x hx
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · exact F.symbolRationalGrid_mono e ω hF (fun _ => 1) hm (dvd_mul_left m l) _ hB
    · exact F.symbolRationalGrid_mono e ω hF (fun _ => 1) hl (dvd_mul_right l m) _ hR)
  have hright' : F.SymbolRationalGrid e ω hF (fun _ => 1) n (B * R) := by
    simpa only [List.prod_cons, List.prod_nil, mul_one] using hright
  refine ⟨n, A * E, Q, B * R, Z, v, hn, hnp.trans (Real.exp_le_exp.mpr hbC), ?_,
    F.symbolSlowBound_mono e ω hF (fun _ => 1) T hT (Real.exp_le_exp.mpr haC) (A * E) hleft',
    hright', hv, hZ, (fun i j => (hh i j).trans hpC), hη, hQ⟩
  calc
    (A * E) * Q * (B * R) = A * (E * Q * B) * R := by group
    _ = A * X * R := by rw [hprod]

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module
open scoped BigOperators

theorem monomialScale_const_mul {σ : Type*} (S : σ → ℝ) (c : ℝ) (α : σ →₀ ℕ) :
    monomialScale (fun i => c * S i) α =
      c ^ Finsupp.weight (fun _ => 1) α * monomialScale S α := by
  classical
  simp only [monomialScale, Finsupp.prod, mul_pow, Finset.prod_mul_distrib,
    Finset.prod_pow_eq_pow_sum, Finsupp.weight_apply, Finsupp.sum, smul_eq_mul, mul_one]

theorem monomialScale_le_exp_mul {σ : Type*} (S T : σ → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) {q : ℝ} (hq : 0 ≤ q)
    (hST : ∀ i, T i ≤ Real.exp q * S i) (α : σ →₀ ℕ) {s : ℕ}
    (hα : Finsupp.weight (fun _ => 1) α ≤ s) :
    monomialScale T α ≤ Real.exp ((s : ℝ) * q) * monomialScale S α := by
  classical
  calc
    monomialScale T α ≤ monomialScale (fun i => Real.exp q * S i) α := by
      apply Finset.prod_le_prod₀
      · intro i _
        exact pow_nonneg (hT i).le _
      · intro i _
        exact pow_le_pow_left₀ (hT i).le (hST i) _
    _ = Real.exp q ^ Finsupp.weight (fun _ => 1) α * monomialScale S α :=
      monomialScale_const_mul S (Real.exp q) α
    _ ≤ Real.exp q ^ s * monomialScale S α :=
      mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (Real.one_le_exp hq) hα)
        (monomialScale_pos S hS α).le
    _ = Real.exp ((s : ℝ) * q) * monomialScale S α := by rw [Real.exp_nat_mul]

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem symbolSlowBound_rescale (S T : σ → ℝ) (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i)
    {p q : ℝ} (hq : 0 ≤ q) (hST : ∀ i, Real.exp (-q) * T i ≤ S i)
    (E : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hE : F.SymbolSlowBound b ω hF (fun _ => 1) S (Real.exp p) E) :
    F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp (p + (s : ℝ) * q)) E := by
  have hratio (i : σ) : T i ≤ Real.exp q * S i := by
    calc
      T i = Real.exp q * (Real.exp (-q) * T i) := by
        rw [← mul_assoc, ← Real.exp_add, add_neg_cancel, Real.exp_zero, one_mul]
      _ ≤ Real.exp q * S i := mul_le_mul_of_nonneg_left (hST i) (Real.exp_pos _).le
  intro z
  apply (hE z).trans
  apply (div_le_div_iff₀ (monomialScale_pos S hS z.val.1)
    (monomialScale_pos T hT z.val.1)).mpr
  have hscale := monomialScale_le_exp_mul S T hS hT hq hratio z.val.1
    (z.property.le.trans (F.adaptedBasis_weight_le_step b ω hF z.val.2))
  calc
    Real.exp p * monomialScale T z.val.1 ≤
        Real.exp p * (Real.exp ((s : ℝ) * q) * monomialScale S z.val.1) :=
      mul_le_mul_of_nonneg_left hscale (Real.exp_pos _).le
    _ = Real.exp (p + (s : ℝ) * q) * monomialScale S z.val.1 := by
      rw [Real.exp_add, mul_assoc]

theorem ControlledSymbolFactorization.rescale {η : L →ₗ[ℚ] ℚ} {S T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF η S X p)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i)
    (hq : 0 ≤ q) (hST : ∀ i, Real.exp (-q) * T i ≤ S i) :
    F.ControlledSymbolFactorization b ω hF η T X (p + (s : ℝ) * q) := by
  obtain ⟨m, E, P, R, W, v, hm, hmp, hprod, hE, hR, hv, hW, hh, hη, hP⟩ := h
  have hpq : p ≤ p + (s : ℝ) * q := le_add_of_nonneg_right (mul_nonneg (Nat.cast_nonneg s) hq)
  exact ⟨m, E, P, R, W, v, hm, hmp.trans (Real.exp_le_exp.mpr hpq), hprod,
    F.symbolSlowBound_rescale b ω hF S T hS hT hq hST E hE,
    hR, hv, hW, (fun i j => (hh i j).trans hpq), hη, hP⟩

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

def SymbolFactorizationIn (T : σ → ℝ)
    (X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)) (p : ℝ) (l : ℕ)
    (W : LieSubalgebra ℚ F.AssociatedGraded) : Prop :=
  ∃ E P R : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
    E * P * R = X ∧ F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) E ∧
    F.SymbolRationalGrid b ω hF (fun _ => 1) l R ∧
    P.coord ∈ realificationLieSubalgebra (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) W)

theorem ControlledSymbolFactorization.exists_in {η : L →ₗ[ℚ] ℚ} {T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF η T X p) :
    ∃ (l : ℕ) (W : LieSubalgebra ℚ F.AssociatedGraded) (u : ι → F.AssociatedGraded),
      0 < l ∧ (l : ℝ) ≤ Real.exp p ∧ Submodule.span ℚ (Set.range u) = W.toSubmodule ∧
      BasisGradedSubmodule (F.associatedGradedBasis b ω hF) ω W.toSubmodule ∧
      (∀ i j, rationalLogHeight ((F.associatedGradedBasis b ω hF).repr (u i) j) ≤ p) ∧
      (∀ x ∈ W, basisGradeProjection (F.associatedGradedBasis b ω hF) ω s x = x →
        F.gradedFrequency b ω hF η x = 0) ∧
      F.SymbolFactorizationIn b ω hF T X p l W := by
  obtain ⟨l, E, P, R, W, u, hl, hlp, hprod, hE, hR, hu, hW, hh, hη, hP⟩ := h
  exact ⟨l, W, u, hl, hlp, hu, hW, hh, hη, E, P, R, hprod, hE, hR, hP⟩

theorem SymbolFactorizationIn.mono {T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.SymbolFactorizationIn b ω hF T X p l W) (hpq : p ≤ q) (hT : ∀ i, 0 < T i) :
    F.SymbolFactorizationIn b ω hF T X q l W := by
  obtain ⟨E, P, R, hprod, hE, hR, hP⟩ := h
  exact ⟨E, P, R, hprod,
    F.symbolSlowBound_mono b ω hF (fun _ => 1) T hT (Real.exp_le_exp.mpr hpq) E hE, hR, hP⟩

end Erdos3.NilpotentLieFiltration

end

section

namespace Erdos3

open Module

theorem monomialScale_div_const {σ : Type*} (S : σ → ℝ) (c : ℝ) (α : σ →₀ ℕ) :
    monomialScale (fun i => S i / c) α =
      monomialScale S α / c ^ Finsupp.weight (fun _ => 1) α := by
  calc
    _ = monomialScale (fun i => c⁻¹ * S i) α := by
      congr 1
      funext i
      simp only [div_eq_mul_inv, mul_comm]
    _ = c⁻¹ ^ Finsupp.weight (fun _ => 1) α * monomialScale S α := monomialScale_const_mul S c⁻¹ α
    _ = _ := by rw [inv_pow, div_eq_mul_inv, mul_comm]

namespace NilpotentLieFiltration

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem symbolRationalGrid_dilation_ratio (w : σ → ℕ) (D d : ℕ) (a : ℤ) (hd : 0 < d)
    (g : F.RealPolynomialSymbolGroup w) (hg : F.SymbolRationalGrid b ω hF w D g) :
    F.SymbolRationalGrid b ω hF w (D * d ^ s)
      (F.realPolynomialSymbolDilationHom w ((a : ℚ) / d) g) := by
  change (fun z => ((F.polynomialSymbolBasis b ω hF w).baseChange ℝ).repr
    (F.realPolynomialSymbolDilationHom w ((a : ℚ) / d) g).coord z) ∈ _
  simp_rw [F.realPolynomialSymbolDilationHom_coord, F.realPolynomialSymbolDilation_repr,
    Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  exact realDenominatorGrid_rational_power_scale (fun z : SymbolBasisIndex w ω => Finsupp.weight w z.val.1)
    D d s a hd (fun z => z.property.le.trans (F.adaptedBasis_weight_le_step b ω hF z.val.2)) _ hg

theorem symbolSlowBound_dilation_inverse_scale (S : σ → ℝ) (hS : ∀ i, 0 < S i)
    (p : ℝ) (r : ℚ) (hr : r ≠ 0) (E : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hE : F.SymbolSlowBound b ω hF (fun _ => 1) S (Real.exp p) E) :
    F.SymbolSlowBound b ω hF (fun _ => 1) (fun i => S i / |(r : ℝ)|) (Real.exp p)
      (F.realPolynomialSymbolDilationHom (fun _ => 1) r E) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have habs : 0 < |(r : ℝ)| := abs_pos.mpr hrR
  intro z
  rw [F.realPolynomialSymbolDilationHom_coord, F.realPolynomialSymbolDilation_repr, abs_mul, abs_pow]
  apply (mul_le_mul_of_nonneg_left (hE z) (pow_nonneg habs.le _)).trans_eq
  rw [monomialScale_div_const]
  field_simp [(monomialScale_pos S hS z.val.1).ne', habs.ne']

theorem symbolSlowBound_dilation_physical (S T : σ → ℝ)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) (p q : ℝ) (hq : 0 ≤ q)
    (r : ℚ) (hr : r ≠ 0)
    (hphysical : ∀ i, Real.exp (-q) * (|(r : ℝ)| * T i) ≤ S i)
    (E : F.RealPolynomialSymbolGroup (fun _ : σ => 1))
    (hE : F.SymbolSlowBound b ω hF (fun _ => 1) S (Real.exp p) E) :
    F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp (p + (s : ℝ) * q))
      (F.realPolynomialSymbolDilationHom (fun _ => 1) r E) := by
  have hrR : (r : ℝ) ≠ 0 := by exact_mod_cast hr
  have habs : 0 < |(r : ℝ)| := abs_pos.mpr hrR
  have hscaled := F.symbolSlowBound_dilation_inverse_scale b ω hF S hS p r hr E hE
  apply F.symbolSlowBound_rescale b ω hF (fun i => S i / |(r : ℝ)|) T
    (fun i => div_pos (hS i) habs) hT hq _ _ hscaled
  intro i
  apply (le_div_iff₀ habs).mpr
  calc
    Real.exp (-q) * T i * |(r : ℝ)| = Real.exp (-q) * (|(r : ℝ)| * T i) := by ring
    _ ≤ S i := hphysical i

end NilpotentLieFiltration
end Erdos3

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

def SymbolFastIn {σ L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (w : σ → ℕ)
    (U : LieSubalgebra ℚ (F.PolynomialSymbol w)) (g : F.RealPolynomialSymbolGroup w) : Prop :=
  g.coord ∈ realificationLieSubalgebra U

theorem SymbolFactorizationIn.exists_fast_factors {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L]
    {s : ℕ} (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    {T : σ → ℝ} {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p : ℝ} {l : ℕ}
    {W : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.SymbolFactorizationIn b ω hF T X p l W) :
    ∃ E P R : F.RealPolynomialSymbolGroup (fun _ : σ => 1),
      E * P * R = X ∧ F.SymbolSlowBound b ω hF (fun _ => 1) T (Real.exp p) E ∧
      F.SymbolRationalGrid b ω hF (fun _ => 1) l R ∧
      F.SymbolFastIn (fun _ => 1) (F.symbolPointwiseSubalgebra b ω hF (fun _ => 1) W) P := h

end Erdos3.NilpotentLieFiltration

end

end OAI
