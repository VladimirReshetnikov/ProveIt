import OAI.Combinatorics.Progressions.Lattices.RealSymbolAffine

namespace OAI

section

namespace Erdos3.VectorPolynomial

variable {σ V : Type*} [AddCommGroup V] [Module ℚ V]

theorem eval_rational_affine (w : σ → ℕ) (r : ℚ) (h x : σ → ℚ)
    (p : VectorPolynomial σ ℚ V) :
    eval x (weightedDilation w r (translate h p)) =
      eval (fun i => r ^ w i * x i + h i) p := by
  rw [eval_weightedDilation, eval_translate]

end Erdos3.VectorPolynomial

namespace Erdos3.NilpotentLieFiltration

open Module VectorPolynomial
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
    (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem SymbolFactorizationIn.dilate_ratio
    {S T : σ → ℝ} {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)}
    {p q : ℝ} {D : ℕ} {U : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.SymbolFactorizationIn b ω hF S X p D U)
    (a : ℤ) (d : ℕ) (ha : a ≠ 0) (hd : 0 < d)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) (hq : 0 ≤ q)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / d : ℚ) : ℝ)| * T i) ≤ S i) :
    F.SymbolFactorizationIn b ω hF T
      (F.realPolynomialSymbolDilationHom (fun _ => 1) ((a : ℚ) / d) X)
      (p + (s : ℝ) * q) (D * d ^ s) U := by
  have hr : (a : ℚ) / d ≠ 0 := div_ne_zero (by exact_mod_cast ha) (by exact_mod_cast hd.ne')
  let φ := F.realPolynomialSymbolDilationHom (fun _ : σ => 1) ((a : ℚ) / d)
  obtain ⟨E, P, R, hprod, hE, hR, hP⟩ := h
  refine ⟨φ E, φ P, φ R, ?_, ?_, ?_, ?_⟩
  · simpa only [map_mul] using congrArg φ hprod
  · exact F.symbolSlowBound_dilation_physical b ω hF S T hS hT p q hq _ hr hphysical E hE
  · exact F.symbolRationalGrid_dilation_ratio b ω hF (fun _ => 1) D d a hd R hR
  · exact F.realSymbolDilation_mem_pointwise b ω hF (fun _ => 1) U _ P.coord hP

theorem symbolFactorizationIn_affine_transport
    {S T : σ → ℝ} {p q : ℝ} {D : ℕ} {U : LieSubalgebra ℚ F.AssociatedGraded}
    (f : VectorPolynomial σ ℚ (ℝ ⊗[ℚ] L)) (hf : F.realification.Adapted (fun _ => 1) f)
    (h : F.SymbolFactorizationIn b ω hF S
      ⟨F.realSymbolOfPolynomial b ω hF (fun _ => 1) f⟩ p D U)
    (a : ℤ) (d : ℕ) (ha : a ≠ 0) (hd : 0 < d) (shift : σ → ℚ)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) (hq : 0 ≤ q)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / d : ℚ) : ℝ)| * T i) ≤ S i) :
    F.SymbolFactorizationIn b ω hF T
      ⟨F.realSymbolOfPolynomial b ω hF (fun _ => 1)
        (weightedDilation (fun _ => 1) ((a : ℚ) / d) (translate shift f))⟩
      (p + (s : ℝ) * q) (D * d ^ s) U := by
  have hsymbol : (⟨F.realSymbolOfPolynomial b ω hF (fun _ => 1)
      (weightedDilation (fun _ => 1) ((a : ℚ) / d) (translate shift f))⟩ :
      F.RealPolynomialSymbolGroup (fun _ : σ => 1)) =
      F.realPolynomialSymbolDilationHom (fun _ => 1) ((a : ℚ) / d)
        ⟨F.realSymbolOfPolynomial b ω hF (fun _ => 1) f⟩ := by
    apply NilpotentLieBCHGroup.ext
    simp only [F.realPolynomialSymbolDilationHom_coord]
    apply realSymbolOfPolynomial_affine
    · exact fun _ => Nat.zero_lt_one
    · exact hf
  rw [hsymbol]
  exact SymbolFactorizationIn.dilate_ratio F b ω hF h a d ha hd hS hT hq hphysical

end Erdos3.NilpotentLieFiltration

end

end OAI
