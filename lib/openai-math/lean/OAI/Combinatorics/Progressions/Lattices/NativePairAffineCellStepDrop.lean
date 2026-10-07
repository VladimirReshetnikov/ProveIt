import OAI.Combinatorics.Progressions.Estimates.JoinedPairQuotientRefiltration

namespace OAI

universe u

section

namespace Erdos3.RationalFilteredNilmanifold

open Module VectorPolynomial
open scoped TensorProduct BigOperators

variable {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
    {s d e : ℕ} (D : RationalFilteredNilmanifold L s d)
    (E : RationalFilteredNilmanifold M s e)
    {σ τ ι : Type*}

theorem pairOrbit_substitute_log {w : σ → ℕ} {v : τ → ℕ}
    (p : D.filtration.realification.PolynomialOrbit w)
    (q : E.filtration.realification.PolynomialOrbit w)
    (f : σ → MvPolynomial τ ℚ) (hf : ∀ i, f i ∈ weightedSupportLE v (w i)) :
    (pairOrbit D E
      (D.filtration.realification.polynomialOrbitSubstitute f hf p)
      (E.filtration.realification.polynomialOrbitSubstitute f hf q)).log =
      VectorPolynomial.substitute f (pairOrbit D E p q).log := by
  simp only [pairOrbit, NilpotentLieFiltration.piRealOrbit,
    NilpotentLieFiltration.PolynomialOrbit.log, NilpotentLieFiltration.polynomialOrbitOfLog, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  cases i <;> exact VectorPolynomial.map_substitute f _ _

theorem pairOrbitSymbol_scalarAffine_substitute
    (p : D.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (q : E.filtration.realification.PolynomialOrbit (fun _ : σ => 1))
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (r : ℚ) (shift : σ → ℚ) :
    pairOrbitSymbol D E
      (D.filtration.realification.polynomialOrbitSubstitute
        (scalarAffinePolynomial r shift) (scalarAffinePolynomial_support r shift) p)
      (E.filtration.realification.polynomialOrbitSubstitute
        (scalarAffinePolynomial r shift) (scalarAffinePolynomial_support r shift) q) b ω hF =
      (pi (pairModels D E)).filtration.realPolynomialSymbolDilationHom (fun _ => 1) r
        (pairOrbitSymbol D E p q b ω hF) := by
  apply NilpotentLieBCHGroup.ext
  change (pi (pairModels D E)).filtration.realSymbolOfPolynomial b ω hF (fun _ => 1)
      (pairOrbit D E _ _).log =
    (pi (pairModels D E)).filtration.realPolynomialSymbolDilation (fun _ => 1) r
      ((pi (pairModels D E)).filtration.realSymbolOfPolynomial b ω hF (fun _ => 1)
        (pairOrbit D E p q).log)
  rw [pairOrbit_substitute_log, VectorPolynomial.substitute_scalarAffinePolynomial]
  apply NilpotentLieFiltration.realSymbolOfPolynomial_affine
  · exact fun _ => Nat.zero_lt_one
  · exact (pairOrbit D E p q).adapted

variable [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
    [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
    [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]

theorem pairOrbitSymbol_scalarAffinePullback
    (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (r : ℚ) (shift : σ → ℚ) :
    pairOrbitSymbol D E (V.scalarAffinePullback r shift).orbit
      (W.scalarAffinePullback r shift).orbit b ω hF =
      (pi (pairModels D E)).filtration.realPolynomialSymbolDilationHom (fun _ => 1) r
        (pairOrbitSymbol D E V.orbit W.orbit b ω hF) :=
  pairOrbitSymbol_scalarAffine_substitute D E V.orbit W.orbit b ω hF r shift

theorem pairOrbitSymbol_scalarAffinePullback_inverse_stride
    (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ (PairAlgebra L M)) (ω : ι → ℕ)
    (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
      Submodule.span ℚ (b '' {i | k ≤ ω i}))
    (Q : ℕ) (hQ : 0 < Q) (shift : σ → ℚ) :
    (pi (pairModels D E)).filtration.realPolynomialSymbolDilationHom (fun _ => 1) ((Q : ℚ)⁻¹)
      (pairOrbitSymbol D E (V.scalarAffinePullback Q shift).orbit
        (W.scalarAffinePullback Q shift).orbit b ω hF) =
      pairOrbitSymbol D E V.orbit W.orbit b ω hF := by
  rw [pairOrbitSymbol_scalarAffinePullback]
  apply NilpotentLieBCHGroup.ext
  simp only [NilpotentLieFiltration.realPolynomialSymbolDilationHom_coord,
    ← NilpotentLieFiltration.realPolynomialSymbolDilation_mul,
    inv_mul_cancel₀ (show (Q : ℚ) ≠ 0 by exact_mod_cast hQ.ne'),
    NilpotentLieFiltration.realPolynomialSymbolDilation_one]

end Erdos3.RationalFilteredNilmanifold

end

section

namespace Erdos3.NilpotentLieFiltration

open Module

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s : ℕ}
  (F : NilpotentLieFiltration L s) (b : Basis ι ℚ L) (ω : ι → ℕ)
  (hF : ∀ j, F.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))

theorem ControlledSymbolFactorizationAtFast.dilate_ratio
    {η : L →ₗ[ℚ] ℚ} {S T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q r : ℝ}
    {U : LieSubalgebra ℚ F.AssociatedGraded}
    (h : F.ControlledSymbolFactorizationAtFast b ω hF η S X p U)
    (a : ℤ) (d : ℕ) (ha : a ≠ 0) (hd : 0 < d)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hdr : (d : ℝ) ≤ Real.exp r)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / d : ℚ) : ℝ)| * T i) ≤ S i) :
    F.ControlledSymbolFactorizationAtFast b ω hF η T
      (F.realPolynomialSymbolDilationHom (fun _ => 1) ((a : ℚ) / d) X)
      (p + (s : ℝ) * (q + r)) U := by
  obtain ⟨m, E, P, R, v, hm, hmp, hprod, hE, hR, hv, hgraded, hh, hzero, hP⟩ := h
  have hf : F.SymbolFactorizationIn b ω hF S X p m U :=
    ⟨E, P, R, hprod, hE, hR, hP⟩
  have hcost : p + (s : ℝ) * q ≤ p + (s : ℝ) * (q + r) := by
    have := mul_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ s) hr
    nlinarith
  have hp : p ≤ p + (s : ℝ) * (q + r) := le_add_of_nonneg_right (by positivity)
  obtain ⟨E', P', R', hprod', hE', hR', hP'⟩ :=
    (SymbolFactorizationIn.dilate_ratio F b ω hF hf a d ha hd hS hT hq hphysical).mono
      F b ω hF hcost hT
  refine ⟨m * d ^ s, E', P', R', v, Nat.mul_pos hm (pow_pos hd _), ?_, hprod',
    hE', hR', hv, hgraded, (fun i j => (hh i j).trans hp), hzero, hP'⟩
  calc
    ((m * d ^ s : ℕ) : ℝ) = (m : ℝ) * (d : ℝ) ^ s := by push_cast; rfl
    _ ≤ Real.exp p * (Real.exp r) ^ s :=
      mul_le_mul hmp (pow_le_pow_left₀ (Nat.cast_nonneg d) hdr s)
        (by positivity) (Real.exp_pos p).le
    _ = Real.exp (p + (s : ℝ) * r) := by rw [← Real.exp_nat_mul, Real.exp_add]
    _ ≤ Real.exp (p + (s : ℝ) * (q + r)) := by
      apply Real.exp_le_exp.mpr
      have := mul_nonneg (Nat.cast_nonneg s : (0 : ℝ) ≤ s) hq
      nlinarith

theorem ControlledSymbolFactorization.dilate_ratio
    {η : L →ₗ[ℚ] ℚ} {S T : σ → ℝ}
    {X : F.RealPolynomialSymbolGroup (fun _ : σ => 1)} {p q r : ℝ}
    (h : F.ControlledSymbolFactorization b ω hF η S X p)
    (a : ℤ) (d : ℕ) (ha : a ≠ 0) (hd : 0 < d)
    (hS : ∀ i, 0 < S i) (hT : ∀ i, 0 < T i) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hdr : (d : ℝ) ≤ Real.exp r)
    (hphysical : ∀ i, Real.exp (-q) * (|(((a : ℚ) / d : ℚ) : ℝ)| * T i) ≤ S i) :
    F.ControlledSymbolFactorization b ω hF η T
      (F.realPolynomialSymbolDilationHom (fun _ => 1) ((a : ℚ) / d) X)
      (p + (s : ℝ) * (q + r)) := by
  obtain ⟨U, hU⟩ := h.exists_fastWitness F b ω hF
  obtain ⟨m, E, P, R, v, hdata⟩ :=
    hU.dilate_ratio F b ω hF a d ha hd hS hT hq hr hdr hphysical
  exact ⟨m, E, P, R, U, v, hdata⟩

end Erdos3.NilpotentLieFiltration

namespace Erdos3.RationalFilteredNilmanifold.Niltest

open Module
open scoped TensorProduct

variable {σ ι L : Type*} [LieRing L] [LieAlgebra ℚ L] {s d : ℕ}
  [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
  {D : RationalFilteredNilmanifold L s d}

theorem scalarAffineCell_controlled_factorization_to_original
    (T : D.Niltest (fun _ : σ => 1))
    (b : Basis ι ℚ L) (ω : ι → ℕ)
    (hF : ∀ j, D.filtration.layer j = Submodule.span ℚ (b '' {i | j ≤ ω i}))
    (Q : ℕ) (hQ : 0 < Q) (shift : σ → ℚ)
    {η : L →ₗ[ℚ] ℚ} {S H : σ → ℝ} {p q r : ℝ}
    (h : D.filtration.ControlledSymbolFactorization b ω hF η S
      ((T.scalarAffinePullback Q shift).symbol b ω hF) p)
    (hS : ∀ i, 0 < S i) (hH : ∀ i, 0 < H i) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hQr : (Q : ℝ) ≤ Real.exp r)
    (hphysical : ∀ i, Real.exp (-q) * (H i / (Q : ℝ)) ≤ S i) :
    D.filtration.ControlledSymbolFactorization b ω hF η H (T.symbol b ω hF)
      (p + (s : ℝ) * (q + r)) := by
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hratio (i : σ) :
      Real.exp (-q) * (|(((1 : ℚ) / Q : ℚ) : ℝ)| * H i) ≤ S i := by
    convert hphysical i using 1
    push_cast
    rw [abs_div, abs_one, abs_of_pos hQreal]
    ring
  have hf := h.dilate_ratio D.filtration b ω hF 1 Q (by norm_num) hQ hS hH hq hr hQr hratio
  rw [Int.cast_one, one_div,
    T.scalarAffinePullback_symbol_inverse_stride b ω hF Q hQ shift] at hf
  exact hf

end Erdos3.RationalFilteredNilmanifold.Niltest

end

section

namespace Erdos3

open Module RationalFilteredNilmanifold
open scoped TensorProduct BigOperators

theorem exists_native_pair_affine_cell_step_drop (s : ℕ) (hs : 1 ≤ s) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {σ : Type*} [Fintype σ] [DecidableEq σ]
      {L M : Type u} [LieRing L] [LieAlgebra ℚ L] [LieRing M] [LieAlgebra ℚ M]
      {d e : ℕ}
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      [TopologicalSpace (ℝ ⊗[ℚ] M)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] M)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] M)] [T2Space (ℝ ⊗[ℚ] M)]
      (D : RationalFilteredNilmanifold L s d) (E : RationalFilteredNilmanifold M s e)
      (V : D.Niltest (fun _ : σ => 1)) (W : E.Niltest (fun _ : σ => 1))
      {p q r : ℝ} (_hp : 2 ≤ p) (_hq : 0 ≤ q) (_hr : 0 ≤ r)
      (_hV : V.ComplexityLE p) (_hW : W.ComplexityLE p)
      (Q : ℕ) (_hQ : 0 < Q) (_hQr : (Q : ℝ) ≤ Real.exp r) (shift : σ → ℤ)
      (η : L →ₗ[ℚ] ℚ) (θ : M →ₗ[ℚ] ℚ)
      (_hηheight : ∀ i, rationalLogHeight (η (D.basis i)) ≤ p)
      (_hθheight : ∀ i, rationalLogHeight (θ (E.basis i)) ≤ p)
      (_hη : ∀ z, z ∈ D.filtration.realification.subgroup s → ∀ x,
        V.observable (z • x) = CircleFourier.character
          ((realifyFunctional η z.coord : ℝ) : CircleFourier.Circle) * V.observable x)
      (_hθ : ∀ z, z ∈ E.filtration.realification.subgroup s → ∀ x,
        W.observable (z • x) = CircleFourier.character
          ((realifyFunctional θ z.coord : ℝ) : CircleFourier.Circle) * W.observable x)
      (origin : σ → ℤ) (lengths : σ → ℕ) (H : σ → ℝ)
      (_hlen : ∀ i, 0 < lengths i) (_hH : ∀ i, 0 < H i)
      (_hσ : (Fintype.card σ : ℝ) ≤ p)
      (_hlarge : ∀ i, Real.exp ((p + C) ^ C) ≤ (lengths i : ℝ))
      (_hphysical : ∀ i, Real.exp (-q) * (H i / (Q : ℝ)) ≤ lengths i)
      (_hbias : Real.exp (-p) ≤ ‖𝔼 x ∈ translatedIntegerBox origin lengths,
        V.eval (fun i => (Q : ℤ) * x i + shift i) *
          W.eval (fun i => (Q : ℤ) * x i + shift i)‖),
      ∃ (b : Basis (Fin (finrank ℚ (PairAlgebra L M))) ℚ (PairAlgebra L M))
        (ω : Fin (finrank ℚ (PairAlgebra L M)) → ℕ)
        (hF : ∀ k, (pi (pairModels D E)).filtration.layer k =
          Submodule.span ℚ (b '' {i | k ≤ ω i})),
        (∀ i j, rationalLogHeight ((pi (pairModels D E)).basis.repr (b i) j) ≤ (p + C) ^ C) ∧
        (pi (pairModels D E)).filtration.ControlledSymbolFactorization b ω hF
          (pairFrequency η θ) H (pairOrbitSymbol D E V.orbit W.orbit b ω hF)
          ((p + C) ^ C + (s : ℝ) * (q + r)) := by
  obtain ⟨C, hC, hstep⟩ := exists_native_pair_positive_step_drop s hs
  refine ⟨C, hC, ?_⟩
  intro σ _ _ L M _ _ _ _ d e _ _ _ _ _ _ _ _ D E V W p q r hp hq hr hV hW
    Q hQ hQr shift η θ hηheight hθheight hη hθ origin lengths H hlen hH hσ hlarge hphysical hbias
  let V' := V.scalarAffinePullback (Q : ℚ) (fun i => (shift i : ℚ))
  let W' := W.scalarAffinePullback (Q : ℚ) (fun i => (shift i : ℚ))
  have hV' : V'.ComplexityLE p := hV
  have hW' : W'.ComplexityLE p := hW
  obtain ⟨b, ω, hF, hb, hfactor⟩ := hstep D E V' W' hp hV' hW'
  have hevalV (x : σ → ℤ) : V'.eval x =
      V.eval (fun i => (Q : ℤ) * x i + shift i) := by
    exact_mod_cast V.scalarAffinePullback_eval_integer (Q : ℤ) shift x
  have hevalW (x : σ → ℤ) : W'.eval x =
      W.eval (fun i => (Q : ℤ) * x i + shift i) := by
    exact_mod_cast W.scalarAffinePullback_eval_integer (Q : ℤ) shift x
  have hc := hfactor η θ hηheight hθheight hη hθ origin lengths hlen hσ hlarge
    (by simpa only [hevalV, hevalW] using hbias)
  have hQreal : (0 : ℝ) < Q := by exact_mod_cast hQ
  have hratio (i : σ) :
      Real.exp (-q) * (|(((1 : ℚ) / Q : ℚ) : ℝ)| * H i) ≤ (lengths i : ℝ) := by
    convert hphysical i using 1
    push_cast
    rw [abs_div, abs_one, abs_of_pos hQreal]
    ring
  have hf := hc.dilate_ratio (pi (pairModels D E)).filtration b ω hF 1 Q
    (by norm_num) hQ (fun i => by exact_mod_cast hlen i) hH hq hr hQr hratio
  refine ⟨b, ω, hF, hb, ?_⟩

  simpa only [Int.cast_one, one_div, V', W',
    pairOrbitSymbol_scalarAffinePullback_inverse_stride D E V W b ω hF Q hQ
      (fun i => (shift i : ℚ))] using hf

end Erdos3

end

end OAI
