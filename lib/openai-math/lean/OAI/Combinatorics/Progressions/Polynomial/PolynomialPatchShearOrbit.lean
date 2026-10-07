/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.MvPolynomial
import Mathlib.Algebra.MvPolynomial.PDeriv
import OAI.Combinatorics.Progressions.Nilpotent.NiltestBasepointNormalization
import OAI.Combinatorics.Progressions.Polynomial.MajorTranslationPolynomialSymbolDegree

namespace OAI

section

namespace Erdos3

open MvPolynomial

variable {σ R : Type*} [CommRing R]

noncomputable def polynomialSubstitutionPoint
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (x : σ → R) : σ → R :=
  fun i => aeval x (F (X i))

theorem polynomialSubstitutionPoint_aeval
    (F : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (x : σ → R) (P : MvPolynomial σ R) :
    aeval (polynomialSubstitutionPoint F x) P = aeval x (F P) := by
  conv_rhs => rw [MvPolynomial.aeval_unique F, MvPolynomial.comp_aeval_apply]
  rfl

theorem polynomialSubstitutionPoint_comp
    (F G : MvPolynomial σ R →ₐ[R] MvPolynomial σ R) (x : σ → R) :
    polynomialSubstitutionPoint (F.comp G) x =
      polynomialSubstitutionPoint G (polynomialSubstitutionPoint F x) := by
  funext i
  exact (polynomialSubstitutionPoint_aeval F x (G (X i))).symm

noncomputable def polynomialPointEquiv
    (e : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) : Equiv.Perm (σ → R) where
  toFun := polynomialSubstitutionPoint e.symm.toAlgHom
  invFun := polynomialSubstitutionPoint e.toAlgHom
  left_inv x := by
    funext i
    change aeval (polynomialSubstitutionPoint e.symm.toAlgHom x) (e (X i)) = x i
    rw [polynomialSubstitutionPoint_aeval]
    change aeval x (e.symm (e (X i))) = x i
    rw [e.symm_apply_apply, aeval_X]
  right_inv x := by
    funext i
    change aeval (polynomialSubstitutionPoint e.toAlgHom x) (e.symm (X i)) = x i
    rw [polynomialSubstitutionPoint_aeval]
    change aeval x (e (e.symm (X i))) = x i
    rw [e.apply_symm_apply, aeval_X]

theorem polynomialPointEquiv_apply
    (e : MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) (x : σ → R) (i : σ) :
    polynomialPointEquiv e x i = aeval x (e.symm (X i)) := rfl

noncomputable def polynomialPointAction :
    (MvPolynomial σ R ≃ₐ[R] MvPolynomial σ R) →* Equiv.Perm (σ → R) where
  toFun := polynomialPointEquiv
  map_one' := by
    ext x i
    change aeval x (X i) = x i
    exact aeval_X x i
  map_mul' e f := by
    ext x i
    change aeval x (f.symm (e.symm (X i))) =
      aeval (polynomialSubstitutionPoint f.symm.toAlgHom x) (e.symm (X i))
    exact (polynomialSubstitutionPoint_aeval f.symm.toAlgHom x (e.symm (X i))).symm

noncomputable def weightedLoweringPointAction (w : σ → ℕ) :
    WeightedLoweringAut w R →* Equiv.Perm (σ → R) :=
  polynomialPointAction.comp (weightedLoweringSubgroup w).subtype

theorem polynomial_map_aeval {S : Type*} [CommRing S] (f : R →+* S)
    (x : σ → R) (P : MvPolynomial σ R) :
    aeval (fun i => f (x i)) (MvPolynomial.map f P) = f (aeval x P) := by
  simpa only [MvPolynomial.aeval_eq_eval, Function.comp_def] using
    (MvPolynomial.map_eval f x P).symm

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*} {w : σ → ℕ}

theorem integerCoefficientPolynomials_aeval {P : MvPolynomial σ ℚ}
    (hP : P ∈ integerCoefficientPolynomials σ) (b : σ → ℤ) :
    ∃ z : ℤ, aeval (fun i => (b i : ℚ)) P = (z : ℚ) := by
  obtain ⟨Q, rfl⟩ := (mem_integerCoefficientPolynomials P).mp hP
  exact ⟨aeval b Q, polynomial_map_aeval (Int.castRingHom ℚ) b Q⟩

theorem integerTupleRatCast_injective :
    Function.Injective (fun b : σ → ℤ => fun i => (b i : ℚ)) := by
  intro b c h
  funext i
  have hi : (b i : ℚ) = (c i : ℚ) := congrFun h i
  exact_mod_cast hi

noncomputable def integerWeightedLoweringPoint (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) (b : σ → ℤ) : σ → ℤ :=
  fun i => Classical.choose (integerCoefficientPolynomials_aeval
    ((integerWeightedLoweringSubgroup w).inv_mem he i) b)

theorem integerWeightedLoweringPoint_cast (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) (b : σ → ℤ) :
    (fun i => (integerWeightedLoweringPoint e he b i : ℚ)) =
      weightedLoweringPointAction w e (fun i => (b i : ℚ)) := by
  funext i
  exact (Classical.choose_spec (integerCoefficientPolynomials_aeval
    ((integerWeightedLoweringSubgroup w).inv_mem he i) b)).symm

theorem integerWeightedLoweringPoint_inv (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) (b : σ → ℤ) :
    integerWeightedLoweringPoint e⁻¹ ((integerWeightedLoweringSubgroup w).inv_mem he)
      (integerWeightedLoweringPoint e he b) = b := by
  apply integerTupleRatCast_injective
  change (fun i => (integerWeightedLoweringPoint e⁻¹ _ (integerWeightedLoweringPoint e he b) i : ℚ)) =
    (fun i => (b i : ℚ))
  rw [integerWeightedLoweringPoint_cast, integerWeightedLoweringPoint_cast, map_inv]
  exact (weightedLoweringPointAction w e).symm_apply_apply _

noncomputable def integerWeightedLoweringPointEquiv (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) : Equiv.Perm (σ → ℤ) where
  toFun := integerWeightedLoweringPoint e he
  invFun := integerWeightedLoweringPoint e⁻¹ ((integerWeightedLoweringSubgroup w).inv_mem he)
  left_inv := integerWeightedLoweringPoint_inv e he
  right_inv b := by
    apply integerTupleRatCast_injective
    change (fun i => (integerWeightedLoweringPoint e he (integerWeightedLoweringPoint e⁻¹ _ b) i : ℚ)) =
      (fun i => (b i : ℚ))
    rw [integerWeightedLoweringPoint_cast, integerWeightedLoweringPoint_cast, map_inv]
    exact (weightedLoweringPointAction w e).apply_symm_apply _

theorem integerWeightedLoweringPointEquiv_cast (e : WeightedLoweringAut w ℚ)
    (he : e ∈ integerWeightedLoweringSubgroup w) (b : σ → ℤ) :
    (fun i => (integerWeightedLoweringPointEquiv e he b i : ℚ)) =
      weightedLoweringPointAction w e (fun i => (b i : ℚ)) :=
  integerWeightedLoweringPoint_cast e he b

end Erdos3

end

section

namespace Erdos3

open MvPolynomial Module

variable {σ : Type*} [Fintype σ] {w : σ → ℕ}

theorem polynomialShear_integral_iff (D : PolynomialShearLieAlgebra w ℚ) :
    (∀ i, D.val (X i) ∈ integerCoefficientPolynomials σ) ↔
      ∀ a : PolynomialShearIndex w, ∃ z : ℤ, (polynomialShearBasis (R := ℚ) w).repr D a = (z : ℚ) := by
  constructor
  · intro h a
    exact (mem_integerCoefficientPolynomials_iff _).mp (h a.1) a.2.val
  · intro h i
    apply (mem_integerCoefficientPolynomials_iff _).mpr
    intro a
    by_cases ha : Finsupp.weight w a + 1 ≤ w i
    · exact h ⟨i, a, ha⟩
    · refine ⟨0, ?_⟩
      apply not_ne_iff.mp
      intro hc
      apply ha
      exact D.property i (MvPolynomial.mem_support_iff.mpr hc)

variable [Fintype (PolynomialShearIndex w)]

theorem polynomialShear_integralVector_iff (D : PolynomialShearLieAlgebra w ℚ) :
    (∀ i, D.val (X i) ∈ integerCoefficientPolynomials σ) ↔
      IntegralVector ((polynomialShearBasis (R := ℚ) w).equivFun D) := by
  rw [polynomialShear_integral_iff]
  constructor
  · intro h
    choose z hz using h
    exact ⟨z, hz⟩
  · rintro ⟨z, hz⟩ a
    exact ⟨z a, hz a⟩

theorem polynomialShear_denominatorGrid_iff (B : ℕ) (D : PolynomialShearLieAlgebra w ℚ) :
    (polynomialShearBasis (R := ℚ) w).equivFun D ∈ denominatorGrid B ↔
      ∀ i, ((B : ℚ) • D).val (X i) ∈ integerCoefficientPolynomials σ := by
  change IntegralVector ((B : ℚ) • (polynomialShearBasis (R := ℚ) w).equivFun D) ↔ _
  rw [← map_smul]
  exact (polynomialShear_integralVector_iff _).symm

theorem polynomialShear_scaledGrid_normalize (B : ℕ) (hB : 0 < B)
    (D : PolynomialShearLieAlgebra w ℚ)
    (hD : (polynomialShearBasis (R := ℚ) w).equivFun D ∈ scaledIntegerGrid B) :
    ∀ i, ((B : ℚ)⁻¹ • D).val (X i) ∈ integerCoefficientPolynomials σ := by
  obtain ⟨z, hz⟩ := hD
  apply (polynomialShear_integralVector_iff _).mpr
  have hBq : (B : ℚ) ≠ 0 := by exact_mod_cast hB.ne'
  have hv : (polynomialShearBasis (R := ℚ) w).equivFun ((B : ℚ)⁻¹ • D) = fun i => (z i : ℚ) := by
    rw [map_smul, hz, smul_smul, inv_mul_cancel₀ hBq, one_smul]
  exact ⟨z, congrFun hv⟩

end Erdos3

end

section

namespace Erdos3

open MvPolynomial Module

variable {σ : Type*} {w : σ → ℕ}

theorem polynomialShearMonomial_pderiv (a : PolynomialShearIndex w) :
    (polynomialShearMonomial (R := ℚ) w a).val =
      monomial a.2.val (1 : ℚ) • pderiv a.1 := by
  classical
  apply MvPolynomial.derivation_ext
  intro i
  rw [polynomialShearMonomial_X]
  change (if i = a.1 then monomial a.2.val (1 : ℚ) else 0) =
    monomial a.2.val (1 : ℚ) * pderiv a.1 (X i)
  by_cases h : i = a.1
  · subst i
    simp
  · simp [h]

theorem polynomialShearMonomial_monomial (a : PolynomialShearIndex w)
    (b : σ →₀ ℕ) (c : ℚ) :
    (polynomialShearMonomial (R := ℚ) w a).val (monomial b c) =
      monomial (a.2.val + (b - Finsupp.single a.1 1)) (c * b a.1) := by
  rw [polynomialShearMonomial_pderiv]
  change monomial a.2.val (1 : ℚ) * pderiv a.1 (monomial b c) = _
  rw [pderiv_monomial, monomial_mul_monomial, one_mul]

theorem polynomialShearMonomial_bracket_X [DecidableEq σ] (a b : PolynomialShearIndex w) (i : σ) :
    (⁅polynomialShearMonomial (R := ℚ) w a, polynomialShearMonomial w b⁆).val (X i) =
      (if i = b.1 then monomial (a.2.val + (b.2.val - Finsupp.single a.1 1)) (b.2.val a.1 : ℚ) else 0) -
      (if i = a.1 then monomial (b.2.val + (a.2.val - Finsupp.single b.1 1)) (a.2.val b.1 : ℚ) else 0) := by
  classical
  change ⁅(polynomialShearMonomial (R := ℚ) w a).val,
    (polynomialShearMonomial (R := ℚ) w b).val⁆ (X i) = _
  rw [Derivation.commutator_apply, polynomialShearMonomial_X, polynomialShearMonomial_X]
  split_ifs <;> simp only [map_zero, polynomialShearMonomial_monomial, one_mul]

noncomputable def polynomialShearBracketCoefficient (a b c : PolynomialShearIndex w) : ℤ := by
  classical
  exact (if c.1 = b.1 then
      if a.2.val + (b.2.val - Finsupp.single a.1 1) = c.2.val then (b.2.val a.1 : ℤ) else 0 else 0) -
    (if c.1 = a.1 then
      if b.2.val + (a.2.val - Finsupp.single b.1 1) = c.2.val then (a.2.val b.1 : ℤ) else 0 else 0)

variable [Fintype σ]

theorem polynomialShear_structureConstants (a b c : PolynomialShearIndex w) :
    lieStructureConstants (polynomialShearBasis w) a b c =
      (polynomialShearBracketCoefficient a b c : ℚ) := by
  classical
  rw [lieStructureConstants, polynomialShearBasis_repr,
    polynomialShearBasis_eq_monomial, polynomialShearBasis_eq_monomial,
    polynomialShearMonomial_bracket_X, coeff_sub]
  simp only [polynomialShearBracketCoefficient, Int.cast_sub, Int.cast_ite,
    Int.cast_natCast, Int.cast_zero]
  split_ifs <;> simp_all [coeff_monomial]

omit [Fintype σ] in
theorem polynomialShearBracketCoefficient_natAbs_le (s : ℕ)
    (hpos : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ s) (a b c : PolynomialShearIndex w) :
    (polynomialShearBracketCoefficient a b c).natAbs ≤ 2 * s := by
  classical
  have ha : a.2.val b.1 ≤ s := (Finsupp.le_weight w (hpos b.1).ne' a.2.val).trans
    ((Nat.le_add_right _ 1).trans (a.2.property.trans (hw a.1)))
  have hb : b.2.val a.1 ≤ s := (Finsupp.le_weight w (hpos a.1).ne' b.2.val).trans
    ((Nat.le_add_right _ 1).trans (b.2.property.trans (hw b.1)))
  unfold polynomialShearBracketCoefficient
  have hleft : (if c.1 = b.1 then
      if a.2.val + (b.2.val - Finsupp.single a.1 1) = c.2.val then (b.2.val a.1 : ℤ) else 0 else 0).natAbs ≤ s := by
    split_ifs <;> simp_all
  have hright : (if c.1 = a.1 then
      if b.2.val + (a.2.val - Finsupp.single b.1 1) = c.2.val then (a.2.val b.1 : ℤ) else 0 else 0).natAbs ≤ s := by
    split_ifs <;> simp_all
  exact (Int.natAbs_sub_le _ _).trans ((Nat.add_le_add hleft hright).trans_eq (by omega))

theorem polynomialShear_structureConstants_height (s : ℕ)
    (hpos : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ s) (a b c : PolynomialShearIndex w) :
    RationalHeightLE (lieStructureConstants (polynomialShearBasis w) a b c) (2 * s + 1) := by
  rw [polynomialShear_structureConstants]
  constructor
  · simpa using (polynomialShearBracketCoefficient_natAbs_le s hpos hw a b c).trans
      (Nat.le_succ (2 * s))
  · simp

end Erdos3

end

section

namespace Erdos3

open MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*}

noncomputable def polynomialShearLattice (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s) :
    Subgroup (polynomialShearFiltration w s hw).Group :=
  (integerWeightedLoweringSubgroup w).comap (polynomialShearBCHEquiv w s hw).toMonoidHom

theorem mem_polynomialShearLattice (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)
    (g : (polynomialShearFiltration w s hw).Group) :
    g ∈ polynomialShearLattice w s hw ↔
      polynomialShearExpAut g.coord ∈ integerWeightedLoweringSubgroup w := Iff.rfl

variable [Fintype σ] {w : σ → ℕ} [Fintype (PolynomialShearIndex w)]

theorem polynomialShearLattice_inner_grid (s : ℕ) (hw : ∀ i, w i ≤ s) :
    scaledIntegerGrid s.factorial ⊆
      bchSubgroupCoordinates (polynomialShearBasis w) (polynomialShearLattice w s hw) := by
  intro x hx
  let D := (polynomialShearBasis (R := ℚ) w).equivFun.symm x
  have hD : (polynomialShearBasis (R := ℚ) w).equivFun D ∈ scaledIntegerGrid s.factorial := by
    simpa only [D, LinearEquiv.apply_symm_apply] using hx
  have hI := polynomialShear_scaledGrid_normalize s.factorial (Nat.factorial_pos s) D hD
  have he := polynomialShear_factorial_exp_integral s hw ((s.factorial : ℚ)⁻¹ • D) hI
  have hc : (s.factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero s)
  rw [smul_smul, mul_inv_cancel₀ hc, one_smul] at he
  exact he

theorem polynomialShearLattice_outer_grid (s : ℕ) (hw : ∀ i, w i ≤ s) :
    bchSubgroupCoordinates (polynomialShearBasis w) (polynomialShearLattice w s hw) ⊆
      denominatorGrid s.factorial := by
  intro x hx
  let D := (polynomialShearBasis (R := ℚ) w).equivFun.symm x
  have hE : polynomialShearExpAut D ∈ integerWeightedLoweringSubgroup w := hx
  have hI (i : σ) := polynomialShear_factorial_log_integral s hw (polynomialShearExpAut D) hE i
  simp only [polynomialShearLog_exp] at hI
  have h := (polynomialShear_denominatorGrid_iff s.factorial D).mpr hI
  simpa only [D, LinearEquiv.apply_symm_apply] using h

noncomputable def polynomialShearRealLattice (s : ℕ) (hw : ∀ i, w i ≤ s) :
    Subgroup (polynomialShearFiltration w s hw).realification.Group :=
  (polynomialShearLattice w s hw).map NilpotentLieBCHGroup.realificationHom

variable [TopologicalSpace (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]
  [T2Space (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ)]

theorem polynomialShearRealLattice_closed_discrete (s : ℕ) (hw : ∀ i, w i ≤ s) :
    IsClosed (polynomialShearRealLattice s hw : Set (polynomialShearFiltration w s hw).realification.Group) ∧
      IsDiscrete (polynomialShearRealLattice s hw : Set (polynomialShearFiltration w s hw).realification.Group) :=
  NilpotentLieBCHGroup.realification_subgroup_closed_discrete (polynomialShearBasis w)
    (polynomialShearLattice w s hw) s.factorial (Nat.factorial_pos s)
    (polynomialShearLattice_outer_grid s hw)

theorem polynomialShearRealLattice_quotient_compact (s : ℕ) (hw : ∀ i, w i ≤ s) :
    CompactSpace ((polynomialShearFiltration w s hw).realification.Group ⧸ polynomialShearRealLattice s hw) :=
  compactSpace_realification_quotient (polynomialShearBasis w)
    (polynomialShearLattice w s hw) s.factorial (Nat.factorial_pos s)
    (polynomialShearLattice_inner_grid s hw)

end Erdos3

end

section

namespace Erdos3

open Module

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) [Fintype (PolynomialShearIndex w)]

noncomputable def polynomialShearIndexOrder :
    PolynomialShearIndex w ≃ Fin (Fintype.card (PolynomialShearIndex w)) :=
  let ρ := Fintype.equivFin (PolynomialShearIndex w)
  let u := fun j => polynomialShearDeficit w (ρ.symm j)
  ρ.trans (Tuple.sort u).symm

noncomputable def polynomialShearOrderedBasis :
    Basis (Fin (Fintype.card (PolynomialShearIndex w))) ℚ (PolynomialShearLieAlgebra w ℚ) :=
  (polynomialShearBasis w).reindex (polynomialShearIndexOrder w)

noncomputable def polynomialShearOrderedWeight (j : Fin (Fintype.card (PolynomialShearIndex w))) : ℕ :=
  polynomialShearDeficit w ((polynomialShearIndexOrder w).symm j)

omit [Fintype σ] in
theorem polynomialShearOrderedWeight_monotone : Monotone (polynomialShearOrderedWeight w) :=
  Tuple.monotone_sort (fun j => polynomialShearDeficit w ((Fintype.equivFin (PolynomialShearIndex w)).symm j))

omit [Fintype σ] in
theorem polynomialShearOrderedWeight_pos (j : Fin (Fintype.card (PolynomialShearIndex w))) :
    0 < polynomialShearOrderedWeight w j := polynomialShearDeficit_pos w _

omit [Fintype σ] in
theorem polynomialShearOrderedWeight_le (s : ℕ) (hw : ∀ i, w i ≤ s)
    (j : Fin (Fintype.card (PolynomialShearIndex w))) : polynomialShearOrderedWeight w j ≤ s :=
  polynomialShearDeficit_le w s hw _

theorem polynomialShearOrderedBasis_layers (r : ℕ) :
    polynomialShearLayer (R := ℚ) w r = Submodule.span ℚ
      (polynomialShearOrderedBasis w '' {j | r ≤ polynomialShearOrderedWeight w j}) := by
  change polynomialShearLayer w r = Submodule.span ℚ
    (((polynomialShearBasis (R := ℚ) w).reindex (polynomialShearIndexOrder w)) ''
      {j | r ≤ polynomialShearDeficit w ((polynomialShearIndexOrder w).symm j)})
  rw [basis_reindex_span_weights, polynomialShearLayer_span]

theorem polynomialShearOrderedBasis_central (s : ℕ) (hw : ∀ i, w i ≤ s) :
    IsCentralLieBasis (polynomialShearOrderedBasis w) :=
  centralLieBasis_of_sorted_filtration (polynomialShearFiltration w s hw)
    (polynomialShearOrderedBasis w) (polynomialShearOrderedWeight w)
    (polynomialShearOrderedWeight_monotone w) (polynomialShearOrderedBasis_layers w)

theorem polynomialShearOrderedBasis_structure_height (s : ℕ)
    (hpos : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ s) (a b c) :
    RationalHeightLE (lieStructureConstants (polynomialShearOrderedBasis w) a b c) (2 * s + 1) := by
  rw [polynomialShearOrderedBasis, lieStructureConstants_reindex]
  exact polynomialShear_structureConstants_height s hpos hw _ _ _

theorem polynomialShearOrderedBasis_inner_grid (s : ℕ) (hw : ∀ i, w i ≤ s) :
    scaledIntegerGrid s.factorial ⊆
      bchSubgroupCoordinates (polynomialShearOrderedBasis w) (polynomialShearLattice w s hw) :=
  bchSubgroup_inner_grid_reindex (polynomialShearBasis w) (polynomialShearIndexOrder w) _
    (polynomialShearLattice_inner_grid s hw)

theorem polynomialShearOrderedBasis_outer_grid (s : ℕ) (hw : ∀ i, w i ≤ s) :
    bchSubgroupCoordinates (polynomialShearOrderedBasis w) (polynomialShearLattice w s hw) ⊆
      denominatorGrid s.factorial :=
  bchSubgroup_outer_grid_reindex (polynomialShearBasis w) (polynomialShearIndexOrder w) _
    (polynomialShearLattice_outer_grid s hw)

theorem polynomialShearIndex_card_le (s : ℕ) (hpos : ∀ i, 0 < w i) (hw : ∀ i, w i ≤ s) :
    Fintype.card (PolynomialShearIndex w) ≤ Fintype.card σ * (Fintype.card σ + 1) ^ s := by
  rw [← finrank_eq_card_basis (polynomialShearBasis (R := ℚ) w)]
  exact polynomialShear_finrank_le w hpos s hw

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)

noncomputable def polynomialShearRealPointAction :
    (polynomialShearFiltration w s hw).realification.Group →* Equiv.Perm (σ → ℝ) :=
  (weightedLoweringPointAction w).comp (polynomialShearRealAutEquiv w s hw).toMonoidHom

theorem polynomialShearRealPointAction_rational
    (g : (polynomialShearFiltration w s hw).Group) (x : σ → ℚ) :
    polynomialShearRealPointAction w s hw (NilpotentLieBCHGroup.realificationHom g)
        (fun i => (x i : ℝ)) =
      fun i => (weightedLoweringPointAction w (polynomialShearBCHEquiv w s hw g) x i : ℝ) := by
  funext i
  have h :
      (polynomialShearRealAutEquiv w s hw (NilpotentLieBCHGroup.realificationHom g)).val.symm (X i) =
      MvPolynomial.map (algebraMap ℚ ℝ) ((polynomialShearBCHEquiv w s hw g).val.symm (X i)) := by
    simpa only [map_inv, MvPolynomial.map_X, Subgroup.coe_inv, AlgEquiv.aut_inv] using
      polynomialShearRealAutEquiv_rational w s hw g⁻¹ (X i)
  change aeval (fun j => (x j : ℝ))
      ((polynomialShearRealAutEquiv w s hw (NilpotentLieBCHGroup.realificationHom g)).val.symm (X i)) =
    (aeval x ((polynomialShearBCHEquiv w s hw g).val.symm (X i)) : ℝ)
  rw [h]
  exact polynomial_map_aeval (algebraMap ℚ ℝ) x _

theorem polynomialShearRealLattice_integer_permutation
    (γ : (polynomialShearFiltration w s hw).realification.Group)
    (hγ : γ ∈ polynomialShearRealLattice s hw) :
    ∃ e : Equiv.Perm (σ → ℤ), ∀ b,
      polynomialShearRealPointAction w s hw γ (fun i => (b i : ℝ)) =
        fun i => (e b i : ℝ) := by
  obtain ⟨g, hg, rfl⟩ := hγ
  let e := integerWeightedLoweringPointEquiv (polynomialShearBCHEquiv w s hw g) hg
  refine ⟨e, fun b => ?_⟩
  have h := congrArg (fun x : σ → ℚ => fun i => (x i : ℝ))
    (integerWeightedLoweringPointEquiv_cast (polynomialShearBCHEquiv w s hw g) hg b)
  have hr := polynomialShearRealPointAction_rational w s hw g (fun i => (b i : ℚ))
  simpa only [Rat.cast_intCast] using hr.trans h.symm

end Erdos3

end

section

namespace Erdos3

variable {σ : Type*} [Fintype σ] (w : σ → ℕ) (s : ℕ) (hw : ∀ i, w i ≤ s)

noncomputable def polynomialShearOrbitSum (K : (σ → ℝ) → ℝ)
    (g : (polynomialShearFiltration w s hw).realification.Group) : ℝ :=
  ∑' b : σ → ℤ, K (polynomialShearRealPointAction w s hw g (fun i => (b i : ℝ)))

theorem polynomialShearOrbitSum_lattice (K : (σ → ℝ) → ℝ)
    (g γ : (polynomialShearFiltration w s hw).realification.Group)
    (hγ : γ ∈ polynomialShearRealLattice s hw) :
    polynomialShearOrbitSum w s hw K (g * γ) = polynomialShearOrbitSum w s hw K g := by
  obtain ⟨e, he⟩ := polynomialShearRealLattice_integer_permutation w s hw γ hγ
  unfold polynomialShearOrbitSum
  simp_rw [map_mul, Equiv.Perm.mul_apply, he]
  exact e.tsum_eq (fun b : σ → ℤ => K (polynomialShearRealPointAction w s hw g (fun i => (b i : ℝ))))

noncomputable def polynomialShearQuotientSum (K : (σ → ℝ) → ℝ) :
    ((polynomialShearFiltration w s hw).realification.Group ⧸ polynomialShearRealLattice s hw) → ℝ :=
  Quotient.lift (polynomialShearOrbitSum w s hw K) (fun g h hgh => by
    have hi := polynomialShearOrbitSum_lattice w s hw K g (g⁻¹ * h)
      (QuotientGroup.leftRel_apply.mp hgh)
    simpa only [mul_inv_cancel_left] using hi.symm)

theorem polynomialShearQuotientSum_mk (K : (σ → ℝ) → ℝ)
    (g : (polynomialShearFiltration w s hw).realification.Group) :
    polynomialShearQuotientSum w s hw K (QuotientGroup.mk g) =
      polynomialShearOrbitSum w s hw K g := rfl

end Erdos3

end

section

namespace Erdos3

open MvPolynomial

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def shearGroupLift (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℝ) :
    (polynomialShearFiltration w s hw).realification.Group :=
  (polynomialShearRealAutEquiv w s hw).symm (A.loweringAt t)⁻¹

theorem shearGroupLift_point (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℝ) (b : Fin d → ℝ) :
    polynomialShearRealPointAction w s hw (A.shearGroupLift s hw t) b = A.loweringPoint t b := by
  change weightedLoweringPointAction w
    (polynomialShearRealAutEquiv w s hw ((polynomialShearRealAutEquiv w s hw).symm (A.loweringAt t)⁻¹)) b = _
  rw [MulEquiv.apply_symm_apply]
  rfl

end PolynomialSlots

namespace PolynomialPatch

variable {σ : Type*} {s d : ℕ}

noncomputable def shearKernel (A : PolynomialPatch σ s d) (x : Fin d → ℝ) : ℝ :=
  A.kernel.value (fun i => aeval x (A.form.topResidualEquiv (X i)))

noncomputable def shearObservable (A : PolynomialPatch σ s d) :
    ((polynomialShearFiltration A.weight s A.weight_le).realification.Group ⧸
      polynomialShearRealLattice s A.weight_le) → ℝ :=
  polynomialShearQuotientSum A.weight s A.weight_le A.shearKernel

theorem value_eq_shearOrbitSum (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t = polynomialShearOrbitSum A.weight s A.weight_le A.shearKernel
      (A.form.shearGroupLift s A.weight_le t) := by
  rw [A.value_top_factorization]
  unfold polynomialShearOrbitSum
  simp_rw [PolynomialSlots.shearGroupLift_point]
  rfl

theorem value_eq_shearObservable (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t = A.shearObservable
      (QuotientGroup.mk (A.form.shearGroupLift s A.weight_le t)) :=
  A.value_eq_shearOrbitSum t

end PolynomialPatch

end Erdos3

end

section

namespace Erdos3

open Module
open scoped TensorProduct

variable {τ : Type*} [Fintype τ] (w : τ → ℕ)

theorem polynomialShearRealificationEquiv_repr (D : ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) :
    (polynomialShearBasis (R := ℝ) w).repr (polynomialShearRealificationEquiv w D) =
      ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr D := by
  have he : polynomialShearRealificationEquiv w D = polynomialShearRealificationLinearEquiv w D :=
    DFunLike.congr_fun (polynomialShearRealificationMap_eq w) D
  rw [he]
  change (polynomialShearBasis (R := ℝ) w).repr
    ((polynomialShearBasis (R := ℝ) w).repr.symm
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr D)) = _
  exact LinearEquiv.apply_symm_apply _ _

theorem polynomialShearRealificationEquiv_symm_repr (D : PolynomialShearLieAlgebra w ℝ) :
    ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr
        ((polynomialShearRealificationEquiv w).symm D) =
      (polynomialShearBasis (R := ℝ) w).repr D := by
  rw [← polynomialShearRealificationEquiv_repr, LieEquiv.apply_symm_apply]

theorem polynomialShearRealAutEquiv_symm_coord (s : ℕ) (hw : ∀ i, w i ≤ s)
    (e : WeightedLoweringAut w ℝ) :
    polynomialShearRealificationEquiv w ((polynomialShearRealAutEquiv w s hw).symm e).coord =
      polynomialShearLog e := by
  change polynomialShearRealificationEquiv w ((polynomialShearRealificationEquiv w).symm
    (polynomialShearLog e)) = _
  exact LieEquiv.apply_symm_apply _ _

namespace PolynomialSlots

variable {σ : Type*} {d : ℕ} {v : Fin d → ℕ}

theorem shearGroupLift_coordinate (A : PolynomialSlots σ d v)
    (s : ℕ) (hv : ∀ i, v i ≤ s) (t : σ → ℝ) (a : PolynomialShearIndex v) :
    ((polynomialShearBasis (R := ℚ) v).baseChange ℝ).repr (A.shearGroupLift s hv t).coord a =
      -(polynomialShearBasis (R := ℝ) v).repr (polynomialShearLog (A.loweringAt t)) a := by
  change ((polynomialShearBasis (R := ℚ) v).baseChange ℝ).repr
    (((polynomialShearRealAutEquiv v s hv).symm (A.loweringAt t)⁻¹).coord) a = _
  rw [map_inv, NilpotentLieBCHGroup.coord_inv, map_neg, Finsupp.neg_apply]
  rw [← polynomialShearRealificationEquiv_repr, polynomialShearRealAutEquiv_symm_coord]

end PolynomialSlots
end Erdos3

end

section

namespace Erdos3.PolynomialSlots

open MvPolynomial Module
open scoped TensorProduct

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ}

noncomputable def shearCoordinatePolynomial (A : PolynomialSlots σ d w)
    (a : PolynomialShearIndex w) : MvPolynomial σ ℝ :=
  -polynomialSlotCoefficient a.2.val (A.symbolicLogSlot a.1)

theorem shearCoordinatePolynomial_degree (A : PolynomialSlots σ d w) (a : PolynomialShearIndex w) :
    A.shearCoordinatePolynomial a ∈ weightedSupportLE (fun _ : σ => 1) (polynomialShearDeficit w a) := by
  exact (weightedSupportLE _ _).neg_mem
    (polynomialSlotCoefficient_degree (fun _ : σ => 1) w (A.symbolicLogSlot_degree a.1) a.2.val)

theorem shearCoordinatePolynomial_eval (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℝ) (a : PolynomialShearIndex w) :
    aeval t (A.shearCoordinatePolynomial a) =
      ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr (A.shearGroupLift s hw t).coord a := by
  rw [shearGroupLift_coordinate, polynomialShearBasis_repr]
  unfold shearCoordinatePolynomial
  rw [map_neg, polynomialSlotCoefficient_eval]
  change -(patchParameterSpecialization t (A.symbolicLogSlot a.1)).coeff a.2.val = _
  rw [symbolicLogSlot_specialization]

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialSlots

open MvPolynomial Module VectorPolynomial
open scoped TensorProduct

variable {σ : Type*} {d : ℕ} {w : Fin d → ℕ} [Fintype (PolynomialShearIndex w)]

noncomputable def shearLogPolynomial (A : PolynomialSlots σ d w) :
    VectorPolynomial σ ℚ (ℝ ⊗[ℚ] PolynomialShearLieAlgebra w ℚ) :=
  VectorPolynomial.ofCoordinates ((polynomialShearBasis (R := ℚ) w).baseChange ℝ)
    A.shearCoordinatePolynomial

theorem shearLogPolynomial_coordinate (A : PolynomialSlots σ d w) (a : PolynomialShearIndex w) :
    VectorPolynomial.coordinate
      (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a).toAddMonoidHom A.shearLogPolynomial =
      A.shearCoordinatePolynomial a :=
  VectorPolynomial.coordinate_ofCoordinates _ _ _

theorem shearLogPolynomial_adapted (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).realification.Adapted (fun _ : σ => 1) A.shearLogPolynomial := by
  rw [NilpotentLieFiltration.adapted_iff_coefficients]
  intro α
  apply ((polynomialShearFiltration w s hw).real_mem_layer_iff_basis_coordinates
    (polynomialShearBasis (R := ℚ) w) (polynomialShearDeficit w)
    (fun j => polynomialShearLayer_span w j) _ _).mpr
  intro a ha
  change (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a)
    (VectorPolynomial.coefficients A.shearLogPolynomial α) = 0
  have hc := congrArg (fun polynomial : MvPolynomial σ ℝ => polynomial.coeff α)
    (A.shearLogPolynomial_coordinate a)
  rw [VectorPolynomial.coeff_coordinate] at hc
  apply hc.trans
  by_contra h
  have hb : Finsupp.weight (fun _ : σ => 1) α ≤ polynomialShearDeficit w a :=
    A.shearCoordinatePolynomial_degree a (MvPolynomial.mem_support_iff.mpr h)
  exact ha hb

theorem shearLogPolynomial_eval (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℝ) :
    VectorPolynomial.eval₂ t A.shearLogPolynomial = (A.shearGroupLift s hw t).coord := by
  apply ((polynomialShearBasis (R := ℚ) w).baseChange ℝ).repr.injective
  ext a
  change (((polynomialShearBasis (R := ℚ) w).baseChange ℝ).coord a)
    (VectorPolynomial.eval₂ t A.shearLogPolynomial) = _
  rw [VectorPolynomial.coordinate_eval₂, shearLogPolynomial_coordinate]
  exact A.shearCoordinatePolynomial_eval s hw t a

noncomputable def shearPolynomialOrbit (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) :
    (polynomialShearFiltration w s hw).realification.PolynomialOrbit (fun _ : σ => 1) :=
  NilpotentLieFiltration.polynomialOrbitOfLog A.shearLogPolynomial (A.shearLogPolynomial_adapted s hw)

theorem shearPolynomialOrbit_realEval (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℝ) :
    (polynomialShearFiltration w s hw).realification.polynomialOrbitRealEval
      (fun _ : σ => 1) t (A.shearPolynomialOrbit s hw) = A.shearGroupLift s hw t := by
  apply NilpotentLieBCHGroup.ext
  exact A.shearLogPolynomial_eval s hw t

theorem shearPolynomialOrbit_integerEval (A : PolynomialSlots σ d w)
    (s : ℕ) (hw : ∀ i, w i ≤ s) (t : σ → ℤ) :
    (polynomialShearFiltration w s hw).realification.polynomialOrbitEval
      (fun _ : σ => 1) t (A.shearPolynomialOrbit s hw) =
      A.shearGroupLift s hw (fun i => (t i : ℝ)) := by
  rw [← NilpotentLieFiltration.polynomialOrbitRealEval_integer]
  exact A.shearPolynomialOrbit_realEval s hw _

end Erdos3.PolynomialSlots

end

section

namespace Erdos3.PolynomialPatch

variable {σ : Type*} {s d : ℕ}

noncomputable def shearOrbit (A : PolynomialPatch σ s d) :
    (polynomialShearFiltration A.weight s A.weight_le).realification.PolynomialOrbit
      (fun _ : σ => 1) := by
  letI := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.form.shearPolynomialOrbit s A.weight_le

theorem shearOrbit_realEval (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    (polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
      (fun _ : σ => 1) t A.shearOrbit = A.form.shearGroupLift s A.weight_le t := by
  let := polynomialShearIndexFintype A.weight (fun i => A.weight_pos i)
  exact A.form.shearPolynomialOrbit_realEval s A.weight_le t

theorem shearOrbit_integerEval (A : PolynomialPatch σ s d) (t : σ → ℤ) :
    (polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
      (fun _ : σ => 1) t A.shearOrbit =
      A.form.shearGroupLift s A.weight_le (fun i => (t i : ℝ)) := by
  rw [← NilpotentLieFiltration.polynomialOrbitRealEval_integer, shearOrbit_realEval]

theorem value_eq_shearOrbit_observable (A : PolynomialPatch σ s d) (t : σ → ℝ) :
    A.value t = A.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitRealEval
        (fun _ : σ => 1) t A.shearOrbit)) := by
  rw [shearOrbit_realEval]
  exact A.value_eq_shearObservable t

theorem value_integer_eq_shearOrbit_observable (A : PolynomialPatch σ s d) (t : σ → ℤ) :
    A.value (fun i => (t i : ℝ)) = A.shearObservable (QuotientGroup.mk
      ((polynomialShearFiltration A.weight s A.weight_le).realification.polynomialOrbitEval
        (fun _ : σ => 1) t A.shearOrbit)) := by
  rw [shearOrbit_integerEval]
  exact A.value_eq_shearObservable _

end Erdos3.PolynomialPatch

end

end OAI
