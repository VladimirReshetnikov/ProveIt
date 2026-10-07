import OAI.Combinatorics.Progressions.Dynamics.NativeEquivalenceTransferBudget
import OAI.Combinatorics.Progressions.Nilpotent.PreparedAdditionNiltest

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {σ I : Type*} [DecidableEq σ]

noncomputable def coordinateSumVector (f : I → (σ → ℤ) → ℂ)
    (i : σ) (a : I) (x : Option σ → ℤ) : ℂ :=
  f a (coordinateAdditionInputs i x 0)

noncomputable def coordinateTensorVector (f : I → (σ → ℤ) → ℂ)
    (i : σ) (a : I × I) (x : Option σ → ℤ) : ℂ :=
  f a.1 (coordinateAdditionInputs i x 1) * f a.2 (coordinateAdditionInputs i x 2)

theorem coordinateAdditionProduct_eq (f : I → (σ → ℤ) → ℂ)
    (i : σ) (a : I) (b : I × I) (x : Option σ → ℤ) :
    coordinateAdditionProduct f ![a, b.1, b.2] i x =
      coordinateSumVector f i a x * star (coordinateTensorVector f i b x) := by
  simp [coordinateAdditionProduct, coordinateSumVector, coordinateTensorVector, mul_assoc]

theorem coordinateSumVector_unit [Fintype I] (f : I → (σ → ℤ) → ℂ)
    (hf : ∀ x, ∑ a, ‖f a x‖ ^ 2 = 1) (i : σ) (x : Option σ → ℤ) :
    ∑ a, ‖coordinateSumVector f i a x‖ ^ 2 = 1 := hf _

theorem coordinateTensorVector_unit [Fintype I] (f : I → (σ → ℤ) → ℂ)
    (hf : ∀ x, ∑ a, ‖f a x‖ ^ 2 = 1) (i : σ) (x : Option σ → ℤ) :
    ∑ a, ‖coordinateTensorVector f i a x‖ ^ 2 = 1 := by
  simp only [coordinateTensorVector, norm_mul, mul_pow, Fintype.sum_prod_type,
    ← Finset.mul_sum, hf, mul_one]

end Erdos3

end

section

namespace Erdos3.NativeIntegerVectorEquivalence

theorem of_addition_family {σ I : Type*} [DecidableEq σ] [Fintype I]
    {s : ℕ} {p q r : ℝ} (f : I → (σ → ℤ) → ℂ) (i : σ)
    (R : NativeIntegerModelFamily (fun _ : Option σ => 1) s q
      (fun a => coordinateAdditionProduct f a i))
    (hcard : (Fintype.card I : ℝ) ≤ Real.exp p)
    (hpr : p ≤ r) (h2pr : 2 * p ≤ r) (hqr : q ≤ r) :
    NativeIntegerVectorEquivalence s r (coordinateSumVector f i) (coordinateTensorVector f i) := by
  refine {
    left_dimension := hcard.trans (Real.exp_le_exp.mpr hpr)
    right_dimension := ?_
    expansion := ?_ }
  · simp only [Fintype.card_prod, Nat.cast_mul]
    calc
      _ ≤ Real.exp p * Real.exp p :=
        mul_le_mul hcard hcard (Nat.cast_nonneg _) (Real.exp_nonneg _)
      _ = Real.exp (2 * p) := by rw [← Real.exp_add, two_mul]
      _ ≤ Real.exp r := Real.exp_le_exp.mpr h2pr
  · intro a b
    have heq : (fun x => coordinateAdditionProduct f ![a, b.1, b.2] i x) =
        (fun x => coordinateSumVector f i a x * star (coordinateTensorVector f i b x)) :=
      funext (coordinateAdditionProduct_eq f i a b)
    exact ⟨heq ▸ (NativeIntegerExpansion.ofModelFamily R ![a, b.1, b.2]).mono hqr⟩

end Erdos3.NativeIntegerVectorEquivalence

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module NilpotentLieBCHGroup

variable {σ L : Type*} [Fintype σ] [DecidableEq σ] [LieRing L] [LieAlgebra ℚ L]
  {s d : ℕ} {D : RationalFilteredNilmanifold L s d} {bound : σ → ℕ}
  (M : D.MultidegreeStructure bound)

theorem exists_controlled_addition_model (i : σ) (hi : bound i = 1)
    (c : σ → ℕ) (hc : ∀ j, c j ≤ 1)
    {p : ℝ} (hM : M.ComplexityLE p) :
    ∃ E : RationalFilteredNilmanifold (M.filtration.additiveTripleSubalgebra i hi.le
        c hc) s
        (finrank ℚ (M.filtration.additiveTripleSubalgebra i hi.le
          c hc)),
      E.filtration = M.filtration.additiveTripleFiltration i hi.le
        c hc ∧
      E.lattice = M.additiveTripleLattice i hi.le
        c hc ∧
      E.GeometryComplexityLE (MultilinearityBudget.ambient p) ∧
      (∀ j a k, rationalLogHeight (D.basis.repr (M.filtration.additiveTripleProjection i hi.le
        c hc j (E.basis a)) k) ≤
          MultilinearityBudget.ambient p) ∧
      finrank ℚ (M.filtration.additiveTripleSubalgebra i hi.le c hc) ≤ 3 * d := by
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  obtain ⟨E, hEF, hEL, hE, hdim, he⟩ :=
    M.exists_additiveTriple_model i hi c hc hM
  have hR := MultilinearityBudget.ambient_bounds hp
  have hE' := hE.mono E hR.2.2.1
  have he' (j : Fin 3) (a) (k) :
      rationalLogHeight (D.basis.repr (M.filtration.additiveTripleProjection i hi.le
        c hc j (E.basis a)) k) ≤
          MultilinearityBudget.ambient p := by
    fin_cases j
    · exact (he a k).1.trans hR.2.2.2
    · exact (he a k).2.1.trans hR.2.2.2
    · exact (he a k).2.2.trans hR.2.2.2
  exact ⟨E, hEF, hEL, hE', he', hdim⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

open Module
open scoped TensorProduct BigOperators NNReal

theorem exists_controlled_addition_family (s : ℕ) :
    ∃ Z : ℕ, 2 ≤ Z ∧ ∀ {σ I : Type*} {L : Type}
      [Fintype σ] [DecidableEq σ] [Fintype I] [LieRing L] [LieAlgebra ℚ L]
      [TopologicalSpace (ℝ ⊗[ℚ] L)] [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)]
      [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {t d : ℕ} {bound : σ → ℕ} (D : RationalFilteredNilmanifold L t d)
      (M : D.MultidegreeStructure bound) (i : σ) (_hi : bound i = 1)
      (_hs : ∑ j, bound j = t) (_ht : t = s + 1) {p : ℝ}, M.ComplexityLE p →
      ∀ (V : D.UnitVerticalObservable (M.realSubgroup bound) I p)
        (g : M.filtration.realification.PolynomialOrbit),
      ∃ R : NativeIntegerModelFamily (fun _ : Option σ => 1) s ((p + Z) ^ Z)
        (fun a => coordinateAdditionProduct
          (fun j y => V.observable j
            (QuotientGroup.mk (M.filtration.realification.polynomialOrbitEval y g))) a i),
        R.dim ≤ 3 * d := by
  obtain ⟨C, _, hnormal⟩ := exists_controlled_group_normalization (s + 1)
  obtain ⟨Z, hZ, hbudget⟩ := MultilinearityBudget.exists_total_bound C
    (MultilinearityBudget.reconstructionExponent s)
  refine ⟨Z, hZ, ?_⟩
  intro σ I L _ _ _ _ _ _ _ _ _ t d bound D M i hi hs ht p hM V g
  subst ht
  classical
  have hp : 0 ≤ p := (Nat.cast_nonneg d).trans hM.1.1
  have hR := MultilinearityBudget.ambient_bounds hp
  obtain ⟨E, hEF, hEL, hE, he, hdim⟩ := M.exists_controlled_addition_model
    i hi (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i) hM
  obtain ⟨n, hn, Q, hQF, hQL, hQ, hq, _⟩ := E.exists_controlled_top_quotient hR.1 hE
  obtain ⟨ε, γ, A, hγ, hfactor, _, hA, hε⟩ := hnormal D p hp hM.1
    (M.filtration.realification.polynomialOrbitEval 0 g)
  let K := M.filtration.additiveTripleSubalgebra i hi.le
    (omittedCoordinateWeight i) (omittedCoordinateWeight_le_one i)
  let J := K ⧸ E.filtration.layerIdeal (s + 1)
  let := moduleTopology ℝ (ℝ ⊗[ℚ] K)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] K) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] K) := realification_moduleTopology_t2 E.basis
  let := moduleTopology ℝ (ℝ ⊗[ℚ] J)
  let : IsTopologicalAddGroup (ℝ ⊗[ℚ] J) := IsModuleTopology.isTopologicalAddGroup ℝ _
  let : T2Space (ℝ ⊗[ℚ] J) := realification_moduleTopology_t2 Q.basis
  have hall (a : Fin 3 → I) := M.exists_prepared_addition_niltest i hi hs
    E hEF hEL Q hQF hQL hp (hM.1.mono D hR.2.1) hE he hQ
    (fun j k => (hq k j).trans (MultilinearityBudget.quotient_bounds hp).2.2)
    V g C ε γ hγ hfactor A hA hε a
  choose T hnorm hcomplex hzero heval using hall
  refine ⟨{
    L := J
    dim := n
    model := Q
    test := T
    norm := fun a => (hnorm a).le
    complexity := fun a => (hcomplex a).mono (hbudget p hp)
    normalized := hzero
    eval := heval }, hn.trans hdim⟩

end Erdos3.RationalFilteredNilmanifold.MultidegreeStructure

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open RationalFilteredNilmanifold.MultidegreeStructure
open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff

theorem exists_addition_family {σ : Type*} [Fintype σ] [DecidableEq σ] (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (i : σ), bound i = 1 →
      ∃ R : NativeIntegerModelFamily (fun _ : Option σ => 1) ((∑ j, bound j) - 1)
        ((p + C) ^ C) (fun a => coordinateAdditionProduct W.eval a i),
        R.dim ≤ 3 * W.dim := by
  obtain ⟨C, hC, hcontrol⟩ := exists_controlled_addition_family ((∑ j, bound j) - 1)
  refine ⟨C, hC, ?_⟩
  intro p W i hi
  have hle : bound i ≤ ∑ j, bound j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have hpos : 1 ≤ ∑ j, bound j := by simpa only [hi] using hle
  exact hcontrol W.model W.multi i hi rfl (Nat.sub_add_cancel hpos).symm
    W.complexity W.vertical W.orbit

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_addition_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] (bound : σ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter bound p)
      (i : σ), bound i = 1 →
      NativeIntegerVectorEquivalence ((∑ j, bound j) - 1) ((p + C) ^ C)
        (coordinateSumVector W.eval i) (coordinateTensorVector W.eval i) := by
  obtain ⟨a, _, hadd⟩ := exists_addition_family bound
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + Polynomial.C a) ^ a + 2 * X + 2)
  refine ⟨C, hC, ?_⟩
  intro p W i hi
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : 0 ≤ (p + a) ^ a := pow_nonneg (add_nonneg hp (Nat.cast_nonneg a)) a
  have hb : (p + a) ^ a + 2 * p + 2 ≤ (p + C) ^ C := by
    simpa [X, Polynomial.eval₂_pow] using hbudget p hp
  have hpr : p ≤ (p + C) ^ C := by linarith only [hp, hpow, hb]
  have h2pr : 2 * p ≤ (p + C) ^ C := by linarith only [hpow, hb]
  have hqr : (p + a) ^ a ≤ (p + C) ^ C := by linarith only [hp, hb]
  obtain ⟨R, _⟩ := hadd W i hi
  exact NativeIntegerVectorEquivalence.of_addition_family W.eval i R
    (by simpa only [Fintype.card_fin] using W.output_bound) hpr h2pr hqr

theorem exists_multilinearity_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p)
      (i : σ), NativeIntegerVectorEquivalence (Fintype.card σ - 1) ((p + C) ^ C)
        (coordinateSumVector W.eval i) (coordinateTensorVector W.eval i) := by
  obtain ⟨C, hC, h⟩ := exists_addition_equivalence (fun _ : σ => 1)
  exact ⟨C, hC, fun W i => by simpa using h W i rfl⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

theorem exists_multilinearity_cyclic_equivalence {σ : Type*} [Fintype σ] [DecidableEq σ] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p)
      (i : σ) (A : Option σ → Unit → ℤ) (b : Option σ → ℤ)
      (N : ℕ) [NeZero N],
      NativeVectorEquivalence (Fintype.card σ - 1) N ((p + C) ^ C)
        (fun j x => coordinateSumVector W.eval i j
          (integerAffineMap A b (fun _ => (x.val : ℤ))))
        (fun k x => coordinateTensorVector W.eval i k
          (integerAffineMap A b (fun _ => (x.val : ℤ)))) := by
  obtain ⟨C, hC, h⟩ := exists_multilinearity_equivalence (σ := σ)
  exact ⟨C, hC, fun W i A b N _ => (h W i).cyclicAffinePullback A b N⟩

end Erdos3.NativeMultidegreeNilcharacter

end

section

namespace Erdos3.NativeMultidegreeNilcharacter

open scoped BigOperators

theorem exists_multilinearity_transfer_budget {σ I : Type*} [Fintype σ] [DecidableEq σ] :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ {p : ℝ} (W : NativeMultidegreeNilcharacter (fun _ : σ => 1) p)
      (i : σ) (A : Option σ → Unit → ℤ) (b : Option σ → ℤ)
      (N : ℕ) [NeZero N] (f : I → ZMod N → ℂ),
      NativeVectorCorrelation (Fintype.card σ - 1) N p
        (fun ij : I × Fin W.outputDim => fun x => f ij.1 x * star
          (coordinateSumVector W.eval i ij.2 (integerAffineMap A b (fun _ => (x.val : ℤ))))) →
      Nonempty (NativeVectorCorrelation (Fintype.card σ - 1) N ((p + C) ^ C)
        (fun ik : I × (Fin W.outputDim × Fin W.outputDim) => fun x => f ik.1 x * star
          (coordinateTensorVector W.eval i ik.2 (integerAffineMap A b (fun _ => (x.val : ℤ)))))) := by
  obtain ⟨a, _, hequiv⟩ := exists_multilinearity_cyclic_equivalence (σ := σ)
  obtain ⟨c, _, htransfer⟩ := NativeVectorEquivalence.exists_transfer_budget
  let X : Polynomial ℕ := Polynomial.X
  obtain ⟨C, hC, hbudget⟩ := exists_natPolynomial_eval_budget
    ((X + (X + Polynomial.C a) ^ a + 2 + Polynomial.C c) ^ c)
  refine ⟨C, hC, ?_⟩
  intro p W i A b N _ f R
  have hp : 0 ≤ p := (Nat.cast_nonneg W.dim).trans W.complexity.1.1
  have hpow : 0 ≤ (p + a) ^ a := pow_nonneg (add_nonneg hp (Nat.cast_nonneg a)) a
  let q := p + (p + a) ^ a + 2
  have hpq : p ≤ q := by dsimp [q]; linarith only [hpow]
  have haq : (p + a) ^ a ≤ q := by dsimp [q]; linarith only [hp]
  have hunit (x : ZMod N) :
      ∑ k, ‖coordinateTensorVector W.eval i k
        (integerAffineMap A b (fun _ => (x.val : ℤ)))‖ ^ 2 = 1 :=
    coordinateTensorVector_unit W.eval W.unit_eval i _
  obtain ⟨S⟩ := htransfer ((hequiv W i A b N).mono haq) hunit f (R.mono hpq)
  have hcost : (q + c) ^ c ≤ (p + C) ^ C := by
    simpa [q, X, Polynomial.eval₂_pow] using hbudget p hp
  exact ⟨S.mono hcost⟩

end Erdos3.NativeMultidegreeNilcharacter

end

end OAI
