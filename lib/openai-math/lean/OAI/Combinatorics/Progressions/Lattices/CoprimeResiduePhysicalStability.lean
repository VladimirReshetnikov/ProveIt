import OAI.Combinatorics.Progressions.Geometry.CoordinateTreeRelabel
import OAI.Combinatorics.Progressions.Lattices.AffineResidueCoordinateEquiv
import OAI.Combinatorics.Progressions.Polynomial.PrimeStabilityPolynomialBudget

namespace OAI

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_congr_assignment {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (I : Finset ι) (x y : ∀ i, σ → ZMod (q i)) (hxy : ∀ i ∈ I, x i = y i) :
    residuePrimeCoordinateMean f lo N M a q I x = residuePrimeCoordinateMean f lo N M a q I y := by
  classical
  let e : ResiduePrimeCoordinateCell lo N M a q I x ≃ ResiduePrimeCoordinateCell lo N M a q I y :=
    Equiv.subtypeEquivRight (fun z => ⟨fun hz i hi => (hz i hi).trans (hxy i hi),
      fun hz i hi => (hz i hi).trans (hxy i hi).symm⟩)
  exact Fintype.expect_equiv e _ _ (fun _ => rfl)

theorem ResiduePrimeCoordinateStable.congr_assignment {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {f : (σ → ℤ) → ℂ} {lo : σ → ℤ} {N : σ → ℕ} {M : ℕ} {a : σ → ℤ} {q : ι → ℕ}
    {r : ℕ} {δ : ℝ} {I : Finset ι} {x y : ∀ i, σ → ZMod (q i)}
    (h : ResiduePrimeCoordinateStable f lo N M a q r δ I x) (hxy : ∀ i ∈ I, x i = y i) :
    ResiduePrimeCoordinateStable f lo N M a q r δ I y := by
  intro J hIJ hJ z hyz hnonempty
  rw [← residuePrimeCoordinateMean_congr_assignment f lo N M a q I x y hxy]
  exact h J hIJ hJ z (fun i hi => (hyz i hi).trans (hxy i hi).symm) hnonempty

theorem residuePrimeCoordinateStable_of_empty {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (hempty : ¬ Nonempty (ResiduePrimeCoordinateCell lo N M a q I x)) :
    ResiduePrimeCoordinateStable f lo N M a q r δ I x := by
  intro J hIJ hJ y hxy hnonempty
  obtain ⟨z⟩ := hnonempty
  exact False.elim (hempty ⟨⟨z.val, fun i hi =>
    (z.property i (Finset.mem_union_left J hi)).trans (hxy i hi)⟩⟩)

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def residuePrimeCoordinateCellEquiv {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i)) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    primeCoordinateCell (fun j => residueIndexLower (lo j) M (a j))
      (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) q I x ≃
    ResiduePrimeCoordinateCell lo N M a q I
      (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (x i)) := by
  refine (primeCoordinateCell_subtypeEquiv _ _ q I x).trans
    ((integerResidueBoxEquiv lo (fun j => lo j + N j) (fun _ => (M : ℤ)) a
      (fun _ => Nat.cast_pos.mpr hM)).subtypeEquiv ?_)
  intro z
  constructor
  · intro hz i hi
    change (fun j => ((a j + (M : ℤ) * z.val j : ℤ) : ZMod (q i))) = _
    rw [← affineResidueCoordinateEquiv_intCast M (q i) a (hcop i)]
    exact congrArg (affineResidueCoordinateEquiv M (q i) a (hcop i)) (hz i hi)
  · intro hz i hi
    apply (affineResidueCoordinateEquiv M (q i) a (hcop i)).injective
    rw [affineResidueCoordinateEquiv_intCast]
    exact hz i hi

theorem residuePrimeCoordinateMean_affine {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i)) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMean f lo N M a q I
      (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (x i)) =
    primeCoordinateMean (fun z => f (fun j => a j + (M : ℤ) * z j))
      (fun j => residueIndexLower (lo j) M (a j))
      (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) q I x := by
  classical
  exact (Fintype.expect_equiv (residuePrimeCoordinateCellEquiv lo N M a q hM hcop I x)
    _ _ (fun _ => rfl)).symm

theorem PrimeCoordinateStable.on_residue_slice {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (hM : 0 < M) (hcop : ∀ i, M.Coprime (q i)) (r : ℕ) (δ : ℝ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i))
    (h : PrimeCoordinateStable (fun z => f (fun j => a j + (M : ℤ) * z j))
      (fun j => residueIndexLower (lo j) M (a j))
      (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) q r δ I x) :
    ResiduePrimeCoordinateStable f lo N M a q r δ I
      (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (x i)) := by
  intro J hIJ hJ y hxy hnonempty
  let inv : ∀ i, σ → ZMod (q i) := fun i =>
    (affineResidueCoordinateEquiv M (q i) a (hcop i)).symm (y i)
  have hy : (fun i => affineResidueCoordinateEquiv M (q i) a (hcop i) (inv i)) = y := by
    funext i
    exact Equiv.apply_symm_apply _ _
  have hagree : ∀ i ∈ I, inv i = x i := by
    intro i hi
    dsimp only [inv]
    rw [hxy i hi]
    exact Equiv.symm_apply_apply _ _
  have hne : (primeCoordinateCell (fun j => residueIndexLower (lo j) M (a j))
      (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) q (I ∪ J) inv).Nonempty := by
    rw [← hy] at hnonempty
    obtain ⟨z⟩ := hnonempty
    exact ⟨((residuePrimeCoordinateCellEquiv lo N M a q hM hcop (I ∪ J) inv).symm z).val,
      ((residuePrimeCoordinateCellEquiv lo N M a q hM hcop (I ∪ J) inv).symm z).property⟩
  rw [residuePrimeCoordinateMean_affine f lo N M a q hM hcop I x]
  have hmean := residuePrimeCoordinateMean_affine f lo N M a q hM hcop (I ∪ J) inv
  rw [hy] at hmean
  rw [hmean]
  exact h J hIJ hJ inv hagree hne

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

theorem residuePrimeCoordinateMean_of_isEmpty {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [IsEmpty σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    residuePrimeCoordinateMean f lo N M a q I x = f (fun j => isEmptyElim j) := by
  classical
  let : Nonempty (ResiduePrimeCoordinateCell lo N M a q I x) :=
    ⟨⟨(fun j => isEmptyElim j), fun _ _ => Subsingleton.elim _ _⟩⟩
  unfold residuePrimeCoordinateMean
  calc
    (𝔼 z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => (z.val j).val)) =
        𝔼 _z : ResiduePrimeCoordinateCell lo N M a q I x, f (fun j => isEmptyElim j) := by
      apply Finset.expect_congr rfl
      intro z _
      exact congrArg f (Subsingleton.elim _ _)
    _ = _ := Fintype.expect_const _

theorem residuePrimeCoordinateStable_of_isEmpty {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [IsEmpty σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (I : Finset ι) (x : ∀ i, σ → ZMod (q i)) :
    ResiduePrimeCoordinateStable f lo N M a q r δ I x := by
  intro J _ _ y _ _
  rw [residuePrimeCoordinateMean_of_isEmpty, residuePrimeCoordinateMean_of_isEmpty, sub_self, norm_zero]
  exact hδ

theorem exists_residue_stable_tree_of_isEmpty {ι σ : Type*}
    [DecidableEq ι] [Fintype σ] [DecidableEq σ] [IsEmpty σ]
    (f : (σ → ℤ) → ℂ) (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ) (q : ι → ℕ)
    (r : ℕ) (δ : ℝ) (hδ : 0 ≤ δ) (mandatory : Finset ι) :
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (q i)),
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧ ResiduePrimeCoordinateStable f lo N M a q r δ I x)
        ∅ (fun _ _ => 0) tree mandatory.card := by
  have h := CoordinateDecisionTree.exists_query_batch
    (fun I x => mandatory ⊆ I ∧ ResiduePrimeCoordinateStable f lo N M a q r δ I x)
    mandatory 0 ∅ (fun _ _ => 0) (by simp) (by
      intro y _
      refine ⟨.leaf, .leaf ⟨?_, residuePrimeCoordinateStable_of_isEmpty f lo N M a q r δ hδ _ y⟩⟩
      simp only [Finset.empty_union, Finset.Subset.refl])
  simpa only [Nat.add_zero] using h

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_adapted_prime_coordinate_stability (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (ω : Fin d → ℕ),
    (∀ j, D.filtration.layer j = Submodule.span ℚ (D.basis '' {i | j ≤ ω i})) →
    ∀ (p δ : ℝ), 2 ≤ p → (d : ℝ) ≤ p → (Fintype.card σ : ℝ) ≤ p →
    0 < δ → δ ≤ 1 → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (lo : σ → ℤ) (N : σ → ℕ), (∀ i, 0 < N i) →
    (∀ i, Real.exp ((p + 2) ^ E) ≤ (N i : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧ PrimeCoordinateStable T.eval lo N (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨parameters⟩ := exists_physical_stability_parameters.{u, v} s
  obtain ⟨Lexp, hLexp, hbounds⟩ :=
    exists_prime_stability_polynomial_budget.{u, v, w} s parameters.K parameters.Kf
  let R : Polynomial ℕ := ((Polynomial.X + 2) ^ parameters.A + 2) ^ Lexp
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget R
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D ω hadapted p δ hp hd hσ hδ hδone hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N hN hlarge
  let b := (p + 2) ^ parameters.A
  have hp0 : 0 ≤ p := by linarith
  have hb : 0 ≤ b := by dsimp [b]; positivity
  have hpb : p ≤ b := by
    calc
      p ≤ p + 2 := by linarith
      _ = (p + 2) ^ 1 := (pow_one _).symm
      _ ≤ (p + 2) ^ parameters.A := pow_le_pow_right₀ (by linarith) parameters.A_pos
  let base : PhysicalEpochSource.{u, v} σ s d := {
    Carrier := L
    dimension := d
    dimension_le := le_rfl
    model := D
    weights := ω
    adapted := hadapted
    fixedMap := T
    lower := lo
    sides := N
    sides_pos := hN
    incomingBudget := p
    recordBudget := b
    incoming_nonneg := hp0
    incoming_le_record := hpb
    geometry := hcomplexity.1
    coordinates_le := hσ }
  let ctx : PrimeStabilityContext.{u, v, w} ι σ s d := {
    parameters := parameters
    base := base
    baseline := T
    orbit := rfl
    positive := hpositive
    complexity := hcomplexity
    recordCap := b
    recordCap_nonneg := hb
    record_le_cap := le_rfl
    inflation := le_rfl
    record_two := hp.trans hpb
    gap := δ
    gap_pos := hδ
    gap_le_one := hδone
    gap_inverse := hδinv
    prime := prime
    power := power
    prime_prime := hprime
    prime_injective := hinj
    primeBudget := p
    primeBudget_nonneg := hp0
    prime_bound := hprimeBound
    witnessSize := r
    mandatory := mandatory }
  obtain ⟨hallowance, hwidth⟩ := hbounds ctx b hb le_rfl le_rfl le_rfl hpb (hr.trans hpb) (hmandatory.trans hpb) (hd.trans hpb)
  have hpower : (b + 2) ^ Lexp ≤ (p + 2) ^ E := by
    simpa [R, b, Polynomial.eval₂_pow] using hpoly p hp0
  have hctxLarge : ctx.HasLargeSides := by
    intro i
    exact (Real.exp_le_exp.mpr (hwidth.trans hpower)).trans (hlarge i)
  obtain ⟨tree, htree⟩ := ctx.exists_stable_tree hctxLarge
  exact ⟨tree, ctx.allowance, hallowance.trans hpower, htree⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_prime_coordinate_box_stability (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ ≤ 1 → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (lo : σ → ℤ) (N : σ → ℕ), (∀ i, 0 < N i) →
    (∀ i, Real.exp ((p + 2) ^ E) ≤ (N i : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧ PrimeCoordinateStable T.eval lo N (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨C, _, hrebase⟩ := RationalFilteredNilmanifold.exists_controlled_adapted_rebase
  obtain ⟨E₀, _, hstability⟩ := exists_adapted_prime_coordinate_stability.{u, v, w} s
  let P : Polynomial ℕ := ((Polynomial.X + Polynomial.C C) ^ C + 2) ^ E₀
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδone hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N hN hlarge
  have hp0 : 0 ≤ p := by linarith
  obtain ⟨F, H, hH, hpq, hgeometry, htest, _⟩ := hrebase D hp0 hcomplexity.1
  let q := (p + C) ^ C
  have hpower : (q + 2) ^ E₀ ≤ (p + 2) ^ E := by
    simpa [P, q, Polynomial.eval₂_pow] using hpoly p hp0
  have hnewLarge : ∀ i, Real.exp ((q + 2) ^ E₀) ≤ (N i : ℝ) :=
    fun i => (Real.exp_le_exp.mpr hpower).trans (hlarge i)
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability F.model F.weight F.model_layers q δ (hp.trans hpq)
    hgeometry.1 (hσ.trans hpq) hδ hδone (hδinv.trans (Real.exp_le_exp.mpr hpq))
    (F.rebaseNiltest H hH T) (F.rebaseNiltest_unit_interval H hH T hpositive) (htest T hcomplexity)
    prime power hprime hinj (fun i => (hprimeBound i).trans (Real.exp_le_exp.mpr hpq))
    mandatory r (hmandatory.trans hpq) (hr.trans hpq) lo N hN hnewLarge
  have heval : (F.rebaseNiltest H hH T).eval = T.eval := funext (F.rebaseNiltest_eval H hH T)
  rw [heval] at htree
  exact ⟨tree, depth, hdepth.trans hpower, htree⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

theorem PrimeCoordinateStable.mono_tolerance
    {ι σ : Type*} [DecidableEq ι] [Fintype σ] [DecidableEq σ]
    {f : (σ → ℤ) → ℂ} {lo : σ → ℤ} {N : σ → ℕ} {q : ι → ℕ}
    {r : ℕ} {δ ε : ℝ} {I : Finset ι} {x : ∀ i, σ → ZMod (q i)}
    (h : PrimeCoordinateStable f lo N q r δ I x) (hδε : δ ≤ ε) :
    PrimeCoordinateStable f lo N q r ε I x := by
  intro J hIJ hJ y hxy hnonempty
  exact (h J hIJ hJ y hxy hnonempty).trans hδε

universe u v w

theorem exists_prime_coordinate_box_stability_pos (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (lo : σ → ℤ) (N : σ → ℕ), (∀ i, 0 < N i) →
    (∀ i, Real.exp ((p + 2) ^ E) ≤ (N i : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧ PrimeCoordinateStable T.eval lo N (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E, hE, hstability⟩ := exists_prime_coordinate_box_stability.{u, v, w} s
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N hN hlarge
  let ε := min δ 1
  have hε : 0 < ε := lt_min hδ (by norm_num)
  have hεone : ε ≤ 1 := min_le_right _ _
  have hεinv : ε⁻¹ ≤ Real.exp p := by
    by_cases hsmall : δ ≤ 1
    · simpa only [ε, min_eq_left hsmall] using hδinv
    · have hlargeδ : 1 ≤ δ := le_of_lt (lt_of_not_ge hsmall)
      simpa only [ε, min_eq_right hlargeδ, inv_one] using Real.one_le_exp (show 0 ≤ p by linarith)
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p ε hp hσ hε hεone hεinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N hN hlarge
  refine ⟨tree, depth, hdepth, htree.map ?_⟩
  intro I x hleaf
  exact ⟨hleaf.1, hleaf.2.mono_tolerance (min_le_left δ 1)⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_coprime_residue_prime_stability (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ), 0 < M →
    (∀ i, M.Coprime (prime i ^ power i)) →
    (∀ j, Real.exp ((p + 2) ^ E) ≤
      (residueIndexLength (lo j) (lo j + N j) M (a j) : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E, hE, hstability⟩ := exists_prime_coordinate_box_stability_pos.{u, v, w} s
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N M a hM hcop hlarge
  let q : ι → ℕ := fun i => prime i ^ power i
  let S := T.scalarAffinePullback (M : ℤ) (fun j => (a j : ℚ))
  have hSpos : S.UnitIntervalValued := hpositive
  have hScomplexity : S.ComplexityLE p := hcomplexity
  have hN : ∀ j, 0 < residueIndexLength (lo j) (lo j + N j) M (a j) := by
    intro j
    exact_mod_cast (Real.exp_pos ((p + 2) ^ E)).trans_le (hlarge j)
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p δ hp hσ hδ hδinv S hSpos hScomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr
    (fun j => residueIndexLower (lo j) M (a j))
    (fun j => residueIndexLength (lo j) (lo j + N j) M (a j)) hN hlarge
  have heval : S.eval = (fun z => T.eval (fun j => a j + (M : ℤ) * z j)) := by
    funext z
    simpa only [S, add_comm] using T.scalarAffinePullback_eval_integer (M : ℤ) a z
  rw [heval] at htree
  let e : ∀ i, (σ → ZMod (q i)) ≃ (σ → ZMod (q i)) :=
    fun i => affineResidueCoordinateEquiv M (q i) a (hcop i)
  have hrelabeled := htree.relabel e
  have hresult : CoordinateDecisionTree.Valid
      (fun I x => mandatory ⊆ I ∧ ResiduePrimeCoordinateStable T.eval lo N M a q r δ I x)
      ∅ (CoordinateDecisionTree.relabelAssignment e (fun _ _ => 0)) (tree.relabel e) depth := by
    apply hrelabeled.map
    intro I x hx
    refine ⟨hx.1, ?_⟩
    have hs := PrimeCoordinateStable.on_residue_slice T.eval lo N M a q hM hcop r δ I
      (CoordinateDecisionTree.relabelAssignment (fun i => (e i).symm) x) hx.2
    simpa only [CoordinateDecisionTree.relabelAssignment, e, Equiv.apply_symm_apply] using hs
  refine ⟨tree.relabel e, depth, hdepth, hresult.congr_assignment ?_ (fun _ _ => 0) ?_⟩
  · intro I x y hxy hx
    exact ⟨hx.1, hx.2.congr_assignment hxy⟩
  · intro i hi
    exact False.elim (Finset.notMem_empty i hi)

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_coprime_residue_physical_stability (s : ℕ) :
    ∃ E : ℕ, 2 ≤ E ∧ ∀ {ι : Type w} {σ : Type u} {L : Type v}
      [Fintype ι] [DecidableEq ι] [Fintype σ] [DecidableEq σ]
      [LieRing L] [LieAlgebra ℚ L] [TopologicalSpace (ℝ ⊗[ℚ] L)]
      [IsTopologicalAddGroup (ℝ ⊗[ℚ] L)] [ContinuousSMul ℝ (ℝ ⊗[ℚ] L)] [T2Space (ℝ ⊗[ℚ] L)]
      {d : ℕ} (D : RationalFilteredNilmanifold L s d) (p δ : ℝ),
    2 ≤ p → (Fintype.card σ : ℝ) ≤ p → 0 < δ → δ⁻¹ ≤ Real.exp p →
    ∀ T : D.Niltest (fun _ : σ => 1), T.UnitIntervalValued → T.ComplexityLE p →
    ∀ (prime power : ι → ℕ), (∀ i, (prime i).Prime) → Function.Injective prime →
    (∀ i, ((prime i ^ power i : ℕ) : ℝ) ≤ Real.exp p) →
    ∀ (mandatory : Finset ι) (r : ℕ), (mandatory.card : ℝ) ≤ p → (r : ℝ) ≤ p →
    ∀ (lo : σ → ℤ) (N : σ → ℕ) (M : ℕ) (a : σ → ℤ), 0 < M → (M : ℝ) ≤ Real.exp p →
    (∀ i, M.Coprime (prime i ^ power i)) →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (N j : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E₀, _, hstability⟩ := exists_coprime_residue_prime_stability.{u, v, w} s
  let P : Polynomial ℕ := Polynomial.X + (Polynomial.X + 2) ^ E₀ + 2
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N M a hM hmodulus hcop hlarge
  have hp0 : 0 ≤ p := by linarith
  have hpower : p + (p + 2) ^ E₀ + 2 ≤ (p + 2) ^ E := by
    simpa [P, Polynomial.eval₂_pow] using hpoly p hp0
  have hparameters : ∀ j, Real.exp ((p + 2) ^ E₀) ≤
      (residueIndexLength (lo j) (lo j + N j) M (a j) : ℝ) := by
    intro j
    apply residueIndexLength_large_of_exp (lo j) (a j) (N j) M p ((p + 2) ^ E₀)
      hM (by positivity) hmodulus
    exact (Real.exp_le_exp.mpr hpower).trans (hlarge j)
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N M a hM hcop hparameters
  exact ⟨tree, depth, hdepth.trans (by linarith), htree⟩

end Erdos3

end

end OAI
