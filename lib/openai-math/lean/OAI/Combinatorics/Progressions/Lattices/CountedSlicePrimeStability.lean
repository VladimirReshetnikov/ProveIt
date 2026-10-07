import OAI.Combinatorics.Progressions.Lattices.ResidueSliceUpperFailure

namespace OAI

section

namespace Erdos3

open scoped TensorProduct BigOperators

universe u v w

theorem exists_residue_prime_stability (s : ℕ) :
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
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (N j : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  classical
  obtain ⟨E₀, _, hstability⟩ := exists_coprime_residue_physical_stability.{u, v, w} s
  let P : Polynomial ℕ := 3 * Polynomial.X + 1 +
    (Polynomial.X + 3 * Polynomial.X ^ 2 + 2) ^ E₀
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N M a hM hmodulus hlarge
  let q : ι → ℕ := fun i => prime i ^ power i
  let K := mandatory ∪ periodPrimeCoordinates prime M
  let cap := p + 3 * p ^ 2
  let depth : ℕ := ⌈(cap + 2) ^ E₀⌉₊
  let Good := fun I x => mandatory ⊆ I ∧ ResiduePrimeCoordinateStable T.eval lo N M a q r δ I x
  have hp0 : 0 ≤ p := by linarith
  have hcap : p ≤ cap := by dsimp only [cap]; nlinarith [sq_nonneg p]
  have hcap0 : 0 ≤ cap := hp0.trans hcap
  have hpower : 3 * p + 1 + (cap + 2) ^ E₀ ≤ (p + 2) ^ E := by
    simpa [P, cap, Polynomial.eval₂_pow] using hpoly p hp0
  have hK := initialResiduePrimeMask_bounds prime power hprime hinj M hM p hp0 hmodulus hprimeBound mandatory hmandatory
  have hKcard : (K.card : ℝ) ≤ 3 * p := hK.1
  have hQ : ((M.lcm (∏ i ∈ K, q i) : ℕ) : ℝ) ≤ Real.exp cap := hK.2
  have hQpos : 0 < M.lcm (∏ i ∈ K, q i) := by
    apply Nat.pos_of_ne_zero
    apply Nat.lcm_ne_zero hM.ne'
    exact (Finset.prod_pos (fun i _ => pow_pos (hprime i).pos (power i))).ne'
  have hside : ∀ j, Real.exp ((cap + 2) ^ E₀) ≤ (N j : ℝ) := by
    intro j
    apply le_trans _ (hlarge j)
    apply Real.exp_le_exp.mpr
    linarith
  have hbranches : ∀ base : ∀ i, σ → ZMod (q i), ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (q i)),
      CoordinateDecisionTree.Valid Good K base tree depth := by
    intro base
    by_cases hnonempty : Nonempty (ResiduePrimeCoordinateCell lo N M a q K base)
    · obtain ⟨u⟩ := hnonempty
      obtain ⟨tree, d', hd', htree⟩ := hstability D cap δ (hp.trans hcap) (hσ.trans hcap) hδ
        (hδinv.trans (Real.exp_le_exp.mpr hcap)) T hpositive (hcomplexity.mono hcap)
        (fun i : {i // i ∉ K} => prime i.val) (fun i => power i.val)
        (fun i => hprime i.val) (fun i j hij => Subtype.ext (hinj hij))
        (fun i => (hprimeBound i.val).trans (Real.exp_le_exp.mpr hcap))
        ∅ r (by simpa only [Finset.card_empty, Nat.cast_zero] using hcap0) (hr.trans hcap)
        lo N (M.lcm (∏ i ∈ K, q i)) (fun j => (u.val j).val) hQpos hQ
        (fun i => initialResidueCombined_coprime prime power hprime hinj M K
          Finset.subset_union_right i.val i.property) hside
      have hsub := htree.map (fun _ _ h => h.2)
      have hlift := hsub.liftOutside K base (fun S x hx =>
        (show Good (K ∪ S.image Subtype.val) (CoordinateDecisionTree.outsideAssignment K base x) from
          ⟨Finset.subset_union_left.trans Finset.subset_union_left,
            hx.lift_outside T.eval lo N M a q
              (selectedPrimePowers_pairwise_coprime prime power hprime hinj) K base u r δ S x⟩))
      have hroot : CoordinateDecisionTree.Valid Good K
          (CoordinateDecisionTree.outsideAssignment K base (fun _ _ => 0)) (tree.liftOutside K) d' := by
        simpa only [Finset.image_empty, Finset.union_empty] using hlift
      have hroot' := hroot.congr_assignment (fun I x y hxy hx =>
        (show Good I y from ⟨hx.1, hx.2.congr_assignment hxy⟩)) base (by
          intro i hi
          simp only [CoordinateDecisionTree.outsideAssignment, hi, dite_true])
      have hdepth : d' ≤ depth := by
        exact_mod_cast hd'.trans (Nat.le_ceil ((cap + 2) ^ E₀))
      exact ⟨tree.liftOutside K, hroot'.mono hdepth⟩
    · exact ⟨.leaf, .leaf ⟨Finset.subset_union_left,
        residuePrimeCoordinateStable_of_empty T.eval lo N M a q r δ K base hnonempty⟩⟩
  obtain ⟨tree, htree⟩ := CoordinateDecisionTree.exists_query_batch Good K depth ∅ (fun _ _ => 0)
    (by simp) (fun base _ => by simpa only [Finset.empty_union] using hbranches base)
  refine ⟨tree, K.card + depth, ?_, htree⟩
  have hceil : (depth : ℝ) ≤ (cap + 2) ^ E₀ + 1 :=
    (Nat.ceil_lt_add_one (show 0 ≤ (cap + 2) ^ E₀ by positivity)).le
  rw [Nat.cast_add]
  linarith

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_prescribed_slice_prime_stability (s : ℕ) :
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
    ∀ (H N : σ → ℕ) (lo a : σ → ℤ) (M : ℕ), 0 < M → (M : ℝ) ≤ Real.exp p →
    (∀ j, Real.exp (-p) * (H j : ℝ) ≤ (N j : ℝ)) →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (H j : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  obtain ⟨E₀, _, hstability⟩ := exists_residue_prime_stability.{u, v, w} s
  let P : Polynomial ℕ := Polynomial.X + (Polynomial.X + 2) ^ E₀
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM hmodulus hwidth hlarge
  have hp0 : 0 ≤ p := by linarith
  have hpower : p + (p + 2) ^ E₀ ≤ (p + 2) ^ E := by
    simpa [P, Polynomial.eval₂_pow] using hpoly p hp0
  have hside : ∀ j, Real.exp ((p + 2) ^ E₀) ≤ (N j : ℝ) := by
    intro j
    have hparent := (Real.exp_le_exp.mpr hpower).trans (hlarge j)
    calc
      Real.exp ((p + 2) ^ E₀) = Real.exp (-p) * Real.exp (p + (p + 2) ^ E₀) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp (-p) * (H j : ℝ) := mul_le_mul_of_nonneg_left hparent (Real.exp_pos _).le
      _ ≤ (N j : ℝ) := hwidth j
  obtain ⟨tree, depth, hdepth, htree⟩ := hstability D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr lo N M a hM hmodulus hside
  exact ⟨tree, depth, hdepth.trans (by linarith), htree⟩

end Erdos3

end

section

namespace Erdos3

open scoped TensorProduct

universe u v w

theorem exists_counted_slice_prime_stability (s : ℕ) :
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
    ∀ (H N : σ → ℕ) (lo a : σ → ℤ) (M : ℕ), 0 < M → (∀ j, N j ≤ H j) →
    (∀ j, Real.exp (-p) * (H j : ℝ) ≤
      (residueIndexLength (lo j) (lo j + N j) M (a j) : ℝ)) →
    (∀ j, Real.exp ((p + 2) ^ E) ≤ (H j : ℝ)) →
    ∃ tree : CoordinateDecisionTree ι (fun i => σ → ZMod (prime i ^ power i)), ∃ depth : ℕ,
      (depth : ℝ) ≤ (p + 2) ^ E ∧
      CoordinateDecisionTree.Valid
        (fun I x => mandatory ⊆ I ∧
          ResiduePrimeCoordinateStable T.eval lo N M a (fun i => prime i ^ power i) r δ I x)
        ∅ (fun _ _ => 0) tree depth := by
  classical
  obtain ⟨E₀, _, hstability⟩ := exists_prescribed_slice_prime_stability.{u, v, w} s
  let P : Polynomial ℕ := (Polynomial.X + 4) ^ E₀ + Polynomial.X + 2
  obtain ⟨E, hE, hpoly⟩ := exists_natPolynomial_fixed_power_budget P
  refine ⟨E, hE, ?_⟩
  intro ι σ L _ _ _ _ _ _ _ _ _ _ d D p δ hp hσ hδ hδinv T hpositive hcomplexity
    prime power hprime hinj hprimeBound mandatory r hmandatory hr H N lo a M hM hNH hcount hlarge
  have hp0 : 0 ≤ p := by linarith
  have hpower : (p + 4) ^ E₀ + p + 2 ≤ (p + 2) ^ E := by
    simpa [P, Polynomial.eval₂_pow] using hpoly p hp0
  have hnonneg : 0 ≤ (p + 4) ^ E₀ := by positivity
  rcases isEmpty_or_nonempty σ with hempty | hnonempty
  · let := hempty
    obtain ⟨tree, htree⟩ := exists_residue_stable_tree_of_isEmpty T.eval lo N M a
      (fun i => prime i ^ power i) r δ hδ.le mandatory
    exact ⟨tree, mandatory.card, hmandatory.trans (by linarith), htree⟩
  · let := hnonempty
    have hcost := fun j => residue_slice_counting_cost (lo j) (a j) (H j) (N j) M p hM (hNH j)
      ((Real.exp_le_exp.mpr (show p + 2 ≤ (p + 2) ^ E by linarith)).trans (hlarge j)) (hcount j)
    have hmodulus : (M : ℝ) ≤ Real.exp (p + 2) := (hcost (Classical.choice hnonempty)).1
    have hpinc : p ≤ p + 2 := by linarith
    have hwidth : ∀ j, Real.exp (-(p + 2)) * (H j : ℝ) ≤ (N j : ℝ) := by
      intro j
      exact (mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr (by linarith))
        (Nat.cast_nonneg (H j))).trans (hcost j).2
    have hsize : ∀ j, Real.exp ((p + 2 + 2) ^ E₀) ≤ (H j : ℝ) := by
      intro j
      apply le_trans _ (hlarge j)
      apply Real.exp_le_exp.mpr
      have heq : p + 2 + 2 = p + 4 := by ring
      rw [heq]
      linarith
    obtain ⟨tree, depth, hdepth, htree⟩ := hstability D (p + 2) δ (hp.trans hpinc)
      (hσ.trans hpinc) hδ (hδinv.trans (Real.exp_le_exp.mpr hpinc))
      T hpositive (hcomplexity.mono hpinc) prime power hprime hinj
      (fun i => (hprimeBound i).trans (Real.exp_le_exp.mpr hpinc))
      mandatory r (hmandatory.trans hpinc) (hr.trans hpinc) H N lo a M hM hmodulus hwidth hsize
    refine ⟨tree, depth, ?_, htree⟩
    have heq : p + 2 + 2 = p + 4 := by ring
    rw [heq] at hdepth
    linarith

end Erdos3

end

end OAI
