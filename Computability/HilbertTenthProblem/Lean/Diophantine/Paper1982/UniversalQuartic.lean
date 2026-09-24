import Diophantine.Paper1982.RecursivelyEnumerableQuartic
import Mathlib.Algebra.MvPolynomial.Funext

/-!
# One universal quartic family with three index parameters

Applying the 58-witness compression a second time fixes its starting witness
count at 58 for every recursively enumerable set. Consequently the exponent
`L4 58` is fixed globally, and only the three positive index parameters vary.

The family is polynomial jointly in the parameters, input, and witnesses.
An ordinary joint multivariate polynomial is constructed below, and its
parameter specializations are proved equal to the explicit quartics.
Following §5, the degree bound counts the input and 58 witnesses, excluding
the three index parameters. Equivalence of membership holds on positive inputs.
-/

namespace Jones1982

/-- The same explicit family, with globally fixed exponent `L4 58`, represents
every recursively enumerable set by three positive index parameters. -/
theorem rePred_quartic58_family {S : Set ℕ} (hS : REPred S) :
    ∃ z u y : ℕ, 0 < z ∧ 0 < u ∧ 0 < y ∧
      (ShortQuadratic.quartic58 z u y (L4 58)).totalDegree ≤ 4 ∧
      Normalized (ShortQuadratic.quartic58 z u y (L4 58)) ∧
      ∀ x : ℕ, 0 < x →
        (x ∈ S ↔ Wset (ShortQuadratic.quartic58 z u y (L4 58)) x) := by
  obtain ⟨Q, hQ, hnorm, hrep⟩ := rePred_quartic58 hS
  obtain ⟨z, u, y, hz, hu, hy, _, hdegree, hnormalized, hcompression⟩ :=
    short_quartic_representation (ν := 58) Q (by decide) hQ hnorm
  exact ⟨z, u, y, hz, hu, hy, hdegree, hnormalized,
    fun x hx => (hrep x hx).trans (hcompression x hx)⟩

namespace UniversalQuartic

/-- Three index parameters, followed by one input and 58 witnesses. -/
abbrev JointVar := Fin 3 ⊕ Fin 59

private theorem isPoly_pow {α : Type*} {f : (α → ℕ) → ℤ}
    (hf : IsPoly f) (n : ℕ) : IsPoly (fun v => f v ^ n) := by
  induction n with
  | zero => simpa only [pow_zero] using (IsPoly.const (α := α) 1)
  | succ n ih => simpa only [pow_succ] using ih.mul hf

private theorem isPoly_sum {α β : Type*} (s : Finset β)
    (f : β → (α → ℕ) → ℤ) :
    (∀ i ∈ s, IsPoly (f i)) → IsPoly (fun v => ∑ i ∈ s, f i v) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro _
      simpa only [Finset.sum_empty] using (IsPoly.const (α := α) 0)
  | @insert i s hi ih =>
      intro hf
      have hfi := hf i (Finset.mem_insert_self i s)
      have hfs := ih (fun j hj => hf j (Finset.mem_insert_of_mem hj))
      simpa only [Finset.sum_insert hi, zero_sub, sub_neg_eq_add] using
        hfi.sub ((IsPoly.const 0).sub hfs)

private noncomputable def witnessEvaluation (v : JointVar → ℕ) :
    Option ShortQuadraticVar → ℤ :=
  (fun i : Fin 59 => (v (Sum.inr i) : ℤ)) ∘ ShortQuadratic.coordinate

set_option maxHeartbeats 1500000 in
/-- The residual formulas depend polynomially on all three index parameters
when the exponent is fixed. This checks the 46 actual residual expressions. -/
private theorem residual_isPoly (L : ℕ) (i : ShortQuadraticEquation) :
    IsPoly (fun v : JointVar → ℕ =>
      MvPolynomial.eval (ShortQuadratic.shiftAssignment (witnessEvaluation v))
        (ShortQuadratic.residual (v (Sum.inl 0)) (v (Sum.inl 1))
          (v (Sum.inl 2)) L i)) := by
  cases i <;>
    simp only [ShortQuadratic.residual, ShortQuadratic.expression,
      ShortQuadratic.bExpr, ShortQuadratic.AExpr, ShortQuadratic.CExpr,
      ShortQuadratic.QExpr, ShortQuadraticExpr.toPolynomial_sub,
      ShortQuadraticExpr.toPolynomial_pow, ShortQuadraticExpr.toPolynomial,
      MvPolynomial.eval_C, MvPolynomial.eval_X, MvPolynomial.eval_add,
      MvPolynomial.eval_sub, MvPolynomial.eval_mul, MvPolynomial.eval_pow,
      ShortQuadratic.shiftAssignment, witnessEvaluation, Function.comp_apply]
  all_goals
    repeat' first
      | exact IsPoly.proj _
      | exact IsPoly.const _
      | apply IsPoly.neg
      | apply IsPoly.add
      | apply IsPoly.sub
      | apply IsPoly.mul
      | apply isPoly_pow

private theorem family_isPoly (L : ℕ) :
    IsPoly (fun v : JointVar → ℕ =>
      MvPolynomial.eval (fun i : Fin 59 => (v (Sum.inr i) : ℤ))
        (ShortQuadratic.quartic58 (v (Sum.inl 0)) (v (Sum.inl 1))
          (v (Sum.inl 2)) L)) := by
  simp only [ShortQuadratic.quartic58, MvPolynomial.eval_rename,
    ShortQuadratic.eval_shiftedSumSquares, ShortQuadratic.sumSquares,
    MvPolynomial.eval_sum, MvPolynomial.eval_pow]
  exact isPoly_sum Finset.univ _ (fun i _ => isPoly_pow (residual_isPoly L i) 2)

/-- One joint integer polynomial, fixed before the represented set or its
index parameters are chosen. -/
noncomputable def jointPolynomial : MvPolynomial JointVar ℤ :=
  Classical.choose
    (Diophantine.isPoly_iff_exists_mvPolynomial.mp (family_isPoly (L4 58)))

theorem eval_jointPolynomial (v : JointVar → ℕ) :
    MvPolynomial.eval (fun i => (v i : ℤ)) jointPolynomial =
      MvPolynomial.eval (fun i : Fin 59 => (v (Sum.inr i) : ℤ))
        (ShortQuadratic.quartic58 (v (Sum.inl 0)) (v (Sum.inl 1))
          (v (Sum.inl 2)) (L4 58)) :=
  Classical.choose_spec
    (Diophantine.isPoly_iff_exists_mvPolynomial.mp (family_isPoly (L4 58))) v

/-- Substitute the three index parameters, retaining the input and all
58 witness variables as polynomial indeterminates. -/
noncomputable def specialize (p : Fin 3 → ℤ)
    (U : MvPolynomial JointVar ℤ) : MvPolynomial (Fin 59) ℤ :=
  MvPolynomial.eval₂ MvPolynomial.C
    (Sum.elim (fun i => MvPolynomial.C (p i)) MvPolynomial.X) U

theorem eval_specialize (p : Fin 3 → ℤ) (a : Fin 59 → ℤ)
    (U : MvPolynomial JointVar ℤ) :
    MvPolynomial.eval a (specialize p U) =
      MvPolynomial.eval (Sum.elim p a) U := by
  unfold specialize
  rw [← MvPolynomial.eval_assoc]
  apply congrArg (fun f => MvPolynomial.eval f U)
  funext i
  cases i <;> simp

private theorem eq_of_eval_nat_eq {α : Type*} {p q : MvPolynomial α ℤ}
    (h : ∀ a : α → ℕ,
      MvPolynomial.eval (fun i => (a i : ℤ)) p =
        MvPolynomial.eval (fun i => (a i : ℤ)) q) : p = q := by
  classical
  apply MvPolynomial.funext_set (fun _ : α => Set.range (fun n : ℕ => (n : ℤ)))
    (fun _ => Set.infinite_range_of_injective (Nat.cast_injective (R := ℤ)))
  intro a ha
  have hex : ∀ i : α, ∃ n : ℕ, (n : ℤ) = a i :=
    fun i => ha i (Set.mem_univ i)
  choose b hb using hex
  have hab : a = fun i => (b i : ℤ) := funext (fun i => (hb i).symm)
  rw [hab]
  exact h b

/-- Specialization is equality of ordinary polynomials, not merely an
equivalence of their existential zero sets. -/
theorem specialize_jointPolynomial (z u y : ℕ) :
    specialize ![(z : ℤ), (u : ℤ), (y : ℤ)] jointPolynomial =
      ShortQuadratic.quartic58 z u y (L4 58) := by
  apply eq_of_eval_nat_eq
  intro a
  rw [eval_specialize]
  have h := eval_jointPolynomial (Sum.elim ![z, u, y] a)
  have hv : (fun i : JointVar => ((Sum.elim ![z, u, y] a i : ℕ) : ℤ)) =
      Sum.elim ![(z : ℤ), (u : ℤ), (y : ℤ)] (fun i => (a i : ℤ)) := by
    funext i
    cases i with
    | inl j => fin_cases j <;> rfl
    | inr j => rfl
  rw [hv] at h
  simpa using h

/-- Degree in the input and witnesses, with the index parameters held fixed,
is at most four for every natural parameter assignment. -/
theorem specialize_jointPolynomial_totalDegree (z u y : ℕ) :
    (specialize ![(z : ℤ), (u : ℤ), (y : ℤ)] jointPolynomial).totalDegree ≤ 4 := by
  rw [specialize_jointPolynomial]
  exact ShortQuadratic.quartic58_totalDegree_le_four z u y (L4 58)

end UniversalQuartic

/-- The universal pair `(58, 4)` (the first row of Theorem 4 of the 1980
announcement) in the article's three-parameter convention:
one joint polynomial is chosen first, and every recursively enumerable set
is represented by a positive parameter triple. The degree counts the input
and 58 witnesses after fixing the index parameters, as specified in §5. -/
theorem universal_quartic58 :
    ∃ U : MvPolynomial (Fin 3 ⊕ Fin 59) ℤ,
      (∀ z u y : ℕ,
        (UniversalQuartic.specialize ![(z : ℤ), (u : ℤ), (y : ℤ)] U).totalDegree ≤ 4) ∧
      ∀ S : Set ℕ, REPred S → ∃ z u y : ℕ, 0 < z ∧ 0 < u ∧ 0 < y ∧
        Normalized (UniversalQuartic.specialize ![(z : ℤ), (u : ℤ), (y : ℤ)] U) ∧
        ∀ x : ℕ, 0 < x →
          (x ∈ S ↔ Wset
            (UniversalQuartic.specialize ![(z : ℤ), (u : ℤ), (y : ℤ)] U) x) := by
  refine ⟨UniversalQuartic.jointPolynomial,
    UniversalQuartic.specialize_jointPolynomial_totalDegree, ?_⟩
  intro S hS
  obtain ⟨z, u, y, hz, hu, hy, _, hnorm, hrep⟩ := rePred_quartic58_family hS
  refine ⟨z, u, y, hz, hu, hy, ?_, ?_⟩
  · rwa [UniversalQuartic.specialize_jointPolynomial]
  · simpa only [UniversalQuartic.specialize_jointPolynomial] using hrep

end Jones1982
