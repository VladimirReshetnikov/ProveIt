import GowersSzemeredi.Proofs03ProgressionAverage

/-! Four-term progression symmetries and a von Neumann estimate with a
uniform factor in any position. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi

/-- The interior/end-point interchange is a projective symmetry of the four
progression forms. Its square is multiplication by -3. -/
def fourFactorChange {N : Nat} (p : ZMod N × ZMod N) : ZMod N × ZMod N :=
  (3 * p.1 - 6 * p.2, 2 * p.1 - 3 * p.2)

theorem fourFactorChange_sq {N : Nat} (p : ZMod N × ZMod N) :
    fourFactorChange (fourFactorChange p) = (-3 * p.1, -3 * p.2) := by
  ext <;> simp only [fourFactorChange] <;> ring

theorem fourFactorChange_bijective {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 4 ≤ N) : Function.Bijective (fourFactorChange (N := N)) := by
  have h3 : (3 : ZMod N) ≠ 0 := by
    intro h
    exact Nat.not_dvd_of_pos_of_lt (by omega) (by omega)
      ((ZMod.natCast_eq_zero_iff 3 N).mp h)
  have hinj : Function.Injective (fourFactorChange (N := N)) := by
    intro p q hpq
    have hh := congrArg fourFactorChange hpq
    rw [fourFactorChange_sq, fourFactorChange_sq] at hh
    apply Prod.ext
    · exact mul_left_cancel₀ (neg_ne_zero.mpr h3) (congrArg Prod.fst hh)
    · exact mul_left_cancel₀ (neg_ne_zero.mpr h3) (congrArg Prod.snd hh)
  exact ⟨hinj, Finite.surjective_of_injective hinj⟩

/-- Under the change of variables, factor one becomes the last factor and
its input is unchanged. The other three functions are composed with scalars. -/
def fourFactorInterchange {N : Nat} (f : Fin 4 → ZMod N → Complex) :
    Fin 4 → ZMod N → Complex :=
  ![fun x => f 2 (-x), fun x => f 3 (-3 * x), fun x => f 0 (3 * x), f 1]

theorem progressionAverage_fourFactorInterchange {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 4 ≤ N) (f : Fin 4 → ZMod N → Complex) :
    progressionAverage (fourFactorInterchange f) = progressionAverage f := by
  let e := Equiv.ofBijective (fourFactorChange (N := N)) (fourFactorChange_bijective hN)
  let F : ZMod N × ZMod N → Complex := fun p => ∏ i : Fin 4, f i (p.1 - (i : Nat) * p.2)
  have hsum := Equiv.sum_comp e F
  have hpoint (p : ZMod N × ZMod N) :
      F (e p) = ∏ i : Fin 4, fourFactorInterchange f i (p.1 - (i : Nat) * p.2) := by
    dsimp [F, e, Equiv.ofBijective]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    norm_num [fourFactorChange, fourFactorInterchange, Matrix.cons_val_two, Matrix.cons_val_three]
    ring_nf
    rfl
  calc
    _ = ∑ p, F (e p) := by
      rw [Fintype.sum_prod_type]
      unfold progressionAverage
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro r _
      exact (hpoint (s, r)).symm
    _ = ∑ p, F p := hsum
    _ = progressionAverage f := by
      dsimp [F]
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm

theorem fourFactorInterchange_discValued {N : Nat}
    (f : Fin 4 → ZMod N → Complex) (hf : ∀ i, DiscValued (f i)) :
    ∀ i, DiscValued (fourFactorInterchange f i) := by
  intro i x
  fin_cases i <;> exact hf _ _

/-- Reversing the four factors preserves their progression average. -/
def fourFactorReverse {N : Nat} (f : Fin 4 → ZMod N → Complex) :
    Fin 4 → ZMod N → Complex := ![f 3, f 2, f 1, f 0]

theorem progressionAverage_fourFactorReverse {N : Nat} [NeZero N]
    (f : Fin 4 → ZMod N → Complex) :
    progressionAverage (fourFactorReverse f) = progressionAverage f := by
  let T : ZMod N × ZMod N → ZMod N × ZMod N := fun p => (p.1 - 3 * p.2, -p.2)
  have hT : Function.Involutive T := by intro p; ext <;> dsimp [T] <;> ring
  let e := hT.toPerm
  let F : ZMod N × ZMod N → Complex := fun p => ∏ i : Fin 4, f i (p.1 - (i : Nat) * p.2)
  have hpoint (p : ZMod N × ZMod N) :
      F (e p) = ∏ i : Fin 4, fourFactorReverse f i (p.1 - (i : Nat) * p.2) := by
    change F (T p) = _
    dsimp [F, T]
    simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
    norm_num [fourFactorReverse, Matrix.cons_val_two, Matrix.cons_val_three]
    ring_nf
    rfl
  calc
    _ = ∑ p, F (e p) := by
      rw [Fintype.sum_prod_type]
      unfold progressionAverage
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro s _
      apply Finset.sum_congr rfl
      intro r _
      exact (hpoint (s, r)).symm
    _ = ∑ p, F p := Equiv.sum_comp e F
    _ = progressionAverage f := by
      dsimp [F]
      rw [Fintype.sum_prod_type]
      exact Finset.sum_comm

theorem fourFactorReverse_discValued {N : Nat}
    (f : Fin 4 → ZMod N → Complex) (hf : ∀ i, DiscValued (f i)) :
    ∀ i, DiscValued (fourFactorReverse f i) := by
  intro i x
  fin_cases i <;> exact hf _ _

theorem fourFactor_uniform_last_bound {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 4 ≤ N) (f : Fin 4 → ZMod N → Complex) (hf : ∀ i, DiscValued (f i))
    (alpha : Real) (hα : 0 ≤ alpha) (hu : UniformOfDegree (f 3) alpha 2) :
    ‖progressionAverage f‖ ≤ alpha ^ (1 / 8 : Real) * (N : Real) ^ 2 := by
  have h := theorem_3_2_holds N 4 (by omega) hN f hf alpha hα (by
    intro i hi
    have heq : i = 3 := Fin.ext (by omega)
    subst i
    exact hu)
  norm_num only [Nat.reduceSub, Nat.cast_ofNat, one_div, Real.rpow_ofNat] at h ⊢
  exact h

/-- For four factors the uniform function may occupy any position. The two
symmetries move it to the last position without changing its argument. -/
theorem fourFactor_uniform_bound {N : Nat} [NeZero N] [Fact N.Prime]
    (hN : 4 ≤ N) (f : Fin 4 → ZMod N → Complex) (hf : ∀ i, DiscValued (f i))
    (alpha : Real) (hα : 0 ≤ alpha) (j : Fin 4) (hu : UniformOfDegree (f j) alpha 2) :
    ‖progressionAverage f‖ ≤ alpha ^ (1 / 8 : Real) * (N : Real) ^ 2 := by
  fin_cases j
  · have h := fourFactor_uniform_last_bound hN (fourFactorReverse f)
      (fourFactorReverse_discValued f hf) alpha hα hu
    rwa [progressionAverage_fourFactorReverse] at h
  · have h := fourFactor_uniform_last_bound hN (fourFactorInterchange f)
      (fourFactorInterchange_discValued f hf) alpha hα hu
    rwa [progressionAverage_fourFactorInterchange hN] at h
  · have h := fourFactor_uniform_last_bound hN (fourFactorInterchange (fourFactorReverse f))
      (fourFactorInterchange_discValued _ (fourFactorReverse_discValued f hf)) alpha hα hu
    rwa [progressionAverage_fourFactorInterchange hN, progressionAverage_fourFactorReverse] at h
  · exact fourFactor_uniform_last_bound hN f hf alpha hα hu

end LeanProofs.GowersSzemeredi
