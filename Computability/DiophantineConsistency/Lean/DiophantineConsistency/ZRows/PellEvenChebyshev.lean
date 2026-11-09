import DiophantineConsistency.ArithmeticPellHalfIndex

/-! # Even Pell ordinates modulo `4A²`

In every model `V` of `𝗜𝚺₁`, for the represented Pell ordinate at base `A = b + 2`:

* `sign_index`: `ψ_A(L) ≡ (−1)^(L−1) L (mod 2(A+1))`, as the pair
  `ψ(2t) + 2t ≡ 0` and `ψ(2t+1) ≡ 2t+1`. The recurrence `ψ(n+2) + ψ(n) + 2ψ(n+1) = 2(A+1)ψ(n+1)`
  is transported against the linear sequence exactly as in
  `ArithmeticPellAuxiliarySeed.quotient_divisor_pair`;
* `even_ordinate`: `ψ_A(2L) = 2A·P` with `P ≡ (−1)^(L−1) L (mod 4A²)`. By the composition
  `ψ_A(2L) = ψ_A(2)·ψ_B(L)` with `B = χ_A(2) = 2A² − 1` (`ArithmeticPellCommonUnit.composition`),
  `P = ψ_B(L)`, and `2(B+1) = 4A²`.

This is the even sibling (L2 of the P138 risk audit) of the odd-quotient law: it is used by the
linear stepping of `ZRows/LinearInterpolation` at the step index. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ZRowsPellEvenChebyshev
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellPeriodicity ArithmeticPellCommonUnit
open ArithmeticPellHalfIndex

variable {V : Type} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

attribute [local irreducible] xcoord ycoord

theorem y_rec (b t : V) :
    ycoord (t+2) b+ycoord t b+2*ycoord (t+1) b=2*(b+3)*ycoord (t+1) b := by
  rw [y_two_step]
  ring

/-- **The signed index modulo `2(A+1)`**, as a pair over even and odd indices. -/
theorem sign_index (b t : V) :
    (ycoord (2*t) b+2*t)%(2*(b+3))=0 ∧ ycoord (2*t+1) b%(2*(b+3))=(2*t+1)%(2*(b+3)) := by
  have hm : 0<2*(b+3) := by simp
  have hk : (2*(b+3)+4)%(2*(b+3))=(4:V)%(2*(b+3)) :=
    mod_add_remove_left_of_dvd (dvd_refl _) hm
  have linear_rec (h : V) : (h+2)+h+2*(h+1)=4*(h+1) := by ring
  induction t using ISigma1.sigma1_succ_induction
  · definability
  case zero =>
    have hy1 : ycoord 1 b=1 := by simpa using y_succ (0:V) b
    simp [hy1]
  case succ t ih =>
    have h2 := transport_opposite (2*(b+3)) (2*(b+3)) 4 _ _ _ _ _ _ hm hk
      (y_rec b (2*t)) (linear_rec (2*t)) ih.1 ih.2
    have h2' : (ycoord (2*(t+1)) b+2*(t+1))%(2*(b+3))=0 := by
      simpa only [show 2*t+2=2*(t+1) by ring] using h2
    have h3 := transport_equal (2*(b+3)) (2*(b+3)) 4 _ _ _ _ _ _ hm hk
      (y_rec b (2*t+1)) (linear_rec (2*t+1)) ih.2
      (by simpa only [add_assoc,one_add_one_eq_two] using h2)
    refine ⟨h2',?_⟩
    simpa only [show 2*t+1+2=2*(t+1)+1 by ring] using h3

/-- **Even ordinates**: `ψ_A(2L) = 2A·P` with `P ≡ ±L (mod 4A²)`, the sign `(−1)^(L−1)`. -/
theorem even_ordinate (b L : V) :
    ∃ P : V, ycoord (2*L) b=2*(b+2)*P ∧
      ((P+L)%(4*(b+2)*(b+2))=0 ∨ P%(4*(b+2)*(b+2))=L%(4*(b+2)*(b+2))) := by
  have hd : 1≤delta b := pos_iff_one_le.mp (by unfold delta; exact mul_pos (by simp) (by simp))
  set a' : V := 2*delta b-1 with ha'
  have hx2 : xcoord 2 b=1+2*delta b := by
    have h := double_x (1:V) b
    have hy1 : ycoord 1 b=1 := by simpa using y_succ (0:V) b
    simpa only [mul_one,hy1] using h
  have hA : a'+2=xcoord 2 b := by
    rw [hx2,ha']
    have h1 : 1≤2*delta b := le_trans hd (by rw [two_mul]; exact le_add_self)
    calc 2*delta b-1+2=2*delta b-1+1+1 := by ring
      _=2*delta b+1 := by rw [tsub_add_cancel_of_le h1]
      _=1+2*delta b := by ring
  have hcomp := (composition a' b 2 hA L).2
  rw [y_two] at hcomp
  have hm : 4*(b+2)*(b+2)=2*(a'+3) := by
    have : a'+3=xcoord 2 b+1 := by rw [← hA]; ring
    rw [this,hx2]
    unfold delta
    ring
  refine ⟨ycoord L a',by rw [← hcomp]; ring,?_⟩
  rw [hm]
  obtain ⟨t,ht|ht⟩ := even_or_odd L
  · subst ht
    exact Or.inl (sign_index a' t).1
  · subst ht
    exact Or.inr (sign_index a' t).2

#print axioms sign_index
#print axioms even_ordinate

end DiophantineConsistency.ZRowsPellEvenChebyshev
