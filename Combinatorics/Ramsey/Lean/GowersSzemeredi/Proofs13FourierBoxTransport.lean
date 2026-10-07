import GowersSzemeredi.Proofs13OddFourierSquare
import GowersSzemeredi.Proofs05BoxPartition

/-! Transporting the two-dimensional Fourier square into the box conventions
used by the polynomial phase-removal theorem. -/

set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open scoped BigOperators

/-- Cube differences list the two directions in reverse order. -/
def fourierSquareEquiv (N : Nat) : Pair N ≃ Point N 2 where
  toFun z := ![z.2, z.1]
  invFun x := (x 1, x 0)
  left_inv z := by ext <;> simp
  right_inv x := by funext i; fin_cases i <;> simp

theorem fourierSquare_cubeDifference {N : Nat} (f : ZMod N → Complex) (z : Pair N) :
    cubeDifference f (fourierSquareEquiv N z) = secondDifference f z.1 z.2 := by
  change cubeDifference f (Fin.cons z.2 (Fin.cons z.1 (fun i => Fin.elim0 i))) = _
  rw [cubeDifference_cons, cubeDifference_cons]
  simp only [cubeDifference, List.ofFn_zero, iteratedDifference, secondDifference]

/-- A bilinear polynomial becomes a Boolean-monomial multilinear polynomial
under the coordinate convention of the cube difference. -/
theorem IsBilinear.to_multilinear {N : Nat} {mu : Pair N → ZMod N} (hmu : IsBilinear mu) :
    IsMultilinear (fun x : Point N 2 => mu ((fourierSquareEquiv N).symm x)) := by
  classical
  obtain ⟨c00, c10, c01, c11, hmu⟩ := hmu
  let e : (Bool × Bool) ≃ (Fin 2 → Bool) := {
    toFun b := ![b.1, b.2]
    invFun v := (v 0, v 1)
    left_inv b := by ext <;> simp
    right_inv v := by funext i; fin_cases i <;> simp }
  refine ⟨fun b => if b 0 then (if b 1 then c11 else c01) else (if b 1 then c10 else c00), ?_⟩
  intro x
  dsimp only
  rw [hmu, ← e.sum_comp]
  simp [e, fourierSquareEquiv, Fintype.sum_prod_type, Fin.prod_univ_two]
  ring

/-- The square regarded as a two-dimensional box, with reversed axes. -/
def fourierSquareBox {N : Nat} (P Q : ModAP N) (hstep : P.step = Q.step) : Box N 2 where
  axis := ![Q, P]
  commonDiff := P.step
  axis_step := by intro i; fin_cases i <;> simp [hstep]

theorem fourierSquareBox_axis_length {N m : Nat} (P Q : ModAP N) (hstep : P.step = Q.step)
    (hP : P.length = m) (hQ : Q.length = m) (i : Fin 2) :
    ((fourierSquareBox P Q hstep).axis i).length = m := by
  fin_cases i <;> simp [fourierSquareBox, hP, hQ]

theorem fourierSquareBox_width {N m : Nat} (P Q : ModAP N) (hstep : P.step = Q.step)
    (hP : P.length = m) (hQ : Q.length = m) : (fourierSquareBox P Q hstep).width = m := by
  apply le_antisymm
  · simpa only [fourierSquareBox_axis_length P Q hstep hP hQ] using
      (fourierSquareBox P Q hstep).width_le_axis_length 0
  · exact Box.le_width_of_le_axis _ (by omega) (fun i => (fourierSquareBox_axis_length P Q hstep hP hQ i).ge)

theorem fourierSquareBox_mem {N : Nat} [NeZero N] (P Q : ModAP N) (hstep : P.step = Q.step)
    (z : Pair N) : fourierSquareEquiv N z ∈ (fourierSquareBox P Q hstep).carrier ↔
      z ∈ P.carrier.product Q.carrier := by
  classical
  simp only [Box.carrier, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro h
    apply Finset.mem_product.mpr
    exact ⟨by simpa [fourierSquareBox, fourierSquareEquiv] using h 1,
      by simpa [fourierSquareBox, fourierSquareEquiv] using h 0⟩
  · intro hz i
    obtain ⟨hP, hQ⟩ := Finset.mem_product.mp hz
    fin_cases i <;> simp [fourierSquareBox, fourierSquareEquiv, hP, hQ]

/-- Pointwise large Fourier coefficients on a dense part of a square imply
the normalized second-moment input to Proposition 17.7. -/
theorem fourierSquare_energy {N m : Nat} [NeZero N]
    (P Q : ModAP N) (hstep : P.step = Q.step) (B : Finset (Pair N))
    (f : ZMod N → Complex) (mu : Pair N → ZMod N) (alpha delta : Real)
    (hα : 0 ≤ alpha) (hB : B ⊆ P.carrier.product Q.carrier)
    (hmass : delta * m * m ≤ B.card)
    (hfourier : ∀ z, z ∈ B → alpha * N / 2 ≤ ‖secondDifferenceFourier f z.1 z.2 (mu z)‖) :
    (delta * alpha ^ 2 / 4) * (N : Real) ^ 2 * (m : Real) ^ 2 ≤
      ∑ x ∈ (fourierSquareBox P Q hstep).carrier,
        ‖fourier (cubeDifference f x) (mu ((fourierSquareEquiv N).symm x))‖ ^ 2 := by
  classical
  let E := B.image (fourierSquareEquiv N)
  have hE : E ⊆ (fourierSquareBox P Q hstep).carrier := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    exact (fourierSquareBox_mem P Q hstep z).mpr (hB hz)
  have hcard : E.card = B.card := Finset.card_image_iff.mpr (fourierSquareEquiv N).injective.injOn
  have hpoint : ∀ x ∈ E, (alpha * N / 2) ^ 2 ≤
      ‖fourier (cubeDifference f x) (mu ((fourierSquareEquiv N).symm x))‖ ^ 2 := by
    intro x hx
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hx
    rw [fourierSquare_cubeDifference, Equiv.symm_apply_apply]
    exact pow_le_pow_left₀ (by positivity) (hfourier z hz) 2
  have hmass' := mul_le_mul_of_nonneg_right hmass (sq_nonneg (alpha * N / 2))
  calc
    _ ≤ (B.card : Real) * (alpha * N / 2) ^ 2 := by nlinarith only [hmass']
    _ = ∑ _x ∈ E, (alpha * N / 2) ^ 2 := by simp [hcard]
    _ ≤ ∑ x ∈ E, ‖fourier (cubeDifference f x) (mu ((fourierSquareEquiv N).symm x))‖ ^ 2 :=
      Finset.sum_le_sum hpoint
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hE (fun _ _ _ => sq_nonneg _)

end LeanProofs.GowersSzemeredi
