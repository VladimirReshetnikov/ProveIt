import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.ArithmeticPow
import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Tactic.LinearCombination

/-! Three-modulus rank-chart CRT with an arbitrarily large natural magnitude. -/
set_option autoImplicit false
set_option Elab.async false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace Trace74RankCRTModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing

section Ring
variable {R : Type*} [CommRing R]

/-- A commutative-ring CRT construction, without a quotient-ring API. -/
theorem merge (m n x y : R) (h : IsCoprime m n) :
    ∃ z : R, m ∣ z-x ∧ n ∣ z-y := by
  obtain ⟨u,v,huv⟩ := h
  refine ⟨x*(v*n)+y*(u*m), ?_, ?_⟩
  · refine ⟨u*(y-x), ?_⟩
    linear_combination x*huv
  · refine ⟨v*(x-y), ?_⟩
    linear_combination y*huv

/-- Solve one linear residue from its explicit Bézout certificate. -/
theorem linear_solution (U m a : R) (h : IsCoprime U m) :
    ∃ x : R, m ∣ U*x+a := by
  obtain ⟨u,v,huv⟩ := h
  refine ⟨-u*a, v*a, ?_⟩
  linear_combination -a*huv

/-- Simultaneously solve three linear congruences. All coprimalities are
explicit, including those for the different coefficients. -/
theorem three_linear (D c h U W a b : R)
    (hDc : IsCoprime D c) (hDh : IsCoprime D h) (hch : IsCoprime c h)
    (hUD : IsCoprime U D) (hUc : IsCoprime U c) (hWh : IsCoprime W h) :
    ∃ z : R, D ∣ U*z+a ∧ c ∣ U*z+b ∧ h ∣ W*z-1 := by
  obtain ⟨x,hx⟩ := linear_solution U D a hUD
  obtain ⟨y,hy⟩ := linear_solution U c b hUc
  obtain ⟨v,hv⟩ := linear_solution W h (-1) hWh
  have hv' : h ∣ W*v-1 := by simpa only [sub_eq_add_neg] using hv
  obtain ⟨z,hzx,hzy⟩ := merge D c x y hDc
  have hzD : D ∣ U*z+a := by
    have hd := dvd_add (dvd_mul_of_dvd_right hzx U) hx
    convert hd using 1 <;> ring
  have hzc : c ∣ U*z+b := by
    have hd := dvd_add (dvd_mul_of_dvd_right hzy U) hy
    convert hd using 1 <;> ring
  obtain ⟨z',hz'z,hz'v⟩ := merge (D*c) h z v (hDh.mul_left hch)
  have hzD' : D ∣ z'-z := dvd_trans (show D ∣ D*c from ⟨c,rfl⟩) hz'z
  have hzc' : c ∣ z'-z := dvd_trans (show c ∣ D*c from ⟨D,by ring⟩) hz'z
  refine ⟨z', ?_, ?_, ?_⟩
  · have hd := dvd_add (dvd_mul_of_dvd_right hzD' U) hzD
    convert hd using 1 <;> ring
  · have hd := dvd_add (dvd_mul_of_dvd_right hzc' U) hzc
    convert hd using 1 <;> ring
  · have hd := dvd_add (dvd_mul_of_dvd_right hz'v W) hv'
    convert hd using 1 <;> ring
end Ring

section Model
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The CRT solution can be made larger than any internal natural bound by
adding a multiple of all three positive moduli. The targets may be signed. -/
theorem positive_three_linear (D c h U W bound : V) (a b : DiffRing V)
    (hD : 0<D) (hc : 0<c) (hh : 0<h)
    (hDc : IsCoprime (ι D : DiffRing V) (ι c))
    (hDh : IsCoprime (ι D : DiffRing V) (ι h))
    (hch : IsCoprime (ι c : DiffRing V) (ι h))
    (hUD : IsCoprime (ι U : DiffRing V) (ι D))
    (hUc : IsCoprime (ι U : DiffRing V) (ι c))
    (hWh : IsCoprime (ι W : DiffRing V) (ι h)) :
    ∃ N : V, bound<N ∧ (ι D : DiffRing V) ∣ ι U*ι N+a ∧
      (ι c : DiffRing V) ∣ ι U*ι N+b ∧ (ι h : DiffRing V) ∣ ι W*ι N-1 := by
  obtain ⟨z,hzD,hzc,hzh⟩ := three_linear (ι D : DiffRing V) (ι c) (ι h) (ι U) (ι W) a b hDc hDh hch hUD hUc hWh
  let P : DiffRing V := ι D*ι c*ι h
  let T : DiffRing V := ι bound+1+|z|
  have hP : (1:DiffRing V)≤P := by
    have hp : (1:V)≤D*c*h := pos_iff_one_le.mp (mul_pos (mul_pos hD hc) hh)
    dsimp [P]
    simpa only [map_mul,map_one] using ι_le_ι.mpr hp
  have hT : (0:DiffRing V)≤T := by
    have hb := ι_nonneg bound
    have hz := abs_nonneg z
    dsimp [T]
    linarith
  have hPT := mul_le_mul_of_nonneg_right hP hT
  have hzabs := neg_le_abs z
  have hbound : (ι bound:DiffRing V)+1≤z+P*T := by dsimp [T] at *; linarith
  obtain ⟨N,hN⟩ := nonneg_iff.mp (show (0:DiffRing V)≤z+P*T by linarith [ι_nonneg bound])
  have hNgt : bound<N := ι_lt_ι.mp (by rw [←hN]; linarith)
  have hdD : (ι D : DiffRing V)∣P*T := ⟨ι c*ι h*T, by dsimp [P]; ring⟩
  have hdc : (ι c : DiffRing V)∣P*T := ⟨ι D*ι h*T, by dsimp [P]; ring⟩
  have hdh : (ι h : DiffRing V)∣P*T := ⟨ι D*ι c*T, by dsimp [P]; ring⟩
  refine ⟨N,hNgt,?_,?_,?_⟩
  · rw [←hN]
    have h := dvd_add hzD (dvd_mul_of_dvd_right hdD (ι U))
    convert h using 1 <;> ring
  · rw [←hN]
    have h := dvd_add hzc (dvd_mul_of_dvd_right hdc (ι U))
    convert h using 1 <;> ring
  · rw [←hN]
    have h := dvd_add hzh (dvd_mul_of_dvd_right hdh (ι W))
    convert h using 1 <;> ring
end Model

#print axioms Trace74RankCRTModel.three_linear
#print axioms Trace74RankCRTModel.positive_three_linear
end Trace74RankCRTModel
