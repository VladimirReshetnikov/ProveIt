import IPRADerivations.AnalyticNumberTheory.Riemann.ResidueSpace
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-! Imported from the packet `analytic-number-theory/riemann_ipra_formalization_2026-11-20`,
`ResidueGram.lean`: the namespace is placed under `LeanProofs.IPRA.AnalyticNumberTheory.Riemann`, the imports
are rewritten to the library, and axioms are audited in `Checks/Axioms.lean`. -/

/-! Three closed Gram-determinant sentences without coefficient witnesses.
All matrix entries are nonnegative natural numbers. The numerical lemma
derives the determinant comparison by completing a rational quadratic form. -/
namespace LeanProofs.IPRA.AnalyticNumberTheory.Riemann.ResidueGram
open LeanProofs.ConciseIPRA PacketLanguage DivisorMatrices ResidueSpace

/-- Rows i<K correspond to generators R_{i+2}; row K is the target. -/
def sample (tar : Target) : PR 4 := program ["K","m","i","n"] <|
  iteE (eqB (v "i") (v "K"))
    (match tar with
     | .one => 1
     | .step => leB (v "m") (v "n")
     | .singleton => eqB (v "m") (v "n"))
    (modE (v "n") (v "i"+2))

/-- All entries are scaled by (J+1)P_J. -/
def entry (tar : Target) : PR 5 := program ["K","m","J","i","j"] <|
  let weightedSum := sumTo "n" (v "J") <|
    call (sample tar) [v "K",v "m",v "i",v "n"+1] *
    call (sample tar) [v "K",v "m",v "j",v "n"+1] *
    (prodTo "z" (v "J") <| iteE (eqB (v "z") (v "n")) 1 ((v "z"+1)*(v "z"+2)))
  let height := iteE (eqB (v "i") (v "K")) 1 (v "i"+1)
  (v "J"+1)*weightedSum + eqB (v "i") (v "j")*call denominator [v "J"]*(v "K"+1)*powE height 2

def leibniz (tar : Target) (odd : Bool) : PR 4 := program ["K","m","J","size"] <|
  sumTo "w" (powE (v "size") (v "size")) <|
    call permOK [v "size",v "w"] *
    eqB (modE (call inversions [v "size",v "w"]) 2) (if odd then 1 else 0) *
    (prodTo "i" (v "size") <| call (entry tar) [v "K",v "m",v "J",v "i",
      digitE (v "w") (v "size") (v "i")])

/-- The diagonal ridge makes the principal minors strictly positive. -/
def minor (tar : Target) : PR 4 := program ["K","m","J","size"] <|
  let args := [v "K",v "m",v "J",v "size"]
  call (leibniz tar false) args - call (leibniz tar true) args

def sentence (tar : Target) : Fm PTm 0 := allN (ctx := []) "m" <| allN "t" <|
  exN "K" <| exN "J" <| zeroTest <|
    let block := call (minor tar) [v "K",v "m"+1,v "J",v "K"+1]
    let core := call (minor tar) [v "K",v "m"+1,v "J",v "K"]
    (v "t"+1)*block - (v "J"+1)*call denominator [v "J"]*core

section Quadratic
open Matrix
open scoped Matrix
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Weighted design Gram matrix with a coordinatewise diagonal penalty. -/
def ridge {ν : Type*} [Fintype ν] [DecidableEq ν] (X : Matrix ν ι ℚ)
    (a : ν → ℚ) (d : ι → ℚ) : Matrix ι ι ℚ :=
  Xᵀ * (Matrix.diagonal a * X) + Matrix.diagonal d

theorem ridge_square {ν : Type*} [Fintype ν] [DecidableEq ν] (X : Matrix ν ι ℚ)
    (a : ν → ℚ) (d v : ι → ℚ) :
    v ⬝ᵥ (ridge X a d *ᵥ v) =
      (∑ j, a j*((X *ᵥ v) j)^2) + ∑ i, d i*(v i)^2 := by
  rw [ridge,Matrix.add_mulVec,dotProduct_add,← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,
    Matrix.dotProduct_transpose_mulVec]
  unfold dotProduct
  simp_rw [Matrix.mulVec_diagonal]
  congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring

theorem ridge_pos {ν : Type*} [Fintype ν] [DecidableEq ν] (X : Matrix ν ι ℚ)
    (a : ν → ℚ) (d v : ι → ℚ) (ha : ∀ j, 0 ≤ a j) (hd : ∀ i, 0 < d i)
    (h : ∃ i, v i ≠ 0) : 0 < v ⬝ᵥ (ridge X a d *ᵥ v) := by
  rw [ridge_square]
  have hobs : 0 ≤ ∑ j, a j*((X *ᵥ v) j)^2 := Finset.sum_nonneg fun j _ =>
    mul_nonneg (ha j) (sq_nonneg _)
  apply add_pos_of_nonneg_of_pos hobs
  apply Finset.sum_pos' (fun i _ => mul_nonneg (hd i).le (sq_nonneg _))
  obtain ⟨i, hi⟩ := h
  exact ⟨i, Finset.mem_univ _, mul_pos (hd i) (sq_pos_of_ne_zero hi)⟩

def objective (A : Matrix ι ι ℚ) (b x : ι → ℚ) (d : ℚ) : ℚ :=
  x ⬝ᵥ (A *ᵥ x) - 2 * (b ⬝ᵥ x) + d

omit [DecidableEq ι] in
theorem complete (A : Matrix ι ι ℚ) (b x z : ι → ℚ) (d : ℚ)
    (hs : Aᵀ = A) (hz : A *ᵥ z = b) :
    objective A b x d = (x-z) ⬝ᵥ (A *ᵥ (x-z)) + (d-b ⬝ᵥ z) := by
  have sym := Matrix.dotProduct_transpose_mulVec A z x
  rw [hs,hz] at sym
  rw [objective, Matrix.mulVec_sub, sub_dotProduct, dotProduct_sub, dotProduct_sub,hz,sym,
    dotProduct_comm x b,dotProduct_comm z b]
  ring

def col (b : ι → ℚ) : Matrix ι Unit ℚ := fun i _ => b i
def row (b : ι → ℚ) : Matrix Unit ι ℚ := fun _ i => b i
def corner (d : ℚ) : Matrix Unit Unit ℚ := fun _ _ => d

theorem block_value (A : Matrix ι ι ℚ) [Invertible A] (b : ι → ℚ) (d : ℚ) :
    (Matrix.fromBlocks A (col b) (row b) (corner d)).det =
      A.det*(d-b ⬝ᵥ (⅟A *ᵥ b)) := by
  rw [Matrix.det_fromBlocks₁₁, Matrix.det_unique (corner d - (row b * ⅟A) * col b), Matrix.mul_assoc]
  rfl

/-- Existence of a rational approximant is equivalent to the determinant
inequality for this finite quadratic program. -/
theorem eliminate (A : Matrix ι ι ℚ) [Invertible A] (b : ι → ℚ) (d t s : ℚ)
    (hs : Aᵀ = A) (hpos : ∀ y : ι → ℚ, 0 ≤ y ⬝ᵥ (A *ᵥ y))
    (hdet : 0 < A.det) (ht : 0 ≤ t) :
    (∃ x, t*objective A b x d ≤ s) ↔
      t*(Matrix.fromBlocks A (col b) (row b) (corner d)).det ≤ s*A.det := by
  let z := ⅟A *ᵥ b
  have hz : A *ᵥ z = b := by simp [z, Matrix.mulVec_mulVec]
  rw [block_value]
  change _ ↔ t*(A.det*(d-b ⬝ᵥ z)) ≤ s*A.det
  rw [show t*(A.det*(d-b ⬝ᵥ z)) = (t*(d-b ⬝ᵥ z))*A.det by ring,
    mul_le_mul_iff_left₀ hdet]
  constructor
  · rintro ⟨x,hx⟩
    rw [complete A b x z d hs hz] at hx
    exact (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (hpos (x-z))) ht).trans hx
  · intro h
    refine ⟨z,?_⟩
    rw [complete A b z z d hs hz]
    simpa using h

end Quadratic
end LeanProofs.IPRA.AnalyticNumberTheory.Riemann.ResidueGram
