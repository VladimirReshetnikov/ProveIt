import IPRADerivations.Analysis.GaussianRationalProductAlgebra
import IPRADerivations.Core.Fubini
import IPRADerivations.Core.MultiSums

/-!
# Rectangular Gaussian-rational products

Rows, columns and contiguous blocks all use the original rational
product fold. Swapping the two internal indices requires no apartness
hypotheses. A rectangle of adjacent blocks agrees with the single
product over their concatenation, including when either count is zero.
-/

set_option autoImplicit false
set_option linter.unusedSimpArgs false

namespace LeanProofs.IPRA.Analysis.GaussianRationalRectangularProduct

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianRationalFiniteProduct (qprod product_zero product_succ product_index_congr
  product_congr_bounded product_split offset_at)
open GaussianRationalFiniteSum (termsEqual)
open GaussianRationalHorner (qmul)
open GaussianRationalProductAlgebra (multiplyBody multiply_body_at product_multiply
  oneTerms product_one_of_terms)
open GaussianRationalSyntheticDivision (qone qmul_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (zero succ)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def rowBody (t : PTm 3) : PTm 2 := inst3 t (fstT (var 1)) (var 0) (sndT (var 1))
def row (t : PTm 3) (i B x : PTm n) : PTm n := qprod (rowBody t) B (pairT i x)
def rectangleBody (t : PTm 3) : PTm 2 := row t (var 0) (fstT (var 1)) (sndT (var 1))
def rectangle (t : PTm 3) (A B x : PTm n) : PTm n := qprod (rectangleBody t) A (pairT B x)
def swap (t : PTm 3) : PTm 3 := inst3 t (var 1) (var 0) (var 2)

@[simp] theorem swap_at (t : PTm 3) (i j x : PTm n) :
    inst3 (swap t) i j x = inst3 t j i x := by
  simp only [swap,inst3,Syn.subst_subst]
  congr 1
  funext k
  fin_cases k <;> rfl

@[simp] theorem subst_row {m : ℕ} (σ : Fin n → PTm m) (t : PTm 3) (i B x : PTm n) :
    Syn.subst σ (row t i B x) = row t (Syn.subst σ i) (Syn.subst σ B) (Syn.subst σ x) := by
  simp [row]

@[simp] theorem subst_rectangle {m : ℕ} (σ : Fin n → PTm m) (t : PTm 3) (A B x : PTm n) :
    Syn.subst σ (rectangle t A B x) = rectangle t (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ x) := by
  simp [rectangle]

theorem row_at (t : PTm 3) (i j x : PTm n) : Γ ⊢[PRAAx]
    inst2 (rowBody t) j (pairT i x) ≐ inst3 t i j x := by
  simpa [rowBody,inst2] using congrInst3 t (fst_pair i x) (.eqRefl j) (snd_pair i x)

theorem row_congr (t : PTm 3) {i j A B x y : PTm n} (hi : Γ ⊢[PRAAx] i ≐ j)
    (hB : Γ ⊢[PRAAx] A ≐ B) (hx : Γ ⊢[PRAAx] x ≐ y) : Γ ⊢[PRAAx] row t i A x ≐ row t j B y :=
  product_index_congr _ hB (congrPairT hi hx)

theorem rectangle_at (t : PTm 3) (i B x : PTm n) : Γ ⊢[PRAAx]
    inst2 (rectangleBody t) i (pairT B x) ≐ row t i B x := by
  simpa [rectangleBody,inst2] using row_congr t (.eqRefl i) (fst_pair B x) (snd_pair B x)

theorem row_succ (t : PTm 3) (i B x : PTm n) : Γ ⊢[PRAAx]
    row t i (succ B) x ≐ qmul (row t i B x) (inst3 t i B x) :=
  (product_succ _ B (pairT i x)).eqTrans (qmul_congr (.eqRefl _) (row_at t i B x))

theorem rectangle_succ (t : PTm 3) (A B x : PTm n) : Γ ⊢[PRAAx]
    rectangle t (succ A) B x ≐ qmul (rectangle t A B x) (row t A B x) :=
  (product_succ _ A (pairT B x)).eqTrans (qmul_congr (.eqRefl _) (rectangle_at t A B x))

theorem empty_columns (t : PTm 3) (A x : PTm n) : Γ ⊢[PRAAx] rectangle t A zero x ≐ qone := by
  apply product_one_of_terms (rectangleBody t) A (pairT zero x)
  refine .allI (.impI ?_)
  simpa [oneTerms,Syn.shift] using
    (rectangle_at (Γ := lt (var 0) (Syn.shift A) :: Γ.map Fm.shift) t (var 0) zero (Syn.shift x)).eqTrans
      (product_zero (rowBody t) (pairT (var 0) (Syn.shift x)))

theorem add_column (t : PTm 3) (A B x : PTm n) : Γ ⊢[PRAAx]
    rectangle t A (succ B) x ≐ qmul (rectangle t A B x) (row (swap t) B A x) := by
  have same : Γ ⊢[PRAAx] termsEqual (rectangleBody t) (multiplyBody (rectangleBody t) (rowBody (swap t)))
      A (pairT (succ B) x) (pairT B x) := by
    refine .allI (.impI ?_)
    let Δ := lt (var 0) (Syn.shift A) :: Γ.map Fm.shift
    let b := Syn.shift B
    let y := Syn.shift x
    let i : PTm (n+1) := var 0
    have last : Δ ⊢[PRAAx] inst2 (rowBody (swap t)) i (pairT b y) ≐ inst3 t i b y := by
      simpa only [swap_at] using row_at (Γ := Δ) (swap t) b i y
    have result := (rectangle_at (Γ := Δ) t i (succ b) y).eqTrans
      ((row_succ t i b y).eqTrans (qmul_congr (rectangle_at t i b y).eqSymm last.eqSymm))
    simpa [termsEqual,Syn.shift,Δ,b,y,i] using result
  exact (product_congr_bounded _ _ _ _ _ same).eqTrans (product_multiply _ _ A (pairT B x))

def transposeLaw (t : PTm 3) (A B x : PTm n) : Fm PTm n :=
  rectangle t A B x ≐ rectangle (swap t) B A x

@[simp] theorem subst_transposeLaw {m : ℕ} (σ : Fin n → PTm m) (t : PTm 3) (A B x : PTm n) :
    (transposeLaw t A B x).subst σ = transposeLaw t (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ x) := by
  simp [transposeLaw]

theorem transpose (t : PTm 3) (A B x : PTm n) : Γ ⊢[PRAAx] transposeLaw t A B x := by
  have all : Γ ⊢[PRAAx] .all (transposeLaw t (Syn.shift A) (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_transposeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (empty_columns t A x).eqTrans (product_zero (rectangleBody (swap t)) (pairT A x)).eqSymm
    · simp only [subst_transposeLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact (add_column t _ _ _).eqTrans
        ((qmul_congr Prf.hyp0 (.eqRefl _)).eqTrans (rectangle_succ (swap t) _ _ _).eqSymm)
  simpa only [subst_transposeLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE B

def blockEntry (t : PTm 2) : PTm 3 :=
  inst2 t (fstT (var 2)*var 0+var 1) (sndT (var 2))

theorem block_entry_at (t : PTm 2) (A i j x : PTm n) : Γ ⊢[PRAAx]
    inst3 (blockEntry t) i j (pairT A x) ≐ inst2 t (A*i+j) x := by
  have entry : inst3 (blockEntry t) i j (pairT A x) =
      inst2 t (fstT (pairT A x)*i+j) (sndT (pairT A x)) := by
    simp only [blockEntry,inst3,inst2,Syn.subst_subst]
    congr 1
    funext k
    fin_cases k <;> simp [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  rw [entry]
  exact congrInst2 t (congrAdd (congrMul (fst_pair A x) (.eqRefl i)) (.eqRefl j)) (snd_pair A x)

theorem block_row (t : PTm 2) (A i x : PTm n) : Γ ⊢[PRAAx]
    row (blockEntry t) i A (pairT A x) ≐ qprod (offB t) A (pairT (A*i) x) := by
  apply product_congr_bounded
  refine .allI (.impI ?_)
  let Δ := lt (var 0) (Syn.shift A) :: Γ.map Fm.shift
  let a := Syn.shift A
  let b := Syn.shift i
  let y := Syn.shift x
  have result := (row_at (Γ := Δ) (blockEntry t) b (var 0) (pairT a y)).eqTrans
    ((block_entry_at t a b (var 0) y).eqTrans (offset_at t (a*b) (var 0) y).eqSymm)
  simpa [termsEqual,Syn.shift,Δ,a,b,y] using result

def blocksLaw (t : PTm 2) (A B x : PTm n) : Fm PTm n :=
  rectangle (blockEntry t) B A (pairT A x) ≐ qprod t (A*B) x

@[simp] theorem subst_blocksLaw {m : ℕ} (σ : Fin n → PTm m) (t : PTm 2) (A B x : PTm n) :
    (blocksLaw t A B x).subst σ = blocksLaw t (Syn.subst σ A) (Syn.subst σ B) (Syn.subst σ x) := by
  simp [blocksLaw]

theorem blocks_step (t : PTm 2) (A B x : PTm n) (ih : Γ ⊢[PRAAx] blocksLaw t A B x) :
    Γ ⊢[PRAAx] blocksLaw t A (succ B) x :=
  (rectangle_succ (blockEntry t) B A (pairT A x)).eqTrans
    ((qmul_congr ih (block_row t A B x)).eqTrans
      ((product_split t (A*B) A x).eqSymm.eqTrans
        (product_index_congr t (mul_succ A B).eqSymm (.eqRefl _))))

theorem blocks (t : PTm 2) (A B x : PTm n) : Γ ⊢[PRAAx] blocksLaw t A B x := by
  have all : Γ ⊢[PRAAx] .all (blocksLaw t (Syn.shift A) (var 0) (Syn.shift x)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_blocksLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift]
      exact (product_zero (rectangleBody (blockEntry t)) (pairT A (pairT A x))).eqTrans
        ((product_index_congr t (mul_zero A) (.eqRefl _)).eqTrans (product_zero t x)).eqSymm
    · simp only [subst_blocksLaw,Syn.subst_var,Syn.repl_zero,subst_repl_shift]
      exact blocks_step t _ _ _ Prf.hyp0
  simpa only [subst_blocksLaw,Syn.subst_var,Syn.inst_zero,Syn.subst_inst_shift] using all.allE B

theorem actual_rectangular_product_transpose_closed (t : PTm 3) : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    univ 3 (transposeLaw t (var 0) (var 1) (var 2)) :=
  closeUniv 3 (transpose t _ _ _)

theorem actual_rectangular_product_blocks_closed (t : PTm 2) : ([] : List (Fm PTm 0)) ⊢[PRAAx]
    univ 3 (blocksLaw t (var 0) (var 1) (var 2)) :=
  closeUniv 3 (blocks t _ _ _)

end LeanProofs.IPRA.Analysis.GaussianRationalRectangularProduct
