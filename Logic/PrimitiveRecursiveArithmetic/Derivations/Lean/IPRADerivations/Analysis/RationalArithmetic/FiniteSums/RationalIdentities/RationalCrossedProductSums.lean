import IPRADerivations.Analysis.Polynomials.SpecialPolynomials.RationalReverseChebyshevCell
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalSumAdditivity
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalIdentities.RationalSumConstants

/-!
# Finite crossed-product comparison on rational rectangles

Compare all pairs of entries in two finite rows. The four terms sum
to products of the actual scalar sums, retaining the cell margin
multiplied by the number of cells in the rectangle.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.RationalCrossedProductSums

open_ipra
open GaussianEuclideanDistanceName (fraction subst_fraction)
open RationalAlgebra (add_congr add_associative add_commutative multiply_congr multiply_commutative
  multiply_add multiply_associative)
open RationalArgmin (rationalLE rationalLE_congr subst_rationalLE)
open RationalArithmetic (add add_guard multiply multiply_guard subst_add subst_multiply)
open RationalFiniteSum (term sum termwiseLE sum_monotone subst_term subst_sum)
open RationalNormalForm (wellFormed)
open RationalSumAdditivity (addedBody addedSum added_term sum_additive)
open RationalSumConstants (constantBody term_constant sum_constant)
open RationalSumLinearity (scaledBody scaledSum scaled_term sum_homogeneous)

variable {n : ℕ} {Γ : List (Fm PTm n)}

def productBody (F G : PTm 2) : PTm 2 := multiply F G

theorem product_at (F G : PTm 2) (i x : PTm n) :
    term (productBody F G) i x = multiply (term F i x) (term G i x) := by
  simp only [term,productBody,inst2,subst_multiply]

def cell (h w u v c : PTm n) : Fm PTm n :=
  rationalLE (add (add (multiply h w) c) (multiply u v)) (add (multiply h v) (multiply w u))

@[simp] theorem subst_cell {l : ℕ} (σ : Fin n → PTm l) (h w u v c : PTm n) :
    (cell h w u v c).subst σ = cell (Syn.subst σ h) (Syn.subst σ w) (Syn.subst σ u) (Syn.subst σ v)
      (Syn.subst σ c) := by simp only [cell,subst_rationalLE,subst_add,subst_multiply]

def rowCells (P Q : PTm 2) (h w N y c : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift N) ⟶
    cell (Syn.shift h) (Syn.shift w) (term P (var 0) (Syn.shift y)) (term Q (var 0) (Syn.shift y)) (Syn.shift c))

@[simp] theorem subst_rowCells {l : ℕ} (σ : Fin n → PTm l) (P Q : PTm 2) (h w N y c : PTm n) :
    (rowCells P Q h w N y c).subst σ =
      rowCells P Q (Syn.subst σ h) (Syn.subst σ w) (Syn.subst σ N) (Syn.subst σ y) (Syn.subst σ c) := by
  simp only [rowCells,Fm.subst_all,Fm.subst_imp,subst_lt,subst_cell,
    subst_term,Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

def rectangleCells (F G P Q : PTm 2) (M N x y c : PTm n) : Fm PTm n := .all
  (lt (var 0) (Syn.shift M) ⟶ rowCells P Q (term F (var 0) (Syn.shift x)) (term G (var 0) (Syn.shift x))
    (Syn.shift N) (Syn.shift y) (Syn.shift c))

@[simp] theorem subst_rectangleCells {l : ℕ} (σ : Fin n → PTm l) (F G P Q : PTm 2) (M N x y c : PTm n) :
    (rectangleCells F G P Q M N x y c).subst σ =
      rectangleCells F G P Q (Syn.subst σ M) (Syn.subst σ N) (Syn.subst σ x) (Syn.subst σ y) (Syn.subst σ c) := by
  simp only [rectangleCells,Fm.subst_all,Fm.subst_imp,subst_lt,subst_rowCells,
    subst_term,Syn.subst_var,Syn.up_zero,Syn.up_succ,Syn.subst_shift,Syn.shift_subst]

private theorem left_row_at (P Q : PTm 2) (i y b : PTm n) :
    Γ ⊢[PRAAx] term (addedBody constantBody (productBody P Q)) i (pairT b y) ≐
      add b (multiply (term P i y) (term Q i y)) := by
  rw [← product_at P Q i y]
  simpa only [term_constant] using added_term (Γ := Γ) constantBody (productBody P Q) i b y

private theorem right_row_at (P Q : PTm 2) (i y h w : PTm n) :
    Γ ⊢[PRAAx] term (addedBody (scaledBody Q) (scaledBody P)) i (pairT (pairT h y) (pairT w y)) ≐
      add (multiply h (term Q i y)) (multiply w (term P i y)) :=
  (added_term _ _ _ _ _).eqTrans (add_congr (scaled_term Q i h y) (scaled_term P i w y))

set_option maxHeartbeats 500000 in
theorem row_order (P Q : PTm 2) (h w N y c : PTm n) (hc : Γ ⊢[PRAAx] rowCells P Q h w N y c) :
    Γ ⊢[PRAAx] rationalLE
      (add (multiply (fraction N one) (multiply h w))
        (add (sum (productBody P Q) N y) (multiply (fraction N one) c)))
      (add (multiply h (sum Q N y)) (multiply w (sum P N y))) := by
  let b := add (multiply h w) c
  let U := addedBody constantBody (productBody P Q)
  let V := addedBody (scaledBody Q) (scaledBody P)
  have all : Γ ⊢[PRAAx] termwiseLE U V N (pairT b y) (pairT (pairT h y) (pairT w y)) := by
    refine .allI (.impI ?_)
    let sh (t : PTm n) := Syn.shift t
    let i : PTm (n+1) := var 0
    let Δ := lt i (sh N) :: Γ.map Fm.shift
    let b' := add (multiply (sh h) (sh w)) (sh c)
    have step : Δ ⊢[PRAAx] cell (sh h) (sh w) (term P i (sh y)) (term Q i (sh y)) (sh c) :=
      Prf.impE hc.allOpen.wk Prf.hyp0
    change Δ ⊢[PRAAx] rationalLE (term U i (sh (pairT b y))) (term V i (sh (pairT (pairT h y) (pairT w y))))
    simp only [b,sh,Syn.shift,subst_pairT,subst_add,subst_multiply]
    exact rationalLE_congr (left_row_at P Q i (sh y) b').eqSymm
      (right_row_at P Q i (sh y) (sh h) (sh w)).eqSymm step
  have l : Γ ⊢[PRAAx] addedSum constantBody (productBody P Q) N b y ≐
      add (multiply (fraction N one) (multiply h w))
        (add (sum (productBody P Q) N y) (multiply (fraction N one) c)) := by
    have a := (sum_constant (Γ := Γ) N b (add_guard _ _)).eqTrans
      ((multiply_commutative _ _).eqTrans (multiply_add (fraction N one) (multiply h w) c))
    exact (sum_additive _ _ _ _ _).eqTrans
      ((add_congr a (.eqRefl _)).eqTrans ((add_associative _ _ _).eqTrans
        (add_congr (.eqRefl _) (add_commutative _ _))))
  have r := (sum_additive (Γ := Γ) (scaledBody Q) (scaledBody P) N (pairT h y) (pairT w y)).eqTrans
    (add_congr (sum_homogeneous Q N h y) (sum_homogeneous P N w y))
  exact rationalLE_congr l r (sum_monotone _ _ _ _ _ all)

set_option maxHeartbeats 500000 in
theorem rectangle_order (F G P Q : PTm 2) (M N x y c : PTm n)
    (hc : Γ ⊢[PRAAx] rectangleCells F G P Q M N x y c) :
    Γ ⊢[PRAAx] rationalLE
      (add (add (multiply (fraction N one) (sum (productBody F G) M x))
        (multiply (fraction M one) (sum (productBody P Q) N y))) (multiply (fraction (M*N) one) c))
      (add (multiply (sum F M x) (sum Q N y)) (multiply (sum G M x) (sum P N y))) := by
  let T := productBody F G
  let J := sum (productBody P Q) N y
  let Psum := sum P N y
  let Qsum := sum Q N y
  let C := fraction N one
  let D := fraction M one
  let K := add J (multiply C c)
  let U := addedBody (scaledBody T) constantBody
  let V := addedBody (scaledBody F) (scaledBody G)
  have all : Γ ⊢[PRAAx] termwiseLE U V M (pairT (pairT C x) K) (pairT (pairT Qsum x) (pairT Psum x)) := by
    refine .allI (.impI ?_)
    let sh (t : PTm n) := Syn.shift t
    let i : PTm (n+1) := var 0
    let Δ := lt i (sh M) :: Γ.map Fm.shift
    have rows : Δ ⊢[PRAAx] rowCells P Q (term F i (sh x)) (term G i (sh x)) (sh N) (sh y) (sh c) :=
      Prf.impE hc.allOpen.wk Prf.hyp0
    have left : Δ ⊢[PRAAx] term U i (pairT (pairT (sh C) (sh x)) (sh K)) ≐
        add (multiply (sh C) (multiply (term F i (sh x)) (term G i (sh x)))) (sh K) := by
      rw [← product_at F G i (sh x)]
      simpa only [term_constant] using
        (added_term (Γ := Δ) (scaledBody T) constantBody i (pairT (sh C) (sh x)) (sh K)).eqTrans
          (add_congr (scaled_term T i (sh C) (sh x)) (.eqRefl _))
    have right : Δ ⊢[PRAAx] term V i (pairT (pairT (sh Qsum) (sh x)) (pairT (sh Psum) (sh x))) ≐
        add (multiply (term F i (sh x)) (sh Qsum)) (multiply (term G i (sh x)) (sh Psum)) :=
      (right_row_at G F i (sh x) (sh Qsum) (sh Psum)).eqTrans
        (add_congr (multiply_commutative _ _) (multiply_commutative _ _))
    simp only [K,J,C,Qsum,Psum,sh,Syn.shift,subst_add,subst_multiply,subst_sum,subst_fraction,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,one] at left right
    change Δ ⊢[PRAAx] rationalLE (term U i (sh (pairT (pairT C x) K))) (term V i (sh (pairT (pairT Qsum x) (pairT Psum x))))
    simp only [K,J,C,Qsum,Psum,sh,Syn.shift,subst_pairT,subst_add,subst_multiply,subst_sum,subst_fraction,
      ConciseIPRA.PTm.subst_succ,ConciseIPRA.PTm.subst_zero,one]
    exact rationalLE_congr left.eqSymm right.eqSymm (row_order _ _ _ _ _ _ _ rows)
  have factor : Γ ⊢[PRAAx] multiply D C ≐ fraction (M*N) one :=
    (RationalNonnegativePowers.fraction_multiply M one N one (le_refl one) (le_refl one)).eqTrans
      (RationalNonnegativePowers.fraction_congr (.eqRefl _) (one_mul one))
  have constant : Γ ⊢[PRAAx] sum constantBody M K ≐ add (multiply D J) (multiply (fraction (M*N) one) c) :=
    (sum_constant M K (add_guard _ _)).eqTrans
      ((multiply_commutative _ _).eqTrans ((multiply_add D J (multiply C c)).eqTrans
        (add_congr (.eqRefl _) ((multiply_associative D C c).eqSymm.eqTrans (multiply_congr factor (.eqRefl _))))))
  have left : Γ ⊢[PRAAx] addedSum (scaledBody T) constantBody M (pairT C x) K ≐
      add (add (multiply C (sum T M x)) (multiply D J)) (multiply (fraction (M*N) one) c) :=
    (sum_additive _ _ _ _ _).eqTrans ((add_congr (sum_homogeneous T M C x) constant).eqTrans
      (add_associative _ _ _).eqSymm)
  have right := (sum_additive (Γ := Γ) (scaledBody F) (scaledBody G) M (pairT Qsum x) (pairT Psum x)).eqTrans
    ((add_congr (sum_homogeneous F M Qsum x) (sum_homogeneous G M Psum x)).eqTrans
      (add_congr (multiply_commutative _ _) (multiply_commutative _ _)))
  exact rationalLE_congr left right (sum_monotone _ _ _ _ _ all)

theorem finite_crossed_product_rectangle_closed (F G P Q : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 5
      (rectangleCells F G P Q (var 0) (var 1) (var 2) (var 3) (var 4) ⟶
        rationalLE (add (add
          (multiply (fraction (var 1) one) (sum (productBody F G) (var 0) (var 2)))
          (multiply (fraction (var 0) one) (sum (productBody P Q) (var 1) (var 3))))
          (multiply (fraction (var 0*var 1) one) (var 4)))
          (add (multiply (sum F (var 0) (var 2)) (sum Q (var 1) (var 3)))
            (multiply (sum G (var 0) (var 2)) (sum P (var 1) (var 3))))) :=
  closeUniv 5 (.impI (rectangle_order F G P Q _ _ _ _ _ Prf.hyp0))

end LeanProofs.IPRA.Analysis.RationalCrossedProductSums
