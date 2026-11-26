import IPRADerivations.Analysis.Stirling.AllOrders.Covariance.GaussianStirlingAllOrderCrossedCells

/-!
# Finite rectangle comparison on the actual first-half grids

On the separated boxes [0,S) and [3S,4S), the finite crossed-product
comparison retains S² times the original positive cell margin.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCrossedRectangles

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction)
open GaussianStirlingAllOrderBoxProductGap (sampleAt weightAt boxMargin)
open GaussianStirlingAllOrderCrossedCells (segmentData bernoulliBody reflectedBody bernoulli_at reflected_at
  weak_cell strong_cell subst_segmentData)
open RationalAlgebra (add_congr multiply_congr)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalArithmetic (add multiply)
open RationalCrossedProductSums (cell rectangleCells productBody rectangle_order)
open RationalFiniteSum (term sum)
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "qzero" => fraction zero one

@[simp] theorem subst_boxMargin {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (q A B : PTm n) :
    Syn.subst σ (boxMargin m q A B) = boxMargin m (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [boxMargin,GaussianStirlingAllOrderBernoulliMeshMargin.margin,GaussianStirlingAllOrderBernoulliMeshMargin.coarseDen,
    GaussianStirlingAllOrderPairedRefinement.centerGap,GaussianStirlingAllOrderCenteredBernoulli.denominator,
    BernoulliBounds.zint,pw,GaussianStirlingAllOrderPairedWeight.gapFraction,
    GaussianStirlingAllOrderPairedWeight.gapNumerator,GaussianStirlingAllOrderPairedWeight.gapDenominator,
    GaussianStirlingAllOrderPowerGap.gap]

private theorem cell_readback (m : ℕ) (q A B S left right i j c : PTm n)
    (h : Γ ⊢[PRAAx] cell (sampleAt m S (left+i)) (weightAt q A B S (left+i))
      (sampleAt m S (right+j)) (weightAt q A B S (right+j)) c) :
    Γ ⊢[PRAAx] cell
      (term (bernoulliBody m) i (segmentData q A B S left)) (term reflectedBody i (segmentData q A B S left))
      (term (bernoulliBody m) j (segmentData q A B S right)) (term reflectedBody j (segmentData q A B S right)) c := by
  have x := (bernoulli_at (Γ := Γ) m i q A B S left).eqSymm
  have w := (reflected_at (Γ := Γ) i q A B S left).eqSymm
  have y := (bernoulli_at (Γ := Γ) m j q A B S right).eqSymm
  have v := (reflected_at (Γ := Γ) j q A B S right).eqSymm
  exact rationalLE_congr (add_congr (add_congr (multiply_congr x w) (.eqRefl c)) (multiply_congr y v))
    (add_congr (multiply_congr x v) (multiply_congr w y)) h

private theorem weaken_at_two (first : Fm PTm (n+1)) (second : Fm PTm (n+2)) {φ : Fm PTm n}
    (h : Γ ⊢[PRAAx] φ) : second :: (first :: Γ.map Fm.shift).map Fm.shift ⊢[PRAAx] φ.shift.shift :=
  ((Prf.wk (ψ := first) h.shift).shift).wk

noncomputable def gridCells (m : ℕ) (q A B S left right M N c : PTm n) : Fm PTm n :=
  rectangleCells (bernoulliBody m) reflectedBody (bernoulliBody m) reflectedBody M N
    (segmentData q A B S left) (segmentData q A B S right) c

set_option maxHeartbeats 580000 in
theorem weak_cells (m : ℕ) (q A B S left right M N : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hS : Γ ⊢[PRAAx] le one S) (hM : Γ ⊢[PRAAx] le (two*(left+M)) (S*num 8))
    (hN : Γ ⊢[PRAAx] le (two*(right+N)) (S*num 8)) :
    Γ ⊢[PRAAx] gridCells m q A B S left right M N qzero := by
  refine .allI (.impI (.allI (.impI ?_)))
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  let i : PTm (n+2) := var 1
  let j : PTm (n+2) := var 0
  let fstHyp : Fm PTm (n+1) := lt (var 0) (Syn.shift M)
  let sndHyp : Fm PTm (n+2) := lt j (sh N)
  let Δ := sndHyp :: (fstHyp :: Γ.map Fm.shift).map Fm.shift
  have hi : Δ ⊢[PRAAx] lt i (sh M) := by
    simpa only [Δ,fstHyp,List.map_cons,Fm.shift,subst_lt,Syn.subst_var,Syn.shift,sh,i,Fin.succ_zero_eq_one] using (Prf.hyp1 : Δ ⊢[PRAAx] fstHyp.shift)
  have hj : Δ ⊢[PRAAx] lt j (sh N) := Prf.hyp0
  have ha : Δ ⊢[PRAAx] le one (sh A) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using weaken_at_two fstHyp sndHyp hA
  have hs : Δ ⊢[PRAAx] le one (sh S) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using weaken_at_two fstHyp sndHyp hS
  have hm : Δ ⊢[PRAAx] le (two*(sh left+sh M)) (sh S*num 8) := by
    simpa [Δ,Fm.shift,Syn.shift,sh,two,one] using weaken_at_two fstHyp sndHyp hM
  have hn : Δ ⊢[PRAAx] le (two*(sh right+sh N)) (sh S*num 8) := by
    simpa [Δ,Fm.shift,Syn.shift,sh,two,one] using weaken_at_two fstHyp sndHyp hN
  have ci : Δ ⊢[PRAAx] le (two*(sh left+i)) (sh S*num 8) := by ipra_le sl hm+2*sl (le_of_lt hi)
  have cj : Δ ⊢[PRAAx] le (two*(sh right+j)) (sh S*num 8) := by ipra_le sl hn+2*sl (le_of_lt hj)
  have order := weak_cell m (sh q) (sh A) (sh B) (sh S) (sh left+i) (sh right+j) ha hs ci cj
  simpa [Δ,fstHyp,sndHyp,Fm.shift,sh,Syn.shift,i,j] using cell_readback m (sh q) (sh A) (sh B) (sh S) (sh left) (sh right) i j _ order

set_option maxHeartbeats 580000 in
theorem box_cells (m : ℕ) (q A B S : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] gridCells m q A B S zero (S*num 3) S S (boxMargin m q A B) := by
  refine .allI (.impI (.allI (.impI ?_)))
  let sh (x : PTm n) := Syn.shift (Syn.shift x)
  let i : PTm (n+2) := var 1
  let j : PTm (n+2) := var 0
  let fstHyp : Fm PTm (n+1) := lt (var 0) (Syn.shift S)
  let sndHyp : Fm PTm (n+2) := lt j (sh S)
  let Δ := sndHyp :: (fstHyp :: Γ.map Fm.shift).map Fm.shift
  have hi : Δ ⊢[PRAAx] lt i (sh S) := by
    simpa only [Δ,fstHyp,List.map_cons,Fm.shift,subst_lt,Syn.subst_var,Syn.shift,sh,i,Fin.succ_zero_eq_one] using (Prf.hyp1 : Δ ⊢[PRAAx] fstHyp.shift)
  have hj : Δ ⊢[PRAAx] lt j (sh S) := Prf.hyp0
  have ha : Δ ⊢[PRAAx] le one (sh A) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using weaken_at_two fstHyp sndHyp hA
  have hb : Δ ⊢[PRAAx] le one (sh B) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using weaken_at_two fstHyp sndHyp hB
  have hs : Δ ⊢[PRAAx] le one (sh S) := by simpa [Δ,Fm.shift,Syn.shift,sh,one] using weaken_at_two fstHyp sndHyp hS
  have ci : Δ ⊢[PRAAx] le (zero+i) (sh S*one) := by ipra_le sl (le_of_lt hi)
  have cj : Δ ⊢[PRAAx] le (two*(sh S*num 3+j)) (sh S*num 8) := by ipra_le 2*sl (le_of_lt hj)
  have order := strong_cell m (sh q) (sh A) (sh B) (sh S) (zero+i) (sh S*num 3+j) ha hb hs ci (le_add_right _ _) cj
  simpa [Δ,fstHyp,sndHyp,Fm.shift,sh,Syn.shift,i,j] using cell_readback m (sh q) (sh A) (sh B) (sh S) zero (sh S*num 3) i j _ order

noncomputable def bernoulliSum (m : ℕ) (q A B S t N : PTm n) : PTm n := sum (bernoulliBody m) N (segmentData q A B S t)
def reflectedSum (q A B S t N : PTm n) : PTm n := sum reflectedBody N (segmentData q A B S t)
noncomputable def pairedSum (m : ℕ) (q A B S t N : PTm n) : PTm n :=
  sum (productBody (bernoulliBody m) reflectedBody) N (segmentData q A B S t)

noncomputable def comparison (m : ℕ) (q A B S left right M N c : PTm n) : Fm PTm n :=
  rationalLE (add (add (multiply (fraction N one) (pairedSum m q A B S left M))
    (multiply (fraction M one) (pairedSum m q A B S right N))) (multiply (fraction (M*N) one) c))
    (add (multiply (bernoulliSum m q A B S left M) (reflectedSum q A B S right N))
      (multiply (reflectedSum q A B S left M) (bernoulliSum m q A B S right N)))

theorem weak_rectangle (m : ℕ) (q A B S left right M N : PTm n) (hA : Γ ⊢[PRAAx] le one A)
    (hS : Γ ⊢[PRAAx] le one S) (hM : Γ ⊢[PRAAx] le (two*(left+M)) (S*num 8))
    (hN : Γ ⊢[PRAAx] le (two*(right+N)) (S*num 8)) :
    Γ ⊢[PRAAx] comparison m q A B S left right M N qzero :=
  rectangle_order _ _ _ _ _ _ _ _ _ (weak_cells m q A B S left right M N hA hS hM hN)

theorem strict_rectangle (m : ℕ) (q A B S : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] comparison m q A B S zero (S*num 3) S S (boxMargin m q A B) :=
  rectangle_order _ _ _ _ _ _ _ _ _ (box_cells m q A B S hA hB hS)

theorem actual_reflected_grid_strict_rectangle_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 1) ⋏ (le one (var 2) ⋏ le one (var 3))) ⟶
        comparison m (var 0) (var 1) (var 2) (var 3) zero (var 3*num 3) (var 3) (var 3)
          (boxMargin m (var 0) (var 1) (var 2))) :=
  closeUniv 4 (.impI (strict_rectangle m _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderCrossedRectangles
