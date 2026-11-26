import IPRADerivations.Analysis.Stirling.AllOrders.ImproperBounds.GaussianStirlingAllOrderPanelPositiveRows
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.RationalSumSegments

/-!
# A mesh-independent lower bound for the original weighted panel

Split the original 8S fold at 3S and 4S. The middle S rows share
a positive rational floor and the two remaining sums are
nonnegative. Normalization divides the middle floor by eight.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPositive

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open ConciseIPRA.PTm (zero)
open LeanProofs.IPRA.PTm (num subst_num)
open GaussianEuclideanDistanceName (fraction fraction_represents)
open GaussianRationalFiniteProduct (offset_at)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (nonnegative_of_representation)
open GaussianRationalSyntheticBounds (add_monotone)
open GaussianStirlingAllOrderKernel (multiply_zero_right)
open GaussianStirlingAllOrderPanelPositiveRows (rowFloor boundDenominator floor_den_positive subst_rowFloor row_nonnegative positive_box_row)
open GaussianStirlingAllOrderPanelTail (panel panelBody panelData panel_row_at subst_panelData)
open RationalAlgebra (add_congr add_commutative multiply_congr multiply_associative multiply_commutative)
open RationalArithmetic (add multiply multiply_monotone add_guard)
open RationalArgmin (rationalLE rationalLE_congr reflexive)
open RationalFiniteSum (term sum termwiseLE sum_monotone canonical_equal)
open RationalNonnegativePowers (fraction_multiply fraction_congr)
open RationalNormalForm (wellFormed normalize_well_formed)
open RationalReciprocalPowerTail (add_zero_right)
open RationalSumConstants (constantBody term_constant sum_constant)
open RationalSumSegments (sum_congr split)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem constant_floor (f : PTm 2) (N x c : PTm n) (hc : Γ ⊢[PRAAx] wellFormed c)
    (h : Γ ⊢[PRAAx] termwiseLE constantBody f N c x) :
    Γ ⊢[PRAAx] rationalLE (multiply (fraction N one) c) (sum f N x) :=
  rationalLE_congr ((sum_constant N c hc).eqTrans (multiply_commutative _ _)) (.eqRefl _)
    (sum_monotone _ _ _ _ _ h)

private theorem nonnegative_fold (f : PTm 2) (N x : PTm n)
    (h : Γ ⊢[PRAAx] termwiseLE constantBody f N (fraction zero one) x) :
    Γ ⊢[PRAAx] rationalLE (fraction zero one) (sum f N x) :=
  rationalLE_congr (multiply_zero_right _) (.eqRefl _)
    (constant_floor f N x _ (normalize_well_formed _ _ (le_refl one)) h)

theorem positive_panel_sum (m : ℕ) (q A B S : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE (multiply (fraction S one) (rowFloor m q A B))
      (sum (panelBody m) (S*num 8) (panelData q A B (S*num 8) zero)) := by
  let f := panelBody m
  let g := offB f
  let l := S*num 3
  let r := S*num 4
  let M := S*num 8
  let data := panelData q A B M zero
  let x := pairT l data
  let y := pairT S x
  let sh (t : PTm n) := Syn.shift t
  let i : PTm (n+1) := var 0
  have hM : Γ ⊢[PRAAx] le one M := positive_product _ _ hS (by ipra_le 7)
  have ha : Γ.map Fm.shift ⊢[PRAAx] le one (sh A) := by simpa [Fm.shift,sh,Syn.shift] using hA.shift
  have hb : Γ.map Fm.shift ⊢[PRAAx] le one (sh B) := by simpa [Fm.shift,sh,Syn.shift] using hB.shift
  have hs : Γ.map Fm.shift ⊢[PRAAx] le one (sh S) := by simpa [Fm.shift,sh,Syn.shift] using hS.shift
  have hm : Γ.map Fm.shift ⊢[PRAAx] le one (sh S*num 8) := by simpa [M,Fm.shift,sh,Syn.shift] using hM.shift
  have left : Γ ⊢[PRAAx] rationalLE (fraction zero one) (sum f l data) := by
    apply nonnegative_fold
    refine .allI (.impI ?_)
    let Δ := lt i (sh S*num 3) :: Γ.map Fm.shift
    have hi : Δ ⊢[PRAAx] lt i (sh S*num 3) := Prf.hyp0
    have hr : Δ ⊢[PRAAx] le i (sh S*num 8) := by ipra_le sl (le_of_lt hi)+5*Groth.ι (IPRA.Q.mk Δ (sh S))
    have z := row_nonnegative m (sh q) (sh A) (sh B) (sh S*num 8) zero i ha.wk hm.wk hr
    have read := panel_row_at (Γ := Δ) m (sh q) (sh A) (sh B) (sh S*num 8) zero i
    rw [term_constant]
    simpa [Δ,f,l,M,data,termwiseLE,term_constant,term,one,Syn.shift,sh,i] using
      rationalLE_congr (.eqRefl _) read.eqSymm z
  have right : Γ ⊢[PRAAx] rationalLE (fraction zero one) (sum (offB g) r y) := by
    apply nonnegative_fold
    refine .allI (.impI ?_)
    let Δ := lt i (sh S*num 4) :: Γ.map Fm.shift
    let a := sh S*num 3
    let d := panelData (sh q) (sh A) (sh B) (sh S*num 8) zero
    have hi : Δ ⊢[PRAAx] lt i (sh S*num 4) := Prf.hyp0
    have hr : Δ ⊢[PRAAx] le (a+(sh S+i)) (sh S*num 8) := by dsimp [a]; ipra_le sl (le_of_lt hi)
    have z := row_nonnegative m (sh q) (sh A) (sh B) (sh S*num 8) zero _ ha.wk hm.wk hr
    have read := (offset_at (Γ := Δ) g (sh S) i (pairT a d)).eqTrans
      ((offset_at f a (sh S+i) d).eqTrans (panel_row_at m (sh q) (sh A) (sh B) (sh S*num 8) zero _))
    rw [term_constant]
    simpa [Δ,f,g,y,x,r,l,M,data,d,a,termwiseLE,term_constant,term,one,Syn.shift,sh,i] using
      rationalLE_congr (.eqRefl _) read.eqSymm z
  have mid : Γ ⊢[PRAAx] rationalLE (multiply (fraction S one) (rowFloor m q A B)) (sum g S x) := by
    apply constant_floor g S x (rowFloor m q A B) (normalize_well_formed _ _ (floor_den_positive m q A B hA))
    refine .allI (.impI ?_)
    let Δ := lt i (sh S) :: Γ.map Fm.shift
    let a := sh S*num 3
    let d := panelData (sh q) (sh A) (sh B) (sh S*num 8) zero
    have hi : Δ ⊢[PRAAx] lt i (sh S) := Prf.hyp0
    have hr : Δ ⊢[PRAAx] le (two*(a+i)) (sh S*num 8) := by dsimp [a]; ipra_le 2*sl (le_of_lt hi)
    have z := positive_box_row m (sh q) (sh A) (sh B) (sh S) (a+i) ha.wk hb.wk hs.wk (le_add_right _ _) hr
    have read := (offset_at (Γ := Δ) f a i d).eqTrans (panel_row_at m (sh q) (sh A) (sh B) (sh S*num 8) zero _)
    rw [term_constant]
    simpa [Δ,g,f,x,l,M,data,d,a,termwiseLE,term_constant,term,Syn.shift,sh,i] using
      rationalLE_congr (.eqRefl _) read.eqSymm z
  have eq : Γ ⊢[PRAAx] sum f M data ≐ add (sum f l data) (add (sum g S x) (sum (offB g) r y)) :=
    (sum_congr f (by dsimp [M,l,r]; ipra_ring : Γ ⊢[PRAAx] M ≐ l+(S+r)) (.eqRefl _)).eqTrans
      ((split f l (S+r) data).eqTrans (add_congr (.eqRefl _) (split g S r x)))
  let C := multiply (fraction S one) (rowFloor m q A B)
  have erase : Γ ⊢[PRAAx] add (fraction zero one) (add C (fraction zero one)) ≐ C :=
    (add_congr (.eqRefl _) (add_zero_right _ (RationalArithmetic.multiply_guard _ _))).eqTrans
      ((add_commutative _ _).eqTrans (add_zero_right _ (RationalArithmetic.multiply_guard _ _)))
  exact rationalLE_congr erase eq.eqSymm (add_monotone _ _ _ _ left (add_monotone _ _ _ _ mid right))

def panelFloor (m : ℕ) (q A B : PTm n) : PTm n := fraction one (num 8*boundDenominator m q A B)

@[simp] theorem subst_panelFloor {l : ℕ} (σ : Fin n → PTm l) (m : ℕ) (q A B : PTm n) :
    Syn.subst σ (panelFloor m q A B) = panelFloor m (Syn.subst σ q) (Syn.subst σ A) (Syn.subst σ B) := by
  simp [panelFloor,boundDenominator,GaussianStirlingAllOrderBernoulliMeshMargin.coarseDen,
    GaussianStirlingAllOrderCenteredBernoulli.denominator,pw,one]

theorem panel_floor_den_positive (m : ℕ) (q A B : PTm n) (hA : Γ ⊢[PRAAx] le one A) :
    Γ ⊢[PRAAx] le one (num 8*boundDenominator m q A B) :=
  positive_product _ _ (by ipra_le 7) (floor_den_positive m q A B hA)

theorem first_panel_positive_lower (m : ℕ) (q A B S : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hB : Γ ⊢[PRAAx] le one B) (hS : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] rationalLE (panelFloor m q A B) (panel m q A B (S*num 8) zero) := by
  let M := S*num 8
  let D := boundDenominator m q A B
  let c := fraction one M
  let w := rowFloor m q A B
  have h8 : Γ ⊢[PRAAx] le one (num 8 : PTm n) := by ipra_le 7
  have hM := positive_product S (num 8) hS h8
  have hD := floor_den_positive m q A B hA
  have fin : Γ ⊢[PRAAx] fraction (one*S) (M*one) ≐ fraction one (num 8) := by
    have h := positive_product _ _ hM (le_refl one)
    apply canonical_equal _ _ _ _ _ _ (normalize_well_formed _ _ h) (normalize_well_formed _ _ h8)
      (fraction_represents _ _ h) (fraction_represents _ _ h8) h h8
    apply ZT.derive
    simp only [ZT.toZ_mul,ZT.toZ_ofNat]
    ipra_simps
    ring
  have eq : Γ ⊢[PRAAx] multiply c (multiply (fraction S one) w) ≐ panelFloor m q A B :=
    (multiply_associative _ _ _).eqSymm.eqTrans
      ((multiply_congr ((fraction_multiply _ _ _ _ hM (le_refl one)).eqTrans fin) (.eqRefl _)).eqTrans
        ((fraction_multiply _ _ _ _ h8 hD).eqTrans (fraction_congr (one_mul one) (.eqRefl _))))
  have hn := nonnegative_of_representation (Γ := Γ) c one M hM (fraction_represents one M hM)
  exact rationalLE_congr eq (.eqRefl _) (multiply_monotone c _ _ hn (positive_panel_sum m q A B S hA hB hS))

theorem actual_original_reciprocal_panel_positive_lower_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 1) ⋏ (le one (var 2) ⋏ le one (var 3))) ⟶
        rationalLE (panelFloor m (var 0) (var 1) (var 2)) (panel m (var 0) (var 1) (var 2) (var 3*num 8) zero)) :=
  closeUniv 4 (.impI (first_panel_positive_lower m _ _ _ _
    Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderPanelPositive
