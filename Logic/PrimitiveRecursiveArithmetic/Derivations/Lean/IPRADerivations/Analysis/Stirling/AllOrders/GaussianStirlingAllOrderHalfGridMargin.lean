import IPRADerivations.Analysis.Stirling.AllOrders.GaussianStirlingAllOrderCrossedSegments

/-!
# The finite reflected half-grid inequality with a uniform margin

Split one axis at S and the other at 3S. Three rectangles supply
weak order and the separated rectangle supplies S² times the
positive rational margin. The same three native sums occur on the
complete half-grid on both sides.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderHalfGridMargin

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianEuclideanDistanceName (fraction)
open GaussianStirlingAllOrderBoxProductGap (boxMargin)
open GaussianStirlingAllOrderCrossedCells (bernoulliBody reflectedBody segmentData)
open GaussianStirlingAllOrderCrossedRectangles (comparison weak_rectangle strict_rectangle bernoulliSum reflectedSum pairedSum)
open GaussianStirlingAllOrderCrossedSegments (bernoulli_split reflected_split paired_split)
open GaussianRationalSyntheticBounds (add_monotone)
open RationalAlgebra (add_congr add_associative add_commutative multiply_congr multiply_commutative multiply_add)
open RationalArgmin (rationalLE rationalLE_congr)
open RationalArithmetic (add add_guard multiply)
open RationalCrossedProductSums (productBody)
open RationalNonnegativePowers (fraction_congr)
open RationalReciprocalPowerTail (add_zero_right)
open RationalSumConstants (count_add)
open RationalSumSegments (sum_congr)
open LeanProofs.IPRA.PTm (num)
open ConciseIPRA.PTm (zero)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

local notation "qzero" => fraction zero one

noncomputable def leftSide (m : ℕ) (q A B S t u N M : PTm n) : PTm n :=
  add (multiply (fraction M one) (pairedSum m q A B S t N))
    (multiply (fraction N one) (pairedSum m q A B S u M))

noncomputable def rightSide (m : ℕ) (q A B S t u N M : PTm n) : PTm n :=
  add (multiply (bernoulliSum m q A B S t N) (reflectedSum q A B S u M))
    (multiply (reflectedSum q A B S t N) (bernoulliSum m q A B S u M))

noncomputable def withMargin (m : ℕ) (q A B S t u N M amount : PTm n) : Fm PTm n :=
  rationalLE (add (leftSide m q A B S t u N M) amount) (rightSide m q A B S t u N M)

private theorem group_four (a b c d : PTm n) : Γ ⊢[PRAAx]
    add (add a b) (add c d) ≐ add (add a c) (add b d) := by
  have mid := (add_associative (Γ := Γ) a b c).eqTrans
    ((add_congr (.eqRefl _) (add_commutative b c)).eqTrans (add_associative a c b).eqSymm)
  exact (add_associative _ _ _).eqSymm.eqTrans
    ((add_congr mid (.eqRefl _)).eqTrans (add_associative _ _ _))

private theorem add_factor (a b c : PTm n) : Γ ⊢[PRAAx] add (multiply a c) (multiply b c) ≐ multiply (add a b) c :=
  (add_congr (multiply_commutative _ _) (multiply_commutative _ _)).eqTrans
    ((multiply_add c a b).eqSymm.eqTrans (multiply_commutative _ _))

theorem swap_axes (m : ℕ) (q A B S t u N M c : PTm n)
    (h : Γ ⊢[PRAAx] withMargin m q A B S t u N M c) :
    Γ ⊢[PRAAx] withMargin m q A B S u t M N c :=
  rationalLE_congr (add_congr (add_commutative _ _) (.eqRefl c))
    ((add_congr (multiply_commutative _ _) (multiply_commutative _ _)).eqTrans (add_commutative _ _)) h

private theorem left_merge (m : ℕ) (q A B S t u N K M : PTm n) :
    Γ ⊢[PRAAx] add (leftSide m q A B S t u N M) (leftSide m q A B S (t+N) u K M) ≐
      leftSide m q A B S t u (N+K) M := by
  let P := pairedSum m q A B S t N
  let Q := pairedSum m q A B S (t+N) K
  let X := pairedSum m q A B S u M
  let C := fraction M one
  let a := fraction N one
  let b := fraction K one
  have l := (multiply_add (Γ := Γ) C P Q).eqSymm.eqTrans
    (multiply_congr (.eqRefl C) (paired_split m q A B S t N K).eqSymm)
  have r := (add_factor (Γ := Γ) a b X).eqTrans (multiply_congr (count_add N K) (.eqRefl X))
  exact (group_four (multiply C P) (multiply a X) (multiply C Q) (multiply b X)).eqTrans (add_congr l r)

private theorem right_merge (m : ℕ) (q A B S t u N K M : PTm n) :
    Γ ⊢[PRAAx] add (rightSide m q A B S t u N M) (rightSide m q A B S (t+N) u K M) ≐
      rightSide m q A B S t u (N+K) M := by
  let H := bernoulliSum m q A B S u M
  let W := reflectedSum q A B S u M
  let P := bernoulliSum m q A B S t N
  let Q := bernoulliSum m q A B S (t+N) K
  let X := reflectedSum q A B S t N
  let Y := reflectedSum q A B S (t+N) K
  have l := (add_factor (Γ := Γ) P Q W).eqTrans (multiply_congr (bernoulli_split m q A B S t N K).eqSymm (.eqRefl W))
  have r := (add_factor (Γ := Γ) X Y H).eqTrans (multiply_congr (reflected_split q A B S t N K).eqSymm (.eqRefl H))
  exact (group_four (multiply P W) (multiply X H) (multiply Q W) (multiply Y H)).eqTrans (add_congr l r)

theorem merge_first (m : ℕ) (q A B S t u N K M c d : PTm n)
    (h : Γ ⊢[PRAAx] withMargin m q A B S t u N M c)
    (g : Γ ⊢[PRAAx] withMargin m q A B S (t+N) u K M d) :
    Γ ⊢[PRAAx] withMargin m q A B S t u (N+K) M (add c d) := by
  let X := leftSide m q A B S t u N M
  let Y := leftSide m q A B S (t+N) u K M
  let P := rightSide m q A B S t u N M
  let Q := rightSide m q A B S (t+N) u K M
  have v := add_monotone (add X c) P (add Y d) Q h g
  have e := (group_four (Γ := Γ) X c Y d).eqTrans (add_congr (left_merge m q A B S t u N K M) (.eqRefl _))
  exact rationalLE_congr e (right_merge m q A B S t u N K M) v

theorem merge_second (m : ℕ) (q A B S t u N M L c d : PTm n)
    (h : Γ ⊢[PRAAx] withMargin m q A B S t u N M c)
    (g : Γ ⊢[PRAAx] withMargin m q A B S t (u+M) N L d) :
    Γ ⊢[PRAAx] withMargin m q A B S t u N (M+L) (add c d) :=
  swap_axes _ _ _ _ _ _ _ _ _ _ (merge_first _ _ _ _ _ _ _ _ _ _ _ _
    (swap_axes _ _ _ _ _ _ _ _ _ _ h) (swap_axes _ _ _ _ _ _ _ _ _ _ g))

private theorem move_grid (q A B S : PTm n) {t u : PTm n} (h : Γ ⊢[PRAAx] t ≐ u) :
    Γ ⊢[PRAAx] segmentData q A B S t ≐ segmentData q A B S u :=
  congrPairT (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) (congrPairT (.eqRefl _) h)))

theorem change_indices (m : ℕ) (q A B S c : PTm n) {t u N M t' u' N' M' : PTm n}
    (et : Γ ⊢[PRAAx] t ≐ t') (eu : Γ ⊢[PRAAx] u ≐ u')
    (eN : Γ ⊢[PRAAx] N ≐ N') (eM : Γ ⊢[PRAAx] M ≐ M')
    (h : Γ ⊢[PRAAx] withMargin m q A B S t u N M c) :
    Γ ⊢[PRAAx] withMargin m q A B S t' u' N' M' c := by
  let f := bernoulliBody m
  let g := reflectedBody
  let p := productBody f g
  have hx := move_grid q A B S et
  have hy := move_grid q A B S eu
  have l : Γ ⊢[PRAAx] leftSide m q A B S t u N M ≐ leftSide m q A B S t' u' N' M' :=
    add_congr (multiply_congr (fraction_congr eM (.eqRefl _)) (sum_congr p eN hx))
      (multiply_congr (fraction_congr eN (.eqRefl _)) (sum_congr p eM hy))
  have r : Γ ⊢[PRAAx] rightSide m q A B S t u N M ≐ rightSide m q A B S t' u' N' M' :=
    add_congr (multiply_congr (sum_congr f eN hx) (sum_congr g eM hy))
      (multiply_congr (sum_congr g eN hx) (sum_congr f eM hy))
  exact rationalLE_congr (add_congr l (.eqRefl c)) r h

private theorem weak_budget (m : ℕ) (q A B S t u N M : PTm n)
    (ha : Γ ⊢[PRAAx] le one A) (hs : Γ ⊢[PRAAx] le one S)
    (hn : Γ ⊢[PRAAx] le (two*(t+N)) (S*num 8)) (hm : Γ ⊢[PRAAx] le (two*(u+M)) (S*num 8)) :
    Γ ⊢[PRAAx] withMargin m q A B S t u N M qzero :=
  rationalLE_congr (add_congr (.eqRefl _) (GaussianStirlingAllOrderKernel.multiply_zero_right (fraction (N*M) one)))
    (.eqRefl _) (weak_rectangle m q A B S t u N M ha hs hn hm)

set_option maxHeartbeats 840000 in
theorem half_grid_margin (m : ℕ) (q A B S : PTm n)
    (ha : Γ ⊢[PRAAx] le one A) (hb : Γ ⊢[PRAAx] le one B) (hs : Γ ⊢[PRAAx] le one S) :
    Γ ⊢[PRAAx] withMargin m q A B S zero zero (S*num 4) (S*num 4) (multiply (fraction (S*S) one) (boxMargin m q A B)) := by
  let T := S*num 3
  let V := S*num 4
  let C := multiply (fraction (S*S) one) (boxMargin m q A B)
  have leftGuard : Γ ⊢[PRAAx] le (two*(zero+S)) (S*num 8) := by ipra_le 6*Groth.ι (IPRA.Q.mk Γ S)
  have rightGuard : Γ ⊢[PRAAx] le (two*(zero+T)) (S*num 8) := by
    dsimp only [T]
    ipra_le 2*Groth.ι (IPRA.Q.mk Γ S)
  have leftTail : Γ ⊢[PRAAx] le (two*(zero+S+T)) (S*num 8) := by dsimp only [T]; ipra_le 0
  have rightTail : Γ ⊢[PRAAx] le (two*(zero+T+S)) (S*num 8) := by dsimp only [T]; ipra_le 0
  have a := weak_budget m q A B S zero zero S T ha hs leftGuard rightGuard
  have b : Γ ⊢[PRAAx] withMargin m q A B S zero (zero+T) S S C :=
    change_indices m q A B S C (.eqRefl zero) (zero_add T).eqSymm (.eqRefl S) (.eqRefl S) (strict_rectangle m q A B S ha hb hs)
  have c := weak_budget m q A B S (zero+S) zero T T ha hs leftTail rightGuard
  have d := weak_budget m q A B S (zero+S) (zero+T) T S ha hs leftTail rightTail
  have s := merge_second m q A B S zero zero S T S qzero C a b
  have t := merge_second m q A B S (zero+S) zero T T S qzero qzero c d
  have combined := merge_first m q A B S zero zero S T (T+S) (add qzero C) (add qzero qzero) s t
  have kept : Γ ⊢[PRAAx] withMargin m q A B S zero zero V V (add (add qzero C) (add qzero qzero)) :=
    change_indices m q A B S _ (.eqRefl zero) (.eqRefl zero)
      (by dsimp only [T,V]; ipra_ring) (by dsimp only [T,V]; ipra_ring) combined
  have hz : Γ ⊢[PRAAx] RationalNormalForm.wellFormed qzero :=
    RationalNormalForm.normalize_well_formed _ _ (le_refl one)
  have hc : Γ ⊢[PRAAx] RationalNormalForm.wellFormed C := RationalArithmetic.multiply_guard _ _
  have e : Γ ⊢[PRAAx] add (add qzero C) (add qzero qzero) ≐ C :=
    (add_congr ((add_commutative _ _).eqTrans (add_zero_right C hc)) (add_zero_right qzero hz)).eqTrans
      (add_zero_right C hc)
  exact rationalLE_congr (add_congr (.eqRefl _) e) (.eqRefl _) kept

theorem actual_reflected_half_grid_margin_closed (m : ℕ) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 4
      ((le one (var 1) ⋏ (le one (var 2) ⋏ le one (var 3))) ⟶
        withMargin m (var 0) (var 1) (var 2) (var 3) zero zero (var 3*num 4) (var 3*num 4)
          (multiply (fraction (var 3*var 3) one) (boxMargin m (var 0) (var 1) (var 2)))) :=
  closeUniv 4 (.impI (half_grid_margin m _ _ _ _ Prf.hyp0.andE₁ Prf.hyp0.andE₂.andE₁ Prf.hyp0.andE₂.andE₂))

end LeanProofs.IPRA.Analysis.GaussianStirlingAllOrderHalfGridMargin
