import IPRADerivations.Analysis.Gamma.EulerProducts.LogGamma.Convergence.GaussianLogGammaEulerResidualIntervalMajorant
import IPRADerivations.Analysis.RationalArithmetic.FiniteSums.GaussianRationalSumMajorant

/-!
# Uniform quadratic bounds for the finite Euler logarithm rows

The zeroth row with real numerator `A` costs at most `S*K²/D²`
when `D ≤ K*A`. The positive rows cost at most `S/(k*D)²` each,
and their entire reciprocal-square sum is at most `2S/D²`.
A common scalar observation allowance `C/U` is retained per row.
-/

set_option autoImplicit false
set_option maxHeartbeats 440000

namespace LeanProofs.IPRA.Analysis.GaussianLogGammaEulerTaylorMajorant

open_ipra
open LeanProofs.IPRA.AnalyticNumberTheory.PhiLower (le_mul_mono)
open GaussianCoefficientNameBounds (bounded_radius_mono)
open GaussianEuclideanDistanceName (fraction fraction_represents fraction_order)
open GaussianLogGammaEulerResidualIntervalMajorant
  (budgetBody budgetData budgetSum budget_term exact_scalar_sum subst_budgetData)
open GaussianRationalFiniteSum (sum_shift_first)
open GaussianRationalHorner (positive_product)
open GaussianRationalMetric (bounded comparison_to_cleared subst_bounded)
open GaussianRationalReciprocal (bound_congr bounded_sum)
open GaussianRationalSumMajorant (majorized majorized_congr from_representation termsMajorized sum_majorized)
open GaussianRationalSyntheticBounds (add_monotone)
open RationalAlgebra (add_congr multiply_congr add_associative add_commutative)
open RationalArgmin (rationalLE rationalLE_congr reflexive)
open RationalArithmetic (add multiply multiply_monotone)
open RationalNonnegativePowers (fraction_congr fraction_multiply)
open RationalReciprocalPowerTail (tail tail_zero tail_succ reciprocalPower potential sharp_tail)
open RationalSumLinearity (scaledBody scaled_term sum_homogeneous)
open RationalSupMetric (denominatorOf)

variable {n : ℕ} {Γ : List (Fm PTm n)}

private theorem fraction_add (a b c d : PTm n) (hb : Γ ⊢[PRAAx] le one b) (hd : Γ ⊢[PRAAx] le one d) :
    Γ ⊢[PRAAx] add (fraction a b) (fraction c d) ≐ fraction (a * d + c * b) (b * d) := by
  have hbd := positive_product _ _ hb hd
  have rep := RationalRepresentations.represents_add _ _ _ _ _ _
    (fraction_represents a b hb) (fraction_represents c d hd)
  apply RationalFiniteSum.canonical_equal _ _ _ _ _ _ (RationalArithmetic.add_guard _ _)
    (RationalNormalForm.normalize_well_formed _ _ hbd) rep (fraction_represents _ _ hbd) hbd hbd
  apply ZT.derive
  simp only [ZT.toZ_add, ZT.toZ_mul, ZT.toZ_ofNat, Q.mk_add, Q.mk_mul, map_add, map_mul]

private alias square_power := Common.pw_two

private def squareSplit (N : PTm n) : Fm PTm n :=
  tail two zero (succ N) ≐ add (fraction one one) (tail two one N)

@[simp] private theorem subst_squareSplit {m : ℕ} (σ : Fin n → PTm m) (N : PTm n) :
    (squareSplit N).subst σ = squareSplit (Syn.subst σ N) := by simp [squareSplit, one, two]

private theorem split_zero : Γ ⊢[PRAAx] squareSplit (zero : PTm n) := by
  have e : Γ ⊢[PRAAx] reciprocalPower two (succ (zero + zero)) ≐ fraction one one :=
    fraction_congr (.eqRefl _) ((square_power _).eqTrans (by ipra_ring))
  exact (tail_succ two zero zero).eqTrans
    ((add_congr (tail_zero two zero) e).eqTrans
      ((add_commutative _ _).eqTrans (add_congr (.eqRefl _) (tail_zero two one).eqSymm)))

private theorem split_succ (N : PTm n) (h : Γ ⊢[PRAAx] squareSplit N) :
    Γ ⊢[PRAAx] squareSplit (succ N) := by
  have next : Γ ⊢[PRAAx] reciprocalPower two (succ (zero + succ N)) ≐ reciprocalPower two (succ (one + N)) :=
    RationalReciprocalPowerTail.reciprocal_congr (.eqRefl two) (by ipra_ring)
  exact (tail_succ two zero (succ N)).eqTrans
    ((add_congr h next).eqTrans
      ((add_associative _ _ _).eqTrans (add_congr (.eqRefl _) (tail_succ two one N).eqSymm)))

private theorem split_square_tail (N : PTm n) : Γ ⊢[PRAAx] squareSplit N := by
  have all : Γ ⊢[PRAAx] .all (squareSplit (var 0)) := by
    refine PRA.qfInd _ trivial ?_ ?_
    · simp only [subst_squareSplit, Syn.subst_var, Syn.inst_zero]
      exact split_zero
    · simp only [subst_squareSplit, Syn.subst_var, Syn.repl_zero]
      exact split_succ (var 0) Prf.hyp0
  simpa only [subst_squareSplit, Syn.subst_var, Syn.inst_zero] using all.allE N

private theorem tail_index_congr (m N r s : PTm n) (h : Γ ⊢[PRAAx] r ≐ s) :
    Γ ⊢[PRAAx] tail m N r ≐ tail m N s := by
  simpa only [RationalReciprocalPowerTail.subst_tail, Syn.subst_var, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (tail (var 0) (var 1) (var 2) : PTm 3)
      (σ := ![m, N, r]) (σ' := ![m, N, s]) (fun i => by
        fin_cases i
        · exact .eqRefl m
        · exact .eqRefl N
        · exact h)

/-- The literal finite sum of reciprocal squares beginning at one is at most two. -/
theorem positive_square_sum (N : PTm n) : Γ ⊢[PRAAx] rationalLE (tail two zero N) (fraction two one) := by
  refine (zero_or_succ N).orE ?_ ?_
  · let Δ := (N ≐ zero) :: Γ
    have e : Δ ⊢[PRAAx] tail two zero N ≐ fraction zero one :=
      (tail_index_congr two zero N zero Prf.hyp0).eqTrans (tail_zero two zero)
    exact rationalLE_congr e.eqSymm (.eqRefl _) (fraction_order zero one two one (le_refl one) (le_refl one)
      (le_congr (by ipra_ring) (by ipra_ring) (zero_le two)))
  · let Δ := (N ≐ succ (pred N)) :: Γ
    have e : Δ ⊢[PRAAx] tail two zero N ≐ add (fraction one one) (tail two one (pred N)) :=
      (tail_index_congr two zero N (succ (pred N)) Prf.hyp0).eqTrans (split_square_tail (pred N))
    have p : Δ ⊢[PRAAx] potential two one ≐ fraction one one :=
      fraction_congr (.eqRefl _) ((congrMul (pred_succ one) (congrAp2 powF (pred_succ one) (.eqRefl one))).eqTrans
        ((one_mul _).eqTrans (pw_one one)))
    have cap := rationalLE_congr (.eqRefl _) p (sharp_tail two one (pred N) (le_refl two) (le_refl one))
    have sum := add_monotone _ _ _ _ (reflexive (fraction one one)) cap
    have eq : Δ ⊢[PRAAx] add (fraction one one) (fraction one one) ≐ fraction two one :=
      (fraction_add one one one one (le_refl one) (le_refl one)).eqTrans (fraction_congr (by ipra_ring) (one_mul one))
    exact rationalLE_congr e.eqSymm eq sum

def rowSquare (A D k : PTm n) : PTm n := (A + k * D) * (A + k * D)

def rowBound (t : PTm 2) (x A D S C U k : PTm n) : Fm PTm n :=
  bounded (inst2 t k x) (S * U + C * rowSquare A D k) (rowSquare A D k * U)

def rowBounds (t : PTm 2) (x A D N S C U : PTm n) : Fm PTm n :=
  .all (lt (var 0) (succ (Syn.shift N)) ⟶
    rowBound t (Syn.shift x) (Syn.shift A) (Syn.shift D) (Syn.shift S) (Syn.shift C) (Syn.shift U) (var 0))

ipra_subst rowBound [rowSquare]

ipra_subst rowBounds [Syn.subst_shift, Syn.shift_subst]

private theorem local_row (t : PTm 2) (x A D N S C U k : PTm n) (h : Γ ⊢[PRAAx] rowBounds t x A D N S C U)
    (hk : Γ ⊢[PRAAx] lt k (succ N)) : Γ ⊢[PRAAx] rowBound t x A D S C U k := by
  have at_k : Γ ⊢[PRAAx] lt k (succ N) ⟶ rowBound t x A D S C U k := by
    simpa only [rowBounds, Fm.subst_imp, subst_lt, subst_rowBound, Syn.subst_var, Syn.inst_zero,
      Syn.subst_inst_shift, ConciseIPRA.PTm.subst_succ] using h.allE k
  exact .impE at_k hk

private theorem reweight (z S T C U V W : PTm n)
    (hU : Γ ⊢[PRAAx] le one U) (hV : Γ ⊢[PRAAx] le one V) (hW : Γ ⊢[PRAAx] le one W)
    (hweight : Γ ⊢[PRAAx] le (S * W) (T * V)) (h : Γ ⊢[PRAAx] bounded z (S * U + C * V) (V * U)) :
    Γ ⊢[PRAAx] bounded z (T * U + C * W) (W * U) := by
  have algebra := add_le_add₂ (mul_le_mul_right (U * U) hweight) (le_refl (C * V * W * U))
  exact bounded_radius_mono z _ _ _ _ (positive_product _ _ hV hU) (positive_product _ _ hW hU)
    (le_congr (by ipra_ring) (by ipra_ring) algebra) h

private abbrev positiveBody := scaledBody budgetBody

private def positiveData (S C U D : PTm n) : PTm n :=
  pairT (fraction one (D * D)) (budgetData S (C * (D * D)) U zero)

private theorem positive_term (S C U D i : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hU : Γ ⊢[PRAAx] le one U) :
    Γ ⊢[PRAAx] inst2 positiveBody i (positiveData S C U D) ≐
      fraction (S * U + C * (D * D * (succ i * succ i))) (D * D * (succ i * succ i) * U) := by
  let k := succ i
  let j := succ (zero + i)
  let L := S * U + (C * (D * D)) * (j * j)
  let Q := j * j * U
  have hj : Γ ⊢[PRAAx] le one j := zero_lt_succ _
  have hQ := positive_product _ _ (positive_product _ _ hj hj) hU
  have hD₂ := positive_product _ _ hD hD
  have eq : Γ ⊢[PRAAx] j ≐ k := congrSucc (zero_add i)
  have final : Γ ⊢[PRAAx] fraction (one * L) (D * D * Q) ≐
      fraction (S * U + C * (D * D * (k * k))) (D * D * (k * k) * U) := by
    have e := natEq eq
    apply fraction_congr <;> apply deriveNat <;> dsimp only [L, Q] <;> ipra_simps <;> rw [e] <;> ring
  exact (scaled_term budgetBody i (fraction one (D * D)) (budgetData S (C * (D * D)) U zero)).eqTrans
    ((multiply_congr (.eqRefl _) (budget_term S (C * (D * D)) U zero i hU)).eqTrans
      ((fraction_multiply one (D * D) L Q hD₂ hQ).eqTrans final))

private theorem scalar_upper (S C U D N : PTm n) (hD : Γ ⊢[PRAAx] le one D) (hU : Γ ⊢[PRAAx] le one U) :
    Γ ⊢[PRAAx] rationalLE (RationalFiniteSum.sum positiveBody N (positiveData S C U D))
      (fraction (two * S * U + C * N * (D * D)) (D * D * U)) := by
  let B := D * D
  let J := C * B
  let W := two * S * U + C * N * B
  let a := fraction S one
  let b := fraction (J * N) U
  let scale := fraction one B
  have hB := positive_product _ _ hD hD
  have nonnegative := GaussianRationalL1.nonnegative_of_representation (Γ := Γ) a S one (le_refl one)
    (fraction_represents _ _ (le_refl one))
  have term := multiply_monotone a _ _ nonnegative (positive_square_sum N)
  have outer := add_monotone _ _ _ _ term (reflexive b)
  have product : Γ ⊢[PRAAx] multiply a (fraction two one) ≐ fraction (two * S) one :=
    (fraction_multiply S one two one (le_refl one) (le_refl one)).eqTrans (fraction_congr (by ipra_ring) (one_mul one))
  have upper : Γ ⊢[PRAAx] add (multiply a (fraction two one)) b ≐ fraction W U :=
    (add_congr product (.eqRefl _)).eqTrans
      ((fraction_add (two * S) one (J * N) U (le_refl one) hU).eqTrans
        (fraction_congr (by dsimp only [W, J]; ipra_ring) (one_mul U)))
  have sum := rationalLE_congr (exact_scalar_sum S J U zero N hU).eqSymm upper outer
  have nonneg := GaussianRationalL1.nonnegative_of_representation (Γ := Γ) scale one B hB (fraction_represents _ _ hB)
  have result := multiply_monotone scale (budgetSum S J U zero N) (fraction W U) nonneg sum
  exact rationalLE_congr (sum_homogeneous budgetBody N scale (budgetData S J U zero)).eqSymm
    ((fraction_multiply one B W U hB hU).eqTrans (fraction_congr (one_mul W) (.eqRefl _))) result

private theorem positive_row (t : PTm 2) (x A D S C U i : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) (hU : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] rowBound t x A D S C U (succ i)) :
    Γ ⊢[PRAAx] majorized (inst2 (shiftBody t) i x) (inst2 positiveBody i (positiveData S C U D)) := by
  let k := succ i
  let v := rowSquare A D k
  let w := D * D * (k * k)
  let u := inst2 t k x
  have hk : Γ ⊢[PRAAx] le one k := zero_lt_succ _
  have hx := le_trans hA (le_add_right A (k * D))
  have hv := positive_product _ _ hx hx
  have hw := positive_product _ _ (positive_product _ _ hD hD) (positive_product _ _ hk hk)
  have ha := le_add_left (Γ := Γ) (k * D) A
  have hWV : Γ ⊢[PRAAx] le w v :=
    le_congr (by dsimp only [w]; ipra_ring) (.eqRefl v) (le_mul_mono ha ha)
  have small := reweight u S S C U v w hU hv hw (le_mul_mono (le_refl S) hWV) h
  have hd := positive_product _ _ hw hU
  have rep := fraction_represents (S * U + C * w) (w * U) hd
  have sign := GaussianRationalL1.nonnegative_of_representation _ _ _ hd rep
  rw [inst2_shiftBody]
  exact majorized_congr (.eqRefl _) (positive_term S C U D i hD hU).eqSymm
    (from_representation u _ _ _ hd sign rep small)

private theorem positive_error (t : PTm 2) (x A D N S C U : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) (hU : Γ ⊢[PRAAx] le one U)
    (h : Γ ⊢[PRAAx] rowBounds t x A D N S C U) :
    Γ ⊢[PRAAx] bounded (GaussianRationalFiniteSum.sum (shiftBody t) N x)
      (two * S * U + C * N * (D * D)) (D * D * U) := by
  let q := positiveData S C U D
  let p := RationalFiniteSum.sum positiveBody N q
  let v := GaussianRationalFiniteSum.sum (shiftBody t) N x
  let L := two * S * U + C * N * (D * D)
  let Q := D * D * U
  have rows : Γ ⊢[PRAAx] termsMajorized (shiftBody t) positiveBody N x q := by
    refine .allI (.impI ?_)
    let s (v : PTm n) := Syn.shift v
    let i : PTm (n + 1) := var 0
    let Δ := lt i (s N) :: Γ.map Fm.shift
    have hs : Δ ⊢[PRAAx] rowBounds t (s x) (s A) (s D) (s N) (s S) (s C) (s U) := by
      simpa only [Δ, s, Fm.shift, Syn.shift, subst_rowBounds] using h.shift.wk
    have ha : Δ ⊢[PRAAx] le one (s A) := by simpa [Δ, s, Fm.shift, Syn.shift] using hA.shift.wk
    have hd : Δ ⊢[PRAAx] le one (s D) := by simpa [Δ, s, Fm.shift, Syn.shift] using hD.shift.wk
    have hu : Δ ⊢[PRAAx] le one (s U) := by simpa [Δ, s, Fm.shift, Syn.shift] using hU.shift.wk
    have hi : Δ ⊢[PRAAx] lt (succ i) (succ (s N)) :=
      le_congr (succ_eq_add_one (succ i)).eqSymm (succ_eq_add_one (s N)).eqSymm (add_le_add_right one Prf.hyp0)
    have row := positive_row t (s x) (s A) (s D) (s S) (s C) (s U) i ha hd hu
      (local_row t (s x) (s A) (s D) (s N) (s S) (s C) (s U) (succ i) hs hi)
    simpa only [Δ, s, i, q, positiveData, Syn.shift, subst_pairT, GaussianEuclideanDistanceName.subst_fraction,
      subst_budgetData, PTm.subst_mul, one, ConciseIPRA.PTm.subst_succ, ConciseIPRA.PTm.subst_zero] using row
  have est : Γ ⊢[PRAAx] majorized v p := sum_majorized _ _ _ _ _ rows
  have hQ := positive_product _ _ (positive_product _ _ hD hD) hU
  have order := comparison_to_cleared p (fraction L Q) (GaussianPositiveRealArithmetic.numerator p) L
    (denominatorOf p) Q (GaussianPositiveRealArithmetic.natural_representation p est.andE₁) (fraction_represents _ _ hQ)
    (scalar_upper S C U D N hD hU)
  exact bounded_radius_mono v _ _ _ _ (RationalArgmin.denominator_positive p) hQ
    (le_congr (mul_comm _ _) (.eqRefl _) order) est.andE₂

def errorNumerator (S C U D K N : PTm n) : PTm n := S * (K * K + two) * U + C * succ N * (D * D)
def errorDenominator (U D : PTm n) : PTm n := D * D * U

/-- Sum the original rows through cutoff `N`, retaining their common observation allowance. -/
theorem finite_sum_bound (t : PTm 2) (x A D K N S C U : PTm n)
    (hA : Γ ⊢[PRAAx] le one A) (hD : Γ ⊢[PRAAx] le one D) (hU : Γ ⊢[PRAAx] le one U)
    (hK : Γ ⊢[PRAAx] le D (K * A)) (h : Γ ⊢[PRAAx] rowBounds t x A D N S C U) :
    Γ ⊢[PRAAx] bounded (GaussianRationalFiniteSum.sum t (succ N) x)
      (errorNumerator S C U D K N) (errorDenominator U D) := by
  let v := inst2 t zero x
  let w := GaussianRationalFiniteSum.sum (shiftBody t) N x
  let A₂ := A * A
  let D₂ := D * D
  let H := S * (K * K) * U + C * D₂
  let T := two * S * U + C * N * D₂
  let B := D₂ * U
  have ha₂ := positive_product _ _ hA hA
  have hd₂ := positive_product _ _ hD hD
  have hB := positive_product _ _ hd₂ hU
  have init := local_row t x A D N S C U zero h (zero_lt_succ N)
  have e : Γ ⊢[PRAAx] rowSquare A D zero ≐ A₂ := by dsimp only [rowSquare, A₂]; ipra_ring
  have first : Γ ⊢[PRAAx] bounded v (S * U + C * A₂) (A₂ * U) :=
    bound_congr (.eqRefl _) (congrAdd (.eqRefl _) (congrMul (.eqRefl _) e)) (congrMul e (.eqRefl _)) init
  have sq : Γ ⊢[PRAAx] le (S * D₂) ((S * (K * K)) * A₂) :=
    le_congr (.eqRefl _) (by dsimp only [A₂]; ipra_ring) (le_mul_mono (le_refl S) (le_mul_mono hK hK))
  have near : Γ ⊢[PRAAx] bounded v H B := reweight v S (S * (K * K)) C U A₂ D₂ hU ha₂ hd₂ sq first
  have far : Γ ⊢[PRAAx] bounded w T B := positive_error t x A D N S C U hA hD hU h
  have total := bounded_sum v w H B T B hB hB near far
  have small := bounded_radius_mono _ _ _ (errorNumerator S C U D K N) (errorDenominator U D)
    (positive_product _ _ hB hB) hB
    (le_of_eq_add (d := zero) (by dsimp only [H, T, B, D₂, errorNumerator, errorDenominator]; ipra_ring)) total
  exact bound_congr (sum_shift_first t N x).eqSymm (.eqRefl _) (.eqRefl _) small

theorem actual_Euler_logarithm_quadratic_sum_bound_closed (t : PTm 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 8
      ((le one (var 1) ⋏ le one (var 2)) ⋏ (le one (var 7) ⋏ le (var 2) (var 3 * var 1)) ⟶
        rowBounds t (var 0) (var 1) (var 2) (var 4) (var 5) (var 6) (var 7) ⟶
        bounded (GaussianRationalFiniteSum.sum t (succ (var 4)) (var 0))
          (errorNumerator (var 5) (var 6) (var 7) (var 2) (var 3) (var 4)) (errorDenominator (var 7) (var 2))) :=
  closeUniv 8 (.impI (.impI (finite_sum_bound t _ _ _ _ _ _ _ _
    Prf.hyp1.andE₁.andE₁ Prf.hyp1.andE₁.andE₂ Prf.hyp1.andE₂.andE₁ Prf.hyp1.andE₂.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianLogGammaEulerTaylorMajorant
