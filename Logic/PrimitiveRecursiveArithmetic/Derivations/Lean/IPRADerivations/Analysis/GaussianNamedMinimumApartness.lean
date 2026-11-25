import IPRADerivations.Analysis.GaussianNamedApartnessTightness
import IPRADerivations.Analysis.GaussianNamedAddRate
import IPRADerivations.Analysis.GaussianNamedRateRadius
import IPRADerivations.Analysis.GaussianSignedNameExponentialOrder
import IPRADerivations.Core.Search

/-!
# Earliest apartness witness and a comparable difference radius

Search up to a given reciprocal apartness witness for the first passing
original norm comparison. If that witness is positive, the preceding
comparison bounds the actual named difference by six times its dyadic
scale. The bound concerns the two original names at independent clocks.
-/

set_option autoImplicit false

namespace LeanProofs.IPRA.Analysis.GaussianNamedMinimumApartness

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open GaussianCoefficientNameBounds (bounded_radius_mono unit unit_positive)
open GaussianEuclideanDistanceName (pointCN)
open GaussianGammaCanonicalExponent (constantF)
open GaussianNameReciprocal (apart anchor R lower_cleared)
open GaussianNamedDifference (nameF data sample_error)
open GaussianNamedInverseRate (independentRate)
open GaussianNamedRateComposition (compose leadingNumerator leadingDenominator symmetric)
open GaussianRationalHorner (positive_product)
open GaussianRationalL1 (rawDen rawGaussian raw_den_positive raw_represents)
open GaussianRationalMetric (comparison_of_cleared qnormSq qnormSq_represents squaredTolerance
  squared_tolerance_represents distanceBounded qsub)
open GaussianRationalReciprocal (normNumerator)
open GaussianReconstructionRoots (norm_from_distance)
open ConciseIPRA.PTm (zero succ)
open LeanProofs.IPRA.PTm (monus num pred)
open Syn
open scoped Fm

variable {n : ℕ} {Γ : List (Fm PTm n)}

def test (f : PR 2) (h x : PTm n) : PTm n :=
  let q := ap2 f (anchor h) x
  monus (rawDen q*rawDen q) (unit h*unit h*normNumerator q)

private def body (f : PR 2) : PTm 2 := test f (var 0) (var 1)

def first (f : PR 2) (h x : PTm n) : PTm n := Search.mu (body f) (succ h) x

@[simp] theorem subst_test {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (h x : PTm n) :
    Syn.subst σ (test f h x) = test f (Syn.subst σ h) (Syn.subst σ x) := by
  simp [test, normNumerator]

@[simp] theorem subst_first {m : ℕ} (σ : Fin n → PTm m) (f : PR 2) (h x : PTm n) :
    Syn.subst σ (first f h x) = first f (Syn.subst σ h) (Syn.subst σ x) := by
  simp [first]

private theorem body_at (f : PR 2) (h x : PTm n) :
    inst2 (body f) h x = test f h x := by
  simp only [inst2, body, subst_test, Syn.subst_var, Matrix.cons_val_zero, Matrix.cons_val_one]

theorem test_spec (f : PR 2) (h x : PTm n) : Γ ⊢[PRAAx] Fm.iff (test f h x ≐ zero) (apart f h x) := by
  let q := ap2 f (anchor h) x
  let d := rawDen q
  let u := unit h
  have hd := raw_den_positive (Γ := Γ) q
  have hu := unit_positive (Γ := Γ) h
  refine .iffI (.impI ?_) (.impI ?_)
  · have clear : (test f h x ≐ zero) :: Γ ⊢[PRAAx] le (d*d) (u*u*normNumerator q) := Prf.hyp0
    exact comparison_of_cleared (squaredTolerance one u) (qnormSq q) (one*one) (normNumerator q) (u*u) (d*d)
      (positive_product _ _ hu.wk hu.wk) (positive_product _ _ hd.wk hd.wk)
      (squared_tolerance_represents one u hu.wk)
      (qnormSq_represents q (rawGaussian q) d hd.wk (raw_represents q))
      (le_congr (by ipra_ring) (by ipra_ring) clear)
  · exact lower_cleared q u hu.wk Prf.hyp0

theorem first_found (f : PR 2) (a x : PTm n) (ha : Γ ⊢[PRAAx] apart f a x) : Γ ⊢[PRAAx]
    le (first f a x) a ⋏ apart f (first f a x) x := by
  have hz : Γ ⊢[PRAAx] inst2 (body f) a x ≐ zero := by
    rw [body_at]
    exact (test_spec f a x).iffMpr ha
  have hit := Search.search_found (N := succ a) hz (le_refl (succ a))
  have found : Γ ⊢[PRAAx] test f (first f a x) x ≐ zero := by
    simpa only [body_at, first] using hit.andE₂.andE₁
  exact .andI hit.andE₂.andE₂ ((test_spec f (first f a x) x).iffMp found)

theorem before_first (f : PR 2) (a x i : PTm n) (hi : Γ ⊢[PRAAx] lt i (first f a x)) :
    Γ ⊢[PRAAx] neg (apart f i x) := by
  have hn := Search.search_minimal (f := body f) (N := succ a) (x := x) hi
  have hz := (test_spec f i x).wk.iffMpr (Prf.hyp0 : (apart f i x :: Γ) ⊢[PRAAx] apart f i x)
  exact .impI (.impE hn.wk (by simpa only [body_at] using hz))

private theorem unit_succ (h : PTm n) : Γ ⊢[PRAAx] unit (succ h) ≐ two*unit h :=
  (pw_succ two h).eqTrans (mul_comm _ _)

theorem inverse_scale (h : PTm n) : Γ ⊢[PRAAx] R h ≐ two*unit h := unit_succ h

private theorem unit_congr {a b : PTm n} (h : Γ ⊢[PRAAx] a ≐ b) :
    Γ ⊢[PRAAx] unit a ≐ unit b := by
  simpa only [GaussianCoefficientNameBounds.subst_unit, Syn.subst_var, Matrix.cons_val_zero] using
    Prf.eqCongr (Γ := Γ) (Ax := PRAAx) (unit (var 0) : PTm 1) (σ := ![a]) (σ' := ![b])
      (fun i => by fin_cases i; exact h)

private theorem unit_anchor (h : PTm n) : Γ ⊢[PRAAx] unit (anchor h) ≐ two*unit (succ h) := by
  have e : Γ ⊢[PRAAx] anchor h ≐ succ (succ h) := by unfold anchor; ipra_ring
  exact (unit_congr e).eqTrans (unit_succ (succ h))

theorem upper_from_previous (g f : PR 2) (y x h : PTm n)
    (hg : Γ ⊢[PRAAx] pointCN g y) (hf : Γ ⊢[PRAAx] pointCN f x)
    (hno : Γ ⊢[PRAAx] neg (apart (nameF g f) h (data y x))) :
    Γ ⊢[PRAAx] independentRate g f y x (num 6) (unit (succ h)) := by
  let t := anchor h
  let U := unit h
  let V := unit (succ h)
  let W := unit t
  let r := ap2 g t y
  let q := ap2 f t x
  let H := nameF g f
  let z := data y x
  let c := ap2 H t z
  have hU := unit_positive (Γ := Γ) h
  have hV := unit_positive (Γ := Γ) (succ h)
  have hW := unit_positive (Γ := Γ) t
  have eV := natEq (unit_succ (Γ := Γ) h)
  have eW := natEq (unit_anchor (Γ := Γ) h)
  have bound := GaussianNamedApartnessTightness.anchor_bound H h z hno
  have near := GaussianRationalDistanceOrder.distance_symmetric c (qsub r q) (num 6) W hW
    (sample_error g f y x t hg hf)
  have mixed := norm_from_distance (qsub r q) c (num 6) W one U hW hU near bound
  have finite : Γ ⊢[PRAAx] distanceBounded r q (num 5) V :=
    bounded_radius_mono _ _ _ (num 5) V (positive_product _ _ hW hU) hV
      (le_of_eq_add (d := zero) (by
        dsimp only [U, V, W, t]
        apply deriveNat
        ipra_simps
        rw [eW, eV]
        ring)) mixed
  have left := GaussianSignedNameExponentialOrder.own_sample_rate g y t hg
  have middle := GaussianNamedAddRate.constant_rate r q (num 5) V hV finite
  have right := symmetric f constantF x q one W hW (GaussianSignedNameExponentialOrder.own_sample_rate f x t hf)
  have both := compose g constantF constantF y r q one W (num 5) V hW hV left middle
  have joined := compose g constantF f y q x (leadingNumerator one W (num 5) V) (leadingDenominator W V)
    one W (positive_product _ _ hW hV) hW both right
  exact GaussianNamedRateRadius.weaken g f y x _ _ (num 6) V
    (positive_product _ _ (positive_product _ _ hW hV) hW) hV
    (le_of_eq_add (d := zero) (by
      dsimp only [leadingNumerator, leadingDenominator, U, V, W, t]
      apply deriveNat
      ipra_simps
      rw [eW]
      ring)) joined

theorem difference_comparable (g f : PR 2) (y x a : PTm n)
    (hg : Γ ⊢[PRAAx] pointCN g y) (hf : Γ ⊢[PRAAx] pointCN f x)
    (ha : Γ ⊢[PRAAx] apart (nameF g f) a (data y x)) : Γ ⊢[PRAAx]
    let b := first (nameF g f) a (data y x)
    apart (nameF g f) b (data y x) ⋏ (b ≐ zero ⋎ independentRate g f y x (num 6) (unit b)) := by
  let H := nameF g f
  let z := data y x
  let b := first H a z
  refine .andI (first_found H a z ha).andE₂ (.orE (zero_or_succ b) (.orI₁ Prf.hyp0) ?_)
  let Δ := (b ≐ succ (pred b)) :: Γ
  have e : Δ ⊢[PRAAx] b ≐ succ (pred b) := Prf.hyp0
  have earlier : Δ ⊢[PRAAx] lt (pred b) b := lt_congr (.eqRefl _) e.eqSymm (le_refl _)
  have no := before_first H a z (pred b) earlier
  have h := upper_from_previous g f y x (pred b) hg.wk hf.wk no
  exact .orI₂ (GaussianNamedDifferenceRate.rate_parameters_congr _ _ _ _ _ _ _ _ (.eqRefl _) (unit_congr e.eqSymm) h)

theorem actual_named_earliest_apart_difference_comparable_closed (g f : PR 2) :
    ([] : List (Fm PTm 0)) ⊢[PRAAx] univ 3
      (let y := var 0
       let x := var 1
       let a := var 2
       let H := nameF g f
       let z := data y x
       let b := first H a z
       (pointCN g y ⋏ pointCN f x) ⟶ apart H a z ⟶ apart H b z ⋏
         (b ≐ zero ⋎ independentRate g f y x (num 6) (unit b))) :=
  closeUniv 3 (.impI (.impI (difference_comparable g f _ _ _ Prf.hyp1.andE₁ Prf.hyp1.andE₂ Prf.hyp0)))

end LeanProofs.IPRA.Analysis.GaussianNamedMinimumApartness
