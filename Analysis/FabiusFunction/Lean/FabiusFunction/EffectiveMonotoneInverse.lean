import FabiusFunction.FabiusComputability
import FabiusFunction.PrimrecNatPow
import Mathlib.Topology.Order.ProjIcc
import Mathlib.Topology.UnitInterval

/-!
# Effective inversion by tolerant bisection

This module isolates the computable-analysis argument used to invert a
strictly increasing map on the unit interval.  Approximate comparisons are
made with a third, inconclusive branch: a certified large signed difference
updates the bracket, while an inconclusive comparison is already a certified
inverse approximation.  Thus the algorithm never attempts to decide equality
of computable reals.
-/

set_option autoImplicit false

open Set

namespace Fabius

/-- A real function is sequentially computable on `s` when it sends every
uniformly computable sequence contained in `s` to a uniformly computable
real sequence. -/
def SequentiallyComputableOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ x : ℕ → ℝ, ComputableRealSequence x →
    (∀ i, x i ∈ s) → ComputableRealSequence (fun i => f (x i))

/-- Clamp a real number to the unit interval. -/
noncomputable def unitClamp (x : ℝ) : ℝ :=
  projIcc (0 : ℝ) 1 zero_le_one x

/-! ### The clamp API

Four one-line facts about `unitClamp` that the computability modules had
each restated privately. -/

/-- The clamp lands in the unit interval. -/
theorem unitClamp_mem_Icc (x : ℝ) : unitClamp x ∈ Icc (0 : ℝ) 1 :=
  (projIcc (0 : ℝ) 1 zero_le_one x).property

/-- The clamp is the identity on the unit interval. -/
theorem unitClamp_of_mem {x : ℝ} (hx : x ∈ Icc (0 : ℝ) 1) :
    unitClamp x = x := by
  simpa only [unitClamp] using
    congrArg Subtype.val (projIcc_of_mem zero_le_one hx)

/-- The clamp is `0` to the left of the unit interval. -/
theorem unitClamp_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) :
    unitClamp x = 0 := by
  simpa only [unitClamp] using
    congrArg Subtype.val (projIcc_of_le_left (b := (1 : ℝ)) zero_le_one hx)

/-- The clamp is `1` to the right of the unit interval. -/
theorem unitClamp_eq_one_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    unitClamp x = 1 := by
  simpa only [unitClamp] using
    congrArg Subtype.val (projIcc_of_right_le (a := (0 : ℝ)) zero_le_one hx)

/-- The clamp is `1`-Lipschitz. -/
theorem abs_unitClamp_sub_unitClamp_le (x y : ℝ) :
    |unitClamp x - unitClamp y| ≤ |x - y| :=
  abs_projIcc_sub_projIcc zero_le_one

private def unitClampNumerator (c : DyadicNumerator) (p : ℕ) : DyadicNumerator :=
  (min (c.1 - c.2) (2 ^ p), 0)

private theorem unitClampNumerator_primrec :
    Primrec₂ unitClampNumerator := by
  have hpow : Primrec₂ (fun (_c : DyadicNumerator) (p : ℕ) => 2 ^ p) :=
    primrec₂_nat_pow.comp₂ (Primrec.const 2).to₂
      Primrec₂.right
  have hsub : Primrec₂ (fun (c : DyadicNumerator) (_p : ℕ) => c.1 - c.2) :=
    Primrec.nat_sub.comp₂
      (Primrec.fst.comp₂ Primrec₂.left)
      (Primrec.snd.comp₂ Primrec₂.left)
  exact Primrec₂.pair.comp₂ (Primrec.nat_min.comp₂ hsub hpow)
    (Primrec.const 0).to₂

private theorem unitClampNumerator_value
    (c : DyadicNumerator) (p : ℕ) :
    (unitClampNumerator c p).value p = unitClamp (c.value p) := by
  unfold unitClampNumerator unitClamp DyadicNumerator.value
  simp only [Nat.cast_zero, sub_zero]
  rw [coe_projIcc]
  by_cases hsign : c.1 ≤ c.2
  · have hvalue : (↑c.1 - ↑c.2 : ℝ) / (2 : ℝ) ^ p ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (by exact_mod_cast hsign)) (by positivity)
    have hsub : c.1 - c.2 = 0 := Nat.sub_eq_zero_of_le hsign
    have hmin : min (1 : ℝ) ((↑c.1 - ↑c.2) / (2 : ℝ) ^ p) ≤ 0 :=
      (min_le_right _ _).trans hvalue
    rw [max_eq_left hmin]
    rw [hsub]
    norm_num
  · have hle : c.2 ≤ c.1 := (Nat.lt_of_not_ge hsign).le
    have hnonneg : 0 ≤ (↑c.1 - ↑c.2 : ℝ) / (2 : ℝ) ^ p :=
      div_nonneg (sub_nonneg.mpr (by exact_mod_cast hle)) (by positivity)
    rw [Nat.cast_min, Nat.cast_sub hle]
    rw [max_eq_right (le_min zero_le_one hnonneg)]
    rw [show (1 : ℝ) = (2 : ℝ) ^ p / (2 : ℝ) ^ p by
      exact (div_self (by positivity)).symm]
    rw [min_div_div_right (by positivity : (0 : ℝ) ≤ (2 : ℝ) ^ p)]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
    rw [min_comm]

/-- Clamping to the unit interval preserves computable real sequences. -/
theorem unitClamp_sequentiallyComputable :
    SequentiallyComputable unitClamp := by
  intro x hx
  obtain ⟨a, haComp, haErr⟩ := hx
  refine ⟨fun i p => unitClampNumerator (a i p) p, ?_, ?_⟩
  · exact unitClampNumerator_primrec.to_comp.comp haComp Computable.snd
  · intro i p
    rw [unitClampNumerator_value]
    exact (abs_projIcc_sub_projIcc zero_le_one).trans (haErr i p)

/-- If the forward value and target are each known within `δ / 8`, their
computed difference is known within `δ / 4`. -/
theorem tolerantDifference_error
    {f : ℝ → ℝ} {c y fApprox yApprox δ : ℝ}
    (hf : |fApprox - f c| ≤ δ / 8)
    (hy : |yApprox - y| ≤ δ / 8) :
    |(fApprox - yApprox) - (f c - y)| ≤ δ / 4 := by
  calc
    |(fApprox - yApprox) - (f c - y)| =
        |(fApprox - f c) - (yApprox - y)| := by ring_nf
    _ ≤ |fApprox - f c| + |yApprox - y| := abs_sub _ _
    _ ≤ δ / 8 + δ / 8 := add_le_add hf hy
    _ = δ / 4 := by ring

/-- A signed approximate difference larger than the tolerance gives a safe
strict left or right update of the inverse bracket. -/
theorem tolerantDifference_safe_updates
    {f g : ℝ → ℝ} {c y D δ : ℝ}
    (hδ : 0 < δ)
    (hc : c ∈ Icc (0 : ℝ) 1)
    (hgy : g y ∈ Icc (0 : ℝ) 1)
    (hmono : StrictMonoOn f (Icc (0 : ℝ) 1))
    (hinv : f (g y) = y)
    (hcert : |D - (f c - y)| ≤ δ / 4) :
    (δ / 2 < D → g y < c) ∧
      (D < -δ / 2 → c < g y) := by
  have hlower : D - δ / 4 ≤ f c - y := by
    have := (le_abs_self (D - (f c - y))).trans hcert
    linarith
  have hupper : f c - y ≤ D + δ / 4 := by
    have := (neg_le_abs (D - (f c - y))).trans hcert
    linarith
  constructor
  · intro hD
    apply (hmono.lt_iff_lt hgy hc).mp
    rw [hinv]
    linarith
  · intro hD
    apply (hmono.lt_iff_lt hc hgy).mp
    rw [hinv]
    linarith

/-- The inconclusive comparison branch is a successful inverse
approximation, by the supplied inverse modulus. -/
theorem tolerantDifference_inconclusive
    {f g : ℝ → ℝ} {c y D δ h : ℝ}
    (hδ : 0 < δ)
    (hleft : g (f c) = c)
    (hmod : ∀ u v, |u - v| < δ → |g u - g v| < h)
    (hcert : |D - (f c - y)| ≤ δ / 4)
    (hnear : |D| ≤ δ / 2) :
    |c - g y| < h := by
  have htrue : |f c - y| < δ := by
    calc
      |f c - y| ≤ |D| + |D - (f c - y)| := by
        simpa only [sub_sub_cancel] using abs_sub D (D - (f c - y))
      _ ≤ δ / 2 + δ / 4 := add_le_add hnear hcert
      _ < δ := by linarith
  simpa only [hleft] using hmod (f c) y htrue

private abbrev TolerantBisectionState := ℕ × Option ℕ

private def tolerantMidpointCode (p d j : ℕ) : DyadicNumerator :=
  ((2 * j + 1) * 2 ^ (p + d + 5), 0)

private def tolerantBisectionNoneStep
    (approx : DyadicNumerator → ℕ → DyadicNumerator)
    (a : ℕ → ℕ → DyadicNumerator) (den : ℕ → ℕ)
    (ip sj : ℕ × ℕ) : TolerantBisectionState :=
  let q := ip.2 + den ip.2 + 3 + sj.1
  let A := approx (tolerantMidpointCode ip.2 (den ip.2) sj.2) q
  let B := a ip.1 q
  let L := A.1 + B.2
  let U := A.2 + B.1
  if U + 4 < L then (2 * sj.2, none)
  else if L + 4 < U then (2 * sj.2 + 1, none)
  else (sj.2, some (2 * sj.2 + 1))

private def tolerantBisectionStep
    (approx : DyadicNumerator → ℕ → DyadicNumerator)
    (a : ℕ → ℕ → DyadicNumerator) (den : ℕ → ℕ)
    (ip : ℕ × ℕ) (ss : ℕ × TolerantBisectionState) :
    TolerantBisectionState :=
  match ss.2.2 with
  | some z => (ss.2.1, some (2 * z))
  | none => tolerantBisectionNoneStep approx a den ip (ss.1, ss.2.1)

private def tolerantBisectionStateAt
    (approx : DyadicNumerator → ℕ → DyadicNumerator)
    (a : ℕ → ℕ → DyadicNumerator) (den : ℕ → ℕ)
    (i p s : ℕ) : TolerantBisectionState :=
  Nat.rec (0, none)
    (fun r state => tolerantBisectionStep approx a den (i, p) (r, state)) s

private def tolerantBisectionState
    (approx : DyadicNumerator → ℕ → DyadicNumerator)
    (a : ℕ → ℕ → DyadicNumerator) (den : ℕ → ℕ)
    (i p : ℕ) : TolerantBisectionState :=
  tolerantBisectionStateAt approx a den i p p

private def tolerantBisectionName
    (approx : DyadicNumerator → ℕ → DyadicNumerator)
    (a : ℕ → ℕ → DyadicNumerator) (den : ℕ → ℕ)
    (i p : ℕ) : DyadicNumerator :=
  let state := tolerantBisectionState approx a den i p
  (state.2.getD state.1, 0)

private theorem tolerantMidpointCode_value (p d s j : ℕ) :
    (tolerantMidpointCode p d j).value (p + d + 3 + s + 3) =
      (2 * (j : ℝ) + 1) / (2 : ℝ) ^ (s + 1) := by
  unfold tolerantMidpointCode DyadicNumerator.value
  simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat, Nat.cast_one,
    Nat.cast_pow, Nat.cast_zero, sub_zero]
  rw [show p + d + 3 + s + 3 = (p + d + 5) + (s + 1) by omega,
    pow_add]
  field_simp
  rw [show p + d + 5 + (s + 1) = 5 + (p + d) + (s + 1) by omega,
    pow_add, pow_add]
  ring

private theorem dyadicDifference_value
    (A B : DyadicNumerator) (q : ℕ) :
    A.value q - B.value q =
      (((A.1 + B.2 : ℕ) : ℝ) - (A.2 + B.1 : ℕ)) / (2 : ℝ) ^ q := by
  unfold DyadicNumerator.value
  push_cast
  ring

private theorem dyadicDifference_gt_margin
    (A B : DyadicNumerator) (q : ℕ)
    (h : A.2 + B.1 + 4 < A.1 + B.2) :
    4 * ((2 : ℝ) ^ q)⁻¹ < A.value q - B.value q := by
  rw [dyadicDifference_value]
  have h' : (A.2 + B.1 : ℝ) + 4 < A.1 + B.2 := by exact_mod_cast h
  have hpow : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  rw [show 4 * ((2 : ℝ) ^ q)⁻¹ = 4 / (2 : ℝ) ^ q by
    rw [div_eq_mul_inv]]
  apply (div_lt_div_iff_of_pos_right hpow).2
  push_cast
  linarith

private theorem dyadicDifference_lt_neg_margin
    (A B : DyadicNumerator) (q : ℕ)
    (h : A.1 + B.2 + 4 < A.2 + B.1) :
    A.value q - B.value q < -4 * ((2 : ℝ) ^ q)⁻¹ := by
  rw [dyadicDifference_value]
  have h' : (A.1 + B.2 : ℝ) + 4 < A.2 + B.1 := by exact_mod_cast h
  have hpow : (0 : ℝ) < (2 : ℝ) ^ q := by positivity
  rw [show -4 * ((2 : ℝ) ^ q)⁻¹ = (-4 : ℝ) / (2 : ℝ) ^ q by
    rw [div_eq_mul_inv]]
  apply (div_lt_div_iff_of_pos_right hpow).2
  push_cast
  linarith

private theorem abs_dyadicDifference_le_margin
    (A B : DyadicNumerator) (q : ℕ)
    (hleft : ¬ A.2 + B.1 + 4 < A.1 + B.2)
    (hright : ¬ A.1 + B.2 + 4 < A.2 + B.1) :
    |A.value q - B.value q| ≤ 4 * ((2 : ℝ) ^ q)⁻¹ := by
  rw [dyadicDifference_value, abs_div]
  have h₁ : (A.1 + B.2 : ℝ) - (A.2 + B.1 : ℝ) ≤ 4 := by
    have hcast : ((A.1 + B.2 : ℕ) : ℝ) ≤ (A.2 + B.1 + 4 : ℕ) := by
      exact_mod_cast (Nat.le_of_not_gt hleft)
    push_cast at hcast
    linarith
  have h₂ : -(4 : ℝ) ≤ (A.1 + B.2 : ℝ) - (A.2 + B.1 : ℝ) := by
    have hcast : ((A.2 + B.1 : ℕ) : ℝ) ≤ (A.1 + B.2 + 4 : ℕ) := by
      exact_mod_cast (Nat.le_of_not_gt hright)
    push_cast at hcast
    linarith
  rw [abs_of_pos (by positivity : (0 : ℝ) < (2 : ℝ) ^ q)]
  simp only [Nat.cast_add]
  have habs : |(A.1 : ℝ) + B.2 - ((A.2 : ℝ) + B.1)| ≤ 4 :=
    (abs_le).2 ⟨h₂, h₁⟩
  calc
    |(A.1 : ℝ) + B.2 - ((A.2 : ℝ) + B.1)| / (2 : ℝ) ^ q ≤
        4 / (2 : ℝ) ^ q :=
      (div_le_div_iff_of_pos_right (by positivity)).2 habs
    _ = 4 * ((2 : ℝ) ^ q)⁻¹ := by rw [div_eq_mul_inv]

private theorem tolerantScale_lt_inv_den
    (p d s : ℕ) (hd : 0 < d) :
    8 * ((2 : ℝ) ^ (p + d + 3 + s))⁻¹ < (d : ℝ)⁻¹ := by
  have hpowNat : d < 2 ^ (p + d + s) :=
    (Nat.lt_two_pow_self (n := d)).trans_le
      (Nat.pow_le_pow_right (by norm_num) (by omega))
  have hpowReal : (d : ℝ) < (2 : ℝ) ^ (p + d + s) := by
    exact_mod_cast hpowNat
  have hscale :
      8 * ((2 : ℝ) ^ (p + d + 3 + s))⁻¹ =
        ((2 : ℝ) ^ (p + d + s))⁻¹ := by
    rw [show p + d + 3 + s = (p + d + s) + 3 by omega, pow_add]
    norm_num
    ring
  rw [hscale]
  exact (inv_lt_inv₀ (by positivity) (by exact_mod_cast hd)).2 hpowReal

private noncomputable def dyadicPoint (j s : ℕ) : ℝ :=
  (j : ℝ) / (2 : ℝ) ^ s

private def TolerantBisectionInvariant
    (g : ℝ → ℝ) (y : ℝ) (p s : ℕ)
    (state : TolerantBisectionState) : Prop :=
  match state.2 with
  | some z => |dyadicPoint z s - g y| < ((2 : ℝ) ^ p)⁻¹
  | none => state.1 < 2 ^ s ∧
      g y ∈ Icc (dyadicPoint state.1 s) (dyadicPoint (state.1 + 1) s)

private theorem five_inv_pow_add_three_le (q : ℕ) :
    5 * ((2 : ℝ) ^ (q + 3))⁻¹ ≤ ((2 : ℝ) ^ q)⁻¹ := by
  rw [pow_add]
  norm_num
  have h : 0 ≤ ((2 : ℝ) ^ q)⁻¹ := by positivity
  nlinarith

private theorem dyadicPoint_midpoint (j s : ℕ) :
    dyadicPoint (2 * j + 1) (s + 1) =
      (2 * (j : ℝ) + 1) / (2 : ℝ) ^ (s + 1) := by
  simp [dyadicPoint]

private theorem dyadicPoint_double (j s : ℕ) :
    dyadicPoint (2 * j) (s + 1) = dyadicPoint j s := by
  unfold dyadicPoint
  rw [pow_succ]
  push_cast
  field_simp

private theorem dyadicPoint_two_mul_add_one (j s : ℕ) :
    dyadicPoint (2 * j + 1) (s + 1) =
      (dyadicPoint j s + dyadicPoint (j + 1) s) / 2 := by
  unfold dyadicPoint
  rw [pow_succ]
  push_cast
  field_simp
  ring

private theorem dyadicPoint_right_half (j s : ℕ) :
    dyadicPoint (2 * j + 2) (s + 1) = dyadicPoint (j + 1) s := by
  rw [show 2 * j + 2 = 2 * (j + 1) by omega, dyadicPoint_double]

private theorem dyadicPoint_width (j s : ℕ) :
    dyadicPoint (j + 1) s - dyadicPoint j s = ((2 : ℝ) ^ s)⁻¹ := by
  unfold dyadicPoint
  push_cast
  field_simp
  ring

private theorem dyadicMidpoint_mem_Icc {j s : ℕ} (hj : j < 2 ^ s) :
    dyadicPoint (2 * j + 1) (s + 1) ∈ Icc (0 : ℝ) 1 := by
  constructor
  · exact div_nonneg (by positivity) (by positivity)
  · apply (div_le_one (by positivity : (0 : ℝ) < (2 : ℝ) ^ (s + 1))).2
    have hnat : 2 * j + 1 ≤ 2 ^ (s + 1) := by
      rw [pow_succ]
      omega
    exact_mod_cast hnat

private theorem dyadicPoint_left_index {j s : ℕ} (hj : j < 2 ^ s) :
    2 * j < 2 ^ (s + 1) := by
  rw [pow_succ]
  omega

private theorem dyadicPoint_right_index {j s : ℕ} (hj : j < 2 ^ s) :
    2 * j + 1 < 2 ^ (s + 1) := by
  rw [pow_succ]
  omega

private theorem tolerantBisectionNoneStep_correct
    {f g : ℝ → ℝ}
    (hdyadic : HasComputableDyadicApproximation f)
    (hmono : StrictMonoOn f (Icc (0 : ℝ) 1))
    (hfmap : MapsTo f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hgmap : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hinv : InvOn g f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (den : ℕ → ℕ) (hdenPos : ∀ p, 0 < den p)
    (hmod : ∀ p {u v : ℝ}, u ∈ Icc (0 : ℝ) 1 →
      v ∈ Icc (0 : ℝ) 1 → |u - v| < ((den p : ℝ))⁻¹ →
      |g u - g v| < ((2 : ℝ) ^ p)⁻¹)
    {x : ℕ → ℝ} (a : ℕ → ℕ → DyadicNumerator)
    (haErr : ∀ i p, |x i - (a i p).value p| ≤ ((2 : ℝ) ^ p)⁻¹)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1)
    (i p s j : ℕ) (hj : j < 2 ^ s)
    (hbracket : g (x i) ∈
      Icc (dyadicPoint j s) (dyadicPoint (j + 1) s)) :
    TolerantBisectionInvariant g (x i) p (s + 1)
      (tolerantBisectionNoneStep hdyadic.approx a den (i, p) (s, j)) := by
  let d := den p
  let q := p + d + 3 + s
  let c := dyadicPoint (2 * j + 1) (s + 1)
  let A := hdyadic.approx (tolerantMidpointCode p d j) q
  let B := a i q
  let D := A.value q - B.value q
  let δ := 8 * ((2 : ℝ) ^ q)⁻¹
  have hd : 0 < d := hdenPos p
  have hδ : 0 < δ := by simp only [δ]; positivity
  have hc : c ∈ Icc (0 : ℝ) 1 := dyadicMidpoint_mem_Icc hj
  have hy : x i ∈ Icc (0 : ℝ) 1 := hx i
  have hgy : g (x i) ∈ Icc (0 : ℝ) 1 := hgmap hy
  have hcode :
      (tolerantMidpointCode p d j).value (q + 3) = c := by
    rw [show q + 3 = p + d + 3 + s + 3 by simp [q],
      tolerantMidpointCode_value, ← dyadicPoint_midpoint]
  have hδeight : δ / 8 = ((2 : ℝ) ^ q)⁻¹ := by
    simp only [δ]
    ring
  have hδhalf : δ / 2 = 4 * ((2 : ℝ) ^ q)⁻¹ := by
    simp only [δ]
    ring
  have hfErr : |A.value q - f c| ≤ δ / 8 := by
    rw [hδeight, abs_sub_comm, ← hcode]
    exact (hdyadic.error (tolerantMidpointCode p d j) q).trans
      (five_inv_pow_add_three_le q)
  have hyErr : |B.value q - x i| ≤ δ / 8 := by
    rw [hδeight, abs_sub_comm]
    exact haErr i q
  have hcert : |D - (f c - x i)| ≤ δ / 4 :=
    tolerantDifference_error hfErr hyErr
  have hscale : δ < (d : ℝ)⁻¹ := by
    simpa only [δ, q, d] using tolerantScale_lt_inv_den p (den p) s (hdenPos p)
  have hsafe := tolerantDifference_safe_updates hδ hc hgy hmono
    (hinv.2 hy) hcert
  unfold tolerantBisectionNoneStep
  dsimp only
  split_ifs with hpositive hnegative
  · change 2 * j < 2 ^ (s + 1) ∧
      g (x i) ∈ Icc (dyadicPoint (2 * j) (s + 1))
        (dyadicPoint (2 * j + 1) (s + 1))
    have hpositive' : A.2 + B.1 + 4 < A.1 + B.2 := by
      simpa only [A, B, q, d] using hpositive
    refine ⟨dyadicPoint_left_index hj, ?_⟩
    rw [dyadicPoint_double]
    exact ⟨hbracket.1, (hsafe.1 (by
      rw [hδhalf]
      exact dyadicDifference_gt_margin A B q hpositive')).le⟩
  · change 2 * j + 1 < 2 ^ (s + 1) ∧
      g (x i) ∈ Icc (dyadicPoint (2 * j + 1) (s + 1))
        (dyadicPoint (2 * j + 1 + 1) (s + 1))
    have hnegative' : A.1 + B.2 + 4 < A.2 + B.1 := by
      simpa only [A, B, q, d] using hnegative
    refine ⟨dyadicPoint_right_index hj, ?_⟩
    rw [show 2 * j + 1 + 1 = 2 * j + 2 by omega,
      dyadicPoint_right_half]
    exact ⟨(hsafe.2 (by
      have hD := dyadicDifference_lt_neg_margin A B q hnegative'
      change D < -δ / 2
      calc
        D = A.value q - B.value q := rfl
        _ < -4 * ((2 : ℝ) ^ q)⁻¹ := hD
        _ = -δ / 2 := by simp only [δ]; ring)).le,
      hbracket.2⟩
  · change |dyadicPoint (2 * j + 1) (s + 1) - g (x i)| <
      ((2 : ℝ) ^ p)⁻¹
    have hpositive' : ¬ A.2 + B.1 + 4 < A.1 + B.2 := by
      simpa only [A, B, q, d] using hpositive
    have hnegative' : ¬ A.1 + B.2 + 4 < A.2 + B.1 := by
      simpa only [A, B, q, d] using hnegative
    have hnear : |D| ≤ δ / 2 := by
      rw [hδhalf]
      exact abs_dyadicDifference_le_margin A B q hpositive' hnegative'
    have htrue : |f c - x i| < δ := by
      calc
        |f c - x i| ≤ |D| + |D - (f c - x i)| := by
          simpa only [sub_sub_cancel] using abs_sub D (D - (f c - x i))
        _ ≤ δ / 2 + δ / 4 := add_le_add hnear hcert
        _ < δ := by linarith
    change |c - g (x i)| < ((2 : ℝ) ^ p)⁻¹
    rw [← hinv.1 hc]
    exact hmod p (hfmap hc) hy (htrue.trans hscale)

private theorem tolerantBisectionStep_correct
    {f g : ℝ → ℝ}
    (hdyadic : HasComputableDyadicApproximation f)
    (hmono : StrictMonoOn f (Icc (0 : ℝ) 1))
    (hfmap : MapsTo f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hgmap : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hinv : InvOn g f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (den : ℕ → ℕ) (hdenPos : ∀ p, 0 < den p)
    (hmod : ∀ p {u v : ℝ}, u ∈ Icc (0 : ℝ) 1 →
      v ∈ Icc (0 : ℝ) 1 → |u - v| < ((den p : ℝ))⁻¹ →
      |g u - g v| < ((2 : ℝ) ^ p)⁻¹)
    {x : ℕ → ℝ} (a : ℕ → ℕ → DyadicNumerator)
    (haErr : ∀ i p, |x i - (a i p).value p| ≤ ((2 : ℝ) ^ p)⁻¹)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1)
    (i p s : ℕ) (state : TolerantBisectionState)
    (hstate : TolerantBisectionInvariant g (x i) p s state) :
    TolerantBisectionInvariant g (x i) p (s + 1)
      (tolerantBisectionStep hdyadic.approx a den (i, p) (s, state)) := by
  rcases state with ⟨j, hit⟩
  cases hit with
  | none =>
      exact tolerantBisectionNoneStep_correct hdyadic hmono hfmap hgmap hinv den
        hdenPos hmod a haErr hx i p s j hstate.1 hstate.2
  | some z =>
      change |dyadicPoint (2 * z) (s + 1) - g (x i)| < ((2 : ℝ) ^ p)⁻¹
      rw [dyadicPoint_double]
      exact hstate

private theorem tolerantBisectionStateAt_invariant
    {f g : ℝ → ℝ}
    (hdyadic : HasComputableDyadicApproximation f)
    (hmono : StrictMonoOn f (Icc (0 : ℝ) 1))
    (hfmap : MapsTo f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hgmap : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hinv : InvOn g f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (den : ℕ → ℕ) (hdenPos : ∀ p, 0 < den p)
    (hmod : ∀ p {u v : ℝ}, u ∈ Icc (0 : ℝ) 1 →
      v ∈ Icc (0 : ℝ) 1 → |u - v| < ((den p : ℝ))⁻¹ →
      |g u - g v| < ((2 : ℝ) ^ p)⁻¹)
    {x : ℕ → ℝ} (a : ℕ → ℕ → DyadicNumerator)
    (haErr : ∀ i p, |x i - (a i p).value p| ≤ ((2 : ℝ) ^ p)⁻¹)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1)
    (i p s : ℕ) :
    TolerantBisectionInvariant g (x i) p s
      (tolerantBisectionStateAt hdyadic.approx a den i p s) := by
  induction s with
  | zero =>
      change 0 < 2 ^ 0 ∧ g (x i) ∈ Icc (dyadicPoint 0 0) (dyadicPoint (0 + 1) 0)
      simpa [dyadicPoint] using And.intro (by norm_num : 0 < 2 ^ 0) (hgmap (hx i))
  | succ s ih =>
      change TolerantBisectionInvariant g (x i) p (s + 1)
        (tolerantBisectionStep hdyadic.approx a den (i, p)
          (s, tolerantBisectionStateAt hdyadic.approx a den i p s))
      exact tolerantBisectionStep_correct hdyadic hmono hfmap hgmap hinv den
        hdenPos hmod a haErr hx i p s _ ih

private theorem tolerantBisectionName_error
    {f g : ℝ → ℝ}
    (hdyadic : HasComputableDyadicApproximation f)
    (hmono : StrictMonoOn f (Icc (0 : ℝ) 1))
    (hfmap : MapsTo f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hgmap : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hinv : InvOn g f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (den : ℕ → ℕ) (hdenPos : ∀ p, 0 < den p)
    (hmod : ∀ p {u v : ℝ}, u ∈ Icc (0 : ℝ) 1 →
      v ∈ Icc (0 : ℝ) 1 → |u - v| < ((den p : ℝ))⁻¹ →
      |g u - g v| < ((2 : ℝ) ^ p)⁻¹)
    {x : ℕ → ℝ} (a : ℕ → ℕ → DyadicNumerator)
    (haErr : ∀ i p, |x i - (a i p).value p| ≤ ((2 : ℝ) ^ p)⁻¹)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1)
    (i p : ℕ) :
    |g (x i) -
      (tolerantBisectionName hdyadic.approx a den i p).value p| ≤
        ((2 : ℝ) ^ p)⁻¹ := by
  have hstate := tolerantBisectionStateAt_invariant hdyadic hmono hfmap hgmap
    hinv den hdenPos hmod a haErr hx i p p
  let state := tolerantBisectionState hdyadic.approx a den i p
  have hstate' : TolerantBisectionInvariant g (x i) p p state := by
    simpa only [state, tolerantBisectionState] using hstate
  unfold tolerantBisectionName DyadicNumerator.value
  simp only [Nat.cast_zero, sub_zero]
  change |g (x i) - dyadicPoint (state.2.getD state.1) p| ≤
    ((2 : ℝ) ^ p)⁻¹
  rcases state with ⟨j, hit⟩
  cases hit with
  | some z =>
      change |g (x i) - dyadicPoint z p| ≤ ((2 : ℝ) ^ p)⁻¹
      rw [abs_sub_comm]
      exact hstate'.le
  | none =>
      change |g (x i) - dyadicPoint j p| ≤ ((2 : ℝ) ^ p)⁻¹
      rw [abs_of_nonneg (sub_nonneg.mpr hstate'.2.1)]
      calc
        g (x i) - dyadicPoint j p ≤
            dyadicPoint (j + 1) p - dyadicPoint j p :=
          sub_le_sub_right hstate'.2.2 _
        _ = ((2 : ℝ) ^ p)⁻¹ := dyadicPoint_width j p

private theorem computable_ite_nat_lt
    {α σ : Type*} [Primcodable α] [Primcodable σ]
    {l r : α → ℕ} {yes no : α → σ}
    (hl : Computable l) (hr : Computable r)
    (hyes : Computable yes) (hno : Computable no) :
    Computable (fun x => if l x < r x then yes x else no x) := by
  have htest : Computable (fun x => decide (l x < r x)) :=
    Primrec.nat_lt.decide.to_comp.comp hl hr
  exact (Computable.cond htest hyes hno).of_eq fun x => by
    simp only [Bool.cond_decide]

private theorem tolerantBisectionNoneStep_computable
    {approx : DyadicNumerator → ℕ → DyadicNumerator}
    {a : ℕ → ℕ → DyadicNumerator} {den : ℕ → ℕ}
    (happrox : Computable₂ approx) (ha : Computable₂ a)
    (hden : Computable den) :
    Computable₂ (tolerantBisectionNoneStep approx a den) := by
  let X := (ℕ × ℕ) × (ℕ × ℕ)
  have hi : Computable (fun z : X => z.1.1) :=
    Computable.fst.comp Computable.fst
  have hp : Computable (fun z : X => z.1.2) :=
    Computable.snd.comp Computable.fst
  have hs : Computable (fun z : X => z.2.1) :=
    Computable.fst.comp Computable.snd
  have hj : Computable (fun z : X => z.2.2) :=
    Computable.snd.comp Computable.snd
  have hd : Computable (fun z : X => den z.1.2) := hden.comp hp
  have hpd : Computable (fun z : X => z.1.2 + den z.1.2) :=
    Primrec.nat_add.to_comp.comp hp hd
  have hpd3 : Computable (fun z : X => z.1.2 + den z.1.2 + 3) :=
    Primrec.nat_add.to_comp.comp hpd (Computable.const 3)
  have hq : Computable (fun z : X => z.1.2 + den z.1.2 + 3 + z.2.1) :=
    Primrec.nat_add.to_comp.comp hpd3 hs
  have htwoj : Computable (fun z : X => 2 * z.2.2) :=
    Primrec.nat_mul.to_comp.comp (Computable.const 2) hj
  have htwoj1 : Computable (fun z : X => 2 * z.2.2 + 1) :=
    Primrec.nat_add.to_comp.comp htwoj (Computable.const 1)
  have hpd5 : Computable (fun z : X => z.1.2 + den z.1.2 + 5) :=
    Primrec.nat_add.to_comp.comp hpd (Computable.const 5)
  have hpow : Computable₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
    computable₂_nat_pow
  have hscale : Computable (fun z : X => 2 ^ (z.1.2 + den z.1.2 + 5)) :=
    hpow.comp (Computable.const 2) hpd5
  have hnum : Computable
      (fun z : X => (2 * z.2.2 + 1) * 2 ^ (z.1.2 + den z.1.2 + 5)) :=
    Primrec.nat_mul.to_comp.comp htwoj1 hscale
  have hcode : Computable
      (fun z : X => tolerantMidpointCode z.1.2 (den z.1.2) z.2.2) := by
    exact (hnum.pair (Computable.const 0)).of_eq fun z => rfl
  have hA : Computable (fun z : X =>
      approx (tolerantMidpointCode z.1.2 (den z.1.2) z.2.2)
        (z.1.2 + den z.1.2 + 3 + z.2.1)) :=
    happrox.comp hcode hq
  have hB : Computable (fun z : X =>
      a z.1.1 (z.1.2 + den z.1.2 + 3 + z.2.1)) :=
    ha.comp hi hq
  have hApos : Computable (fun z : X =>
      (approx (tolerantMidpointCode z.1.2 (den z.1.2) z.2.2)
        (z.1.2 + den z.1.2 + 3 + z.2.1)).1) :=
    Computable.fst.comp hA
  have hAneg : Computable (fun z : X =>
      (approx (tolerantMidpointCode z.1.2 (den z.1.2) z.2.2)
        (z.1.2 + den z.1.2 + 3 + z.2.1)).2) :=
    Computable.snd.comp hA
  have hBpos : Computable (fun z : X =>
      (a z.1.1 (z.1.2 + den z.1.2 + 3 + z.2.1)).1) :=
    Computable.fst.comp hB
  have hBneg : Computable (fun z : X =>
      (a z.1.1 (z.1.2 + den z.1.2 + 3 + z.2.1)).2) :=
    Computable.snd.comp hB
  have hL : Computable (fun z : X =>
      (approx (tolerantMidpointCode z.1.2 (den z.1.2) z.2.2)
          (z.1.2 + den z.1.2 + 3 + z.2.1)).1 +
        (a z.1.1 (z.1.2 + den z.1.2 + 3 + z.2.1)).2) :=
    Primrec.nat_add.to_comp.comp hApos hBneg
  have hU : Computable (fun z : X =>
      (approx (tolerantMidpointCode z.1.2 (den z.1.2) z.2.2)
          (z.1.2 + den z.1.2 + 3 + z.2.1)).2 +
        (a z.1.1 (z.1.2 + den z.1.2 + 3 + z.2.1)).1) :=
    Primrec.nat_add.to_comp.comp hAneg hBpos
  let L : X → ℕ := fun z =>
    (approx (tolerantMidpointCode z.1.2 (den z.1.2) z.2.2)
      (z.1.2 + den z.1.2 + 3 + z.2.1)).1 +
      (a z.1.1 (z.1.2 + den z.1.2 + 3 + z.2.1)).2
  let U : X → ℕ := fun z =>
    (approx (tolerantMidpointCode z.1.2 (den z.1.2) z.2.2)
      (z.1.2 + den z.1.2 + 3 + z.2.1)).2 +
      (a z.1.1 (z.1.2 + den z.1.2 + 3 + z.2.1)).1
  have hL' : Computable L := hL
  have hU' : Computable U := hU
  have hL4 : Computable (fun z => L z + 4) :=
    Primrec.nat_add.to_comp.comp hL' (Computable.const 4)
  have hU4 : Computable (fun z => U z + 4) :=
    Primrec.nat_add.to_comp.comp hU' (Computable.const 4)
  have houtLeft : Computable (fun z : X =>
      (2 * z.2.2, (none : Option ℕ))) :=
    htwoj.pair (Computable.const none)
  have houtRight : Computable (fun z : X =>
      (2 * z.2.2 + 1, (none : Option ℕ))) :=
    htwoj1.pair (Computable.const none)
  have hsome : Computable (fun z : X => some (2 * z.2.2 + 1)) :=
    Computable.option_some.comp htwoj1
  have houtHit : Computable (fun z : X =>
      (z.2.2, some (2 * z.2.2 + 1))) := hj.pair hsome
  have helse : Computable (fun z : X =>
      if L z + 4 < U z then (2 * z.2.2 + 1, none)
      else (z.2.2, some (2 * z.2.2 + 1))) :=
    computable_ite_nat_lt hL4 hU' houtRight houtHit
  have hall : Computable (fun z : X =>
      if U z + 4 < L z then (2 * z.2.2, none)
      else if L z + 4 < U z then (2 * z.2.2 + 1, none)
      else (z.2.2, some (2 * z.2.2 + 1))) :=
    computable_ite_nat_lt hU4 hL' houtLeft helse
  exact hall.of_eq fun z => by
    simp only [L, U]
    rfl

set_option maxHeartbeats 600000 in
private theorem tolerantBisectionStep_computable
    {approx : DyadicNumerator → ℕ → DyadicNumerator}
    {a : ℕ → ℕ → DyadicNumerator} {den : ℕ → ℕ}
    (happrox : Computable₂ approx) (ha : Computable₂ a)
    (hden : Computable den) :
    Computable₂ (tolerantBisectionStep approx a den) := by
  let X := (ℕ × ℕ) × (ℕ × TolerantBisectionState)
  change Computable (fun z : X =>
    tolerantBisectionStep approx a den z.1 z.2)
  have hj : Computable (fun z : X => z.2.2.1) :=
    Computable.fst.comp (Computable.snd.comp Computable.snd)
  have hs : Computable (fun z : X => z.2.1) :=
    Computable.fst.comp Computable.snd
  have hhit : Computable (fun z : X => z.2.2.2) :=
    Computable.snd.comp (Computable.snd.comp Computable.snd)
  have hsj : Computable (fun z : X => (z.2.1, z.2.2.1)) := hs.pair hj
  have hnone : Computable (fun z : X =>
      tolerantBisectionNoneStep approx a den z.1 (z.2.1, z.2.2.1)) :=
    (tolerantBisectionNoneStep_computable happrox ha hden).comp
      Computable.fst hsj
  have hsome : Computable₂ (fun (z : X) hit =>
      (z.2.2.1, some (2 * hit))) := by
    change Computable (fun w : X × ℕ => (w.1.2.2.1, some (2 * w.2)))
    have hj' : Computable (fun w : X × ℕ => w.1.2.2.1) :=
      hj.comp Computable.fst
    have htwo : Computable (fun w : X × ℕ => 2 * w.2) :=
      Primrec.nat_mul.to_comp.comp (Computable.const 2) Computable.snd
    exact hj'.pair (Computable.option_some.comp htwo)
  refine (Computable.option_casesOn hhit hnone hsome).of_eq ?_
  rintro ⟨ip, s, j, hit⟩
  cases hit <;> rfl

private theorem tolerantBisectionName_computable
    {approx : DyadicNumerator → ℕ → DyadicNumerator}
    {a : ℕ → ℕ → DyadicNumerator} {den : ℕ → ℕ}
    (happrox : Computable₂ approx) (ha : Computable₂ a)
    (hden : Computable den) :
    Computable₂ (tolerantBisectionName approx a den) := by
  let X := ℕ × ℕ
  have hp : Computable (fun z : X => z.2) := Computable.snd
  have hbase : Computable (fun _z : X =>
      ((0, none) : TolerantBisectionState)) := Computable.const (0, none)
  have hstep : Computable₂ (fun (z : X) ss =>
      tolerantBisectionStep approx a den z ss) :=
    tolerantBisectionStep_computable happrox ha hden
  have hstate : Computable (fun z : X =>
      tolerantBisectionState approx a den z.1 z.2) := by
    simpa only [tolerantBisectionState, tolerantBisectionStateAt] using
      Computable.nat_rec hp hbase hstep
  have hj : Computable (fun z : X =>
      (tolerantBisectionState approx a den z.1 z.2).1) :=
    Computable.fst.comp hstate
  have hhit : Computable (fun z : X =>
      (tolerantBisectionState approx a den z.1 z.2).2) :=
    Computable.snd.comp hstate
  have hnum : Computable (fun z : X =>
      (tolerantBisectionState approx a den z.1 z.2).2.getD
        (tolerantBisectionState approx a den z.1 z.2).1) :=
    Primrec.option_getD.to_comp.comp hhit hj
  exact (hnum.pair (Computable.const 0)).of_eq fun z => by
    rfl

/-- Tolerant bisection turns every computable dyadic name in the unit
interval into a computable dyadic name of its inverse image, with the same
requested output precision. -/
theorem tolerantBisection_correct
    {f g : ℝ → ℝ}
    (hdyadic : HasComputableDyadicApproximation f)
    (hmono : StrictMonoOn f (Icc (0 : ℝ) 1))
    (hfmap : MapsTo f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hgmap : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hinv : InvOn g f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (den : ℕ → ℕ) (hdenComp : Computable den)
    (hdenPos : ∀ p, 0 < den p)
    (hmod : ∀ p {u v : ℝ}, u ∈ Icc (0 : ℝ) 1 →
      v ∈ Icc (0 : ℝ) 1 → |u - v| < ((den p : ℝ))⁻¹ →
      |g u - g v| < ((2 : ℝ) ^ p)⁻¹)
    {x : ℕ → ℝ} (a : ℕ → ℕ → DyadicNumerator)
    (haComp : Computable₂ a)
    (haErr : ∀ i p, |x i - (a i p).value p| ≤ ((2 : ℝ) ^ p)⁻¹)
    (hx : ∀ i, x i ∈ Icc (0 : ℝ) 1) :
    ∃ b : ℕ → ℕ → DyadicNumerator, Computable₂ b ∧
      ∀ i p, |g (x i) - (b i p).value p| ≤ ((2 : ℝ) ^ p)⁻¹ := by
  refine ⟨tolerantBisectionName hdyadic.approx a den,
    tolerantBisectionName_computable hdyadic.computable haComp hdenComp, ?_⟩
  exact tolerantBisectionName_error hdyadic hmono hfmap hgmap hinv den
    hdenPos hmod a haErr hx

/-- A computably approximable strictly increasing bijection of the unit
interval has a sequentially computable inverse whenever a computable
reciprocal inverse modulus is supplied. -/
theorem effectiveInversionOn_Icc
    {f g : ℝ → ℝ}
    (hdyadic : HasComputableDyadicApproximation f)
    (hmono : StrictMonoOn f (Icc (0 : ℝ) 1))
    (hfmap : MapsTo f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hgmap : MapsTo g (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (hinv : InvOn g f (Icc (0 : ℝ) 1) (Icc (0 : ℝ) 1))
    (den : ℕ → ℕ) (hdenComp : Computable den)
    (hdenPos : ∀ p, 0 < den p)
    (hmod : ∀ p {u v : ℝ}, u ∈ Icc (0 : ℝ) 1 →
      v ∈ Icc (0 : ℝ) 1 → |u - v| < ((den p : ℝ))⁻¹ →
      |g u - g v| < ((2 : ℝ) ^ p)⁻¹) :
    SequentiallyComputableOn g (Icc (0 : ℝ) 1) := by
  intro x hxComp hx
  obtain ⟨a, haComp, haErr⟩ := hxComp
  exact tolerantBisection_correct hdyadic hmono hfmap hgmap hinv den hdenComp
    hdenPos hmod a haComp haErr hx

end Fabius
