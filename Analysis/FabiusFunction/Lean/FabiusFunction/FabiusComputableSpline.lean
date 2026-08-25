import FabiusFunction.FabiusComputability
import FabiusFunction.ThueMorseBinomialLog

/-!
# A primitive-recursive Fabius evaluator

This module certifies a natural-number algorithm for the bounded Fabius
function.  It clamps a signed-natural dyadic numerator, evaluates a finite
centered Thue--Morse spline, and rounds half-up to the requested dyadic grid.
The evaluator is primitive recursive and has error at most
`5 * 2^(-(p+3))`; together with the global Lipschitz bound this proves
sequential computability and the combined computable-real-function theorem.
-/

namespace Fabius

set_option autoImplicit false

open scoped BigOperators
open Finset

private theorem nat_pow_primrec : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

/-! ## A primitive-recursive Thue--Morse bit -/

def tmBitPR : ℕ → ℕ
  | 0 => 0
  | n + 1 => (tmBitPR ((n + 1) / 2) + (n + 1) % 2) % 2
termination_by n => n
decreasing_by exact Nat.div_lt_self (by omega) (by omega)

@[simp] theorem tmBitPR_zero : tmBitPR 0 = 0 := by
  rw [tmBitPR]

theorem tmBitPR_of_pos (n : ℕ) (hn : 0 < n) :
    tmBitPR n = (tmBitPR (n / 2) + n % 2) % 2 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn.ne'
  rw [tmBitPR]

theorem tmBitPR_eq_thueMorseBit (n : ℕ) : tmBitPR n = thueMorseBit n := by
  unfold thueMorseBit
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn : n = 0
      · subst n
        simp [binaryWeight]
      · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
        have hdiv : n / 2 < n := Nat.div_lt_self hnpos (by omega)
        rw [tmBitPR_of_pos n hnpos]
        rcases Nat.mod_two_eq_zero_or_one n with hmod | hmod
        · have hrepr : n = 2 * (n / 2) := by
            have hd := Nat.div_add_mod n 2
            omega
          have hw : binaryWeight n = binaryWeight (n / 2) :=
            (congrArg binaryWeight hrepr).trans (binaryWeight_two_mul _)
          rw [hmod, add_zero, hw, ih _ hdiv]
          omega
        · have hrepr : n = 2 * (n / 2) + 1 := by
            have hd := Nat.div_add_mod n 2
            omega
          have hw : binaryWeight n = binaryWeight (n / 2) + 1 :=
            (congrArg binaryWeight hrepr).trans (binaryWeight_two_mul_add_one _)
          rw [hmod, hw, ih _ hdiv]
          rw [Nat.add_mod]
          norm_num

private def tmStep (_ : Unit) (l : List ℕ) : Option ℕ :=
  some ((((l[l.length / 2]?).getD 0) + l.length % 2) % 2)

private theorem tmStep_primrec : Primrec₂ tmStep := by
  apply Primrec.option_some.comp₂
  exact Primrec.nat_mod.comp₂
    (Primrec.nat_add.comp₂
      (Primrec.option_getD.comp₂
        (Primrec.list_getElem?.comp₂ Primrec₂.right
          (Primrec.nat_div.comp₂
            (Primrec.list_length.comp₂ Primrec₂.right)
            (Primrec.const 2).to₂))
        (Primrec.const 0).to₂)
      (Primrec.nat_mod.comp₂
        (Primrec.list_length.comp₂ Primrec₂.right)
        (Primrec.const 2).to₂))
    (Primrec.const 2).to₂

private theorem tmBitPR_primrec_aux :
    Primrec₂ (fun _ : Unit => tmBitPR) := by
  apply Primrec.nat_strong_rec (fun _ : Unit => tmBitPR) tmStep_primrec
  intro _ n
  unfold tmStep
  by_cases hn : n = 0
  · subst n
    simp
  · have hdiv : n / 2 < n :=
      Nat.div_lt_self (Nat.pos_of_ne_zero hn) (by omega)
    simp only [List.length_map, List.length_range, List.getElem?_map]
    rw [List.getElem?_range hdiv]
    simp [tmBitPR_of_pos n (Nat.pos_of_ne_zero hn)]

theorem tmBitPR_primrec : Primrec tmBitPR :=
  tmBitPR_primrec_aux.comp (Primrec.const ()) Primrec.id

/-! ## Signed-natural matched-grid spline -/

def splineTermPR (p a r : ℕ) : ℕ :=
  (2 * a - 2 * r - 1) ^ p

private theorem splineTermPR_primrec :
    Primrec₂ (fun pa : ℕ × ℕ => splineTermPR pa.1 pa.2) := by
  unfold splineTermPR
  exact nat_pow_primrec.comp₂
    (Primrec.nat_sub.comp₂
      (Primrec.nat_sub.comp₂
        (Primrec.nat_mul.comp₂ (Primrec.const 2).to₂
          (Primrec.snd.comp₂ Primrec₂.left))
        (Primrec.nat_mul.comp₂ (Primrec.const 2).to₂ Primrec₂.right))
      (Primrec.const 1).to₂)
    (Primrec.fst.comp₂ Primrec₂.left)

private def splineFoldStep (pa : ℕ × ℕ) (sr : (ℕ × ℕ) × ℕ) : ℕ × ℕ :=
  let t := splineTermPR pa.1 pa.2 sr.2
  let b := tmBitPR sr.2
  (sr.1.1 + (1 - b) * t, sr.1.2 + b * t)

private theorem splineFoldStep_primrec : Primrec₂ splineFoldStep := by
  let hr : Primrec₂ (fun (_ : ℕ × ℕ) (sr : (ℕ × ℕ) × ℕ) => sr.2) :=
    Primrec.snd.comp₂ Primrec₂.right
  let hpos : Primrec₂
      (fun (_ : ℕ × ℕ) (sr : (ℕ × ℕ) × ℕ) => sr.1.1) :=
    Primrec.fst.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
  let hneg : Primrec₂
      (fun (_ : ℕ × ℕ) (sr : (ℕ × ℕ) × ℕ) => sr.1.2) :=
    Primrec.snd.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
  let hb : Primrec₂
      (fun (_ : ℕ × ℕ) (sr : (ℕ × ℕ) × ℕ) => tmBitPR sr.2) :=
    tmBitPR_primrec.comp₂ hr
  let ht : Primrec₂
      (fun (pa : ℕ × ℕ) (sr : (ℕ × ℕ) × ℕ) =>
        splineTermPR pa.1 pa.2 sr.2) :=
    splineTermPR_primrec.comp₂ Primrec₂.left hr
  unfold splineFoldStep
  exact Primrec₂.pair.comp₂
    (Primrec.nat_add.comp₂ hpos
      (Primrec.nat_mul.comp₂
        (Primrec.nat_sub.comp₂ (Primrec.const 1).to₂ hb) ht))
    (Primrec.nat_add.comp₂ hneg (Primrec.nat_mul.comp₂ hb ht))

def splineSumsPR (p a : ℕ) : ℕ × ℕ :=
  (List.range a).foldl (fun s r => splineFoldStep (p, a) (s, r)) (0, 0)

theorem splineSumsPR_primrec : Primrec₂ splineSumsPR := by
  change Primrec (fun pa : ℕ × ℕ =>
    (List.range pa.2).foldl (fun s r => splineFoldStep pa (s, r)) (0, 0))
  exact Primrec.list_foldl
    (Primrec.list_range.comp Primrec.snd)
    (Primrec.const (0, 0))
    splineFoldStep_primrec

def splineDenPR : ℕ → ℕ
  | 0 => 1
  | p + 1 => splineDenPR p * 2 ^ (p + 1) * (p + 1)

private theorem splineDenStep_primrec :
    Primrec₂ (fun p d : ℕ => d * 2 ^ (p + 1) * (p + 1)) := by
  exact Primrec.nat_mul.comp₂
    (Primrec.nat_mul.comp₂ Primrec₂.right
      (nat_pow_primrec.comp₂ (Primrec.const 2).to₂
        (Primrec.succ.comp₂ Primrec₂.left)))
    (Primrec.succ.comp₂ Primrec₂.left)

theorem splineDenPR_primrec : Primrec splineDenPR := by
  exact (Primrec.nat_rec₁ 1 splineDenStep_primrec).of_eq fun n => by
    induction n with
    | zero => rfl
    | succ n ih => simp only [splineDenPR]; rw [ih]

theorem splineDenPR_eq (p : ℕ) :
    splineDenPR p = 2 ^ (p + 1).choose 2 * p.factorial := by
  induction p with
  | zero => simp [splineDenPR]
  | succ p ih =>
      rw [splineDenPR, ih, Nat.factorial_succ]
      rw [show (p + 1 + 1).choose 2 = (p + 1) + (p + 1).choose 2 by
        rw [show 2 = 1 + 1 by omega, Nat.choose_succ_succ]
        simp]
      rw [pow_add]
      ring

abbrev SignedRatCode := (ℕ × ℕ) × ℕ

def splineCodePR (p a : ℕ) : SignedRatCode :=
  (splineSumsPR p a, splineDenPR p)

theorem splineCodePR_primrec : Primrec₂ splineCodePR := by
  exact Primrec₂.pair.comp₂ splineSumsPR_primrec
    (splineDenPR_primrec.comp₂ Primrec₂.left)

theorem splineCodePR_computable : Computable₂ splineCodePR :=
  splineCodePR_primrec.to_comp

/-! ## Semantic identity -/

private lemma tmBitPR_eq_zero_or_one (n : ℕ) :
    tmBitPR n = 0 ∨ tmBitPR n = 1 := by
  rw [tmBitPR_eq_thueMorseBit]
  unfold thueMorseBit
  omega

private lemma splineFoldStep_diff (p a r : ℕ) (s : ℕ × ℕ) :
    ((splineFoldStep (p, a) (s, r)).1 : ℤ) -
        ((splineFoldStep (p, a) (s, r)).2 : ℤ) =
      ((s.1 : ℤ) - (s.2 : ℤ)) +
        thueMorseSign r * (splineTermPR p a r : ℤ) := by
  rcases tmBitPR_eq_zero_or_one r with hb | hb
  · have hsign : thueMorseSign r = 1 := by
      rw [thueMorseSign_eq_one_sub_two_mul_bit,
        ← tmBitPR_eq_thueMorseBit, hb]
      norm_num
    simp [splineFoldStep, hb, hsign]
    ring
  · have hsign : thueMorseSign r = -1 := by
      rw [thueMorseSign_eq_one_sub_two_mul_bit,
        ← tmBitPR_eq_thueMorseBit, hb]
      norm_num
    simp [splineFoldStep, hb, hsign]
    ring

private lemma splineFold_diff (p a : ℕ) (l : List ℕ) (s : ℕ × ℕ) :
    (((l.foldl (fun s r => splineFoldStep (p, a) (s, r)) s).1 : ℤ) -
      ((l.foldl (fun s r => splineFoldStep (p, a) (s, r)) s).2 : ℤ)) =
      ((s.1 : ℤ) - (s.2 : ℤ)) +
        (l.map (fun r =>
          thueMorseSign r * (splineTermPR p a r : ℤ))).sum := by
  induction l generalizing s with
  | nil => simp
  | cons r l ih =>
      rw [List.foldl_cons, ih, List.map_cons, List.sum_cons,
        splineFoldStep_diff]
      ring

theorem splineSumsPR_diff (p a : ℕ) :
    ((splineSumsPR p a).1 : ℤ) - ((splineSumsPR p a).2 : ℤ) =
      ∑ r ∈ Finset.range a,
        thueMorseSign r * (splineTermPR p a r : ℤ) := by
  rw [splineSumsPR, splineFold_diff]
  simp only [Int.natCast_zero, zero_sub, neg_zero, zero_add]
  rw [← List.sum_toFinset _ List.nodup_range, List.toFinset_range]

def rawSplineNumerator (p a : ℕ) : ℤ :=
  ∑ r ∈ Finset.range a,
    thueMorseSign r * (splineTermPR p a r : ℤ)

noncomputable def rawSplineValue (p a : ℕ) : ℝ :=
  (rawSplineNumerator p a : ℝ) /
    ((2 : ℝ) ^ (p + 1).choose 2 * (p.factorial : ℝ))

theorem rangeLength_matched (p a : ℕ) :
    fabiusDiscreteLimitRangeLength ((a : ℝ) / (2 : ℝ) ^ p) p = a := by
  unfold fabiusDiscreteLimitRangeLength
  have hscale : (2 : ℝ) ^ p * ((a : ℝ) / (2 : ℝ) ^ p) = a := by
    field_simp
  rw [hscale]
  apply (Nat.floor_eq_iff (by positivity)).2
  constructor <;> norm_num

private lemma splineTermPR_cast (p a r : ℕ) (hr : r < a) :
    (splineTermPR p a r : ℝ) =
      ((2 : ℝ) * a - 2 * r - 1) ^ p := by
  unfold splineTermPR
  have h₁ : 2 * r ≤ 2 * a := by omega
  have h₂ : 1 ≤ 2 * a - 2 * r := by omega
  rw [Nat.cast_pow, Nat.cast_sub h₂, Nat.cast_sub h₁]
  push_cast
  ring

private lemma matched_power (p a r : ℕ) (hr : r < a) :
    ((r : ℝ) - (2 : ℝ) ^ p * ((a : ℝ) / (2 : ℝ) ^ p) + 1 / 2) ^ p =
      ((-1 : ℝ) ^ p / (2 : ℝ) ^ p) * (splineTermPR p a r : ℝ) := by
  rw [show (2 : ℝ) ^ p * ((a : ℝ) / (2 : ℝ) ^ p) = a by field_simp,
    splineTermPR_cast p a r hr]
  have hbase : (r : ℝ) - a + 1 / 2 =
      (-1 : ℝ) / 2 * ((2 : ℝ) * a - 2 * r - 1) := by ring
  rw [hbase, mul_pow, div_pow]

theorem rawSplineValue_eq_uniformSpline (p a : ℕ) :
    rawSplineValue p a =
      fabiusUniformSpline p ((a : ℝ) / (2 : ℝ) ^ p) := by
  rw [fabiusUniformSpline, rangeLength_matched]
  have hnum : (rawSplineNumerator p a : ℝ) =
      ∑ r ∈ range a,
        (thueMorseSign r : ℝ) * (splineTermPR p a r : ℝ) := by
    unfold rawSplineNumerator
    push_cast
    rfl
  have hsum :
      (∑ r ∈ range a, (thueMorseSign r : ℝ) *
        ((r : ℝ) - (2 : ℝ) ^ p * ((a : ℝ) / (2 : ℝ) ^ p) + 1 / 2) ^ p) =
      ((-1 : ℝ) ^ p / (2 : ℝ) ^ p) * (rawSplineNumerator p a : ℝ) := by
    calc
      _ = ∑ r ∈ range a, ((-1 : ℝ) ^ p / (2 : ℝ) ^ p) *
          ((thueMorseSign r : ℝ) * (splineTermPR p a r : ℝ)) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [mem_range] at hr
        rw [matched_power p a r hr]
        ring
      _ = ((-1 : ℝ) ^ p / (2 : ℝ) ^ p) *
          ∑ r ∈ range a,
            ((thueMorseSign r : ℝ) * (splineTermPR p a r : ℝ)) := by
        rw [Finset.mul_sum]
      _ = _ := by rw [← hnum]
  rw [hsum]
  unfold rawSplineValue
  rw [show (p + 1).choose 2 = p.choose 2 + p by
    rw [show p + 1 = p.succ by omega, show 2 = 1 + 1 by omega,
      Nat.choose_succ_succ]
    simp [Nat.add_comm]]
  rw [pow_add]
  have hsign : (-1 : ℝ) ^ p * (-1 : ℝ) ^ p = 1 := by
    rw [← pow_add]
    exact (Even.add_self p).neg_one_pow
  field_simp
  ring_nf at hsign ⊢
  rw [hsign]
  ring

theorem splineCodePR_value (p a : ℕ) :
    (((splineCodePR p a).1.1 : ℝ) - ((splineCodePR p a).1.2 : ℝ)) /
        (splineCodePR p a).2 =
      fabiusUniformSpline p ((a : ℝ) / (2 : ℝ) ^ p) := by
  rw [splineCodePR, splineDenPR_eq]
  have hdiff := splineSumsPR_diff p a
  have hdiffR :
      ((splineSumsPR p a).1 : ℝ) - ((splineSumsPR p a).2 : ℝ) =
        (rawSplineNumerator p a : ℝ) := by
    exact_mod_cast hdiff
  rw [hdiffR]
  push_cast
  simpa only [rawSplineValue] using rawSplineValue_eq_uniformSpline p a

/-! ## Signed-pair fast-grid wrapper -/

private theorem natPowPrimrec : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) :=
  Primrec₂.unpaired'.1 Nat.Primrec.pow

private theorem addThreePrimrec : Primrec (fun p : ℕ => p + 3) :=
  Primrec.nat_add.comp Primrec.id (Primrec.const 3)

/-- Clamp the signed natural-pair numerator `c.1 - c.2` into `[0,2^s]`. -/
def clampDyadicNumeratorPR (c : DyadicNumerator) (s : ℕ) : ℕ :=
  if c.1 ≤ c.2 then 0 else min (c.1 - c.2) (2 ^ s)

theorem clampDyadicNumeratorPR_primrec : Primrec₂ clampDyadicNumeratorPR := by
  apply Primrec₂.mk
  exact Primrec.ite
    (Primrec.nat_le.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.snd.comp Primrec.fst))
    (Primrec.const 0)
    (Primrec.nat_min.comp
      (Primrec.nat_sub.comp (Primrec.fst.comp Primrec.fst)
        (Primrec.snd.comp Primrec.fst))
      (natPowPrimrec.comp (Primrec.const 2) Primrec.snd))

lemma clampDyadicNumeratorPR_le (c : DyadicNumerator) (s : ℕ) :
    clampDyadicNumeratorPR c s ≤ 2 ^ s := by
  unfold clampDyadicNumeratorPR
  split <;> simp

lemma clampDyadicNumeratorPR_ratio_mem_Icc (c : DyadicNumerator) (s : ℕ) :
    (clampDyadicNumeratorPR c s : ℝ) / (2 : ℝ) ^ s ∈ Set.Icc 0 1 := by
  constructor
  · positivity
  · rw [div_le_one (by positivity)]
    exact_mod_cast clampDyadicNumeratorPR_le c s

lemma fabiusReal_clampDyadicNumeratorPR
    (F : BoundedFabius) (hF : IsFabius F) (c : DyadicNumerator) (s : ℕ) :
    fabiusReal F ((clampDyadicNumeratorPR c s : ℝ) / (2 : ℝ) ^ s) =
      fabiusReal F (c.value s) := by
  by_cases hsign : c.1 ≤ c.2
  · have hvalue : c.value s ≤ 0 := by
      rw [DyadicNumerator.value]
      exact div_nonpos_of_nonpos_of_nonneg
        (sub_nonpos.mpr (by exact_mod_cast hsign)) (by positivity)
    rw [hF.zero_of_nonpos _ hvalue]
    simp [clampDyadicNumeratorPR, hsign, hF.zero_of_nonpos]
  · have hlt : c.2 < c.1 := Nat.lt_of_not_ge hsign
    by_cases hgrid : c.1 - c.2 ≤ 2 ^ s
    · rw [clampDyadicNumeratorPR, if_neg hsign, min_eq_left hgrid]
      congr 1
      rw [DyadicNumerator.value]
      rw [Nat.cast_sub hlt.le]
    · have hscale : 2 ^ s ≤ c.1 - c.2 := Nat.le_of_not_ge hgrid
      have hvalue : 1 ≤ c.value s := by
        rw [DyadicNumerator.value, one_le_div₀ (by positivity)]
        rw [← Nat.cast_sub hlt.le]
        exact_mod_cast hscale
      rw [hF.one_of_one_le _ hvalue]
      rw [clampDyadicNumeratorPR, if_neg hsign, min_eq_right hscale]
      have hratio : ((2 ^ s : ℕ) : ℝ) / (2 : ℝ) ^ s = 1 := by
        push_cast
        field_simp
      rw [hratio, hF.one_of_one_le _ le_rfl]

lemma splineSumsPR_second_le_first_of_matched
    (p a : ℕ) (hp : 0 < p) (ha : a ≤ 2 ^ p) :
    (splineSumsPR p a).2 ≤ (splineSumsPR p a).1 := by
  have hx : (a : ℝ) / (2 : ℝ) ^ p ∈ Set.Icc 0 1 := by
    constructor
    · positivity
    · rw [div_le_one (by positivity)]
      exact_mod_cast ha
  have hs := ProbabilityRepresentation.fabiusUniformSpline_mem_Icc p hp hx
  have hcode := splineCodePR_value p a
  rw [splineCodePR] at hcode
  have hden : (0 : ℝ) < splineDenPR p := by
    rw [splineDenPR_eq]
    positivity
  have hdiff : (0 : ℝ) ≤
      ((splineSumsPR p a).1 : ℝ) - (splineSumsPR p a).2 := by
    have := hs.1
    rw [← hcode] at this
    have hmul := mul_nonneg this hden.le
    rw [div_mul_cancel₀ _ hden.ne'] at hmul
    exact hmul
  exact_mod_cast (sub_nonneg.mp hdiff)

theorem matchedSplineNatRatio_eq_uniformSpline (p a : ℕ)
    (hp : 0 < p) (ha : a ≤ 2 ^ p) :
    (((splineSumsPR p a).1 - (splineSumsPR p a).2 : ℕ) : ℝ) /
        splineDenPR p =
      fabiusUniformSpline p ((a : ℝ) / (2 : ℝ) ^ p) := by
  have hle := splineSumsPR_second_le_first_of_matched p a hp ha
  have hcode := splineCodePR_value p a
  rw [splineCodePR] at hcode
  rw [Nat.cast_sub hle]
  exact hcode

/-- Half-up nearest-integer rounding of a nonnegative rational after scaling. -/
theorem nearestNatRatio_error (N D scale : ℕ) (hD : 0 < D) (hs : 0 < scale) :
    let q := (2 * (scale * N) + D) / (2 * D)
    |(q : ℝ) / scale - (N : ℝ) / D| ≤ 1 / (2 * (scale : ℝ)) := by
  dsimp
  let q := (2 * (scale * N) + D) / (2 * D)
  have hden : 0 < 2 * D := by omega
  have hloN : q * (2 * D) ≤ 2 * (scale * N) + D := by
    exact Nat.div_mul_le_self _ _
  have huN : 2 * (scale * N) + D < (2 * D) * (q + 1) := by
    exact Nat.lt_mul_div_succ _ hden
  have hloR : (q : ℝ) * (2 * D) ≤ 2 * (scale * N) + D := by
    exact_mod_cast hloN
  have huR : (2 : ℝ) * (scale * N) + D < (2 * D) * (q + 1) := by
    exact_mod_cast huN
  have hDR : (0 : ℝ) < D := by exact_mod_cast hD
  have hsR : (0 : ℝ) < scale := by exact_mod_cast hs
  rw [abs_le]
  constructor
  · field_simp
    nlinarith
  · field_simp
    nlinarith

/-- The matched-grid evaluator. At requested precision `p`, the input pair
is interpreted at exponent `p+3`; the result is returned at exponent `p`. -/
def fabiusSplineApproxPR (c : DyadicNumerator) (p : ℕ) : DyadicNumerator :=
  let s := p + 3
  let a := clampDyadicNumeratorPR c s
  let sums := splineSumsPR s a
  let numerator := sums.1 - sums.2
  let denominator := splineDenPR s
  ((2 * (2 ^ p * numerator) + denominator) / (2 * denominator), 0)

theorem fabiusSplineApproxPR_primrec : Primrec₂ fabiusSplineApproxPR := by
  let hs : Primrec₂ (fun (_ : DyadicNumerator) (p : ℕ) => p + 3) :=
    addThreePrimrec.comp₂ Primrec₂.right
  let ha : Primrec₂ (fun c p => clampDyadicNumeratorPR c (p + 3)) :=
    clampDyadicNumeratorPR_primrec.comp₂ Primrec₂.left hs
  let hsum : Primrec₂ (fun c p => splineSumsPR (p + 3)
      (clampDyadicNumeratorPR c (p + 3))) :=
    splineSumsPR_primrec.comp₂ hs ha
  let hnum : Primrec₂ (fun c p =>
      (splineSumsPR (p + 3) (clampDyadicNumeratorPR c (p + 3))).1 -
      (splineSumsPR (p + 3) (clampDyadicNumeratorPR c (p + 3))).2) :=
    Primrec.nat_sub.comp₂ (Primrec.fst.comp₂ hsum) (Primrec.snd.comp₂ hsum)
  let hden : Primrec₂ (fun (_ : DyadicNumerator) p => splineDenPR (p + 3)) :=
    splineDenPR_primrec.comp₂ hs
  let hpTwo : Primrec₂ (fun (_ : DyadicNumerator) p => 2 ^ p) :=
    natPowPrimrec.comp₂ (Primrec.const 2).to₂ Primrec₂.right
  apply Primrec₂.pair.comp₂
  · exact Primrec.nat_div.comp₂
      (Primrec.nat_add.comp₂
        (Primrec.nat_mul.comp₂ (Primrec.const 2).to₂
          (Primrec.nat_mul.comp₂ hpTwo hnum))
        hden)
      (Primrec.nat_mul.comp₂ (Primrec.const 2).to₂ hden)
  · exact (Primrec.const 0).to₂

theorem fabiusSplineApproxPR_computable : Computable₂ fabiusSplineApproxPR :=
  fabiusSplineApproxPR_primrec.to_comp

theorem fabiusSplineApproxPR_error
    (F : BoundedFabius) (hF : IsFabius F) (c : DyadicNumerator) (p : ℕ) :
    |fabiusReal F (c.value (p + 3)) -
        (fabiusSplineApproxPR c p).value p| ≤
      5 * ((2 : ℝ) ^ (p + 3))⁻¹ := by
  let s := p + 3
  let a := clampDyadicNumeratorPR c s
  let N := (splineSumsPR s a).1 - (splineSumsPR s a).2
  let D := splineDenPR s
  let Q := (2 * (2 ^ p * N) + D) / (2 * D)
  have hs : s = p + 3 := rfl
  have hspos : 0 < s := by omega
  have ha : a ≤ 2 ^ s := clampDyadicNumeratorPR_le c s
  have hq : (a : ℝ) / (2 : ℝ) ^ s ∈ Set.Icc 0 1 :=
    clampDyadicNumeratorPR_ratio_mem_Icc c s
  have hspline :
      |fabiusUniformSpline s ((a : ℝ) / (2 : ℝ) ^ s) -
          fabiusReal F ((a : ℝ) / (2 : ℝ) ^ s)| ≤
        ((2 : ℝ) ^ s)⁻¹ :=
    abs_fabiusUniformSpline_sub_fabiusReal_le F hF s hspos hq
  have hratio : (N : ℝ) / D =
      fabiusUniformSpline s ((a : ℝ) / (2 : ℝ) ^ s) := by
    exact matchedSplineNatRatio_eq_uniformSpline s a hspos ha
  have hD : 0 < D := by
    dsimp [D]
    rw [splineDenPR_eq]
    positivity
  have hround : |(Q : ℝ) / (2 : ℝ) ^ p - (N : ℝ) / D| ≤
      1 / (2 * ((2 : ℝ) ^ p)) := by
    simpa [Q] using nearestNatRatio_error N D (2 ^ p) hD (by positivity)
  have hclamp :
      fabiusReal F ((a : ℝ) / (2 : ℝ) ^ s) =
        fabiusReal F (c.value s) := by
    exact fabiusReal_clampDyadicNumeratorPR F hF c s
  have hout : (fabiusSplineApproxPR c p).value p =
      (Q : ℝ) / (2 : ℝ) ^ p := by
    simp [fabiusSplineApproxPR, Q, N, D, a, s, DyadicNumerator.value]
  rw [show p + 3 = s by rfl, hout, ← hclamp]
  calc
    |fabiusReal F ((a : ℝ) / (2 : ℝ) ^ s) -
        (Q : ℝ) / (2 : ℝ) ^ p| ≤
        |fabiusReal F ((a : ℝ) / (2 : ℝ) ^ s) -
          fabiusUniformSpline s ((a : ℝ) / (2 : ℝ) ^ s)| +
        |fabiusUniformSpline s ((a : ℝ) / (2 : ℝ) ^ s) -
          (Q : ℝ) / (2 : ℝ) ^ p| :=
      abs_sub_le _ _ _
    _ ≤ ((2 : ℝ) ^ s)⁻¹ + 1 / (2 * ((2 : ℝ) ^ p)) := by
      gcongr
      · simpa [abs_sub_comm] using hspline
      · rw [← hratio]
        simpa [abs_sub_comm] using hround
    _ ≤ 5 * ((2 : ℝ) ^ (p + 3))⁻¹ := by
      rw [hs, show p + 3 = ((p + 1) + 1) + 1 by omega,
        pow_succ, pow_succ, pow_succ]
      have hp : (2 : ℝ) ^ p ≠ 0 := by positivity
      field_simp
      norm_num

/-- The centered-spline evaluator packaged for the computability bridge. -/
def fabiusHasComputableDyadicApproximation
    (F : BoundedFabius) (hF : IsFabius F) :
    HasComputableDyadicApproximation (fabiusReal F) where
  approx := fabiusSplineApproxPR
  computable := fabiusSplineApproxPR_computable
  error := fabiusSplineApproxPR_error F hF

/-! ## Sequential computability and the combined result -/

/-- Every bounded/CDF Fabius solution preserves computable real sequences. -/
theorem fabiusReal_sequentiallyComputable
    (F : BoundedFabius) (hF : IsFabius F) :
    SequentiallyComputable (fabiusReal F) :=
  sequentiallyComputable_of_lipschitzWith_two_of_dyadicApproximation
    (fabiusReal_lipschitzWith_two F hF)
    (fabiusHasComputableDyadicApproximation F hF)

/-- Every bounded/CDF Fabius solution is computable in the
Wikipedia/Grzegorczyk sense. -/
theorem fabiusReal_isComputableRealFunction
    (F : BoundedFabius) (hF : IsFabius F) :
    IsComputableRealFunction (fabiusReal F) where
  sequentiallyComputable := fabiusReal_sequentiallyComputable F hF
  effectivelyUniformContinuous :=
    fabiusReal_effectivelyUniformContinuous F hF

/-- The canonical bounded/CDF Fabius function preserves computable real
sequences. -/
theorem fabius_sequentiallyComputable :
    SequentiallyComputable (fabiusReal fabius) :=
  fabiusReal_sequentiallyComputable fabius fabius_spec

/-- The canonical bounded/CDF Fabius function is computable in the
Wikipedia/Grzegorczyk sense. -/
theorem fabius_isComputableRealFunction :
    IsComputableRealFunction (fabiusReal fabius) :=
  fabiusReal_isComputableRealFunction fabius fabius_spec

end Fabius
