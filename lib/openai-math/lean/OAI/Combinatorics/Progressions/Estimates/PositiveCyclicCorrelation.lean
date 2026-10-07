/- Modified for ProveIt: import Lean 4.32 compatibility declarations.
Statements and proofs are unchanged from the pinned upstream source. -/
import OAI.Compat.BigOperators
import OAI.Combinatorics.Progressions.Sampling.CyclicIntervalSampling

namespace OAI

section

open scoped BigOperators

namespace Erdos3

def intervalCutUpper (S : Finset ℕ) (N a : ℕ) : ℕ :=
  (insert N (S.filter (a < ·))).min' (Finset.insert_nonempty _ _)

theorem intervalCutUpper_le_end (S : Finset ℕ) (N a : ℕ) :
    intervalCutUpper S N a ≤ N :=
  Finset.min'_le _ _ (Finset.mem_insert_self _ _)

theorem intervalCutUpper_le_cut (S : Finset ℕ) (N : ℕ) {a b : ℕ}
    (hb : b ∈ S) (hab : a < b) : intervalCutUpper S N a ≤ b :=
  Finset.min'_le _ _ (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hb, hab⟩))

theorem le_intervalCutUpper (S : Finset ℕ) (N : ℕ) {a : ℕ} (ha : a ≤ N) :
    a ≤ intervalCutUpper S N a := by
  apply Finset.le_min'
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact ha
  · exact (Finset.mem_filter.mp hb).2.le

theorem lt_intervalCutUpper (S : Finset ℕ) (N : ℕ) {a : ℕ} (ha : a < N) :
    a < intervalCutUpper S N a := by
  apply (Finset.lt_min'_iff _ _).mpr
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact ha
  · exact (Finset.mem_filter.mp hb).2

theorem exists_intervalCut (S : Finset ℕ) (N : ℕ) (hzero : 0 ∈ S)
    {x : ℕ} (hx : x < N) :
    ∃ a ∈ S, a ≤ x ∧ x < intervalCutUpper S N a := by
  let A := S.filter (· ≤ x)
  have hA : A.Nonempty := ⟨0, Finset.mem_filter.mpr ⟨hzero, Nat.zero_le _⟩⟩
  let a := A.max' hA
  have ha := Finset.mem_filter.mp (Finset.max'_mem A hA)
  refine ⟨a, ha.1, ha.2, ?_⟩
  apply (Finset.lt_min'_iff _ _).mpr
  intro b hb
  rcases Finset.mem_insert.mp hb with rfl | hb
  · exact hx
  · obtain ⟨hbS, hab⟩ := Finset.mem_filter.mp hb
    by_contra hxb
    have hbA : b ∈ A := Finset.mem_filter.mpr ⟨hbS, by omega⟩
    have hba : b ≤ a := Finset.le_max' A b hbA
    omega

theorem intervalCut_unique (S : Finset ℕ) (N : ℕ) {a b x : ℕ}
    (ha : a ∈ S) (hb : b ∈ S)
    (hax : a ≤ x) (hxa : x < intervalCutUpper S N a)
    (hbx : b ≤ x) (hxb : x < intervalCutUpper S N b) : a = b := by
  rcases lt_trichotomy a b with hab | hab | hba
  · have hh := intervalCutUpper_le_cut S N hb hab
    omega
  · exact hab
  · have hh := intervalCutUpper_le_cut S N ha hba
    omega

def cyclicCutCell (S : Finset ℕ) (N a : ℕ) : Finset (ZMod N) :=
  cyclicInterval (a : ZMod N) (intervalCutUpper S N a - a)

theorem mem_cyclicCutCell {N : ℕ} [NeZero N] (S : Finset ℕ) {a : ℕ} (ha : a ≤ N)
    (x : ZMod N) : x ∈ cyclicCutCell S N a ↔ a ≤ x.val ∧ x.val < intervalCutUpper S N a :=
  mem_cyclicInterval_representatives a _ (le_intervalCutUpper S N ha)
    (intervalCutUpper_le_end S N a) x

theorem sum_cyclicCutCell_indicator {N : ℕ} [NeZero N] (S : Finset ℕ)
    (hzero : 0 ∈ S) (hbound : ∀ a ∈ S, a ≤ N) (x : ZMod N) :
    (∑ a : S, finiteIndicator (cyclicCutCell S N a) x) = 1 := by
  obtain ⟨a, ha, hax, hxa⟩ := exists_intervalCut S N hzero x.val_lt
  have hmem : x ∈ cyclicCutCell S N a := (mem_cyclicCutCell S (hbound a ha) x).mpr ⟨hax, hxa⟩
  rw [Finset.sum_eq_single (⟨a, ha⟩ : S)]
  · simp only [finiteIndicator, hmem, ite_true]
  · intro b _ hba
    have hnot : x ∉ cyclicCutCell S N b := by
      intro hx
      have hb := (mem_cyclicCutCell S (hbound b b.property) x).mp hx
      have he := intervalCut_unique S N b.property ha hb.1 hb.2 hax hxa
      exact hba (Subtype.ext he)
    simp only [finiteIndicator, hnot, ite_false]
  · simp

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def cubeRepresentativeSum {d N : ℕ} (k : Fin d → ZMod N) (ω : Fin d → Bool) : ℕ :=
  ∑ i, if ω i then (k i).val else 0

theorem cubeRepresentativeSum_intCast {d N : ℕ} (k : Fin d → ZMod N) (ω : Fin d → Bool) :
    (cubeRepresentativeSum k ω : ℤ) = cubeShift (fun i => ((k i).val : ℤ)) ω := by
  simp [cubeRepresentativeSum, cubeShift]

theorem cubeRepresentativeSum_zmodCast {d N : ℕ} [NeZero N] (k : Fin d → ZMod N) (ω : Fin d → Bool) :
    (cubeRepresentativeSum k ω : ZMod N) = cubeShift k ω := by
  simp [cubeRepresentativeSum, cubeShift]

theorem cubeRepresentativeSum_le {d N : ℕ} [NeZero N]
    (k : Fin d → ZMod N) (ω : Fin d → Bool) : cubeRepresentativeSum k ω ≤ d * N := by
  calc
    _ ≤ ∑ _i : Fin d, N := Finset.sum_le_sum (fun i _ => by
      split_ifs <;> [exact (k i).val_lt.le; exact Nat.zero_le _])
    _ = _ := by simp

def cubeCarryShift (d N : ℕ) (b : (Fin d → Bool) → Fin (d + 1)) : (Fin d → Bool) → ℤ :=
  fun ω => -((b ω).val : ℤ) * N

theorem exists_cube_carry_code {d N : ℕ} [NeZero N]
    (k : Fin d → ZMod N) {a : ℕ} (ha : a < N) :
    ∃ b : (Fin d → Bool) → Fin (d + 1), ∀ ω,
      cyclicTranslationOffset (cubeShift k ω) a =
        cubeShift (fun i => ((k i).val : ℤ)) ω + cubeCarryShift d N b ω := by
  let b (ω : Fin d → Bool) : Fin (d + 1) :=
    ⟨(a + cubeRepresentativeSum k ω) / N, (Nat.div_lt_iff_lt_mul (NeZero.pos N)).mpr (by
      have hs := cubeRepresentativeSum_le k ω
      nlinarith)⟩
  refine ⟨b, ?_⟩
  intro ω
  have ha' : (a : ZMod N).val = a := by simp [ZMod.val_natCast, Nat.mod_eq_of_lt ha]
  have hadd := cyclic_representative_add (cubeShift k ω) (a : ZMod N)
  rw [ha'] at hadd
  have hcast : ((a + cubeRepresentativeSum k ω : ℕ) : ZMod N) = cubeShift k ω + (a : ZMod N) := by
    rw [Nat.cast_add, cubeRepresentativeSum_zmodCast, add_comm]
  have hval := congrArg (fun x : ZMod N => (x.val : ℤ)) hcast
  rw [ZMod.val_natCast] at hval
  have hdiv := Nat.mod_add_div (a + cubeRepresentativeSum k ω) N
  have hdiv' := congrArg (fun x : ℕ => (x : ℤ)) hdiv
  simp only [Nat.cast_add, Nat.cast_mul] at hdiv'
  rw [hval, hadd] at hdiv'
  rw [← cubeRepresentativeSum_intCast]
  change (cubeShift k ω).val - (if N - (cubeShift k ω).val ≤ a then (N : ℤ) else 0) =
    (cubeRepresentativeSum k ω : ℤ) + -(((a + cubeRepresentativeSum k ω) / N : ℕ) : ℤ) * N
  nlinarith

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] {N : ℕ}

def commonCyclicCuts (h : ι → ZMod N) : Finset ℕ :=
  (Finset.univ.image (quarterLower N)) ∪ (Finset.univ.image (quarterUpper N)) ∪
    (Finset.univ.image (fun i => N - (h i).val))

theorem quarterLower_mem_commonCyclicCuts (h : ι → ZMod N) (i : Fin 4) :
    quarterLower N i ∈ commonCyclicCuts h := by
  simp only [commonCyclicCuts, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl ⟨i, rfl⟩)

theorem quarterUpper_mem_commonCyclicCuts (h : ι → ZMod N) (i : Fin 4) :
    quarterUpper N i ∈ commonCyclicCuts h := by
  simp only [commonCyclicCuts, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨i, rfl⟩)

theorem wrap_mem_commonCyclicCuts (h : ι → ZMod N) (i : ι) :
    N - (h i).val ∈ commonCyclicCuts h := by
  simp only [commonCyclicCuts, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
  exact Or.inr ⟨i, rfl⟩

theorem zero_mem_commonCyclicCuts (h : ι → ZMod N) : 0 ∈ commonCyclicCuts h := by
  simpa only [quarterLower, Fin.val_zero, zero_mul, Nat.zero_div] using
    quarterLower_mem_commonCyclicCuts h 0

theorem commonCyclicCuts_le (h : ι → ZMod N) {a : ℕ} (ha : a ∈ commonCyclicCuts h) : a ≤ N := by
  simp only [commonCyclicCuts, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and] at ha
  rcases ha with (⟨i, rfl⟩ | ⟨i, rfl⟩) | ⟨i, rfl⟩
  · exact (quarter_bounds N i).1.trans (quarter_bounds N i).2
  · exact (quarter_bounds N i).2
  · exact Nat.sub_le _ _

theorem commonCyclicCuts_card_le (h : ι → ZMod N) :
    (commonCyclicCuts h).card ≤ Fintype.card ι + 8 := by
  have hL := Finset.card_image_le (s := Finset.univ) (f := quarterLower N)
  have hU := Finset.card_image_le (s := Finset.univ) (f := quarterUpper N)
  have hW := Finset.card_image_le (s := Finset.univ) (f := fun i => N - (h i).val)
  have hLU := Finset.card_union_le (Finset.univ.image (quarterLower N)) (Finset.univ.image (quarterUpper N))
  have hAll := Finset.card_union_le
    ((Finset.univ.image (quarterLower N)) ∪ (Finset.univ.image (quarterUpper N)))
    (Finset.univ.image (fun i => N - (h i).val))
  simp only [Finset.card_univ, Fintype.card_fin] at hL hU hW
  unfold commonCyclicCuts
  omega

theorem exists_mem_cyclicQuarter [NeZero N] (x : ZMod N) : ∃ i, x ∈ cyclicQuarter N i := by
  by_contra hn
  push Not at hn
  have hz (i : Fin 4) : finiteIndicator (cyclicQuarter N i) x = 0 := by
    simp only [finiteIndicator, hn i, ite_false]
  have hs := sum_cyclicQuarter_indicator x
  simp only [hz, Finset.sum_const_zero] at hs
  norm_num at hs

theorem commonCyclicCut_short [NeZero N] (h : ι → ZMod N) {a : ℕ}
    (ha : a ∈ commonCyclicCuts h) :
    2 * (((intervalCutUpper (commonCyclicCuts h) N a - a : ℕ) : ℤ) - 1) < N ∧
    3 * (((intervalCutUpper (commonCyclicCuts h) N a - a : ℕ) : ℤ) - 1) < N := by
  have haN := commonCyclicCuts_le h ha
  have huN := intervalCutUpper_le_end (commonCyclicCuts h) N a
  by_cases he : a = N
  · have hN := NeZero.pos N
    constructor <;> omega
  · have haN' : a < N := by omega
    obtain ⟨i, hi⟩ := exists_mem_cyclicQuarter (a : ZMod N)
    rw [mem_cyclicQuarter, ZMod.val_natCast_of_lt haN'] at hi
    have hub := intervalCutUpper_le_cut (commonCyclicCuts h) N
      (quarterUpper_mem_commonCyclicCuts h i) hi.2
    have h2 := quarter_short N (NeZero.pos N) i
    have h3 := quarter_diameter_lt_third N (NeZero.pos N) i
    constructor <;> omega

theorem sum_commonCyclicCut_indicator [NeZero N] (h : ι → ZMod N) (x : ZMod N) :
    (∑ a : commonCyclicCuts h, finiteIndicator (cyclicCutCell (commonCyclicCuts h) N a) x) = 1 :=
  sum_cyclicCutCell_indicator _ (zero_mem_commonCyclicCuts h)
    (fun _ ha => commonCyclicCuts_le h ha) x

theorem commonCyclicCut_representative [NeZero N] (h : ι → ZMod N) {a : ℕ}
    (ha : a ∈ commonCyclicCuts h) (i : ι) {x : ZMod N}
    (hx : x ∈ cyclicCutCell (commonCyclicCuts h) N a) :
    (((h i + x).val : ℕ) : ℤ) = (x.val : ℤ) + cyclicTranslationOffset (h i) a := by
  have hxi := (mem_cyclicCutCell _ (commonCyclicCuts_le h ha) x).mp hx
  have hw : (N - (h i).val ≤ x.val) ↔ (N - (h i).val ≤ a) := by
    constructor
    · intro hwx
      by_contra hwa
      have hu := intervalCutUpper_le_cut (commonCyclicCuts h) N
        (wrap_mem_commonCyclicCuts h i) (by omega : a < N - (h i).val)
      omega
    · intro hwa
      omega
  rw [cyclic_representative_add, cyclicTranslationOffset]
  simp only [hw]
  ring

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

theorem exists_correlating_commonCyclicCut {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    (h : ι → ZMod N) (f u : ZMod N → ℂ) {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B) (hf : ∀ x, ‖f x‖ ≤ 1) (hu : ∀ x, ‖u x‖ ≤ B)
    (hc : ρ ≤ ‖finiteCorrelation Finset.univ f u‖) :
    ∃ a : commonCyclicCuts h, (cyclicCutCell (commonCyclicCuts h) N a).Nonempty ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8)) ≤
        ‖finiteCorrelation (cyclicCutCell (commonCyclicCuts h) N a) f u‖ ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8) * B) ≤
        ((cyclicCutCell (commonCyclicCuts h) N a).card : ℝ) / N := by
  have hsum (x : ZMod N) :
      (∑ a : commonCyclicCuts h, u x * finiteIndicator (cyclicCutCell (commonCyclicCuts h) N a) x) = u x := by
    rw [← Finset.mul_sum, sum_commonCyclicCut_indicator, mul_one]
  have hcard : (Fintype.card (commonCyclicCuts h) : ℝ) ≤ (Fintype.card ι : ℝ) + 8 := by
    rw [Fintype.card_coe]
    exact_mod_cast commonCyclicCuts_card_le h
  obtain ⟨a, ha⟩ := exists_correlating_summand Finset.univ_nonempty f u
    (fun a : commonCyclicCuts h => fun x => u x * finiteIndicator (cyclicCutCell (commonCyclicCuts h) N a) x)
    hρ (by positivity : (0 : ℝ) < (Fintype.card ι : ℝ) + 8) hcard (fun x _ => hf x)
    (fun x _ => by rw [hsum, sub_self, norm_zero]; positivity) hc
  have hh := retained_restricted_correlation (cyclicCutCell (commonCyclicCuts h) N a) f u
    (ρ := ρ / (2 * ((Fintype.card ι : ℝ) + 8))) (by positivity) hB
    (fun x _ => hf x) (fun x _ => hu x) ha
  refine ⟨a, hh.1, hh.2.1, ?_⟩
  simpa only [div_div, ZMod.card] using hh.2.2

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

variable {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]

noncomputable def translatedCyclicProduct (h : ι → ZMod N) (u : ι → ℤ → ℂ) (x : ZMod N) : ℂ :=
  ∏ i, u i ((h i + x).val : ℤ)

theorem translatedCyclicProduct_on_cut (h : ι → ZMod N) (u : ι → ℤ → ℂ) {a : ℕ}
    (ha : a ∈ commonCyclicCuts h) {x : ZMod N}
    (hx : x ∈ cyclicCutCell (commonCyclicCuts h) N a) :
    translatedCyclicProduct h u x = ∏ i, u i ((x.val : ℤ) + cyclicTranslationOffset (h i) a) := by
  unfold translatedCyclicProduct
  apply Finset.prod_congr rfl
  intro i _
  rw [commonCyclicCut_representative h ha i hx]

omit [NeZero N] in
theorem translatedCyclicProduct_norm_bound (h : ι → ZMod N) (u : ι → ℤ → ℂ)
    {p : ℝ} (hu : ∀ i x, ‖u i x‖ ≤ Real.exp p) (x : ZMod N) :
    ‖translatedCyclicProduct h u x‖ ≤ Real.exp ((Fintype.card ι : ℝ) * p) := by
  unfold translatedCyclicProduct
  rw [norm_prod]
  calc
    _ ≤ ∏ _i : ι, Real.exp p := Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hu i _)
    _ = _ := by rw [Finset.prod_const, Finset.card_univ, Real.exp_nat_mul]

theorem translatedCyclicProduct_cut_correlation (h : ι → ZMod N) (u : ι → ℤ → ℂ)
    (f : ZMod N → ℂ) {a : ℕ} (ha : a ∈ commonCyclicCuts h) :
    finiteCorrelation (cyclicCutCell (commonCyclicCuts h) N a) f (translatedCyclicProduct h u) =
      finiteCorrelation (Finset.Ico (a : ℤ) (a + (intervalCutUpper (commonCyclicCuts h) N a - a : ℕ)))
        (fun x => f (x : ZMod N)) (fun x => ∏ i, u i (x + cyclicTranslationOffset (h i) a)) := by
  have haN := commonCyclicCuts_le h ha
  have hupper := intervalCutUpper_le_end (commonCyclicCuts h) N a
  have hle := le_intervalCutUpper (commonCyclicCuts h) N haN
  calc
    _ = finiteCorrelation (cyclicCutCell (commonCyclicCuts h) N a) f
        (fun x => ∏ i, u i ((x.val : ℤ) + cyclicTranslationOffset (h i) a)) := by
      unfold finiteCorrelation
      apply Finset.expect_congr rfl
      intro x hx
      rw [translatedCyclicProduct_on_cut h u ha hx]
    _ = _ := cyclicInterval_representative_correlation (N := N) a
      (intervalCutUpper (commonCyclicCuts h) N a - a) (by omega)
      (commonCyclicCut_short h ha).1 f (fun x => ∏ i, u i (x + cyclicTranslationOffset (h i) a))

theorem exists_correlating_integer_product_interval (h : ι → ZMod N) (u : ι → ℤ → ℂ)
    (f : ZMod N → ℂ) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hu : ∀ x, ‖translatedCyclicProduct h u x‖ ≤ B)
    (hc : ρ ≤ ‖finiteCorrelation Finset.univ f (translatedCyclicProduct h u)‖) :
    ∃ a : commonCyclicCuts h,
      let len := intervalCutUpper (commonCyclicCuts h) N a - a
      0 < len ∧ a.val + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8)) ≤
        ‖finiteCorrelation (Finset.Ico (a.val : ℤ) (a.val + len)) (fun x => f (x : ZMod N))
          (fun x => ∏ i, u i (x + cyclicTranslationOffset (h i) a))‖ ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8) * B) ≤ (len : ℝ) / N := by
  obtain ⟨a, ha, hcorr, hvol⟩ := exists_correlating_commonCyclicCut h f
    (translatedCyclicProduct h u) hρ hB hf hu hc
  have huN := intervalCutUpper_le_end (commonCyclicCuts h) N a
  have hlen : intervalCutUpper (commonCyclicCuts h) N a - a.val ≤ N := by omega
  have hcard : (cyclicCutCell (commonCyclicCuts h) N a).card =
      intervalCutUpper (commonCyclicCuts h) N a - a.val := cyclicInterval_card _ hlen
  refine ⟨a, ?_, ?_, (commonCyclicCut_short h a.property).1, ?_, ?_⟩
  · rw [← hcard]
    exact ha.card_pos
  · have haN := commonCyclicCuts_le h a.property
    have hal := le_intervalCutUpper (commonCyclicCuts h) N haN
    omega
  · rwa [translatedCyclicProduct_cut_correlation h u f a.property] at hcorr
  · rwa [hcard] at hvol

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def integerCubeProductWithShift {d : ℕ} (R : ℤ → ℂ) (k : Fin d → ℤ)
    (c : (Fin d → Bool) → ℤ) (n : ℤ) : ℂ :=
  ∏ ω, conjugationPower (booleanWeight ω) (R (n + cubeShift k ω + c ω))

theorem exists_cyclic_cube_product_interval {d N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (R : ℤ → ℂ) (k : Fin d → ZMod N)
    {ρ : ℝ} (hρ : 0 < ρ) (hf : ∀ x, ‖f x‖ ≤ 1) (hR : ∀ n, ‖R n‖ ≤ 1)
    (hcorr : ρ ≤ ‖finiteCorrelation Finset.univ f (cubeProduct (fun n : ZMod N => R n.val) (List.ofFn k))‖) :
    ∃ (b : (Fin d → Bool) → Fin (d + 1)) (a len : ℕ),
      0 < len ∧ a + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      ρ / (2 * ((2 : ℝ) ^ d + 8)) ≤
        ‖finiteCorrelation (Finset.Ico (a : ℤ) (a + len)) (fun n => f (n : ZMod N))
          (integerCubeProductWithShift R (fun i => ((k i).val : ℤ)) (cubeCarryShift d N b))‖ ∧
      ρ / (2 * ((2 : ℝ) ^ d + 8)) ≤ (len : ℝ) / N := by
  classical
  let shifts (ω : Fin d → Bool) := cubeShift k ω
  let u (ω : Fin d → Bool) (n : ℤ) := conjugationPower (booleanWeight ω) (R n)
  have heval (n : ZMod N) : translatedCyclicProduct shifts u n =
      cubeProduct (fun n : ZMod N => R n.val) (List.ofFn k) n := by
    rw [cubeProduct_eq_boolean_product]
    unfold translatedCyclicProduct
    apply Finset.prod_congr rfl
    intro ω _
    simp only [shifts, u, add_comm]
  have hcap (n : ZMod N) : ‖translatedCyclicProduct shifts u n‖ ≤ 1 := by
    rw [heval]
    exact cubeProduct_norm_le_one _ (fun x => hR x.val) _ n
  have hc : ρ ≤ ‖finiteCorrelation Finset.univ f (translatedCyclicProduct shifts u)‖ := by
    simpa only [finiteCorrelation, heval] using hcorr
  obtain ⟨a, hlen, hend, hshort, hcor, hvol⟩ := exists_correlating_integer_product_interval
    shifts u f hρ (by norm_num : (0 : ℝ) < 1) hf hcap hc
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, Nat.cast_pow,
    Nat.cast_ofNat, mul_one] at hcor hvol
  let len := intervalCutUpper (commonCyclicCuts shifts) N a.val - a.val
  have haN : a.val < N := by omega
  obtain ⟨b, hb⟩ := exists_cube_carry_code k haN
  have hprod (n : ℤ) : (∏ ω, u ω (n + cyclicTranslationOffset (shifts ω) a.val)) =
      integerCubeProductWithShift R (fun i => ((k i).val : ℤ)) (cubeCarryShift d N b) n := by
    unfold integerCubeProductWithShift
    apply Finset.prod_congr rfl
    intro ω _
    simp only [u, shifts, hb, add_assoc]
  refine ⟨b, a.val, len, hlen, hend, hshort, ?_, hvol⟩
  simpa only [finiteCorrelation, hprod] using hcor

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

def doubleDifferenceCarryShift (N : ℕ) (b : Fin 3 → Fin 3) : Fin 4 → ℤ :=
  ![0, -(b 0).val * (N : ℤ), -(b 1).val * (N : ℤ), -(b 2).val * (N : ℤ)]

def integerDoubleDifferenceWithShift (R : ℤ → ℂ) (k l : ℤ) (c : Fin 4 → ℤ) (n : ℤ) : ℂ :=
  (R (n + c 0) * star (R (n + k + c 1))) *
    star (R (n + l + c 2) * star (R (n + k + l + c 3)))

theorem exists_double_difference_carry_code {N : ℕ} [NeZero N]
    (k l : ZMod N) (a : ℕ) :
    ∃ b : Fin 3 → Fin 3,
      cyclicTranslationOffset k a = k.val + doubleDifferenceCarryShift N b 1 ∧
      cyclicTranslationOffset l a = l.val + doubleDifferenceCarryShift N b 2 ∧
      cyclicTranslationOffset (k + l) a = k.val + l.val + doubleDifferenceCarryShift N b 3 := by
  classical
  let b : Fin 3 → Fin 3 :=
    ![if N - k.val ≤ a then 1 else 0,
      if N - l.val ≤ a then 1 else 0,
      if N - k.val ≤ l.val then (if N - (k + l).val ≤ a then 2 else 1)
        else (if N - (k + l).val ≤ a then 1 else 0)]
  refine ⟨b, ?_, ?_, ?_⟩
  · by_cases hk : N - k.val ≤ a <;>
      simp [cyclicTranslationOffset, doubleDifferenceCarryShift, b, hk, sub_eq_add_neg]
  · by_cases hl : N - l.val ≤ a <;>
      simp [cyclicTranslationOffset, doubleDifferenceCarryShift, b, hl, sub_eq_add_neg]
  · rw [cyclicTranslationOffset, cyclic_representative_add]
    by_cases hkl : N - k.val ≤ l.val <;> by_cases ha : N - (k + l).val ≤ a <;>
      simp [doubleDifferenceCarryShift, b, hkl, ha] <;> ring

theorem exists_cyclic_double_difference_interval {N : ℕ} [NeZero N]
    (f : ZMod N → ℂ) (R : ℤ → ℂ) (k l : ZMod N) {ρ : ℝ} (hρ : 0 < ρ)
    (hf : ∀ n, ‖f n‖ ≤ 1) (hR : ∀ n, ‖R n‖ ≤ 1)
    (hcorr : ρ ≤ ‖finiteCorrelation Finset.univ f
      (multiplicativeDerivative (multiplicativeDerivative (fun n : ZMod N => R n.val) k) l)‖) :
    ∃ (b : Fin 3 → Fin 3) (a len : ℕ), 0 < len ∧ a + len ≤ N ∧
      2 * ((len : ℤ) - 1) < N ∧
      ρ / 24 ≤ ‖𝔼 n ∈ Finset.Ico (a : ℤ) (a + len), f (n : ZMod N) *
        star (integerDoubleDifferenceWithShift R k.val l.val (doubleDifferenceCarryShift N b) n)‖ ∧
      ρ / 24 ≤ (len : ℝ) / N := by
  let shifts : Fin 4 → ZMod N := ![0, k, l, k + l]
  let u : Fin 4 → ℤ → ℂ := ![R, fun n => star (R n), fun n => star (R n), R]
  have heval (n : ZMod N) : translatedCyclicProduct shifts u n =
      multiplicativeDerivative (multiplicativeDerivative (fun n : ZMod N => R n.val) k) l n := by
    simp only [translatedCyclicProduct, shifts, u, Fin.prod_univ_four, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, zero_add,
      multiplicativeDerivative, star_mul, star_star]
    simp only [add_comm k n, add_comm l n, add_assoc, add_comm l k]
    ring_nf
  have hcap (n : ZMod N) : ‖translatedCyclicProduct shifts u n‖ ≤ 1 := by
    rw [heval]
    exact multiplicativeDerivative_norm_le_one _
      (multiplicativeDerivative_norm_le_one _ (fun x => hR x.val) k) l n
  have hc : ρ ≤ ‖finiteCorrelation Finset.univ f (translatedCyclicProduct shifts u)‖ := by
    simpa only [finiteCorrelation, heval] using hcorr
  obtain ⟨a, hlen, hend, hshort, hcor, hvol⟩ := exists_correlating_integer_product_interval
    shifts u f hρ (by norm_num : (0 : ℝ) < 1) hf hcap hc
  norm_num only [Fintype.card_fin, Nat.cast_ofNat, mul_one] at hcor hvol
  let len := intervalCutUpper (commonCyclicCuts shifts) N a.val - a.val
  have haN : a.val < N := by omega
  have hoff : cyclicTranslationOffset (0 : ZMod N) a.val = 0 := by
    simp [cyclicTranslationOffset, Nat.not_le.mpr haN]
  obtain ⟨b, hk, hl, hkl⟩ := exists_double_difference_carry_code k l a.val
  have hprod (n : ℤ) : (∏ i, u i (n + cyclicTranslationOffset (shifts i) a.val)) =
      integerDoubleDifferenceWithShift R k.val l.val (doubleDifferenceCarryShift N b) n := by
    simp only [Fin.prod_univ_four, shifts, u, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons, hoff, hk, hl, hkl,
      integerDoubleDifferenceWithShift, doubleDifferenceCarryShift, star_mul, star_star,
      add_zero, add_assoc]
    ring
  refine ⟨b, a.val, len, hlen, hend, hshort, ?_, hvol⟩
  simpa only [finiteCorrelation, hprod] using hcor

end Erdos3

end

section

open scoped BigOperators

namespace Erdos3

theorem re_finiteCorrelation_mul_indicator {H : Type*} [AddCommGroup H] [Fintype H]
    [DecidableEq H] (I : Finset H) (f u : H → ℂ) :
    (finiteCorrelation Finset.univ f (fun x => u x * finiteIndicator I x)).re =
      ((I.card : ℝ) / Fintype.card H) * (finiteCorrelation I f u).re := by
  rw [finiteCorrelation_mul_indicator]
  simp [Complex.mul_re]

theorem retained_restricted_correlation_re {H : Type*} [AddCommGroup H] [Fintype H]
    [DecidableEq H] (I : Finset H) (f u : H → ℂ)
    {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hf : ∀ x ∈ I, ‖f x‖ ≤ 1) (hu : ∀ x ∈ I, ‖u x‖ ≤ B)
    (hc : ρ ≤ (finiteCorrelation Finset.univ f (fun x => u x * finiteIndicator I x)).re) :
    I.Nonempty ∧ ρ ≤ (finiteCorrelation I f u).re ∧
      ρ / B ≤ (I.card : ℝ) / Fintype.card H := by
  obtain ⟨hI, _, hvol⟩ := retained_restricted_correlation I f u hρ hB hf hu
    (hc.trans (Complex.re_le_norm _))
  rw [re_finiteCorrelation_mul_indicator] at hc
  have hv0 : 0 ≤ (I.card : ℝ) / Fintype.card H := by positivity
  have hv1 : (I.card : ℝ) / Fintype.card H ≤ 1 := by
    apply (div_le_one (by exact_mod_cast Fintype.card_pos)).mpr
    exact_mod_cast Finset.card_le_univ I
  have hpos : 0 ≤ (finiteCorrelation I f u).re := by
    by_contra hn
    have hnonpos := mul_nonpos_of_nonneg_of_nonpos hv0 (le_of_not_ge hn)
    linarith
  refine ⟨hI, hc.trans ?_, hvol⟩
  exact (mul_le_mul_of_nonneg_right hv1 hpos).trans_eq (one_mul _)

theorem exists_re_correlating_commonCyclicCut {ι : Type*} [Fintype ι] {N : ℕ} [NeZero N]
    (h : ι → ZMod N) (f u : ZMod N → ℂ) {ρ B : ℝ}
    (hρ : 0 < ρ) (hB : 0 < B) (hf : ∀ x, ‖f x‖ ≤ 1) (hu : ∀ x, ‖u x‖ ≤ B)
    (hc : ρ ≤ (finiteCorrelation Finset.univ f u).re) :
    ∃ a : commonCyclicCuts h, (cyclicCutCell (commonCyclicCuts h) N a).Nonempty ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8)) ≤
        (finiteCorrelation (cyclicCutCell (commonCyclicCuts h) N a) f u).re ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8) * B) ≤
        ((cyclicCutCell (commonCyclicCuts h) N a).card : ℝ) / N := by
  classical
  let v (a : commonCyclicCuts h) (x : ZMod N) :=
    u x * finiteIndicator (cyclicCutCell (commonCyclicCuts h) N a) x
  have hsum : (fun x => ∑ a : commonCyclicCuts h, v a x) = u := by
    funext x
    change (∑ a : commonCyclicCuts h,
      u x * finiteIndicator (cyclicCutCell (commonCyclicCuts h) N a) x) = u x
    rw [← Finset.mul_sum, sum_commonCyclicCut_indicator, mul_one]
  have hcard : (Fintype.card (commonCyclicCuts h) : ℝ) ≤ (Fintype.card ι : ℝ) + 8 := by
    rw [Fintype.card_coe]
    exact_mod_cast commonCyclicCuts_card_le h
  have hsumre : ρ ≤ ∑ a : commonCyclicCuts h, (finiteCorrelation Finset.univ f (v a)).re := by
    rw [← Complex.re_sum, ← finiteCorrelation_sum_right, hsum]
    exact hc
  have hne : (Finset.univ : Finset (commonCyclicCuts h)).Nonempty :=
    ⟨⟨0, zero_mem_commonCyclicCuts h⟩, Finset.mem_univ _⟩
  have hconstants : (∑ _a : commonCyclicCuts h, ρ / (2 * ((Fintype.card ι : ℝ) + 8))) ≤ ρ := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc
      _ ≤ ((Fintype.card ι : ℝ) + 8) * (ρ / (2 * ((Fintype.card ι : ℝ) + 8))) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = ρ / 2 := by field_simp
      _ ≤ ρ := by linarith
  obtain ⟨a, _, ha⟩ := Finset.exists_le_of_sum_le hne (hconstants.trans hsumre)
  obtain ⟨hcell, hcor, hvol⟩ := retained_restricted_correlation_re
    (cyclicCutCell (commonCyclicCuts h) N a) f u
    (ρ := ρ / (2 * ((Fintype.card ι : ℝ) + 8))) (by positivity) hB
    (fun x _ => hf x) (fun x _ => hu x) ha
  refine ⟨a, hcell, hcor, ?_⟩
  simpa only [div_div, ZMod.card] using hvol

theorem exists_re_correlating_integer_product_interval {ι : Type*} [Fintype ι]
    {N : ℕ} [NeZero N] (h : ι → ZMod N) (u : ι → ℤ → ℂ)
    (f : ZMod N → ℂ) {ρ B : ℝ} (hρ : 0 < ρ) (hB : 0 < B)
    (hf : ∀ x, ‖f x‖ ≤ 1) (hu : ∀ x, ‖translatedCyclicProduct h u x‖ ≤ B)
    (hc : ρ ≤ (finiteCorrelation Finset.univ f (translatedCyclicProduct h u)).re) :
    ∃ a : commonCyclicCuts h,
      let len := intervalCutUpper (commonCyclicCuts h) N a - a
      0 < len ∧ a.val + len ≤ N ∧ 2 * ((len : ℤ) - 1) < N ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8)) ≤
        (finiteCorrelation (Finset.Ico (a.val : ℤ) (a.val + len)) (fun x => f (x : ZMod N))
          (fun x => ∏ i, u i (x + cyclicTranslationOffset (h i) a))).re ∧
      ρ / (2 * ((Fintype.card ι : ℝ) + 8) * B) ≤ (len : ℝ) / N := by
  obtain ⟨a, ha, hcorr, hvol⟩ := exists_re_correlating_commonCyclicCut h f
    (translatedCyclicProduct h u) hρ hB hf hu hc
  have huN := intervalCutUpper_le_end (commonCyclicCuts h) N a
  have hlen : intervalCutUpper (commonCyclicCuts h) N a - a.val ≤ N := by omega
  have hcard : (cyclicCutCell (commonCyclicCuts h) N a).card =
      intervalCutUpper (commonCyclicCuts h) N a - a.val := cyclicInterval_card _ hlen
  refine ⟨a, ?_, ?_, (commonCyclicCut_short h a.property).1, ?_, ?_⟩
  · rw [← hcard]
    exact ha.card_pos
  · have haN := commonCyclicCuts_le h a.property
    have hal := le_intervalCutUpper (commonCyclicCuts h) N haN
    omega
  · rwa [translatedCyclicProduct_cut_correlation h u f a.property] at hcorr
  · rwa [hcard] at hvol

end Erdos3

end

end OAI
