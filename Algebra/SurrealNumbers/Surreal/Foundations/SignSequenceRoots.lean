import Surreal.Foundations.SignSequenceProductCuts
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Square roots in the actual sign field

Every nonnegative sign number has a nonnegative square root, supplying
the square-root prerequisite of `found:sub:modulus`. The transition and
countable option closure follow the Bach--Conway construction formalized
by Karol Pąk, *Surreal Numbers: A
Study of Square Roots*, Formalized Mathematics 33 (2025), equations
(I.1)--(I.4), Definitions 2--5, and Theorems 7, 12--13:
https://mizar.uwb.edu.pl/fm/fm33/surreals.pdf.

Cross pairs of lower and upper square approximants create lower options;
same-side pairs create upper options. Zero denominators are excluded.
Finite products and a countable union preserve explicit lower-universe
smallness, so the resulting separated option families admit an actual cut.

Simplicity induction seeds the families with roots of nonnegative canonical
options. The arbitrary-presentation product-cut law and mutual prefix
simplicity identify the constructed cut's square with the input. This proof
is algebraic; no convergence of an approximation sequence is used.

The odd-degree polynomial root requirement for real closedness remains
separate. No `IsRealClosed` instance is introduced here.
-/

universe u

namespace Surreal.Foundations.SignSequence

noncomputable section

open Set

/-- The rational transition in the Bach--Conway square-root construction. -/
def squareRootTransition (x a b : SignSequence.{u}) : SignSequence.{u} :=
  (x + a * b) / (a + b)

/-- The sign of the new square error is determined by the old two errors. -/
theorem squareRootTransition_sq_sub (x a b : SignSequence.{u}) (hab : a + b ≠ 0) :
    squareRootTransition x a b ^ 2 - x =
      (x - a ^ 2) * (x - b ^ 2) / (a + b) ^ 2 := by
  unfold squareRootTransition
  field_simp
  ring

/-- Nonnegative inputs and a positive sum give a positive new approximant. -/
theorem squareRootTransition_pos {x a b : SignSequence.{u}}
    (hx : 0 < x) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : 0 < a + b) :
    0 < squareRootTransition x a b :=
  div_pos (add_pos_of_pos_of_nonneg hx (mul_nonneg ha hb)) hab

/-- Cross pairs stay strictly below the desired square. -/
theorem squareRootTransition_sq_lt {x a b : SignSequence.{u}}
    (ha : a ^ 2 < x) (hb : x < b ^ 2) (hab : a + b ≠ 0) :
    squareRootTransition x a b ^ 2 < x := by
  apply sub_neg.mp
  rw [squareRootTransition_sq_sub x a b hab]
  exact div_neg_of_neg_of_pos
    (mul_neg_of_pos_of_neg (sub_pos.mpr ha) (sub_neg.mpr hb))
    (sq_pos_of_ne_zero hab)

/-- Two lower approximants produce a strict upper square approximant. -/
theorem lt_squareRootTransition_sq_of_lower {x a b : SignSequence.{u}}
    (ha : a ^ 2 < x) (hb : b ^ 2 < x) (hab : a + b ≠ 0) :
    x < squareRootTransition x a b ^ 2 := by
  apply sub_pos.mp
  rw [squareRootTransition_sq_sub x a b hab]
  exact div_pos (mul_pos (sub_pos.mpr ha) (sub_pos.mpr hb)) (sq_pos_of_ne_zero hab)

/-- Two upper approximants also produce a strict upper square approximant. -/
theorem lt_squareRootTransition_sq_of_upper {x a b : SignSequence.{u}}
    (ha : x < a ^ 2) (hb : x < b ^ 2) (hab : a + b ≠ 0) :
    x < squareRootTransition x a b ^ 2 := by
  apply sub_pos.mp
  rw [squareRootTransition_sq_sub x a b hab]
  exact div_pos (mul_pos_of_neg_of_neg (sub_neg.mpr ha) (sub_neg.mpr hb))
    (sq_pos_of_ne_zero hab)

/-- All admissible transitions between two specified option sets. -/
def squareRootTransitions (x : SignSequence.{u}) (A B : Set SignSequence.{u}) :
    Set SignSequence.{u} :=
  {z | ∃ a ∈ A, ∃ b ∈ B, a + b ≠ 0 ∧ squareRootTransition x a b = z}

instance small_squareRootTransitions (x : SignSequence.{u})
    (A B : Set SignSequence.{u}) [Small.{u} A] [Small.{u} B] :
    Small.{u} (squareRootTransitions x A B) := by
  apply small_subset (s := Set.image2 (squareRootTransition x) A B)
  rintro z ⟨a, ha, b, hb, _, rfl⟩
  exact ⟨a, ha, b, hb, rfl⟩

/-- One stage retains old options and adds cross/same-side transitions. -/
def squareRootOptionStep (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) :
    Set SignSequence.{u} × Set SignSequence.{u} :=
  (p.1 ∪ squareRootTransitions x p.1 p.2,
    p.2 ∪ squareRootTransitions x p.1 p.1 ∪ squareRootTransitions x p.2 p.2)

/-- The finite stages of the internal option recursion. -/
def squareRootOptionStages (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) :
    ℕ → Set SignSequence.{u} × Set SignSequence.{u}
  | 0 => p
  | n + 1 => squareRootOptionStep x (squareRootOptionStages x p n)

/-- The final option sets use only a countable union of finite stages. -/
def squareRootOptions (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) :
    Set SignSequence.{u} × Set SignSequence.{u} :=
  (⋃ n, (squareRootOptionStages x p n).1, ⋃ n, (squareRootOptionStages x p n).2)

/-- The square inequalities maintained by both option families. -/
def IsSquareRootBracket (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) : Prop :=
  (∀ a ∈ p.1, 0 ≤ a ∧ a ^ 2 < x) ∧ (∀ b ∈ p.2, 0 < b ∧ x < b ^ 2)

/-- Every stage preserves the strict square bracket; denominator guards
are essential for same-side lower pairs containing zero. -/
theorem IsSquareRootBracket.step {x : SignSequence.{u}}
    {p : Set SignSequence.{u} × Set SignSequence.{u}}
    (h : IsSquareRootBracket x p) (hx : 0 < x) :
    IsSquareRootBracket x (squareRootOptionStep x p) := by
  constructor
  · rintro z (hz | ⟨a, ha, b, hb, hab, rfl⟩)
    · exact h.1 z hz
    · obtain ⟨ha₀, ha₂⟩ := h.1 a ha
      obtain ⟨hb₀, hb₂⟩ := h.2 b hb
      exact ⟨(squareRootTransition_pos hx ha₀ hb₀.le
        (add_pos_of_nonneg_of_pos ha₀ hb₀)).le, squareRootTransition_sq_lt ha₂ hb₂ hab⟩
  · rintro z ((hz | ⟨a, ha, b, hb, hab, rfl⟩) | ⟨a, ha, b, hb, hab, rfl⟩)
    · exact h.2 z hz
    · obtain ⟨ha₀, ha₂⟩ := h.1 a ha
      obtain ⟨hb₀, hb₂⟩ := h.1 b hb
      exact ⟨squareRootTransition_pos hx ha₀ hb₀
        (lt_of_le_of_ne (add_nonneg ha₀ hb₀) hab.symm),
        lt_squareRootTransition_sq_of_lower ha₂ hb₂ hab⟩
    · obtain ⟨ha₀, ha₂⟩ := h.2 a ha
      obtain ⟨hb₀, hb₂⟩ := h.2 b hb
      exact ⟨squareRootTransition_pos hx ha₀.le hb₀.le (add_pos ha₀ hb₀),
        lt_squareRootTransition_sq_of_upper ha₂ hb₂ hab⟩

theorem IsSquareRootBracket.stages {x : SignSequence.{u}}
    {p : Set SignSequence.{u} × Set SignSequence.{u}}
    (h : IsSquareRootBracket x p) (hx : 0 < x) (n : ℕ) :
    IsSquareRootBracket x (squareRootOptionStages x p n) := by
  induction n with
  | zero => exact h
  | succ n ih => exact ih.step hx

/-- The countable option closure still consists of nonnegative strict
lower approximants and positive strict upper approximants. -/
theorem IsSquareRootBracket.options {x : SignSequence.{u}}
    {p : Set SignSequence.{u} × Set SignSequence.{u}}
    (h : IsSquareRootBracket x p) (hx : 0 < x) :
    IsSquareRootBracket x (squareRootOptions x p) := by
  constructor
  · intro a ha
    obtain ⟨n, hn⟩ := mem_iUnion.mp ha
    exact (h.stages hx n).1 a hn
  · intro b hb
    obtain ⟨n, hn⟩ := mem_iUnion.mp hb
    exact (h.stages hx n).2 b hn

/-- Strict square bracketing gives the numerical separation needed by
the actual small-cut constructor. -/
theorem IsSquareRootBracket.separated {x : SignSequence.{u}}
    {p : Set SignSequence.{u} × Set SignSequence.{u}}
    (h : IsSquareRootBracket x p) {a b : SignSequence.{u}}
    (ha : a ∈ p.1) (hb : b ∈ p.2) : a < b :=
  (sq_lt_sq₀ (h.1 a ha).1 (h.2 b hb).1.le).mp ((h.1 a ha).2.trans (h.2 b hb).2)

/-- Both option families increase at each internal stage. -/
theorem squareRootOptionStages_monotone (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) :
    Monotone (squareRootOptionStages x p) := by
  apply monotone_nat_of_le_succ
  intro n
  exact ⟨fun _ h => Or.inl h, fun _ h => Or.inl (Or.inl h)⟩

theorem squareRootOptionStage_subset_left (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) (n : ℕ) :
    (squareRootOptionStages x p n).1 ⊆ (squareRootOptions x p).1 :=
  subset_iUnion (fun n => (squareRootOptionStages x p n).1) n

theorem squareRootOptionStage_subset_right (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) (n : ℕ) :
    (squareRootOptionStages x p n).2 ⊆ (squareRootOptions x p).2 :=
  subset_iUnion (fun n => (squareRootOptionStages x p n).2) n

/-- The countable union is closed under cross-pair transitions. -/
theorem squareRootOptions_cross {x a b : SignSequence.{u}}
    {p : Set SignSequence.{u} × Set SignSequence.{u}}
    (ha : a ∈ (squareRootOptions x p).1) (hb : b ∈ (squareRootOptions x p).2)
    (hab : a + b ≠ 0) : squareRootTransition x a b ∈ (squareRootOptions x p).1 := by
  obtain ⟨n, hn⟩ := mem_iUnion.mp ha
  obtain ⟨m, hm⟩ := mem_iUnion.mp hb
  apply squareRootOptionStage_subset_left x p (max n m + 1)
  exact Or.inr ⟨a, (squareRootOptionStages_monotone x p (le_max_left n m)).1 hn,
    b, (squareRootOptionStages_monotone x p (le_max_right n m)).2 hm, hab, rfl⟩

/-- Same-side lower pairs give upper options, provided their sum is nonzero. -/
theorem squareRootOptions_lower {x a b : SignSequence.{u}}
    {p : Set SignSequence.{u} × Set SignSequence.{u}}
    (ha : a ∈ (squareRootOptions x p).1) (hb : b ∈ (squareRootOptions x p).1)
    (hab : a + b ≠ 0) : squareRootTransition x a b ∈ (squareRootOptions x p).2 := by
  obtain ⟨n, hn⟩ := mem_iUnion.mp ha
  obtain ⟨m, hm⟩ := mem_iUnion.mp hb
  apply squareRootOptionStage_subset_right x p (max n m + 1)
  exact Or.inl (Or.inr ⟨a, (squareRootOptionStages_monotone x p (le_max_left n m)).1 hn,
    b, (squareRootOptionStages_monotone x p (le_max_right n m)).1 hm, hab, rfl⟩)

/-- Same-side upper pairs also give upper options. -/
theorem squareRootOptions_upper {x a b : SignSequence.{u}}
    {p : Set SignSequence.{u} × Set SignSequence.{u}}
    (ha : a ∈ (squareRootOptions x p).2) (hb : b ∈ (squareRootOptions x p).2)
    (hab : a + b ≠ 0) : squareRootTransition x a b ∈ (squareRootOptions x p).2 := by
  obtain ⟨n, hn⟩ := mem_iUnion.mp ha
  obtain ⟨m, hm⟩ := mem_iUnion.mp hb
  apply squareRootOptionStage_subset_right x p (max n m + 1)
  exact Or.inr ⟨a, (squareRootOptionStages_monotone x p (le_max_left n m)).2 hn,
    b, (squareRootOptionStages_monotone x p (le_max_right n m)).2 hm, hab, rfl⟩

/-- Every finite option stage is permitted-small when the seeds are. -/
theorem small_squareRootOptionStages (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) [Small.{u} p.1] [Small.{u} p.2]
    (n : ℕ) : Small.{u} (squareRootOptionStages x p n).1 ∧
      Small.{u} (squareRootOptionStages x p n).2 := by
  induction n with
  | zero =>
    change Small.{u} p.1 ∧ Small.{u} p.2
    exact ⟨inferInstance, inferInstance⟩
  | succ n ih =>
    letI := ih.1
    letI := ih.2
    constructor <;> dsimp only [squareRootOptionStages, squareRootOptionStep] <;> infer_instance

instance small_squareRootOptionStages_left (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) [Small.{u} p.1] [Small.{u} p.2]
    (n : ℕ) : Small.{u} (squareRootOptionStages x p n).1 :=
  (small_squareRootOptionStages x p n).1

instance small_squareRootOptionStages_right (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) [Small.{u} p.1] [Small.{u} p.2]
    (n : ℕ) : Small.{u} (squareRootOptionStages x p n).2 :=
  (small_squareRootOptionStages x p n).2

/-- Countably many small stages still form a permitted-small left family. -/
instance small_squareRootOptions_left (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) [Small.{u} p.1] [Small.{u} p.2] :
    Small.{u} (squareRootOptions x p).1 := by
  change Small.{u} (⋃ n, (squareRootOptionStages x p n).1)
  infer_instance

/-- Countably many small stages still form a permitted-small right family. -/
instance small_squareRootOptions_right (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) [Small.{u} p.1] [Small.{u} p.2] :
    Small.{u} (squareRootOptions x p).2 := by
  change Small.{u} (⋃ n, (squareRootOptionStages x p n).2)
  infer_instance

/-- The algebraic closure gives legal cut data in the original birthday
universe. The root proof below chooses canonical-option seeds to identify
the resulting square with `x`. -/
def squareRootOptionCut (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) [Small.{u} p.1] [Small.{u} p.2]
    (hx : 0 < x) (hp : IsSquareRootBracket x p) :
    SmallCutData.{u, u + 1} SignSequence.{u} (· < ·) :=
  SmallCutData.ofSmallSets (squareRootOptions x p).1 (squareRootOptions x p).2
    (fun _ ha _ hb => (hp.options hx).separated ha hb)

/-- The separator condition remains the original two set-indexed bounds. -/
theorem squareRootOptionCut_realizes_iff (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) [Small.{u} p.1] [Small.{u} p.2]
    (hx : 0 < x) (hp : IsSquareRootBracket x p) (y : SignSequence.{u}) :
    (squareRootOptionCut x p hx hp).IsRealizedBy y ↔
      (∀ a ∈ (squareRootOptions x p).1, a < y) ∧
        (∀ b ∈ (squareRootOptions x p).2, y < b) :=
  SmallCutData.ofSmallSets_isRealizedBy_iff _ _ _ _

/-- The constructed cut strictly separates every generated approximant. -/
theorem squareRootOptionCut_bounds (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) [Small.{u} p.1] [Small.{u} p.2]
    (hx : 0 < x) (hp : IsSquareRootBracket x p) :
    (∀ a ∈ (squareRootOptions x p).1, a < cut (squareRootOptionCut x p hx hp)) ∧
      (∀ b ∈ (squareRootOptions x p).2, cut (squareRootOptionCut x p hx hp) < b) :=
  (squareRootOptionCut_realizes_iff x p hx hp _).mp (cut_realizes _)

private theorem mulOption_lt_of_lt_squareRootTransition {x y a b : SignSequence.{u}}
    (hab : 0 < a + b) (h : y < squareRootTransition x a b) :
    mulOption y y a b < x := by
  have hmul := (lt_div_iff₀ hab).mp h
  dsimp only [mulOption]
  nlinarith

private theorem lt_mulOption_of_squareRootTransition_lt {x y a b : SignSequence.{u}}
    (hab : 0 < a + b) (h : squareRootTransition x a b < y) :
    x < mulOption y y a b := by
  have hmul := (div_lt_iff₀ hab).mp h
  dsimp only [mulOption]
  nlinarith

/-- Closure under the three algebraic transition families makes `x` a
separator of the candidate root's product cut. This uses no root hypothesis. -/
theorem squareRootOptionCut_product_realized (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) [Small.{u} p.1] [Small.{u} p.2]
    (hx : 0 < x) (hp : IsSquareRootBracket x p) :
    (productCut (squareRootOptionCut x p hx hp)
      (squareRootOptionCut x p hx hp)).IsRealizedBy x := by
  let c := squareRootOptionCut x p hx hp
  have hl : ∀ i : c.Left, c.left i ∈ (squareRootOptions x p).1 :=
    fun i => ((equivShrink (squareRootOptions x p).1).symm i).property
  have hr : ∀ i : c.Right, c.right i ∈ (squareRootOptions x p).2 :=
    fun i => ((equivShrink (squareRootOptions x p).2).symm i).property
  have hb := squareRootOptionCut_bounds x p hx hp
  have hs := hp.options hx
  apply (productCut_realizes_iff c c x).mpr
  constructor
  · constructor
    · intro i j
      have hi := (hs.1 _ (hl i)).1
      have hj := (hs.1 _ (hl j)).1
      by_cases hij : c.left i + c.left j = 0
      · have hi₀ : c.left i = 0 := by linarith
        have hj₀ : c.left j = 0 := by linarith
        simpa only [mulOption, hi₀, hj₀, zero_mul, mul_zero, add_zero, sub_zero] using hx
      · exact mulOption_lt_of_lt_squareRootTransition
          (lt_of_le_of_ne (add_nonneg hi hj) (Ne.symm hij))
          (hb.2 _ (squareRootOptions_lower (hl i) (hl j) hij))
    · intro i j
      have hij := add_pos (hs.2 _ (hr i)).1 (hs.2 _ (hr j)).1
      exact mulOption_lt_of_lt_squareRootTransition hij
        (hb.2 _ (squareRootOptions_upper (hr i) (hr j) hij.ne'))
  · constructor
    · intro i j
      have hij := add_pos_of_nonneg_of_pos (hs.1 _ (hl i)).1 (hs.2 _ (hr j)).1
      exact lt_mulOption_of_squareRootTransition_lt hij
        (hb.1 _ (squareRootOptions_cross (hl i) (hr j) hij.ne'))
    · intro i j
      have hji := add_pos_of_nonneg_of_pos (hs.1 _ (hl j)).1 (hs.2 _ (hr i)).1
      have h := lt_mulOption_of_squareRootTransition_lt hji
        (hb.1 _ (squareRootOptions_cross (hl j) (hr i) hji.ne'))
      dsimp only [mulOption] at h ⊢
      nlinarith

/-- Without imposing any seed coverage, the square of the constructed
cut is already a sign prefix of the input. -/
theorem squareRootOptionCut_sq_isPrefix (x : SignSequence.{u})
    (p : Set SignSequence.{u} × Set SignSequence.{u}) [Small.{u} p.1] [Small.{u} p.2]
    (hx : 0 < x) (hp : IsSquareRootBracket x p) :
    IsPrefix (cut (squareRootOptionCut x p hx hp) ^ 2) x := by
  simpa only [pow_two] using productCut_isPrefix_of_realizes _ _ x
    (squareRootOptionCut_product_realized x p hx hp)

/-- Every nonnegative element of the actual sign field has a nonnegative
square root. Simplicity induction supplies roots of smaller canonical
options, while the internal countable closure remains permitted-small. -/
theorem exists_nonneg_sq (x : SignSequence.{u}) :
    0 ≤ x → ∃ y : SignSequence.{u}, 0 ≤ y ∧ y ^ 2 = x := by
  induction x using simpler_wellFounded.induction with
  | h x ih =>
    intro hx
    rcases hx.eq_or_lt with hx | hx
    · subst x
      exact ⟨0, le_rfl, by simp⟩
    let L := {i : LeftIndex x // 0 ≤ leftOption x i}
    have hL (i : L) : ∃ y : SignSequence.{u}, 0 ≤ y ∧ y ^ 2 = leftOption x i.val :=
      ih _ (leftOption_simpler x i.val) i.property
    have hR (i : RightIndex x) :
        ∃ y : SignSequence.{u}, 0 ≤ y ∧ y ^ 2 = rightOption x i :=
      ih _ (rightOption_simpler x i) (hx.trans (lt_rightOption x i)).le
    let l : L → SignSequence.{u} := fun i => (hL i).choose
    let r : RightIndex x → SignSequence.{u} := fun i => (hR i).choose
    have hl (i : L) : 0 ≤ l i ∧ l i ^ 2 = leftOption x i.val := (hL i).choose_spec
    have hr (i : RightIndex x) : 0 ≤ r i ∧ r i ^ 2 = rightOption x i := (hR i).choose_spec
    let p : Set SignSequence.{u} × Set SignSequence.{u} := ({0} ∪ Set.range l, Set.range r)
    haveI : Small.{u} p.1 := by
      change Small.{u} ({0} ∪ Set.range l : Set SignSequence.{u})
      infer_instance
    haveI : Small.{u} p.2 := by
      change Small.{u} (Set.range r)
      infer_instance
    have hp : IsSquareRootBracket x p := by
      constructor
      · rintro a (ha | ⟨i, rfl⟩)
        · obtain rfl := Set.mem_singleton_iff.mp ha
          exact ⟨le_rfl, by simpa only [zero_pow (by decide : 2 ≠ 0)] using hx⟩
        · exact ⟨(hl i).1, (hl i).2.trans_lt (leftOption_lt x i.val)⟩
      · rintro b ⟨i, rfl⟩
        have hs : x < r i ^ 2 := (lt_rightOption x i).trans_eq (hr i).2.symm
        refine ⟨lt_of_le_of_ne (hr i).1 ?_, hs⟩
        intro hzero
        rw [← hzero, zero_pow (by decide : 2 ≠ 0)] at hs
        exact (hx.trans hs).false
    let c := squareRootOptionCut x p hx hp
    have hb := squareRootOptionCut_bounds x p hx hp
    have hy : 0 < cut c := hb.1 0
      (squareRootOptionStage_subset_left x p 0 (Or.inl (Set.mem_singleton 0)))
    refine ⟨cut c, hy.le, IsPrefix.antisymm (squareRootOptionCut_sq_isPrefix x p hx hp) ?_⟩
    apply isPrefix_of_separates_options x (cut c ^ 2)
    · intro i
      by_cases hi : 0 ≤ leftOption x i
      · let j : L := ⟨i, hi⟩
        have hly : l j < cut c := hb.1 _
          (squareRootOptionStage_subset_left x p 0 (Or.inr (Set.mem_range_self j)))
        exact (hl j).2.symm.trans_lt ((sq_lt_sq₀ (hl j).1 hy.le).mpr hly)
      · exact (lt_of_not_ge hi).trans_le (sq_nonneg _)
    · intro i
      have hyr : cut c < r i := hb.2 _
        (squareRootOptionStage_subset_right x p 0 (Set.mem_range_self i))
      exact ((sq_lt_sq₀ hy.le (hr i).1).mpr hyr).trans_eq (hr i).2

/-- The nonnegative root is unique in the numerical order. -/
theorem existsUnique_nonneg_sq (x : SignSequence.{u}) (hx : 0 ≤ x) :
    ∃! y : SignSequence.{u}, 0 ≤ y ∧ y ^ 2 = x := by
  obtain ⟨y, hy, hy₂⟩ := exists_nonneg_sq x hx
  exact ⟨y, ⟨hy, hy₂⟩, fun z hz => (sq_eq_sq₀ hz.1 hy).mp (hz.2.trans hy₂.symm)⟩

/-- The nonnegative square root, with value zero on negative inputs.
The value is chosen from the root-existence theorem, not postulated. -/
def sqrt (x : SignSequence.{u}) : SignSequence.{u} :=
  if hx : 0 ≤ x then (exists_nonneg_sq x hx).choose else 0

theorem sqrt_nonneg (x : SignSequence.{u}) : 0 ≤ sqrt x := by
  by_cases hx : 0 ≤ x
  · rw [sqrt, dif_pos hx]
    exact (exists_nonneg_sq x hx).choose_spec.1
  · rw [sqrt, dif_neg hx]

@[simp] theorem sqrt_sq {x : SignSequence.{u}} (hx : 0 ≤ x) : sqrt x ^ 2 = x := by
  rw [sqrt, dif_pos hx]
  exact (exists_nonneg_sq x hx).choose_spec.2

/-- Any nonnegative square root agrees with the constructed one. -/
theorem sqrt_eq_of_nonneg_sq {x y : SignSequence.{u}} (hy : 0 ≤ y) (hy₂ : y ^ 2 = x) :
    sqrt x = y :=
  (sq_eq_sq₀ (sqrt_nonneg x) hy).mp ((sqrt_sq (hy₂ ▸ sq_nonneg y)).trans hy₂.symm)

@[simp] theorem sqrt_zero : sqrt (0 : SignSequence.{u}) = 0 :=
  sqrt_eq_of_nonneg_sq le_rfl (by simp)

@[simp] theorem sqrt_one : sqrt (1 : SignSequence.{u}) = 1 :=
  sqrt_eq_of_nonneg_sq zero_le_one (by simp)

/-- Square roots of squares recover absolute value, including negative inputs. -/
@[simp] theorem sqrt_sq_eq_abs (x : SignSequence.{u}) : sqrt (x ^ 2) = |x| :=
  sqrt_eq_of_nonneg_sq (abs_nonneg x) (sq_abs x)

/-- A positive input has a strictly positive constructed square root. -/
theorem sqrt_pos {x : SignSequence.{u}} (hx : 0 < x) : 0 < sqrt x := by
  apply lt_of_le_of_ne (sqrt_nonneg x)
  intro h
  have hs := sqrt_sq hx.le
  rw [← h, zero_pow (by decide : 2 ≠ 0)] at hs
  exact hx.ne hs

end

end Surreal.Foundations.SignSequence
