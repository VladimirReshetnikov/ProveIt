-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Algebra.Order.BigOperators.Expect
import OAI.Combinatorics.Progressions.FixedDensity.GeneratorCells
import OAI.Combinatorics.Progressions.FixedDensity.OrderedPattern
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def EdgeWeightsInUnitInterval {k : ℕ} {V : Fin k → Type*}
    (H : WeightedSimplexSystem V) : Prop :=
  ∀ j x, 0 ≤ H.edgeWeight j x ∧ H.edgeWeight j x ≤ 1

def EdgeSupDistanceLe {k : ℕ} {V : Fin k → Type*}
    (H G : WeightedSimplexSystem V) (ε : ℝ) : Prop :=
  ∀ j x, |H.edgeWeight j x - G.edgeWeight j x| ≤ ε

theorem abs_prod_sub_prod_le_card_mul
    {ι : Type*}
    (s : Finset ι) (f g : ι → ℝ) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf0 : ∀ i ∈ s, 0 ≤ f i)
    (hf1 : ∀ i ∈ s, f i ≤ 1)
    (hg0 : ∀ i ∈ s, 0 ≤ g i)
    (hg1 : ∀ i ∈ s, g i ≤ 1)
    (hfg : ∀ i ∈ s, |f i - g i| ≤ ε) :
    |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
      (s.card : ℝ) * ε := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      simp
  | @insert a s ha ih =>
      have hfa0 : 0 ≤ f a := hf0 a (Finset.mem_insert_self a s)
      have hfa1 : f a ≤ 1 := hf1 a (Finset.mem_insert_self a s)
      have hga0 : 0 ≤ g a := hg0 a (Finset.mem_insert_self a s)
      have hga1 : g a ≤ 1 := hg1 a (Finset.mem_insert_self a s)
      have hdiffa :
          |f a - g a| ≤ ε :=
        hfg a (Finset.mem_insert_self a s)
      have hfprod0 : 0 ≤ ∏ i ∈ s, f i :=
        Finset.prod_nonneg fun i hi => hf0 i (Finset.mem_insert_of_mem hi)
      have hfprod1 : (∏ i ∈ s, f i) ≤ 1 :=
        Finset.prod_le_one₀
          (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hf1 i (Finset.mem_insert_of_mem hi))
      have hgprod0 : 0 ≤ ∏ i ∈ s, g i :=
        Finset.prod_nonneg fun i hi => hg0 i (Finset.mem_insert_of_mem hi)
      have hgprod1 : (∏ i ∈ s, g i) ≤ 1 :=
        Finset.prod_le_one₀
          (fun i hi => hg0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hg1 i (Finset.mem_insert_of_mem hi))
      have ih' :
          |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
            (s.card : ℝ) * ε :=
        ih
          (fun i hi => hf0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hf1 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hg0 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hg1 i (Finset.mem_insert_of_mem hi))
          (fun i hi => hfg i (Finset.mem_insert_of_mem hi))
      have hfirst :
          |f a - g a| * |∏ i ∈ s, f i| ≤ ε := by
        calc
          |f a - g a| * |∏ i ∈ s, f i| ≤
              ε * |∏ i ∈ s, f i| :=
            mul_le_mul_of_nonneg_right hdiffa (abs_nonneg _)
          _ ≤ ε * 1 :=
            mul_le_mul_of_nonneg_left
              (by simpa [abs_of_nonneg hfprod0] using hfprod1) hε
          _ = ε := mul_one ε
      have hsecond :
          |g a| *
              |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
            (s.card : ℝ) * ε := by
        calc
          |g a| *
                |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| ≤
              1 *
                |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| :=
            mul_le_mul_of_nonneg_right
              (by simpa [abs_of_nonneg hga0] using hga1)
              (abs_nonneg _)
          _ ≤ 1 * ((s.card : ℝ) * ε) :=
            mul_le_mul_of_nonneg_left ih' zero_le_one
          _ = (s.card : ℝ) * ε := one_mul _
      rw [Finset.prod_insert ha, Finset.prod_insert ha,
        Finset.card_insert_of_notMem ha]
      calc
        |f a * (∏ i ∈ s, f i) -
              g a * ∏ i ∈ s, g i| =
            |(f a - g a) * (∏ i ∈ s, f i) +
              g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i)| := by
                congr 1
                ring
        _ ≤
            |f a - g a| * |∏ i ∈ s, f i| +
              |g a| *
                |(∏ i ∈ s, f i) - ∏ i ∈ s, g i| := by
          simpa [abs_mul] using
            abs_add_le
              ((f a - g a) * (∏ i ∈ s, f i))
              (g a * ((∏ i ∈ s, f i) - ∏ i ∈ s, g i))
        _ ≤ ε + (s.card : ℝ) * ε :=
          add_le_add hfirst hsecond
        _ = ((s.card + 1 : ℕ) : ℝ) * ε := by
          push_cast
          ring

theorem simplexWeight_abs_sub_le
    {k : ℕ} {V : Fin k → Type*}
    (H G : WeightedSimplexSystem V) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hH : EdgeWeightsInUnitInterval H)
    (hG : EdgeWeightsInUnitInterval G)
    (hHG : EdgeSupDistanceLe H G ε)
    (x : (i : Fin k) → V i) :
    |H.simplexWeight x - G.simplexWeight x| ≤ (k : ℝ) * ε := by
  change
    |(∏ j : Fin k, H.edgeWeight j (deleteCoordinate x j)) -
        ∏ j : Fin k, G.edgeWeight j (deleteCoordinate x j)| ≤
      (k : ℝ) * ε
  simpa using
    abs_prod_sub_prod_le_card_mul Finset.univ
      (fun j => H.edgeWeight j (deleteCoordinate x j))
      (fun j => G.edgeWeight j (deleteCoordinate x j))
      hε
      (fun j _ => (hH j (deleteCoordinate x j)).1)
      (fun j _ => (hH j (deleteCoordinate x j)).2)
      (fun j _ => (hG j (deleteCoordinate x j)).1)
      (fun j _ => (hG j (deleteCoordinate x j)).2)
      (fun j _ => hHG j (deleteCoordinate x j))

theorem simplexCount_abs_sub_le
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)] [∀ i, Nonempty (V i)]
    (H G : WeightedSimplexSystem V) {ε : ℝ}
    (hε : 0 ≤ ε)
    (hH : EdgeWeightsInUnitInterval H)
    (hG : EdgeWeightsInUnitInterval G)
    (hHG : EdgeSupDistanceLe H G ε) :
    |H.simplexCount - G.simplexCount| ≤ (k : ℝ) * ε := by
  rw [WeightedSimplexSystem.simplexCount,
    WeightedSimplexSystem.simplexCount, ← mean_sub]
  calc
    |mean (fun x => H.simplexWeight x - G.simplexWeight x)| ≤
        mean (fun x => |H.simplexWeight x - G.simplexWeight x|) := by
      exact Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _ => (k : ℝ) * ε) :=
      mean_mono fun x => simplexWeight_abs_sub_le H G hε hH hG hHG x
    _ = (k : ℝ) * ε := mean_const _

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def orderedAPEdgeFactor
    (k N : ℕ) (f g : ZMod N → ℝ)
    (j i : Fin k) (x : Fin k → ZMod N) : ℝ :=
  (if i < j then
      f (apSimplexForm k N i (deleteCoordinate x i))
    else 1) *
  (if j < i then
      g (apSimplexForm k N i (deleteCoordinate x i))
    else 1)

@[simp]
theorem orderedAPEdgeFactor_self
    (k N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin k) (x : Fin k → ZMod N) :
    orderedAPEdgeFactor k N f g j j x = 1 := by
  simp [orderedAPEdgeFactor]

@[simp]
theorem deleteCoordinate_update_same
    {k : ℕ} {G : Type*}
    (x : Fin k → G) (i : Fin k) (a : G) :
    deleteCoordinate (Function.update x i a) i =
      deleteCoordinate x i := by
  funext q
  simp [deleteCoordinate, q.2]

theorem insertNth_eraseCoordinate_eq_update
    {n : ℕ} {G : Type*}
    (i : Fin (n + 1)) (a : G) (x : Fin (n + 1) → G) :
    Fin.insertNth i a (eraseCoordinate i x) =
      Function.update x i a := by
  exact Fin.insertNth_removeNth i a x

theorem insertNth_insertNth_eraseCoordinate
    {n : ℕ} {G : Type*}
    (j : Fin (n + 2)) (t : Fin (n + 1))
    (a b : G) (y : Fin (n + 1) → G) :
    Fin.insertNth j a
        (Fin.insertNth t b (eraseCoordinate t y)) =
      (Function.update (Fin.insertNth j a y)
        (j.succAbove t) b : Fin (n + 2) → G) := by
  rw [insertNth_eraseCoordinate_eq_update, Fin.insertNth_update]

def apMixedCutTest
    (n N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin (n + 2)) (a : ZMod N) :
    CutTestFamily (ZMod N) (n + 1) :=
  fun t z =>
    orderedAPEdgeFactor (n + 2) N f g j (j.succAbove t)
      (Fin.insertNth j a (Fin.insertNth t 0 z))

theorem apMixedCutTest_eraseCoordinate
    (n N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin (n + 2)) (a : ZMod N)
    (t : Fin (n + 1)) (y : Fin (n + 1) → ZMod N) :
    apMixedCutTest n N f g j a t (eraseCoordinate t y) =
      orderedAPEdgeFactor (n + 2) N f g j (j.succAbove t)
        (Fin.insertNth j a y) := by
  rw [apMixedCutTest, insertNth_insertNth_eraseCoordinate]
  unfold orderedAPEdgeFactor
  simp only [deleteCoordinate_update_same]

theorem apMixedCutTest_bounded
    (n N : ℕ) (f g : ZMod N → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (j : Fin (n + 2)) (a : ZMod N) :
    IsBoundedCutTest (apMixedCutTest n N f g j a) := by
  constructor
  · intro t z
    unfold apMixedCutTest orderedAPEdgeFactor
    by_cases htj : j.succAbove t < j
    · have hjt : ¬j < j.succAbove t :=
        not_lt_of_ge (le_of_lt htj)
      simp [htj, hjt, hf0]
    · by_cases hjt : j < j.succAbove t
      · simp [htj, hjt, hg0]
      · exact (Fin.succAbove_ne j t
          (le_antisymm (not_lt.mp hjt) (not_lt.mp htj))).elim
  · intro t z
    unfold apMixedCutTest orderedAPEdgeFactor
    by_cases htj : j.succAbove t < j
    · have hjt : ¬j < j.succAbove t :=
        not_lt_of_ge (le_of_lt htj)
      simpa [htj, hjt] using
        hf1 (apSimplexForm (n + 2) N (j.succAbove t)
          (deleteCoordinate
            (Fin.insertNth j a (Fin.insertNth t 0 z))
            (j.succAbove t)))
    · by_cases hjt : j < j.succAbove t
      · simpa [htj, hjt] using
          hg1 (apSimplexForm (n + 2) N (j.succAbove t)
            (deleteCoordinate
              (Fin.insertNth j a (Fin.insertNth t 0 z))
              (j.succAbove t)))
      · exact (Fin.succAbove_ne j t
          (le_antisymm (not_lt.mp hjt) (not_lt.mp htj))).elim

theorem prod_orderedAPEdgeFactor
    (k N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin k) (x : Fin k → ZMod N) :
    (∏ i : Fin k, orderedAPEdgeFactor k N f g j i x) =
      (∏ i ∈ (Finset.univ : Finset (Fin k)) with i < j,
        f (apSimplexForm k N i (deleteCoordinate x i))) *
      ∏ i ∈ (Finset.univ : Finset (Fin k)) with j < i,
        g (apSimplexForm k N i (deleteCoordinate x i)) := by
  rw [Finset.prod_filter, Finset.prod_filter,
    ← Finset.prod_mul_distrib]
  rfl

theorem prod_apMixedCutTest_eraseCoordinate
    (n N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin (n + 2)) (a : ZMod N)
    (y : Fin (n + 1) → ZMod N) :
    (∏ t : Fin (n + 1),
        apMixedCutTest n N f g j a t
          (eraseCoordinate t y)) =
      (∏ i ∈ (Finset.univ : Finset (Fin (n + 2))) with i < j,
        f (apSimplexForm (n + 2) N i
          (deleteCoordinate (Fin.insertNth j a y) i))) *
      ∏ i ∈ (Finset.univ : Finset (Fin (n + 2))) with j < i,
        g (apSimplexForm (n + 2) N i
          (deleteCoordinate (Fin.insertNth j a y) i)) := by
  simp_rw [apMixedCutTest_eraseCoordinate]
  calc
    (∏ t : Fin (n + 1),
        orderedAPEdgeFactor (n + 2) N f g j
          (j.succAbove t) (Fin.insertNth j a y)) =
        ∏ i : Fin (n + 2),
          orderedAPEdgeFactor (n + 2) N f g j i
            (Fin.insertNth j a y) := by
      symm
      calc
        (∏ i : Fin (n + 2),
            orderedAPEdgeFactor (n + 2) N f g j i
              (Fin.insertNth j a y)) =
            orderedAPEdgeFactor (n + 2) N f g j j
                (Fin.insertNth j a y) *
              ∏ t : Fin (n + 1),
                orderedAPEdgeFactor (n + 2) N f g j
                  (j.succAbove t) (Fin.insertNth j a y) :=
          Fin.prod_univ_succAbove _ j
        _ = ∏ t : Fin (n + 1),
              orderedAPEdgeFactor (n + 2) N f g j
                (j.succAbove t) (Fin.insertNth j a y) := by
          rw [orderedAPEdgeFactor_self, one_mul]
    _ = _ := prod_orderedAPEdgeFactor
      (n + 2) N f g j (Fin.insertNth j a y)

theorem apSimplexForm_deleteCoordinate_insertNth
    (n N : ℕ) (j : Fin (n + 2))
    (a : ZMod N) (y : Fin (n + 1) → ZMod N) :
    apSimplexForm (n + 2) N j
        (deleteCoordinate (Fin.insertNth j a y) j) =
      ∑ t : Fin (n + 1),
        ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
          ZMod N) * y t) := by
  rw [apSimplexForm_deleteCoordinate_eq_weightedSum]
  simp

theorem mean_insertNth
    {G : Type*} [Fintype G] (n : ℕ)
    (j : Fin (n + 1)) (F : (Fin (n + 1) → G) → ℝ) :
    mean F =
      mean₂ (fun a : G => fun y : Fin n → G =>
        F (Fin.insertNth j a y)) := by
  calc
    mean F =
        mean (fun p : G × (Fin n → G) =>
          F (Fin.insertNth j p.1 p.2)) := by
      unfold mean
      apply Fintype.expect_equiv
        (Fin.insertNthEquiv (fun _ : Fin (n + 1) => G) j).symm
      intro x
      congr 1
      simp
    _ = mean₂ (fun a : G => fun y : Fin n → G =>
          F (Fin.insertNth j a y)) := by
      simpa [mean, mean₂] using
        (Finset.expect_product
          (Finset.univ : Finset G)
          (Finset.univ : Finset (Fin n → G))
          (fun p : G × (Fin n → G) =>
            F (Fin.insertNth j p.1 p.2)))

theorem mixedSimplexTerm_ap_insertNth
    (n N : ℕ) (f g : ZMod N → ℝ)
    (j : Fin (n + 2)) (a : ZMod N)
    (y : Fin (n + 1) → ZMod N) :
    mixedSimplexTerm
        (apSimplexSystem (n + 2) N f)
        (apSimplexSystem (n + 2) N g) j
        (Fin.insertNth j a y) =
      (f (∑ t : Fin (n + 1),
          ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
            ZMod N) * y t)) -
        g (∑ t : Fin (n + 1),
          ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
            ZMod N) * y t))) *
      ∏ t : Fin (n + 1),
        apMixedCutTest n N f g j a t
          (eraseCoordinate t y) := by
  unfold mixedSimplexTerm
  change
    (f (apSimplexForm (n + 2) N j
        (deleteCoordinate (Fin.insertNth j a y) j)) -
      g (apSimplexForm (n + 2) N j
        (deleteCoordinate (Fin.insertNth j a y) j))) *
      (∏ i ∈ (Finset.univ : Finset (Fin (n + 2))) with i < j,
        f (apSimplexForm (n + 2) N i
          (deleteCoordinate (Fin.insertNth j a y) i))) *
      (∏ i ∈ (Finset.univ : Finset (Fin (n + 2))) with j < i,
        g (apSimplexForm (n + 2) N i
          (deleteCoordinate (Fin.insertNth j a y) i))) = _
  rw [apSimplexForm_deleteCoordinate_insertNth,
    prod_apMixedCutTest_eraseCoordinate]
  ring

theorem mixedSimplexCorrelation_ap_eq_mean_linearCutCorrelation
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial (n + 1)))
    (f g : ZMod N → ℝ) (j : Fin (n + 2)) :
    mixedSimplexCorrelation
        (apSimplexSystem (n + 2) N f)
        (apSimplexSystem (n + 2) N g) j =
      mean (fun a : ZMod N =>
        linearCutCorrelation (n + 1)
          (apFaceScalingEquiv hN j) f g
          (apMixedCutTest n N f g j a)) := by
  unfold mixedSimplexCorrelation
  rw [mean_insertNth (n + 1) j]
  unfold mean₂
  apply congrArg mean
  funext a
  unfold linearCutCorrelation
  apply congrArg mean
  funext y
  change
    mixedSimplexTerm
        (apSimplexSystem (n + 2) N f)
        (apSimplexSystem (n + 2) N g) j
        (Fin.insertNth j a y) =
      (f (∑ i, apFaceScalingEquiv hN j i (y i)) -
        g (∑ i, apFaceScalingEquiv hN j i (y i))) *
      ∏ i, apMixedCutTest n N f g j a i
        (eraseCoordinate i y)
  rw [mixedSimplexTerm_ap_insertNth]
  simp only [apFaceScalingEquiv_apply]

theorem abs_mixedSimplexCorrelation_ap_le
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial (n + 1)))
    (f g : ZMod N → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    {ε : ℝ} (hcut : CutDiscrepancyLe (n + 1) f g ε)
    (j : Fin (n + 2)) :
    |mixedSimplexCorrelation
        (apSimplexSystem (n + 2) N f)
        (apSimplexSystem (n + 2) N g) j| ≤ ε := by
  rw [mixedSimplexCorrelation_ap_eq_mean_linearCutCorrelation
    n N hN f g j]
  calc
    |mean (fun a : ZMod N =>
        linearCutCorrelation (n + 1)
          (apFaceScalingEquiv hN j) f g
          (apMixedCutTest n N f g j a))| ≤
        mean (fun a : ZMod N =>
          |linearCutCorrelation (n + 1)
            (apFaceScalingEquiv hN j) f g
            (apMixedCutTest n N f g j a)|) := by
      exact Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _a : ZMod N => ε) := by
      apply mean_mono
      intro a
      exact hcut.abs_linearCutCorrelation_le
        (apFaceScalingEquiv hN j)
        (apMixedCutTest n N f g j a)
        (apMixedCutTest_bounded n N f g
          hf0 hf1 hg0 hg1 j a)
    _ = ε := mean_const _

theorem apSimplexSystem_mixedCorrelationLe
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial (n + 1)))
    (f g : ZMod N → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    {ε : ℝ} (hcut : CutDiscrepancyLe (n + 1) f g ε) :
    MixedSimplexCorrelationLe
      (apSimplexSystem (n + 2) N f)
      (apSimplexSystem (n + 2) N g) ε := by
  intro j
  exact abs_mixedSimplexCorrelation_ap_le
    n N hN f g hf0 hf1 hg0 hg1 hcut j

theorem cyclicAPCount_abs_sub_le_of_cutDiscrepancy
    (n N : ℕ) [NeZero N]
    (hN : Nat.Coprime N (Nat.factorial (n + 1)))
    (f g : ZMod N → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    {ε : ℝ} (hcut : CutDiscrepancyLe (n + 1) f g ε) :
    |cyclicAPCount (n + 2) N f -
        cyclicAPCount (n + 2) N g| ≤
      ((n + 2 : ℕ) : ℝ) * ε := by
  rw [← apSimplexSystem_simplexCount_eq_cyclicAPCount n N f,
    ← apSimplexSystem_simplexCount_eq_cyclicAPCount n N g]
  exact simplexCount_abs_sub_le_of_mixedCorrelation
    (apSimplexSystem (n + 2) N f)
    (apSimplexSystem (n + 2) N g)
    (apSimplexSystem_mixedCorrelationLe
      n N hN f g hf0 hf1 hg0 hg1 hcut)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def deletedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    Fin n → G :=
  fun t => x (finSuccAboveEquiv j t)

@[simp]
theorem deletedFaceTuple_finTupleToDeletedVector
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (y : Fin n → G) :
    deletedFaceTuple j (finTupleToDeletedVector j y) = y := by
  funext t
  simp [deletedFaceTuple]

@[simp]
theorem finTupleToDeletedVector_deletedFaceTuple
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : DeletedVector (fun _ : Fin (n + 1) => G) j) :
    finTupleToDeletedVector j (deletedFaceTuple j x) = x := by
  funext i
  change
    x (finSuccAboveEquiv j
      ((finSuccAboveEquiv j).symm i)) = x i
  rw [(finSuccAboveEquiv j).apply_symm_apply]

@[simp]
theorem deletedFaceTuple_deleteCoordinate
    {G : Type*} {n : ℕ} (j : Fin (n + 1))
    (x : Fin (n + 1) → G) (t : Fin n) :
    deletedFaceTuple j (deleteCoordinate x j) t =
      x (j.succAbove t) :=
  rfl

noncomputable def canonicalEdgeFunction
    {G : Type*} {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) :
    (Fin n → G) → ℝ :=
  fun y => H.edgeWeight j (finTupleToDeletedVector j y)

abbrev SimplexRegularitySystem
    (G : Type*) (n : ℕ)
    [Fintype G] [DecidableEq G] :=
  (j : Fin (n + 1)) →
    FaceRegularityState (Fin n → G)

noncomputable def regularizedSimplexSystem
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n) :
    WeightedSimplexSystem (fun _ : Fin (n + 1) => G) where
  edgeWeight j x :=
    (S j).structured (canonicalEdgeFunction H j)
      (deletedFaceTuple j x)

@[simp]
theorem regularizedSimplexSystem_edge_finTuple
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n)
    (j : Fin (n + 1)) (y : Fin n → G) :
    (regularizedSimplexSystem H S).edgeWeight j
        (finTupleToDeletedVector j y) =
      (S j).structured (canonicalEdgeFunction H j) y := by
  simp [regularizedSimplexSystem]

theorem canonicalEdgeFunction_nonneg
    {G : Type*} {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1)) (y : Fin n → G) :
    0 ≤ canonicalEdgeFunction H j y :=
  (hH j (finTupleToDeletedVector j y)).1

theorem canonicalEdgeFunction_le_one
    {G : Type*} {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (j : Fin (n + 1)) (y : Fin n → G) :
    canonicalEdgeFunction H j y ≤ 1 :=
  (hH j (finTupleToDeletedVector j y)).2

theorem regularizedSimplexSystem_unitInterval
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    {H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G)}
    (hH : EdgeWeightsInUnitInterval H)
    (S : SimplexRegularitySystem G n) :
    EdgeWeightsInUnitInterval (regularizedSimplexSystem H S) := by
  intro j x
  constructor
  · exact
      (S j).structured_nonneg
        (canonicalEdgeFunction_nonneg hH j)
        (deletedFaceTuple j x)
  · exact
      (S j).structured_le_one
        (canonicalEdgeFunction_le_one hH j)
        (deletedFaceTuple j x)

def orderedSimplexEdgeFactor
    {G : Type*} {k : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin k => G))
    (j i : Fin k) (x : Fin k → G) : ℝ :=
  (if i < j then H.edgeWeight i (deleteCoordinate x i) else 1) *
  (if j < i then K.edgeWeight i (deleteCoordinate x i) else 1)

@[simp]
theorem orderedSimplexEdgeFactor_self
    {G : Type*} {k : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin k => G))
    (j : Fin k) (x : Fin k → G) :
    orderedSimplexEdgeFactor H K j j x = 1 := by
  simp [orderedSimplexEdgeFactor]

def insertErasedCoordinate
    {G : Type*} {n : ℕ} (t : Fin n) (a : G)
    (z : Fin (n - 1) → G) :
    Fin n → G := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ m => exact Fin.insertNth t a z

@[simp]
theorem insertErasedCoordinate_eraseCoordinate
    {G : Type*} {n : ℕ}
    (t : Fin n) (a : G) (y : Fin n → G) :
    insertErasedCoordinate t a (eraseCoordinate t y) =
      Function.update y t a := by
  cases n with
  | zero => exact Fin.elim0 t
  | succ m =>
      exact insertNth_eraseCoordinate_eq_update t a y

def simplexMixedCutTest
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G) :
    CutTestFamily G n :=
  fun t z =>
    orderedSimplexEdgeFactor H K j (j.succAbove t)
      (Fin.insertNth j a (insertErasedCoordinate t a z))

theorem simplexMixedCutTest_eraseCoordinate
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G)
    (t : Fin n) (y : Fin n → G) :
    simplexMixedCutTest H K j a t (eraseCoordinate t y) =
      orderedSimplexEdgeFactor H K j (j.succAbove t)
        (Fin.insertNth j a y) := by
  rw [simplexMixedCutTest,
    insertErasedCoordinate_eraseCoordinate,
    Fin.insertNth_update]
  unfold orderedSimplexEdgeFactor
  simp only [deleteCoordinate_update_same]

theorem simplexMixedCutTest_bounded
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (hK : EdgeWeightsInUnitInterval K)
    (j : Fin (n + 1)) (a : G) :
    IsBoundedCutTest (simplexMixedCutTest H K j a) := by
  constructor
  · intro t z
    unfold simplexMixedCutTest orderedSimplexEdgeFactor
    by_cases htj : j.succAbove t < j
    · have hjt : ¬j < j.succAbove t :=
        not_lt_of_ge (le_of_lt htj)
      simp [htj, hjt, (hH _ _).1]
    · by_cases hjt : j < j.succAbove t
      · simp [htj, hjt, (hK _ _).1]
      · exact
          (Fin.succAbove_ne j t
            (le_antisymm (not_lt.mp hjt)
              (not_lt.mp htj))).elim
  · intro t z
    unfold simplexMixedCutTest orderedSimplexEdgeFactor
    by_cases htj : j.succAbove t < j
    · have hjt : ¬j < j.succAbove t :=
        not_lt_of_ge (le_of_lt htj)
      simpa [htj, hjt] using
        (hH (j.succAbove t)
          (deleteCoordinate
            (Fin.insertNth j a (insertErasedCoordinate t a z))
            (j.succAbove t))).2
    · by_cases hjt : j < j.succAbove t
      · simpa [htj, hjt] using
          (hK (j.succAbove t)
            (deleteCoordinate
              (Fin.insertNth j a (insertErasedCoordinate t a z))
              (j.succAbove t))).2
      · exact
          (Fin.succAbove_ne j t
            (le_antisymm (not_lt.mp hjt)
              (not_lt.mp htj))).elim

theorem prod_orderedSimplexEdgeFactor
    {G : Type*} {k : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin k => G))
    (j : Fin k) (x : Fin k → G) :
    (∏ i : Fin k, orderedSimplexEdgeFactor H K j i x) =
      (∏ i ∈ (Finset.univ : Finset (Fin k)) with i < j,
        H.edgeWeight i (deleteCoordinate x i)) *
      ∏ i ∈ (Finset.univ : Finset (Fin k)) with j < i,
        K.edgeWeight i (deleteCoordinate x i) := by
  rw [Finset.prod_filter, Finset.prod_filter,
    ← Finset.prod_mul_distrib]
  rfl

theorem prod_simplexMixedCutTest_eraseCoordinate
    {G : Type*} {n : ℕ}
    (H K : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (j : Fin (n + 1)) (a : G)
    (y : Fin n → G) :
    (∏ t : Fin n,
        simplexMixedCutTest H K j a t
          (eraseCoordinate t y)) =
      (∏ i ∈ (Finset.univ : Finset (Fin (n + 1))) with i < j,
        H.edgeWeight i
          (deleteCoordinate (Fin.insertNth j a y) i)) *
      ∏ i ∈ (Finset.univ : Finset (Fin (n + 1))) with j < i,
        K.edgeWeight i
          (deleteCoordinate (Fin.insertNth j a y) i) := by
  simp_rw [simplexMixedCutTest_eraseCoordinate]
  calc
    (∏ t : Fin n,
        orderedSimplexEdgeFactor H K j (j.succAbove t)
          (Fin.insertNth j a y)) =
        ∏ i : Fin (n + 1),
          orderedSimplexEdgeFactor H K j i
            (Fin.insertNth j a y) := by
      symm
      calc
        (∏ i : Fin (n + 1),
            orderedSimplexEdgeFactor H K j i
              (Fin.insertNth j a y)) =
            orderedSimplexEdgeFactor H K j j
                (Fin.insertNth j a y) *
              ∏ t : Fin n,
                orderedSimplexEdgeFactor H K j
                  (j.succAbove t) (Fin.insertNth j a y) :=
          Fin.prod_univ_succAbove _ j
        _ =
            ∏ t : Fin n,
              orderedSimplexEdgeFactor H K j
                (j.succAbove t) (Fin.insertNth j a y) := by
          rw [orderedSimplexEdgeFactor_self, one_mul]
    _ = _ :=
      prod_orderedSimplexEdgeFactor H K j
        (Fin.insertNth j a y)

theorem mixedSimplexTerm_regularized_insertNth
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n)
    (j : Fin (n + 1)) (a : G) (y : Fin n → G) :
    mixedSimplexTerm H (regularizedSimplexSystem H S) j
        (Fin.insertNth j a y) =
      (S j).residual (canonicalEdgeFunction H j) y *
        cutTestProduct
          (simplexMixedCutTest H
            (regularizedSimplexSystem H S) j a) y := by
  have hHj :
      H.edgeWeight j
          (deleteCoordinate (Fin.insertNth j a y) j) =
        canonicalEdgeFunction H j y := by
    simp [canonicalEdgeFunction,
      deleteCoordinate_eq_finTupleToDeletedVector]
  have hKj :
      (regularizedSimplexSystem H S).edgeWeight j
          (deleteCoordinate (Fin.insertNth j a y) j) =
        (S j).structured (canonicalEdgeFunction H j) y := by
    simp [regularizedSimplexSystem,
      deleteCoordinate_eq_finTupleToDeletedVector]
  unfold mixedSimplexTerm FaceRegularityState.residual
  rw [hHj, hKj]
  rw [show
      cutTestProduct
          (simplexMixedCutTest H
            (regularizedSimplexSystem H S) j a) y =
        (∏ i ∈ (Finset.univ : Finset (Fin (n + 1))) with i < j,
          H.edgeWeight i
            (deleteCoordinate (Fin.insertNth j a y) i)) *
        ∏ i ∈ (Finset.univ : Finset (Fin (n + 1))) with j < i,
          (regularizedSimplexSystem H S).edgeWeight i
            (deleteCoordinate (Fin.insertNth j a y) i) by
      exact prod_simplexMixedCutTest_eraseCoordinate
        H (regularizedSimplexSystem H S) j a y]
  ring

theorem mixedSimplexCorrelation_regularized_eq_mean
    {G : Type*} [Fintype G] [DecidableEq G] {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (S : SimplexRegularitySystem G n)
    (j : Fin (n + 1)) :
    mixedSimplexCorrelation H (regularizedSimplexSystem H S) j =
      mean (fun a : G =>
        (S j).faceCutCorrelation
          (canonicalEdgeFunction H j)
          (simplexMixedCutTest H
            (regularizedSimplexSystem H S) j a)) := by
  unfold mixedSimplexCorrelation
  rw [mean_insertNth n j]
  unfold mean₂
  apply congrArg mean
  funext a
  unfold FaceRegularityState.faceCutCorrelation
  apply congrArg mean
  funext y
  exact mixedSimplexTerm_regularized_insertNth H S j a y

theorem abs_mixedSimplexCorrelation_regularized_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (S : SimplexRegularitySystem G n)
    {ε : ℝ}
    (hregular :
      ∀ j, (S j).IsFaceCutRegular
        (canonicalEdgeFunction H j) ε)
    (j : Fin (n + 1)) :
    |mixedSimplexCorrelation H
        (regularizedSimplexSystem H S) j| ≤ ε := by
  rw [mixedSimplexCorrelation_regularized_eq_mean]
  let K := regularizedSimplexSystem H S
  have hK : EdgeWeightsInUnitInterval K :=
    regularizedSimplexSystem_unitInterval hH S
  calc
    |mean (fun a : G =>
        (S j).faceCutCorrelation
          (canonicalEdgeFunction H j)
          (simplexMixedCutTest H K j a))| ≤
        mean (fun a : G =>
          |(S j).faceCutCorrelation
            (canonicalEdgeFunction H j)
            (simplexMixedCutTest H K j a)|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean (fun _a : G => ε) := by
      apply mean_mono
      intro a
      exact hregular j
        (simplexMixedCutTest H K j a)
        (simplexMixedCutTest_bounded H K hH hK j a)
    _ = ε := mean_const _

theorem regularizedSimplexSystem_mixedCorrelationLe
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (S : SimplexRegularitySystem G n)
    {ε : ℝ}
    (hregular :
      ∀ j, (S j).IsFaceCutRegular
        (canonicalEdgeFunction H j) ε) :
    MixedSimplexCorrelationLe H
      (regularizedSimplexSystem H S) ε := by
  intro j
  exact abs_mixedSimplexCorrelation_regularized_le
    H hH S hregular j

theorem simplexCount_abs_sub_regularized_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (S : SimplexRegularitySystem G n)
    {ε : ℝ}
    (hregular :
      ∀ j, (S j).IsFaceCutRegular
        (canonicalEdgeFunction H j) ε) :
    |H.simplexCount -
        (regularizedSimplexSystem H S).simplexCount| ≤
      ((n + 1 : ℕ) : ℝ) * ε :=
  simplexCount_abs_sub_le_of_mixedCorrelation
    H (regularizedSimplexSystem H S)
    (regularizedSimplexSystem_mixedCorrelationLe
      H hH S hregular)

theorem exists_regularizedSimplexSystem_count_close
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {n : ℕ}
    (H : WeightedSimplexSystem
      (fun _ : Fin (n + 1) => G))
    (hH : EdgeWeightsInUnitInterval H)
    (S₀ : SimplexRegularitySystem G n)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ S : SimplexRegularitySystem G n,
      (∀ j, (S j).partition ≤ (S₀ j).partition) ∧
      (∀ j, (S j).IsFaceCutRegular
        (canonicalEdgeFunction H j) ε) ∧
      |H.simplexCount -
          (regularizedSimplexSystem H S).simplexCount| ≤
        ((n + 1 : ℕ) : ℝ) * ε ∧
      ∀ j, ∃ m i : ℕ,
        1 < (m : ℝ) * ε ^ 2 ∧
        i < m ∧
        FacePartition.complexity (S j).partition ≤
          2 ^ i *
            FacePartition.complexity (S₀ j).partition := by
  classical
  have hj (j : Fin (n + 1)) :
      ∃ T : FaceRegularityState (Fin n → G),
        T.partition ≤ (S₀ j).partition ∧
        T.IsFaceCutRegular (canonicalEdgeFunction H j) ε ∧
        ∃ m i : ℕ,
          1 < (m : ℝ) * ε ^ 2 ∧
          i < m ∧
          FacePartition.complexity T.partition ≤
            2 ^ i *
              FacePartition.complexity (S₀ j).partition := by
    obtain ⟨m, i, T, hlong, hi, hTS, hregular, hcomplexity⟩ :=
      (S₀ j).exists_faceCutRegular_refinement
        (canonicalEdgeFunction H j)
        (canonicalEdgeFunction_nonneg hH j)
        (canonicalEdgeFunction_le_one hH j) hε
    exact
      ⟨T, hTS, hregular, m, i,
        hlong, hi, hcomplexity⟩
  choose S hS using hj
  refine
    ⟨S, fun j => (hS j).1, fun j => (hS j).2.1,
      ?_, fun j => (hS j).2.2⟩
  exact simplexCount_abs_sub_regularized_le
    H hH S (fun j => (hS j).2.1)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable local instance orderedFaceLinearOrder
    (k r : ℕ) : LinearOrder (OrderedFace k r) := by
  classical
  exact (Fintype.equivFin (OrderedFace k r)).linearOrder

abbrev OrderedRegularitySystem
    (G : Type*) [Fintype G] [DecidableEq G]
    (k r : ℕ) :=
  (e : OrderedFace k r) →
    FaceRegularityState (Fin r → G)

noncomputable def regularizedOrderedPattern
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r) :
    WeightedOrderedPattern G k r where
  edgeWeight e :=
    (S e).structured (H.edgeWeight e)

@[simp]
theorem regularizedOrderedPattern_edgeWeight
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (e : OrderedFace k r) (y : Fin r → G) :
    (regularizedOrderedPattern H S).edgeWeight e y =
      (S e).structured (H.edgeWeight e) y :=
  rfl

theorem regularizedOrderedPattern_unitInterval
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    {H : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    (S : OrderedRegularitySystem G k r) :
    (regularizedOrderedPattern H S).EdgeWeightsInUnitInterval := by
  intro e y
  exact
    ⟨(S e).structured_nonneg
        (fun z => (hH e z).1) y,
      (S e).structured_le_one
        (fun z => (hH e z).2) y⟩

theorem orderedFaceTuple_split_update_eq
    {G : Type*} {k r : ℕ}
    (e f : OrderedFace k r) (i : Fin r)
    (hmissing : e i ∉ Set.range f)
    (a : G) (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm
          (Function.update y i a, z)) =
      orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm (y, z)) := by
  funext t
  by_cases hfe : f t ∈ Set.range e
  · obtain ⟨q, hq⟩ := hfe
    have hqi : q ≠ i := by
      intro h
      apply hmissing
      exact ⟨t, (h ▸ hq).symm⟩
    have hleft :=
      congrFun
        (orderedFaceTuple_splitOrderedFaceEquiv_symm
          e (Function.update y i a) z) q
    have hright :=
      congrFun
        (orderedFaceTuple_splitOrderedFaceEquiv_symm
          e y z) q
    change
      ((splitOrderedFaceEquiv e).symm
          (Function.update y i a, z)) (e q) =
        Function.update y i a q at hleft
    change
      ((splitOrderedFaceEquiv e).symm (y, z)) (e q) =
        y q at hright
    change
      ((splitOrderedFaceEquiv e).symm
          (Function.update y i a, z)) (f t) =
        ((splitOrderedFaceEquiv e).symm (y, z)) (f t)
    rw [← hq]
    rw [hleft, hright]
    simp [hqi]
  · let v : OrderedFaceComplement e := ⟨f t, hfe⟩
    have hleft :=
      congrFun
        (orderedFaceComplementTuple_splitOrderedFaceEquiv_symm
          e (Function.update y i a) z) v
    have hright :=
      congrFun
        (orderedFaceComplementTuple_splitOrderedFaceEquiv_symm
          e y z) v
    exact hleft.trans hright.symm

theorem orderedFaceTuple_split_insertErased_eq
    {G : Type*} {k r : ℕ}
    (e f : OrderedFace k r) (i : Fin r)
    (hmissing : e i ∉ Set.range f)
    (a : G) (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm
          (insertErasedCoordinate i a
            (eraseCoordinate i y), z)) =
      orderedFaceTuple f
        ((splitOrderedFaceEquiv e).symm (y, z)) := by
  rw [insertErasedCoordinate_eraseCoordinate]
  exact orderedFaceTuple_split_update_eq
    e f i hmissing a y z

noncomputable def orderedPatternEdgeFactor
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e f : OrderedFace k r) (x : Fin k → G) : ℝ :=
  (if f < e then
      H.edgeWeight f (orderedFaceTuple f x)
    else 1) *
    (if e < f then
      K.edgeWeight f (orderedFaceTuple f x)
    else 1)

@[simp]
theorem orderedPatternEdgeFactor_self
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e : OrderedFace k r) (x : Fin k → G) :
    orderedPatternEdgeFactor H K e e x = 1 := by
  simp [orderedPatternEdgeFactor]

theorem prod_orderedPatternEdgeFactor
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e : OrderedFace k r) (x : Fin k → G) :
    (∏ f : OrderedFace k r,
        orderedPatternEdgeFactor H K e f x) =
      (∏ f ∈ (Finset.univ : Finset (OrderedFace k r))
          with f < e,
        H.edgeWeight f (orderedFaceTuple f x)) *
      ∏ f ∈ (Finset.univ : Finset (OrderedFace k r))
          with e < f,
        K.edgeWeight f (orderedFaceTuple f x) := by
  rw [Finset.prod_filter, Finset.prod_filter,
    ← Finset.prod_mul_distrib]
  rfl

theorem orderedPatternEdgeFactor_split_insertErased_eq
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e f : OrderedFace k r) (i : Fin r)
    (hmissing : e i ∉ Set.range f)
    (a : G) (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    orderedPatternEdgeFactor H K e f
        ((splitOrderedFaceEquiv e).symm
          (insertErasedCoordinate i a
            (eraseCoordinate i y), z)) =
      orderedPatternEdgeFactor H K e f
        ((splitOrderedFaceEquiv e).symm (y, z)) := by
  unfold orderedPatternEdgeFactor
  rw [orderedFaceTuple_split_insertErased_eq
    e f i hmissing a y z]

theorem orderedPatternEdgeFactor_nonneg
    {G : Type*} {k r : ℕ}
    {H K : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    (hK : K.EdgeWeightsInUnitInterval)
    (e f : OrderedFace k r) (x : Fin k → G) :
    0 ≤ orderedPatternEdgeFactor H K e f x := by
  by_cases hfe : f < e
  · have hef : ¬e < f :=
      not_lt_of_ge (le_of_lt hfe)
    simpa [orderedPatternEdgeFactor, hfe, hef] using
      (hH f (orderedFaceTuple f x)).1
  · by_cases hef : e < f
    · simpa [orderedPatternEdgeFactor, hfe, hef] using
        (hK f (orderedFaceTuple f x)).1
    · simp [orderedPatternEdgeFactor, hfe, hef]

theorem orderedPatternEdgeFactor_le_one
    {G : Type*} {k r : ℕ}
    {H K : WeightedOrderedPattern G k r}
    (hH : H.EdgeWeightsInUnitInterval)
    (hK : K.EdgeWeightsInUnitInterval)
    (e f : OrderedFace k r) (x : Fin k → G) :
    orderedPatternEdgeFactor H K e f x ≤ 1 := by
  by_cases hfe : f < e
  · have hef : ¬e < f :=
      not_lt_of_ge (le_of_lt hfe)
    simpa [orderedPatternEdgeFactor, hfe, hef] using
      (hH f (orderedFaceTuple f x)).2
  · by_cases hef : e < f
    · simpa [orderedPatternEdgeFactor, hfe, hef] using
        (hK f (orderedFaceTuple f x)).2
    · simp [orderedPatternEdgeFactor, hfe, hef]

noncomputable def orderedPatternMixedCutTest
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e : OrderedFace k r) (a : G)
    (z : OrderedFaceComplement e → G) :
    CutTestFamily G r :=
  fun i y =>
    ∏ f : OrderedFace k r,
      if hfe : f = e then 1
      else if
          orderedFaceMissingCoordinate e f
              (Ne.symm hfe) = i
        then
          orderedPatternEdgeFactor H K e f
            ((splitOrderedFaceEquiv e).symm
              (insertErasedCoordinate i a y, z))
        else 1

theorem orderedPatternMixedCutTest_bounded
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    (hK : K.EdgeWeightsInUnitInterval)
    (e : OrderedFace k r) (a : G)
    (z : OrderedFaceComplement e → G) :
    IsBoundedCutTest
      (orderedPatternMixedCutTest H K e a z) := by
  constructor
  · intro i y
    unfold orderedPatternMixedCutTest
    apply Finset.prod_nonneg
    intro f _hf
    split_ifs
    · positivity
    · exact orderedPatternEdgeFactor_nonneg
        hH hK e f _
    · positivity
  · intro i y
    unfold orderedPatternMixedCutTest
    apply Finset.prod_le_one₀
    · intro f _hf
      split_ifs
      · positivity
      · exact orderedPatternEdgeFactor_nonneg
          hH hK e f _
      · positivity
    · intro f _hf
      split_ifs
      · exact le_rfl
      · exact orderedPatternEdgeFactor_le_one
          hH hK e f _
      · exact le_rfl

theorem cutTestProduct_orderedPatternMixedCutTest
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e : OrderedFace k r) (a : G)
    (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    cutTestProduct
        (orderedPatternMixedCutTest H K e a z) y =
      ∏ f : OrderedFace k r,
        orderedPatternEdgeFactor H K e f
          ((splitOrderedFaceEquiv e).symm (y, z)) := by
  classical
  unfold cutTestProduct orderedPatternMixedCutTest
  rw [Finset.prod_comm]
  apply Fintype.prod_congr
  intro f
  by_cases hfe : f = e
  · subst f
    simp
  · let i :=
      orderedFaceMissingCoordinate e f (Ne.symm hfe)
    have hmissing :
        e i ∉ Set.range f := by
      exact orderedFaceMissingCoordinate_not_mem_range
        e f (Ne.symm hfe)
    calc
      (∏ j : Fin r,
          if hfe' : f = e then 1
          else if
              orderedFaceMissingCoordinate e f
                  (Ne.symm hfe') = j
            then
              orderedPatternEdgeFactor H K e f
                ((splitOrderedFaceEquiv e).symm
                  (insertErasedCoordinate j a
                    (eraseCoordinate j y), z))
            else 1) =
          (if hfe' : f = e then 1
          else if
              orderedFaceMissingCoordinate e f
                  (Ne.symm hfe') = i
            then
              orderedPatternEdgeFactor H K e f
                ((splitOrderedFaceEquiv e).symm
                  (insertErasedCoordinate i a
                    (eraseCoordinate i y), z))
            else 1) := by
        apply Fintype.prod_eq_single i
        intro j hji
        have hne :
            orderedFaceMissingCoordinate e f
                (Ne.symm hfe) ≠ j := by
          intro h
          exact hji h.symm
        simp [hfe, hne]
      _ =
          orderedPatternEdgeFactor H K e f
            ((splitOrderedFaceEquiv e).symm
              (insertErasedCoordinate i a
                (eraseCoordinate i y), z)) := by
        simp [hfe, i]
      _ =
          orderedPatternEdgeFactor H K e f
            ((splitOrderedFaceEquiv e).symm (y, z)) :=
        orderedPatternEdgeFactor_split_insertErased_eq
          H K e f i hmissing a y z

noncomputable def mixedOrderedPatternTerm
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e : OrderedFace k r) (x : Fin k → G) : ℝ :=
  (H.edgeWeight e (orderedFaceTuple e x) -
      K.edgeWeight e (orderedFaceTuple e x)) *
    (∏ f ∈ (Finset.univ : Finset (OrderedFace k r))
        with f < e,
      H.edgeWeight f (orderedFaceTuple f x)) *
    ∏ f ∈ (Finset.univ : Finset (OrderedFace k r))
        with e < f,
      K.edgeWeight f (orderedFaceTuple f x)

theorem patternWeight_sub_eq_sum_mixedOrderedPatternTerm
    {G : Type*} {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (x : Fin k → G) :
    H.patternWeight x - K.patternWeight x =
      ∑ e : OrderedFace k r,
        mixedOrderedPatternTerm H K e x := by
  unfold WeightedOrderedPattern.patternWeight
  simpa [mixedOrderedPatternTerm] using
    prod_sub_prod_eq_sum_ordered
      (Finset.univ : Finset (OrderedFace k r))
      (fun e => H.edgeWeight e (orderedFaceTuple e x))
      (fun e => K.edgeWeight e (orderedFaceTuple e x))

noncomputable def mixedOrderedPatternCorrelation
    {G : Type*} [Fintype G] {k r : ℕ}
    (H K : WeightedOrderedPattern G k r)
    (e : OrderedFace k r) : ℝ :=
  mean (mixedOrderedPatternTerm H K e)

theorem patternCount_sub_eq_sum_mixedOrderedPatternCorrelation
    {G : Type*} [Fintype G] {k r : ℕ}
    (H K : WeightedOrderedPattern G k r) :
    H.patternCount - K.patternCount =
      ∑ e : OrderedFace k r,
        mixedOrderedPatternCorrelation H K e := by
  rw [WeightedOrderedPattern.patternCount,
    WeightedOrderedPattern.patternCount, ← mean_sub]
  calc
    mean (fun x => H.patternWeight x - K.patternWeight x) =
        mean (fun x =>
          ∑ e : OrderedFace k r,
            mixedOrderedPatternTerm H K e x) := by
      apply congrArg mean
      funext x
      exact
        patternWeight_sub_eq_sum_mixedOrderedPatternTerm
          H K x
    _ =
        ∑ e : OrderedFace k r,
          mean (mixedOrderedPatternTerm H K e) :=
      mean_finset_sum Finset.univ
        (fun e => mixedOrderedPatternTerm H K e)
    _ = _ := by
      rfl

theorem abs_patternCount_sub_le_sum_mixedOrderedPatternCorrelation
    {G : Type*} [Fintype G] {k r : ℕ}
    (H K : WeightedOrderedPattern G k r) :
    |H.patternCount - K.patternCount| ≤
      ∑ e : OrderedFace k r,
        |mixedOrderedPatternCorrelation H K e| := by
  rw [patternCount_sub_eq_sum_mixedOrderedPatternCorrelation]
  exact Finset.abs_sum_le_sum_abs _ _

theorem mixedOrderedPatternTerm_regularized_split
    {G : Type*} [Fintype G] [DecidableEq G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (e : OrderedFace k r) (a : G)
    (y : Fin r → G)
    (z : OrderedFaceComplement e → G) :
    mixedOrderedPatternTerm H
        (regularizedOrderedPattern H S) e
        ((splitOrderedFaceEquiv e).symm (y, z)) =
      (S e).residual (H.edgeWeight e) y *
        cutTestProduct
          (orderedPatternMixedCutTest H
            (regularizedOrderedPattern H S) e a z) y := by
  have hprod :=
    prod_orderedPatternEdgeFactor
      H (regularizedOrderedPattern H S) e
        ((splitOrderedFaceEquiv e).symm (y, z))
  have hcut :=
    cutTestProduct_orderedPatternMixedCutTest
      H (regularizedOrderedPattern H S) e a y z
  simp only [regularizedOrderedPattern_edgeWeight] at hprod
  unfold mixedOrderedPatternTerm FaceRegularityState.residual
  simp only [
    orderedFaceTuple_splitOrderedFaceEquiv_symm,
    regularizedOrderedPattern_edgeWeight]
  rw [mul_assoc, ← hprod, ← hcut]

theorem mixedOrderedPatternCorrelation_regularized_eq_mean
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (S : OrderedRegularitySystem G k r)
    (e : OrderedFace k r) :
    mixedOrderedPatternCorrelation H
        (regularizedOrderedPattern H S) e =
      mean (fun z : OrderedFaceComplement e → G =>
        (S e).faceCutCorrelation
          (H.edgeWeight e)
          (orderedPatternMixedCutTest H
            (regularizedOrderedPattern H S) e
            (Classical.choice inferInstance) z)) := by
  unfold mixedOrderedPatternCorrelation
  rw [mean_splitOrderedFace e]
  rw [mean₂_comm]
  unfold mean₂
  apply congrArg mean
  funext z
  unfold FaceRegularityState.faceCutCorrelation
  apply congrArg mean
  funext y
  exact mixedOrderedPatternTerm_regularized_split
    H S e (Classical.choice inferInstance) y z

theorem abs_mixedOrderedPatternCorrelation_regularized_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    (S : OrderedRegularitySystem G k r)
    {ε : ℝ}
    (hregular :
      ∀ e, (S e).IsFaceCutRegular
        (H.edgeWeight e) ε)
    (e : OrderedFace k r) :
    |mixedOrderedPatternCorrelation H
        (regularizedOrderedPattern H S) e| ≤ ε := by
  rw [mixedOrderedPatternCorrelation_regularized_eq_mean]
  let K := regularizedOrderedPattern H S
  have hK : K.EdgeWeightsInUnitInterval :=
    regularizedOrderedPattern_unitInterval hH S
  calc
    |mean (fun z : OrderedFaceComplement e → G =>
        (S e).faceCutCorrelation
          (H.edgeWeight e)
          (orderedPatternMixedCutTest H K e
            (Classical.choice inferInstance) z))| ≤
        mean (fun z : OrderedFaceComplement e → G =>
          |(S e).faceCutCorrelation
            (H.edgeWeight e)
            (orderedPatternMixedCutTest H K e
              (Classical.choice inferInstance) z)|) :=
      Finset.abs_expect_le Finset.univ _
    _ ≤ mean
        (fun _z : OrderedFaceComplement e → G => ε) := by
      apply mean_mono
      intro z
      exact hregular e
        (orderedPatternMixedCutTest H K e
          (Classical.choice inferInstance) z)
        (orderedPatternMixedCutTest_bounded
          H K hH hK e (Classical.choice inferInstance) z)
    _ = ε := mean_const _

theorem patternCount_abs_sub_regularizedOrderedPattern_le
    {G : Type*} [Fintype G] [DecidableEq G] [Nonempty G]
    {k r : ℕ}
    (H : WeightedOrderedPattern G k r)
    (hH : H.EdgeWeightsInUnitInterval)
    (S : OrderedRegularitySystem G k r)
    {ε : ℝ}
    (hregular :
      ∀ e, (S e).IsFaceCutRegular
        (H.edgeWeight e) ε) :
    |H.patternCount -
        (regularizedOrderedPattern H S).patternCount| ≤
      (Fintype.card (OrderedFace k r) : ℝ) * ε := by
  calc
    |H.patternCount -
        (regularizedOrderedPattern H S).patternCount| ≤
        ∑ e : OrderedFace k r,
          |mixedOrderedPatternCorrelation H
            (regularizedOrderedPattern H S) e| :=
      abs_patternCount_sub_le_sum_mixedOrderedPatternCorrelation
        H (regularizedOrderedPattern H S)
    _ ≤ ∑ _e : OrderedFace k r, ε :=
      Finset.sum_le_sum fun e _ =>
        abs_mixedOrderedPatternCorrelation_regularized_le
          H hH S hregular e
    _ = (Fintype.card (OrderedFace k r) : ℝ) * ε := by
      simp

end Erdos3.FixedDensity

end

end OAI
