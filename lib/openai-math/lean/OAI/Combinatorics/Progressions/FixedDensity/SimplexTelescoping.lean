-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Algebra.BigOperators.Ring.Finset
import OAI.Combinatorics.Progressions.Results.LinearFormsBasic
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

abbrev DeletedVector {k : ℕ} (V : Fin k → Type*) (j : Fin k) :=
  (i : {i : Fin k // i ≠ j}) → V i.1

def deleteCoordinate {k : ℕ} {V : Fin k → Type*}
    (x : (i : Fin k) → V i) (j : Fin k) :
    DeletedVector V j :=
  fun i => x i.1

structure WeightedSimplexSystem {k : ℕ} (V : Fin k → Type*) where
  edgeWeight : (j : Fin k) → DeletedVector V j → ℝ

namespace WeightedSimplexSystem

def simplexWeight {k : ℕ} {V : Fin k → Type*}
    (H : WeightedSimplexSystem V) (x : (i : Fin k) → V i) : ℝ :=
  ∏ j : Fin k, H.edgeWeight j (deleteCoordinate x j)

noncomputable def simplexCount {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)] (H : WeightedSimplexSystem V) : ℝ :=
  mean H.simplexWeight

theorem simplexWeight_nonneg {k : ℕ} {V : Fin k → Type*}
    (H : WeightedSimplexSystem V)
    (hH : ∀ j x, 0 ≤ H.edgeWeight j x)
    (x : (i : Fin k) → V i) :
    0 ≤ H.simplexWeight x := by
  exact Finset.prod_nonneg fun j _ => hH j (deleteCoordinate x j)

theorem simplexCount_nonneg {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : WeightedSimplexSystem V)
    (hH : ∀ j x, 0 ≤ H.edgeWeight j x) :
    0 ≤ H.simplexCount :=
  mean_nonneg (H.simplexWeight_nonneg hH)

theorem simplexWeight_mono {k : ℕ} {V : Fin k → Type*}
    (H G : WeightedSimplexSystem V)
    (hH : ∀ j x, 0 ≤ H.edgeWeight j x)
    (hHG : ∀ j x, H.edgeWeight j x ≤ G.edgeWeight j x)
    (x : (i : Fin k) → V i) :
    H.simplexWeight x ≤ G.simplexWeight x := by
  exact Finset.prod_le_prod₀
    (fun j _ => hH j (deleteCoordinate x j))
    (fun j _ => hHG j (deleteCoordinate x j))

theorem simplexCount_mono {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V)
    (hH : ∀ j x, 0 ≤ H.edgeWeight j x)
    (hHG : ∀ j x, H.edgeWeight j x ≤ G.edgeWeight j x) :
    H.simplexCount ≤ G.simplexCount :=
  mean_mono (H.simplexWeight_mono G hH hHG)

end WeightedSimplexSystem

def apSimplexForm (k N : ℕ) (j : Fin k)
    (x : DeletedVector (fun _ : Fin k => ZMod N) j) : ZMod N :=
  ∑ i : {i : Fin k // i ≠ j},
    (((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i

def simplexCoordinateSum (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, x i

def simplexCoordinateMoment (k N : ℕ)
    (x : Fin k → ZMod N) : ZMod N :=
  ∑ i : Fin k, (i : ZMod N) * x i

theorem apSimplexForm_deleteCoordinate (k N : ℕ) (j : Fin k)
    (x : Fin k → ZMod N) :
    apSimplexForm k N j (deleteCoordinate x j) =
      simplexCoordinateMoment k N x -
        (j : ZMod N) * simplexCoordinateSum k N x := by
  classical
  let f : Fin k → ZMod N :=
    fun i => (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x i
  have hsplit :=
    Fintype.sum_subtype_add_sum_subtype (fun i : Fin k => i ≠ j) f
  have hcomplement :
      (∑ i : {i : Fin k // ¬i ≠ j}, f i.1) = 0 := by
    apply Finset.sum_eq_zero
    intro i
    simp only [Finset.mem_univ, forall_const]
    have hij : i.1 = j := not_ne_iff.mp i.2
    rw [hij]
    simp [f]
  have hsum : (∑ i : {i : Fin k // i ≠ j}, f i.1) = ∑ i : Fin k, f i := by
    rw [hcomplement, add_zero] at hsplit
    exact hsplit
  rw [apSimplexForm]
  change (∑ i : {i : Fin k // i ≠ j}, f i.1) =
    simplexCoordinateMoment k N x -
      (j : ZMod N) * simplexCoordinateSum k N x
  rw [hsum]
  simp only [simplexCoordinateMoment, simplexCoordinateSum, f]
  push_cast
  simp_rw [sub_mul]
  rw [Finset.sum_sub_distrib, Finset.mul_sum]

def apSimplexSystem (k N : ℕ) (f : ZMod N → ℝ) :
    WeightedSimplexSystem (fun _ : Fin k => ZMod N) where
  edgeWeight j x := f (apSimplexForm k N j x)

theorem apSimplexSystem_simplexWeight
    (k N : ℕ) (f : ZMod N → ℝ)
    (x : Fin k → ZMod N) :
    (apSimplexSystem k N f).simplexWeight x =
      cyclicAPProduct k N f
        (simplexCoordinateMoment k N x)
        (-simplexCoordinateSum k N x) := by
  apply Finset.prod_congr rfl
  intro j _
  change
    f (apSimplexForm k N j (deleteCoordinate x j)) =
      f (cyclicAPTerm
        (simplexCoordinateMoment k N x)
        (-simplexCoordinateSum k N x) j)
  congr 1
  rw [apSimplexForm_deleteCoordinate]
  simp [cyclicAPTerm]
  ring

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def simplexTailSum (r N : ℕ) (y : Fin r → ZMod N) : ZMod N :=
  ∑ i : Fin r, y i

def simplexTailMoment (r N : ℕ) (y : Fin r → ZMod N) : ZMod N :=
  ∑ i : Fin r, (i.succ.succ : ZMod N) * y i

def simplexCoordinatesOfAP (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) : Fin (r + 2) → ZMod N :=
  Fin.cases
    (simplexTailMoment r N y - a - d - simplexTailSum r N y)
    (Fin.cases (a - simplexTailMoment r N y) y)

@[simp]
theorem simplexCoordinatesOfAP_zero (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) :
    simplexCoordinatesOfAP r N a d y 0 =
      simplexTailMoment r N y - a - d - simplexTailSum r N y :=
  rfl

@[simp]
theorem simplexCoordinatesOfAP_one (r N : ℕ) (a d : ZMod N)
    (y : Fin r → ZMod N) :
    simplexCoordinatesOfAP r N a d y 1 =
      a - simplexTailMoment r N y :=
  rfl

@[simp]
theorem simplexCoordinatesOfAP_succ_succ (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) (i : Fin r) :
    simplexCoordinatesOfAP r N a d y i.succ.succ = y i :=
  rfl

theorem simplexCoordinateSum_decompose (r N : ℕ)
    (x : Fin (r + 2) → ZMod N) :
    simplexCoordinateSum (r + 2) N x =
      x 0 + x 1 +
        simplexTailSum r N (fun i => x i.succ.succ) := by
  simp [simplexCoordinateSum, simplexTailSum, Fin.sum_univ_succ,
    add_assoc]

theorem simplexCoordinateMoment_decompose (r N : ℕ)
    (x : Fin (r + 2) → ZMod N) :
    simplexCoordinateMoment (r + 2) N x =
      x 1 + simplexTailMoment r N (fun i => x i.succ.succ) := by
  simp [simplexCoordinateMoment, simplexTailMoment,
    Fin.sum_univ_succ]

@[simp]
theorem simplexCoordinateSum_coordinatesOfAP (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) :
    simplexCoordinateSum (r + 2) N
        (simplexCoordinatesOfAP r N a d y) = -d := by
  rw [simplexCoordinateSum_decompose]
  simp
  ring

@[simp]
theorem simplexCoordinateMoment_coordinatesOfAP (r N : ℕ)
    (a d : ZMod N) (y : Fin r → ZMod N) :
    simplexCoordinateMoment (r + 2) N
        (simplexCoordinatesOfAP r N a d y) = a := by
  rw [simplexCoordinateMoment_decompose]
  simp

def simplexAPEquiv (r N : ℕ) :
    (Fin (r + 2) → ZMod N) ≃
      (ZMod N × ZMod N) × (Fin r → ZMod N) where
  toFun x :=
    ((simplexCoordinateMoment (r + 2) N x,
      -simplexCoordinateSum (r + 2) N x),
      fun i => x i.succ.succ)
  invFun y := simplexCoordinatesOfAP r N y.1.1 y.1.2 y.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun i => Fin.cases ?_ (fun _ => rfl) i) i
    · change
        simplexCoordinatesOfAP r N
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)
            (fun i => x i.succ.succ) 0 =
          x 0
      rw [simplexCoordinatesOfAP_zero,
        simplexCoordinateMoment_decompose,
        simplexCoordinateSum_decompose]
      ring
    · change
        simplexCoordinatesOfAP r N
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)
            (fun i => x i.succ.succ) 1 =
          x 1
      rw [simplexCoordinatesOfAP_one,
        simplexCoordinateMoment_decompose]
      ring
  right_inv y := by
    rcases y with ⟨⟨a, d⟩, tail⟩
    apply Prod.ext
    · apply Prod.ext
      · change
          simplexCoordinateMoment (r + 2) N
              (simplexCoordinatesOfAP r N a d tail) =
            a
        exact simplexCoordinateMoment_coordinatesOfAP r N a d tail
      · change
          -simplexCoordinateSum (r + 2) N
              (simplexCoordinatesOfAP r N a d tail) =
            d
        rw [simplexCoordinateSum_coordinatesOfAP]
        simp
    · funext i
      change simplexCoordinatesOfAP r N a d tail i.succ.succ = tail i
      exact simplexCoordinatesOfAP_succ_succ r N a d tail i

theorem mean_equiv {α β : Type*} [Fintype α] [Fintype β]
    (e : α ≃ β) (f : α → ℝ) (g : β → ℝ)
    (h : ∀ x, f x = g (e x)) :
    mean f = mean g := by
  exact Fintype.expect_equiv e f g h

theorem mean_prod {α β : Type*} [Fintype α] [Fintype β]
    (f : α → β → ℝ) :
    mean (fun p : α × β => f p.1 p.2) = mean₂ f := by
  simpa [mean, mean₂] using
    (Finset.expect_product'
      (Finset.univ : Finset α) (Finset.univ : Finset β) f)

theorem mean_prod_fst {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty β] (f : α → ℝ) :
    mean (fun p : α × β => f p.1) = mean f := by
  calc
    mean (fun p : α × β => f p.1) =
        mean₂ (fun a (_ : β) => f a) := by
      exact mean_prod (fun a (_ : β) => f a)
    _ = mean f := by
      simp [mean₂]

theorem apSimplexSystem_simplexCount_eq_cyclicAPCount
    (r N : ℕ) [NeZero N] (f : ZMod N → ℝ) :
    (apSimplexSystem (r + 2) N f).simplexCount =
      cyclicAPCount (r + 2) N f := by
  rw [WeightedSimplexSystem.simplexCount, cyclicAPCount]
  calc
    mean (apSimplexSystem (r + 2) N f).simplexWeight =
        mean (fun x : Fin (r + 2) → ZMod N =>
          cyclicAPProduct (r + 2) N f
            (simplexCoordinateMoment (r + 2) N x)
            (-simplexCoordinateSum (r + 2) N x)) := by
      apply congrArg mean
      funext x
      exact apSimplexSystem_simplexWeight (r + 2) N f x
    _ =
        mean (fun y :
            (ZMod N × ZMod N) × (Fin r → ZMod N) =>
          cyclicAPProduct (r + 2) N f y.1.1 y.1.2) := by
      apply mean_equiv (simplexAPEquiv r N)
      intro x
      rfl
    _ =
        mean (fun p : ZMod N × ZMod N =>
          cyclicAPProduct (r + 2) N f p.1 p.2) := by
      exact mean_prod_fst
        (fun p : ZMod N × ZMod N =>
          cyclicAPProduct (r + 2) N f p.1 p.2)
    _ =
        mean₂ (fun a d =>
          cyclicAPProduct (r + 2) N f a d) := by
      exact mean_prod
        (fun a d => cyclicAPProduct (r + 2) N f a d)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

structure SimplexHypergraph {k : ℕ} (V : Fin k → Type*) where
  edge : (j : Fin k) → DeletedVector V j → Prop

namespace SimplexHypergraph

noncomputable def edgeFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (j : Fin k) :
    Finset (DeletedVector V j) := by
  classical
  exact Finset.univ.filter (H.edge j)

@[simp]
theorem mem_edgeFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (j : Fin k)
    (x : DeletedVector V j) :
    x ∈ H.edgeFinset j ↔ H.edge j x := by
  classical
  simp [edgeFinset]

noncomputable def simplexFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    Finset ((i : Fin k) → V i) := by
  classical
  exact Finset.univ.filter fun x => ∀ j, H.edge j (deleteCoordinate x j)

@[simp]
theorem mem_simplexFinset {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) (x : (i : Fin k) → V i) :
    x ∈ H.simplexFinset ↔
      ∀ j, H.edge j (deleteCoordinate x j) := by
  classical
  simp [simplexFinset]

noncomputable def toWeighted {k : ℕ} {V : Fin k → Type*}
    (H : SimplexHypergraph V) : WeightedSimplexSystem V := by
  classical
  exact
    { edgeWeight := fun j x => if H.edge j x then 1 else 0 }

@[simp]
theorem toWeighted_edgeWeight_of_edge {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    {j : Fin k} {x : DeletedVector V j}
    (hx : H.edge j x) :
    H.toWeighted.edgeWeight j x = 1 := by
  classical
  simp [toWeighted, hx]

@[simp]
theorem toWeighted_edgeWeight_of_not_edge {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    {j : Fin k} {x : DeletedVector V j}
    (hx : ¬H.edge j x) :
    H.toWeighted.edgeWeight j x = 0 := by
  classical
  simp [toWeighted, hx]

theorem toWeighted_edgeWeight_nonneg {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    (j : Fin k) (x : DeletedVector V j) :
    0 ≤ H.toWeighted.edgeWeight j x := by
  classical
  simp only [toWeighted]
  split <;> norm_num

theorem toWeighted_edgeWeight_le_one {k : ℕ}
    {V : Fin k → Type*} (H : SimplexHypergraph V)
    (j : Fin k) (x : DeletedVector V j) :
    H.toWeighted.edgeWeight j x ≤ 1 := by
  classical
  simp only [toWeighted]
  split <;> norm_num

theorem toWeighted_simplexWeight_eq_indicator {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    [∀ i, DecidableEq (V i)]
    (H : SimplexHypergraph V) (x : (i : Fin k) → V i) :
    H.toWeighted.simplexWeight x =
      finsetIndicator H.simplexFinset x := by
  classical
  by_cases hx : x ∈ H.simplexFinset
  · have hedges :
        ∀ j, H.edge j (deleteCoordinate x j) :=
      (H.mem_simplexFinset x).mp hx
    simp [WeightedSimplexSystem.simplexWeight, toWeighted,
      finsetIndicator, hx, hedges]
  · have hnot :
        ¬∀ j, H.edge j (deleteCoordinate x j) := by
      simpa using hx
    push Not at hnot
    obtain ⟨j, hj⟩ := hnot
    have hzero :
        ∏ i : Fin k,
            H.toWeighted.edgeWeight i (deleteCoordinate x i) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      exact toWeighted_edgeWeight_of_not_edge H hj
    rw [WeightedSimplexSystem.simplexWeight, hzero]
    exact (finsetIndicator_of_not_mem hx).symm

theorem toWeighted_simplexCount_eq_card_div {k : ℕ}
    {V : Fin k → Type*} [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V) :
    H.toWeighted.simplexCount =
      (H.simplexFinset.card : ℝ) /
        Fintype.card ((i : Fin k) → V i) := by
  classical
  rw [WeightedSimplexSystem.simplexCount]
  have hfun :
      H.toWeighted.simplexWeight =
        finsetIndicator H.simplexFinset := by
    funext x
    exact toWeighted_simplexWeight_eq_indicator H x
  rw [hfun, mean_finsetIndicator]

def IsSimplexCover {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : (j : Fin k) → Finset (DeletedVector V j)) : Prop :=
  ∀ x ∈ H.simplexFinset,
    ∃ j, deleteCoordinate x j ∈ deleted j

theorem isSimplexCover_iff {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H : SimplexHypergraph V)
    (deleted : (j : Fin k) → Finset (DeletedVector V j)) :
    H.IsSimplexCover deleted ↔
      ∀ x, (∀ j, deleteCoordinate x j ∉ deleted j) →
        ∃ j, ¬H.edge j (deleteCoordinate x j) := by
  classical
  constructor
  · intro hcover x hsurvives
    by_contra h
    push Not at h
    have hx : x ∈ H.simplexFinset := by
      simpa using h
    obtain ⟨j, hj⟩ := hcover x hx
    exact hsurvives j hj
  · intro hnosimplex x hx
    by_contra h
    push Not at h
    obtain ⟨j, hj⟩ := hnosimplex x h
    exact hj ((H.mem_simplexFinset x).mp hx j)

end SimplexHypergraph

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem prod_sub_prod_eq_sum_ordered
    {ι : Type*} [LinearOrder ι]
    (s : Finset ι) (f g : ι → ℝ) :
    (∏ i ∈ s, f i) - ∏ i ∈ s, g i =
      ∑ i ∈ s,
        (f i - g i) *
          (∏ j ∈ s with j < i, f j) *
          ∏ j ∈ s with i < j, g j := by
  have h :=
    Finset.prod_add_ordered s g (fun i => f i - g i)
  have hleft :
      (∏ i ∈ s, (g i + (f i - g i))) =
        ∏ i ∈ s, f i := by
    apply Finset.prod_congr rfl
    intro i _
    ring
  have hlower (i : ι) :
      (∏ j ∈ s with j < i,
          (g j + (f j - g j))) =
        ∏ j ∈ s with j < i, f j := by
    apply Finset.prod_congr rfl
    intro j _
    ring
  rw [hleft] at h
  simp_rw [hlower] at h
  linarith

def mixedSimplexTerm {k : ℕ} {V : Fin k → Type*}
    (H G : WeightedSimplexSystem V) (j : Fin k)
    (x : (i : Fin k) → V i) : ℝ :=
  (H.edgeWeight j (deleteCoordinate x j) -
      G.edgeWeight j (deleteCoordinate x j)) *
    (∏ i ∈ (Finset.univ : Finset (Fin k)) with i < j,
      H.edgeWeight i (deleteCoordinate x i)) *
    ∏ i ∈ (Finset.univ : Finset (Fin k)) with j < i,
      G.edgeWeight i (deleteCoordinate x i)

theorem simplexWeight_sub_eq_sum_mixed
    {k : ℕ} {V : Fin k → Type*}
    (H G : WeightedSimplexSystem V)
    (x : (i : Fin k) → V i) :
    H.simplexWeight x - G.simplexWeight x =
      ∑ j : Fin k, mixedSimplexTerm H G j x := by
  change
    (∏ j : Fin k,
        H.edgeWeight j (deleteCoordinate x j)) -
      ∏ j : Fin k,
        G.edgeWeight j (deleteCoordinate x j) =
      ∑ j : Fin k, mixedSimplexTerm H G j x
  simpa [mixedSimplexTerm] using
    prod_sub_prod_eq_sum_ordered Finset.univ
      (fun j : Fin k =>
        H.edgeWeight j (deleteCoordinate x j))
      (fun j : Fin k =>
        G.edgeWeight j (deleteCoordinate x j))

noncomputable def mixedSimplexCorrelation
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) (j : Fin k) : ℝ :=
  mean (mixedSimplexTerm H G j)

theorem simplexCount_sub_eq_sum_mixedCorrelation
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) :
    H.simplexCount - G.simplexCount =
      ∑ j : Fin k, mixedSimplexCorrelation H G j := by
  rw [WeightedSimplexSystem.simplexCount,
    WeightedSimplexSystem.simplexCount, ← mean_sub]
  calc
    mean (fun x => H.simplexWeight x - G.simplexWeight x) =
        mean (fun x =>
          ∑ j : Fin k, mixedSimplexTerm H G j x) := by
      apply congrArg mean
      funext x
      exact simplexWeight_sub_eq_sum_mixed H G x
    _ = ∑ j : Fin k, mean (mixedSimplexTerm H G j) :=
      mean_finset_sum Finset.univ
        (fun j => mixedSimplexTerm H G j)
    _ = ∑ j : Fin k, mixedSimplexCorrelation H G j := by
      rfl

theorem abs_simplexCount_sub_le_sum_mixedCorrelation
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) :
    |H.simplexCount - G.simplexCount| ≤
      ∑ j : Fin k, |mixedSimplexCorrelation H G j| := by
  rw [simplexCount_sub_eq_sum_mixedCorrelation]
  exact Finset.abs_sum_le_sum_abs _ _

def MixedSimplexCorrelationLe
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) (ε : ℝ) : Prop :=
  ∀ j, |mixedSimplexCorrelation H G j| ≤ ε

theorem simplexCount_abs_sub_le_of_mixedCorrelation
    {k : ℕ} {V : Fin k → Type*}
    [∀ i, Fintype (V i)]
    (H G : WeightedSimplexSystem V) {ε : ℝ}
    (h : MixedSimplexCorrelationLe H G ε) :
    |H.simplexCount - G.simplexCount| ≤ (k : ℝ) * ε := by
  calc
    |H.simplexCount - G.simplexCount| ≤
        ∑ j : Fin k, |mixedSimplexCorrelation H G j| :=
      abs_simplexCount_sub_le_sum_mixedCorrelation H G
    _ ≤ ∑ _j : Fin k, ε :=
      Finset.sum_le_sum fun j _ => h j
    _ = (k : ℝ) * ε := by
      simp

end Erdos3.FixedDensity

end

end OAI
