-- Modified for ProveIt: added `import OAI.Compat.*` lines (backported names); see lib/openai-math/README.md.
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.ZMod.Units
import Mathlib.RingTheory.Int.Basic
import OAI.Combinatorics.Progressions.FixedDensity.PolynomialApproximation
import OAI.Combinatorics.Progressions.FixedDensity.SimplexTelescoping
import OAI.Compat.BigOperators

namespace OAI

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def eraseCoordinate {G : Type*} {r : ℕ}
    (i : Fin r) (x : Fin r → G) : Fin (r - 1) → G := by
  cases r with
  | zero => exact Fin.elim0 i
  | succ n => exact fun j => x (i.succAbove j)

@[simp]
theorem eraseCoordinate_apply {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) (j : Fin n) :
    eraseCoordinate i x j = x (i.succAbove j) :=
  rfl

theorem eraseCoordinate_eq_removeNth
    {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (x : Fin (n + 1) → G) :
    eraseCoordinate i x = Fin.removeNth i x :=
  rfl

@[simp]
theorem eraseCoordinate_insertNth {G : Type*} {n : ℕ}
    (i : Fin (n + 1)) (a : G) (x : Fin n → G) :
    eraseCoordinate i (Fin.insertNth i a x) = x := by
  funext j
  simp only [eraseCoordinate_apply, Fin.insertNth_apply_succAbove]

abbrev CutTestFamily (G : Type*) (r : ℕ) :=
  (i : Fin r) → (Fin (r - 1) → G) → ℝ

def IsBoundedCutTest {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) : Prop :=
  (∀ i x, 0 ≤ u i x) ∧ (∀ i x, u i x ≤ 1)

theorem IsBoundedCutTest.nonneg
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) :
    ∀ i x, 0 ≤ u i x :=
  hu.1

theorem IsBoundedCutTest.le_one
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) :
    ∀ i x, u i x ≤ 1 :=
  hu.2

theorem isBoundedCutTest_const
    {G : Type*} {r : ℕ} {c : ℝ}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    IsBoundedCutTest (fun _ : Fin r => fun _ : Fin (r - 1) → G => c) :=
  ⟨fun _ _ => hc0, fun _ _ => hc1⟩

@[simp]
theorem isBoundedCutTest_zero
    {G : Type*} {r : ℕ} :
    IsBoundedCutTest
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (0 : ℝ)) :=
  isBoundedCutTest_const (by positivity) (by norm_num)

@[simp]
theorem isBoundedCutTest_one
    {G : Type*} {r : ℕ} :
    IsBoundedCutTest
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) :=
  isBoundedCutTest_const (by positivity) le_rfl

theorem IsBoundedCutTest.mono
    {G : Type*} {r : ℕ} {u v : CutTestFamily G r}
    (hu : IsBoundedCutTest u)
    (hv0 : ∀ i x, 0 ≤ v i x)
    (hvu : ∀ i x, v i x ≤ u i x) :
    IsBoundedCutTest v :=
  ⟨hv0, fun i x => (hvu i x).trans (hu.le_one i x)⟩

theorem IsBoundedCutTest.mul
    {G : Type*} {r : ℕ} {u v : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (hv : IsBoundedCutTest v) :
    IsBoundedCutTest (fun i x => u i x * v i x) := by
  constructor
  · exact fun i x => mul_nonneg (hu.nonneg i x) (hv.nonneg i x)
  · exact fun coordinate point =>
      (mul_le_of_le_one_left (hv.nonneg coordinate point)
        (hu.le_one coordinate point)).trans (hv.le_one coordinate point)

noncomputable def cutCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x : Fin r → G =>
    (f (∑ i, x i) - g (∑ i, x i)) *
      ∏ i, u i (eraseCoordinate i x)

def CutDiscrepancyLe
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (ε : ℝ) : Prop :=
  ∀ u : CutTestFamily G r,
    (∀ i x, 0 ≤ u i x) →
    (∀ i x, u i x ≤ 1) →
    |cutCorrelation r f g u| ≤ ε

theorem CutDiscrepancyLe.apply_bounded
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε)
    (u : CutTestFamily G r) (hu : IsBoundedCutTest u) :
    |cutCorrelation r f g u| ≤ ε :=
  h u hu.nonneg hu.le_one

@[simp]
theorem cutCorrelation_self
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f f u = 0 := by
  simp [cutCorrelation]

theorem cutCorrelation_swap
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r g f u = -cutCorrelation r f g u := by
  calc
    cutCorrelation r g f u =
        mean (fun x : Fin r → G =>
          (-1 : ℝ) *
            ((f (∑ i, x i) - g (∑ i, x i)) *
              ∏ i, u i (eraseCoordinate i x))) := by
      apply congrArg mean
      funext x
      ring
    _ = (-1 : ℝ) *
        mean (fun x : Fin r → G =>
          (f (∑ i, x i) - g (∑ i, x i)) *
            ∏ i, u i (eraseCoordinate i x)) :=
      mean_smul _ _
    _ = -cutCorrelation r f g u := by
      simp [cutCorrelation]

theorem cutCorrelation_add_middle
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g h : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f h u =
      cutCorrelation r f g u + cutCorrelation r g h u := by
  rw [cutCorrelation, cutCorrelation, cutCorrelation, ← mean_add]
  apply congrArg mean
  funext x
  ring

theorem CutDiscrepancyLe.mono
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε ε' : ℝ}
    (h : CutDiscrepancyLe r f g ε) (hε : ε ≤ ε') :
    CutDiscrepancyLe r f g ε' := by
  intro u hu0 hu1
  exact (h u hu0 hu1).trans hε

theorem CutDiscrepancyLe.refl
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) :
    CutDiscrepancyLe r f f 0 := by
  intro u _ _
  simp

theorem CutDiscrepancyLe.refl_of_nonneg
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) {ε : ℝ} (hε : 0 ≤ ε) :
    CutDiscrepancyLe r f f ε :=
  (CutDiscrepancyLe.refl r f).mono hε

theorem CutDiscrepancyLe.of_eq
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} (hfg : f = g) :
    CutDiscrepancyLe r f g 0 := by
  subst g
  exact CutDiscrepancyLe.refl r f

theorem CutDiscrepancyLe.symm
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε) :
    CutDiscrepancyLe r g f ε := by
  intro u hu0 hu1
  rw [cutCorrelation_swap, abs_neg]
  exact h u hu0 hu1

theorem CutDiscrepancyLe.triangle
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g h : G → ℝ} {ε δ : ℝ}
    (hfg : CutDiscrepancyLe r f g ε)
    (hgh : CutDiscrepancyLe r g h δ) :
    CutDiscrepancyLe r f h (ε + δ) := by
  intro u hu0 hu1
  calc
    |cutCorrelation r f h u| =
        |cutCorrelation r f g u + cutCorrelation r g h u| := by
      rw [cutCorrelation_add_middle]
    _ ≤ |cutCorrelation r f g u| + |cutCorrelation r g h u| :=
      abs_add_le _ _
    _ ≤ ε + δ :=
      add_le_add (hfg u hu0 hu1) (hgh u hu0 hu1)

theorem CutDiscrepancyLe.epsilon_nonneg
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε) :
    0 ≤ ε := by
  exact (abs_nonneg (cutCorrelation r f g
    (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)))).trans
      (h (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ))
        (fun _ _ => by norm_num) (fun _ _ => le_rfl))

theorem mean_add_right
    {G : Type*} [Fintype G] [AddCommGroup G]
    (h : G → ℝ) (c : G) :
    mean (fun x => h (x + c)) = mean h := by
  unfold mean
  exact Fintype.expect_equiv (Equiv.addRight c)
    (fun x => h (x + c)) h (fun _ => rfl)

theorem mean_sum_fin_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (h : G → ℝ) :
    mean (fun x : Fin (n + 1) → G => h (∑ i, x i)) = mean h := by
  calc
    mean (fun x : Fin (n + 1) → G => h (∑ i, x i)) =
        mean (fun p : G × (Fin n → G) =>
          h (p.1 + ∑ i, p.2 i)) := by
      unfold mean
      apply Fintype.expect_equiv
        (Fin.insertNthEquiv (fun _ : Fin (n + 1) => G) 0).symm
      intro x
      congr 1
      rw [Fin.sum_univ_succ]
      rfl
    _ = mean₂ (fun a : G => fun y : Fin n → G =>
          h (a + ∑ i, y i)) := by
      simpa [mean, mean₂] using
        (Finset.expect_product (Finset.univ : Finset G)
          (Finset.univ : Finset (Fin n → G))
          (fun p : G × (Fin n → G) => h (p.1 + ∑ i, p.2 i)))
    _ = mean₂ (fun y : Fin n → G => fun a : G =>
          h (a + ∑ i, y i)) := mean₂_comm _
    _ = mean (fun _ : Fin n → G => mean h) := by
      apply congrArg mean
      funext y
      exact mean_add_right h (∑ i, y i)
    _ = mean h := mean_const _

theorem mean_sum_fin_of_pos
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) (h : G → ℝ) :
    mean (fun x : Fin r → G => h (∑ i, x i)) = mean h := by
  cases r with
  | zero => simp at hr
  | succ n => exact mean_sum_fin_succ n h

@[simp]
theorem cutCorrelation_one
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) :
    cutCorrelation r f g
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
    mean (fun x : Fin r → G =>
      f (∑ i, x i) - g (∑ i, x i)) := by
  simp [cutCorrelation]

theorem cutCorrelation_one_eq_mean_sub
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) (f g : G → ℝ) :
    cutCorrelation r f g
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
    mean f - mean g := by
  calc
    cutCorrelation r f g
        (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) =
      mean (fun x : Fin r → G =>
        f (∑ i, x i) - g (∑ i, x i)) :=
      cutCorrelation_one r f g
    _ = mean (fun z : G => f z - g z) :=
      mean_sum_fin_of_pos hr (fun z => f z - g z)
    _ = mean f - mean g := mean_sub f g

theorem CutDiscrepancyLe.abs_mean_sub_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε) (hr : 0 < r) :
    |mean f - mean g| ≤ ε := by
  have hone := h
    (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ))
    (fun _ _ => by norm_num) (fun _ _ => le_rfl)
  simpa [cutCorrelation_one_eq_mean_sub hr f g] using hone

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

noncomputable def mulAddEquivOfIsUnit
    {R : Type*} [CommRing R] (a : R) (ha : IsUnit a) :
    R ≃+ R :=
  DistribMulAction.toAddEquiv R ha.unit

@[simp]
theorem mulAddEquivOfIsUnit_apply
    {R : Type*} [CommRing R] (a : R) (ha : IsUnit a)
    (x : R) :
    mulAddEquivOfIsUnit a ha x = a * x := by
  change (ha.unit : R) * x = a * x
  rw [IsUnit.unit_spec]

def coordinatewiseAddEquiv
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G) :
    (ι → G) ≃ (ι → G) where
  toFun x i := e i (x i)
  invFun x i := (e i).symm (x i)
  left_inv x := by
    funext i
    exact (e i).symm_apply_apply (x i)
  right_inv x := by
    funext i
    exact (e i).apply_symm_apply (x i)

@[simp]
theorem coordinatewiseAddEquiv_apply
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G)
    (x : ι → G) (i : ι) :
    coordinatewiseAddEquiv e x i = e i (x i) :=
  rfl

@[simp]
theorem coordinatewiseAddEquiv_symm_apply
    {ι G : Type*} [AddCommGroup G] (e : ι → G ≃+ G)
    (x : ι → G) (i : ι) :
    (coordinatewiseAddEquiv e).symm x i =
      (e i).symm (x i) :=
  rfl

def pullCutTest
    {G : Type*} [AddCommGroup G] {r : ℕ}
    (e : Fin r → G ≃+ G) (u : CutTestFamily G r) :
    CutTestFamily G r := by
  cases r with
  | zero =>
      exact fun i => Fin.elim0 i
  | succ n =>
      exact fun i y =>
        u i (fun t => (e (i.succAbove t)).symm (y t))

theorem IsBoundedCutTest.pull
    {G : Type*} [AddCommGroup G] {r : ℕ}
    {e : Fin r → G ≃+ G} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) :
    IsBoundedCutTest (pullCutTest e u) := by
  constructor
  · intro i x
    cases r with
    | zero => exact Fin.elim0 i
    | succ n =>
        exact hu.nonneg i
          (fun t => (e (i.succAbove t)).symm (x t))
  · intro i x
    cases r with
    | zero => exact Fin.elim0 i
    | succ n =>
        exact hu.le_one i
          (fun t => (e (i.succAbove t)).symm (x t))

noncomputable def linearCutCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (e : Fin r → G ≃+ G)
    (f g : G → ℝ) (u : CutTestFamily G r) : ℝ :=
  mean fun x : Fin r → G =>
    (f (∑ i, e i (x i)) -
        g (∑ i, e i (x i))) *
      ∏ i, u i (eraseCoordinate i x)

theorem linearCutCorrelation_eq_cutCorrelation
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (e : Fin r → G ≃+ G)
    (f g : G → ℝ) (u : CutTestFamily G r) :
    linearCutCorrelation r e f g u =
      cutCorrelation r f g (pullCutTest e u) := by
  cases r with
  | zero =>
      simp [linearCutCorrelation, cutCorrelation, pullCutTest]
  | succ n =>
      unfold linearCutCorrelation cutCorrelation mean
      apply Fintype.expect_equiv (coordinatewiseAddEquiv e)
      intro x
      congr 1
      apply Finset.prod_congr rfl
      intro i _
      change
        u i (eraseCoordinate i x) =
          u i (fun t =>
            (e (i.succAbove t)).symm
              (eraseCoordinate i
                (coordinatewiseAddEquiv e x) t))
      congr 1
      funext t
      simp

theorem CutDiscrepancyLe.abs_linearCutCorrelation_le
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (h : CutDiscrepancyLe r f g ε)
    (e : Fin r → G ≃+ G)
    (u : CutTestFamily G r) (hu : IsBoundedCutTest u) :
    |linearCutCorrelation r e f g u| ≤ ε := by
  rw [linearCutCorrelation_eq_cutCorrelation]
  exact h.apply_bounded (pullCutTest e u) hu.pull

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

def sumFiberTuple {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) : Fin (n + 1) → G :=
  Fin.cons (z - ∑ i, y i) y

@[simp]
theorem sumFiberTuple_zero {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) :
    sumFiberTuple n z y 0 = z - ∑ i, y i :=
  rfl

@[simp]
theorem sumFiberTuple_succ {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) (i : Fin n) :
    sumFiberTuple n z y i.succ = y i :=
  rfl

@[simp]
theorem sum_sumFiberTuple {G : Type*} [AddCommGroup G]
    (n : ℕ) (z : G) (y : Fin n → G) :
    ∑ i, sumFiberTuple n z y i = z := by
  simp [sumFiberTuple, Fin.sum_univ_succ]

def sumFiberEquiv (G : Type*) [AddCommGroup G] (n : ℕ) :
    (Fin (n + 1) → G) ≃ G × (Fin n → G) where
  toFun x := (∑ i, x i, Fin.tail x)
  invFun p := sumFiberTuple n p.1 p.2
  left_inv x := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · change (∑ k, x k) - ∑ j, Fin.tail x j = x 0
      rw [Fin.sum_univ_succ]
      change x 0 + (∑ j : Fin n, x j.succ) -
        ∑ j : Fin n, x j.succ = x 0
      abel
    · rfl
  right_inv p := by
    apply Prod.ext
    · exact sum_sumFiberTuple n p.1 p.2
    · funext j
      rfl

noncomputable def zeroFiberDelta
    {G : Type*} [Fintype G] [AddCommGroup G] (z : G) : ℝ := by
  classical
  exact if z = 0 then (Fintype.card G : ℝ) else 0

@[simp]
theorem zeroFiberDelta_zero
    {G : Type*} [Fintype G] [AddCommGroup G] :
    zeroFiberDelta (G := G) 0 = Fintype.card G := by
  classical
  simp [zeroFiberDelta]

@[simp]
theorem zeroFiberDelta_of_ne
    {G : Type*} [Fintype G] [AddCommGroup G]
    {z : G} (hz : z ≠ 0) :
    zeroFiberDelta z = 0 := by
  classical
  simp [zeroFiberDelta, hz]

theorem zeroFiberDelta_nonneg
    {G : Type*} [Fintype G] [AddCommGroup G] (z : G) :
    0 ≤ zeroFiberDelta z := by
  classical
  simp only [zeroFiberDelta]
  split_ifs
  · positivity
  · exact le_rfl

noncomputable def fiberConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (w : (Fin r → G) → ℝ) (z : G) : ℝ := by
  cases r with
  | zero =>
      exact zeroFiberDelta z * w (fun i => Fin.elim0 i)
  | succ n =>
      exact mean fun y : Fin n → G => w (sumFiberTuple n z y)

@[simp]
theorem fiberConvolution_arity_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (w : (Fin 0 → G) → ℝ) (z : G) :
    fiberConvolution 0 w z =
      zeroFiberDelta z * w (fun i => Fin.elim0 i) :=
  rfl

@[simp]
theorem fiberConvolution_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (w : (Fin (n + 1) → G) → ℝ) (z : G) :
    fiberConvolution (n + 1) w z =
      mean fun y : Fin n → G => w (sumFiberTuple n z y) :=
  rfl

def cutTestProduct {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) (x : Fin r → G) : ℝ :=
  ∏ i, u i (eraseCoordinate i x)

@[simp]
theorem cutTestProduct_one {G : Type*} {r : ℕ} (x : Fin r → G) :
    cutTestProduct
      (fun _ : Fin r => fun _ : Fin (r - 1) → G => (1 : ℝ)) x = 1 := by
  simp [cutTestProduct]

theorem cutTestProduct_nonneg
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (x : Fin r → G) :
    0 ≤ cutTestProduct u x :=
  Finset.prod_nonneg fun i _ => hu.nonneg i (eraseCoordinate i x)

theorem cutTestProduct_le_one
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (x : Fin r → G) :
    cutTestProduct u x ≤ 1 :=
  Finset.prod_le_one₀
    (fun i _ => hu.nonneg i (eraseCoordinate i x))
    (fun i _ => hu.le_one i (eraseCoordinate i x))

theorem cutTestProduct_mem_Icc
    {G : Type*} {r : ℕ} {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (x : Fin r → G) :
    cutTestProduct u x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨cutTestProduct_nonneg hu x, cutTestProduct_le_one hu x⟩

@[simp]
theorem cutTestProduct_mul
    {G : Type*} {r : ℕ} (u v : CutTestFamily G r)
    (x : Fin r → G) :
    cutTestProduct (fun i y => u i y * v i y) x =
      cutTestProduct u x * cutTestProduct v x := by
  simp [cutTestProduct, Finset.prod_mul_distrib]

noncomputable def generalizedConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (u : CutTestFamily G r) (z : G) : ℝ :=
  fiberConvolution r (cutTestProduct u) z

@[simp]
theorem generalizedConvolution_arity_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (u : CutTestFamily G 0) (z : G) :
    generalizedConvolution 0 u z = zeroFiberDelta z := by
  simp [generalizedConvolution, cutTestProduct]

@[simp]
theorem generalizedConvolution_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (u : CutTestFamily G (n + 1)) (z : G) :
    generalizedConvolution (n + 1) u z =
      mean fun y : Fin n → G =>
        cutTestProduct u (sumFiberTuple n z y) :=
  rfl

theorem fiberConvolution_add
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (w v : (Fin r → G) → ℝ) (z : G) :
    fiberConvolution r (w + v) z =
      fiberConvolution r w z + fiberConvolution r v z := by
  cases r with
  | zero =>
      rw [fiberConvolution_arity_zero, fiberConvolution_arity_zero,
        fiberConvolution_arity_zero]
      simp [mul_add]
  | succ n =>
      rw [fiberConvolution_succ, fiberConvolution_succ,
        fiberConvolution_succ]
      exact mean_add
        (fun y : Fin n → G => w (sumFiberTuple n z y))
        (fun y : Fin n → G => v (sumFiberTuple n z y))

theorem fiberConvolution_smul
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (c : ℝ) (w : (Fin r → G) → ℝ) (z : G) :
    fiberConvolution r (fun x => c * w x) z =
      c * fiberConvolution r w z := by
  cases r with
  | zero =>
      rw [fiberConvolution_arity_zero, fiberConvolution_arity_zero]
      ring
  | succ n =>
      rw [fiberConvolution_succ, fiberConvolution_succ]
      exact mean_smul c (fun y : Fin n → G =>
        w (sumFiberTuple n z y))

@[simp]
theorem fiberConvolution_zero_weight
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (z : G) :
    fiberConvolution r (fun _ => (0 : ℝ)) z = 0 := by
  simpa using fiberConvolution_smul r 0 (fun _ => (1 : ℝ)) z

@[simp]
theorem fiberConvolution_const_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (c : ℝ) (z : G) :
    fiberConvolution (n + 1) (fun _ => c) z = c := by
  rw [fiberConvolution_succ]
  exact mean_const c

theorem fiberConvolution_linearCombination
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (a b : ℝ) (w v : (Fin r → G) → ℝ) (z : G) :
    fiberConvolution r (fun x => a * w x + b * v x) z =
      a * fiberConvolution r w z + b * fiberConvolution r v z := by
  change fiberConvolution r
    ((fun x => a * w x) + (fun x => b * v x)) z = _
  rw [fiberConvolution_add, fiberConvolution_smul,
    fiberConvolution_smul]

theorem fiberConvolution_nonneg_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    (hw : ∀ x, 0 ≤ w x) (z : G) :
    0 ≤ fiberConvolution (n + 1) w z := by
  rw [fiberConvolution_succ]
  exact mean_nonneg fun y => hw (sumFiberTuple n z y)

theorem fiberConvolution_le_one_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w : (Fin (n + 1) → G) → ℝ}
    (hw : ∀ x, w x ≤ 1) (z : G) :
    fiberConvolution (n + 1) w z ≤ 1 := by
  rw [fiberConvolution_succ]
  exact mean_le_of_le_const fun y => hw (sumFiberTuple n z y)

theorem fiberConvolution_mono_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {w v : (Fin (n + 1) → G) → ℝ}
    (hwv : ∀ x, w x ≤ v x) (z : G) :
    fiberConvolution (n + 1) w z ≤ fiberConvolution (n + 1) v z := by
  rw [fiberConvolution_succ, fiberConvolution_succ]
  exact mean_mono fun y => hwv (sumFiberTuple n z y)

theorem generalizedConvolution_nonneg_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {u : CutTestFamily G (n + 1)}
    (hu : IsBoundedCutTest u) (z : G) :
    0 ≤ generalizedConvolution (n + 1) u z :=
  fiberConvolution_nonneg_succ (cutTestProduct_nonneg hu) z

theorem generalizedConvolution_le_one_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    {n : ℕ} {u : CutTestFamily G (n + 1)}
    (hu : IsBoundedCutTest u) (z : G) :
    generalizedConvolution (n + 1) u z ≤ 1 :=
  fiberConvolution_le_one_succ (cutTestProduct_le_one hu) z

theorem generalizedConvolution_mem_Icc
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (z : G) :
    generalizedConvolution r u z ∈ Set.Icc (0 : ℝ) 1 := by
  cases r with
  | zero => simp at hr
  | succ n =>
      exact ⟨generalizedConvolution_nonneg_succ hu z,
        generalizedConvolution_le_one_succ hu z⟩

theorem generalizedConvolution_nonneg
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (z : G) :
    0 ≤ generalizedConvolution r u z :=
  (generalizedConvolution_mem_Icc hr hu z).1

theorem generalizedConvolution_le_one
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) {u : CutTestFamily G r}
    (hu : IsBoundedCutTest u) (z : G) :
    generalizedConvolution r u z ≤ 1 :=
  (generalizedConvolution_mem_Icc hr hu z).2

@[simp]
theorem generalizedConvolution_one_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (z : G) :
    generalizedConvolution (n + 1)
      (fun _ : Fin (n + 1) => fun _ : Fin n → G => (1 : ℝ)) z = 1 := by
  rw [generalizedConvolution_succ]
  calc
    mean (fun y : Fin n → G =>
        cutTestProduct
          (fun _ : Fin (n + 1) => fun _ : Fin n → G => (1 : ℝ))
          (sumFiberTuple n z y)) =
        mean (fun _ : Fin n → G => (1 : ℝ)) := by
      apply congrArg mean
      funext y
      exact cutTestProduct_one (sumFiberTuple n z y)
    _ = 1 := mean_const 1

@[simp]
theorem generalizedConvolution_zero_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (z : G) :
    generalizedConvolution (n + 1)
      (fun _ : Fin (n + 1) => fun _ : Fin n → G => (0 : ℝ)) z = 0 := by
  rw [generalizedConvolution_succ]
  simp [cutTestProduct]

theorem fiberConvolution_pairing_zero
    {G : Type*} [Fintype G] [AddCommGroup G]
    (w : (Fin 0 → G) → ℝ) (h : G → ℝ) :
    mean (fun x : Fin 0 → G => h (∑ i, x i) * w x) =
      mean (fun z : G => h z * fiberConvolution 0 w z) := by
  classical
  let e : Fin 0 → G := fun i => Fin.elim0 i
  calc
    mean (fun x : Fin 0 → G => h (∑ i, x i) * w x) =
        h 0 * w e := by
      have heq :
          (fun x : Fin 0 → G => h (∑ i, x i) * w x) =
            (fun _ : Fin 0 → G => h 0 * w e) := by
        funext x
        have hx : x = e := Subsingleton.elim _ _
        subst x
        simp [e]
      rw [heq]
      exact mean_const _
    _ = mean (fun z : G => h z * fiberConvolution 0 w z) := by
      rw [mean, Fintype.expect_eq_sum_div_card]
      simp [fiberConvolution_arity_zero, zeroFiberDelta, e]
      field_simp

theorem fiberConvolution_pairing_succ
    {G : Type*} [Fintype G] [AddCommGroup G]
    (n : ℕ) (w : (Fin (n + 1) → G) → ℝ) (h : G → ℝ) :
    mean (fun x : Fin (n + 1) → G => h (∑ i, x i) * w x) =
      mean (fun z : G => h z * fiberConvolution (n + 1) w z) := by
  calc
    mean (fun x : Fin (n + 1) → G => h (∑ i, x i) * w x) =
        mean (fun p : G × (Fin n → G) =>
          h p.1 * w (sumFiberTuple n p.1 p.2)) := by
      unfold mean
      apply Fintype.expect_equiv (sumFiberEquiv G n)
      intro x
      change h (∑ i, x i) * w x =
        h (∑ i, x i) *
          w (sumFiberTuple n (∑ i, x i) (Fin.tail x))
      have hx : sumFiberTuple n (∑ i, x i) (Fin.tail x) = x :=
        (sumFiberEquiv G n).left_inv x
      rw [hx]
    _ = mean₂ (fun z : G => fun y : Fin n → G =>
          h z * w (sumFiberTuple n z y)) := by
      simpa [mean, mean₂] using
        (Finset.expect_product (Finset.univ : Finset G)
          (Finset.univ : Finset (Fin n → G))
          (fun p : G × (Fin n → G) =>
            h p.1 * w (sumFiberTuple n p.1 p.2)))
    _ = mean (fun z : G =>
          h z * mean (fun y : Fin n → G =>
            w (sumFiberTuple n z y))) := by
      apply congrArg mean
      funext z
      exact mean_smul (h z) _
    _ = mean (fun z : G =>
          h z * fiberConvolution (n + 1) w z) := by
      rfl

theorem fiberConvolution_pairing
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (w : (Fin r → G) → ℝ) (h : G → ℝ) :
    mean (fun x : Fin r → G => h (∑ i, x i) * w x) =
      mean (fun z : G => h z * fiberConvolution r w z) := by
  cases r with
  | zero => exact fiberConvolution_pairing_zero w h
  | succ n => exact fiberConvolution_pairing_succ n w h

theorem mean_fiberConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (w : (Fin r → G) → ℝ) :
    mean (fiberConvolution r w) = mean w := by
  have hpair := fiberConvolution_pairing r w (fun _ : G => (1 : ℝ))
  simpa using hpair.symm

theorem mean_generalizedConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (u : CutTestFamily G r) :
    mean (generalizedConvolution r u) = mean (cutTestProduct u) :=
  mean_fiberConvolution r (cutTestProduct u)

theorem cutCorrelation_eq_mean_mul_generalizedConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f g u =
      mean (fun z : G =>
        (f z - g z) * generalizedConvolution r u z) := by
  exact fiberConvolution_pairing r (cutTestProduct u)
    (fun z => f z - g z)

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators

theorem apCoefficient_isUnit_of_coprime_factorial
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) :
    IsUnit (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) := by
  rw [ZMod.coe_int_isUnit_iff_isCoprime,
    Int.isCoprime_iff_nat_coprime]
  have hdiff :
      (i : ℤ) - (j : ℤ) ≠ 0 := by
    intro h
    apply hij
    apply Fin.ext
    exact_mod_cast sub_eq_zero.mp h
  have hpos :
      0 < Int.natAbs ((i : ℤ) - (j : ℤ)) :=
    Int.natAbs_pos.mpr hdiff
  have hle :
      Int.natAbs ((i : ℤ) - (j : ℤ)) ≤ k - 1 := by
    have hi : (i : ℕ) ≤ k - 1 := by omega
    have hj : (j : ℕ) ≤ k - 1 := by omega
    exact Int.natAbs_coe_sub_coe_le_of_le hi hj
  have hdvd :
      Int.natAbs ((i : ℤ) - (j : ℤ)) ∣
        Nat.factorial (k - 1) :=
    Nat.dvd_factorial hpos hle
  simpa using hN.coprime_dvd_right hdvd

noncomputable def apCoefficientAddEquiv
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) :
    ZMod N ≃+ ZMod N :=
  mulAddEquivOfIsUnit
    ((((i : ℤ) - (j : ℤ) : ℤ) : ZMod N))
    (apCoefficient_isUnit_of_coprime_factorial hN i j hij)

@[simp]
theorem apCoefficientAddEquiv_apply
    {k N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial (k - 1)))
    (i j : Fin k) (hij : i ≠ j) (x : ZMod N) :
    apCoefficientAddEquiv hN i j hij x =
      (((i : ℤ) - (j : ℤ) : ℤ) : ZMod N) * x := by
  simp [apCoefficientAddEquiv]

noncomputable def finSuccAboveEquiv {n : ℕ} (j : Fin (n + 1)) :
    Fin n ≃ {i : Fin (n + 1) // i ≠ j} :=
  Equiv.ofBijective
    (fun t : Fin n => ⟨j.succAbove t, Fin.succAbove_ne j t⟩)
    ⟨by
      intro a b hab
      apply Fin.succAbove_right_injective
      exact congrArg Subtype.val hab,
    by
      intro i
      obtain ⟨t, ht⟩ := Fin.exists_succAbove_eq i.2
      exact ⟨t, Subtype.ext ht⟩⟩

@[simp]
theorem finSuccAboveEquiv_apply_val
    {n : ℕ} (j : Fin (n + 1)) (t : Fin n) :
    (finSuccAboveEquiv j t).1 = j.succAbove t :=
  rfl

noncomputable def finTupleToDeletedVector
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G) :
    DeletedVector (fun _ : Fin (n + 1) => G) j :=
  fun i => y ((finSuccAboveEquiv j).symm i)

@[simp]
theorem finTupleToDeletedVector_succAbove
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1))
    (y : Fin n → G)
    (t : Fin n) :
    finTupleToDeletedVector j y
        (finSuccAboveEquiv j t) =
      y t := by
  simp [finTupleToDeletedVector]

theorem apSimplexForm_finTupleToDeletedVector
    (n N : ℕ) (j : Fin (n + 1))
    (y : Fin n → ZMod N) :
    apSimplexForm (n + 1) N j
        (finTupleToDeletedVector j y) =
      ∑ t : Fin n,
        ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
          ZMod N) * y t) := by
  rw [apSimplexForm]
  symm
  exact Fintype.sum_equiv (finSuccAboveEquiv j)
    (fun t : Fin n =>
      ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
        ZMod N) * y t))
    (fun i : {i : Fin (n + 1) // i ≠ j} =>
      ((((i.1 : ℤ) - (j : ℤ) : ℤ) : ZMod N) *
        finTupleToDeletedVector j y i))
    (fun t => by simp)

theorem deleteCoordinate_eq_finTupleToDeletedVector
    {n : ℕ} {G : Type*}
    (j : Fin (n + 1)) (x : Fin (n + 1) → G) :
    deleteCoordinate x j =
      finTupleToDeletedVector j
        (fun t => x (j.succAbove t)) := by
  funext i
  change x i.1 =
    x (j.succAbove ((finSuccAboveEquiv j).symm i))
  apply congrArg x
  have hi :=
    congrArg Subtype.val
      ((finSuccAboveEquiv j).apply_symm_apply i)
  exact hi.symm

theorem apSimplexForm_deleteCoordinate_eq_weightedSum
    (n N : ℕ) (j : Fin (n + 1))
    (x : Fin (n + 1) → ZMod N) :
    apSimplexForm (n + 1) N j (deleteCoordinate x j) =
      ∑ t : Fin n,
        ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
          ZMod N) * x (j.succAbove t)) := by
  rw [deleteCoordinate_eq_finTupleToDeletedVector,
    apSimplexForm_finTupleToDeletedVector]

noncomputable def apFaceScalingEquiv
    {n N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial n))
    (j : Fin (n + 1)) (t : Fin n) :
    ZMod N ≃+ ZMod N :=
  apCoefficientAddEquiv
    (by simpa using hN) (j.succAbove t) j
    (Fin.succAbove_ne j t)

@[simp]
theorem apFaceScalingEquiv_apply
    {n N : ℕ}
    (hN : Nat.Coprime N (Nat.factorial n))
    (j : Fin (n + 1)) (t : Fin n) (x : ZMod N) :
    apFaceScalingEquiv hN j t x =
      ((((j.succAbove t : ℤ) - (j : ℤ) : ℤ) :
        ZMod N) * x) := by
  simp [apFaceScalingEquiv]

end Erdos3.FixedDensity

end

section

namespace Erdos3.FixedDensity

open scoped BigOperators Polynomial

def bernoulliAssignmentWeight
    {κ : Type*} [Fintype κ]
    (p : κ → ℝ) (b : κ → Bool) : ℝ :=
  ∏ i, if b i then p i else 1 - p i

def booleanValue {κ : Type*} (b : κ → Bool) (i : κ) : ℝ :=
  if b i then 1 else 0

theorem bernoulliAssignmentWeight_nonneg
    {κ : Type*} [Fintype κ]
    {p : κ → ℝ}
    (hp0 : ∀ i, 0 ≤ p i) (hp1 : ∀ i, p i ≤ 1)
    (b : κ → Bool) :
    0 ≤ bernoulliAssignmentWeight p b := by
  apply Finset.prod_nonneg
  intro i _
  by_cases hi : b i
  · simpa [hi] using hp0 i
  · simp only [hi, Bool.false_eq_true,
      ↓reduceIte]
    linarith [hp1 i]

theorem sum_bernoulliAssignmentWeight
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) :
    ∑ b : κ → Bool, bernoulliAssignmentWeight p b = 1 := by
  change
    (∑ b : κ → Bool,
      ∏ i, if b i then p i else 1 - p i) = 1
  calc
    (∑ b : κ → Bool,
        ∏ i, if b i then p i else 1 - p i) =
        ∏ i, ∑ bit : Bool,
          if bit then p i else 1 - p i :=
      (Fintype.prod_sum
        (fun i : κ => fun bit : Bool =>
          if bit then p i else 1 - p i)).symm
    _ = ∏ _i : κ, (1 : ℝ) := by
      apply Fintype.prod_congr
      intro i
      simp
    _ = 1 := by simp

theorem sum_bernoulliAssignmentWeight_mul_selected
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (p : κ → ℝ) (s : Finset κ) :
    ∑ b : κ → Bool,
        bernoulliAssignmentWeight p b *
          ∏ i ∈ s, booleanValue b i =
      ∏ i ∈ s, p i := by
  calc
    (∑ b : κ → Bool,
        bernoulliAssignmentWeight p b *
          ∏ i ∈ s, booleanValue b i) =
        ∑ b : κ → Bool,
          ∏ i,
            (if b i then p i else 1 - p i) *
              (if i ∈ s then booleanValue b i else 1) := by
      apply Fintype.sum_congr
      intro b
      have hselected :
          (∏ i ∈ s, booleanValue b i) =
            ∏ i, if i ∈ s then booleanValue b i else 1 :=
        (Fintype.prod_ite_mem s
          (fun i => booleanValue b i)).symm
      rw [bernoulliAssignmentWeight, hselected]
      rw [← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ bit : Bool,
          (if bit then p i else 1 - p i) *
            (if i ∈ s then
              (if bit then (1 : ℝ) else 0) else 1) :=
      (Fintype.prod_sum
        (fun i : κ => fun bit : Bool =>
          (if bit then p i else 1 - p i) *
            (if i ∈ s then
              (if bit then (1 : ℝ) else 0) else 1))).symm
    _ = ∏ i, if i ∈ s then p i else 1 := by
      apply Fintype.prod_congr
      intro i
      by_cases hi : i ∈ s <;> simp [hi]
    _ = ∏ i ∈ s, p i := by
      exact Fintype.prod_ite_mem s p

theorem sum_bernoulliAssignmentWeight_mul_embedding
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    [DecidableEq κ]
    (p : κ → ℝ) (e : ι ↪ κ) :
    ∑ b : κ → Bool,
        bernoulliAssignmentWeight p b *
          ∏ i : ι, booleanValue b (e i) =
      ∏ i : ι, p (e i) := by
  simpa only [Finset.prod_map, Finset.mem_univ, true_and,
    Finset.coe_univ, Function.Embedding.coeFn_mk] using
    (sum_bernoulliAssignmentWeight_mul_selected p
      (Finset.univ.map e))

abbrev CutTestCoordinate (G : Type*) (r : ℕ) :=
  Fin r × (Fin (r - 1) → G)

abbrev BooleanCutAssignment (G : Type*) (r : ℕ) :=
  CutTestCoordinate G r → Bool

def cutTestFamilyOfBooleanAssignment
    {G : Type*} {r : ℕ}
    (b : BooleanCutAssignment G r) :
    CutTestFamily G r :=
  fun i y => booleanValue b ⟨i, y⟩

theorem cutTestFamilyOfBooleanAssignment_bounded
    {G : Type*} {r : ℕ}
    (b : BooleanCutAssignment G r) :
    IsBoundedCutTest (cutTestFamilyOfBooleanAssignment b) := by
  constructor <;> intro i y <;>
    unfold cutTestFamilyOfBooleanAssignment booleanValue <;>
    split <;> norm_num

def cutTestCoordinateValue
    {G : Type*} {r : ℕ}
    (u : CutTestFamily G r) :
    CutTestCoordinate G r → ℝ :=
  fun q => u q.1 q.2

def usedCutTestCoordinateEmbedding
    {G : Type*} {r : ℕ} (x : Fin r → G) :
    Fin r ↪ CutTestCoordinate G r where
  toFun i := ⟨i, eraseCoordinate i x⟩
  inj' := by
    intro i j h
    exact congrArg Prod.fst h

@[simp]
theorem usedCutTestCoordinateEmbedding_apply
    {G : Type*} {r : ℕ} (x : Fin r → G) (i : Fin r) :
    usedCutTestCoordinateEmbedding x i =
      (i, eraseCoordinate i x) :=
  rfl

theorem cutTestProduct_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G] {r : ℕ}
    (u : CutTestFamily G r) (x : Fin r → G) :
    cutTestProduct u x =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutTestProduct
            (cutTestFamilyOfBooleanAssignment b) x := by
  classical
  symm
  simpa [cutTestProduct, cutTestCoordinateValue,
    cutTestFamilyOfBooleanAssignment,
    usedCutTestCoordinateEmbedding_apply] using
    (sum_bernoulliAssignmentWeight_mul_embedding
      (cutTestCoordinateValue u)
      (usedCutTestCoordinateEmbedding x))

theorem cutCorrelation_eq_sum_boolean
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ) (u : CutTestFamily G r) :
    cutCorrelation r f g u =
      ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutCorrelation r f g
            (cutTestFamilyOfBooleanAssignment b) := by
  unfold cutCorrelation
  calc
    mean (fun x : Fin r → G =>
        (f (∑ i, x i) - g (∑ i, x i)) *
          ∏ i, u i (eraseCoordinate i x)) =
        mean (fun x : Fin r → G =>
          ∑ b : BooleanCutAssignment G r,
            bernoulliAssignmentWeight
                (cutTestCoordinateValue u) b *
              ((f (∑ i, x i) - g (∑ i, x i)) *
                cutTestProduct
                  (cutTestFamilyOfBooleanAssignment b) x)) := by
      apply congrArg mean
      funext x
      change
        (f (∑ i, x i) - g (∑ i, x i)) *
            cutTestProduct u x =
          _
      rw [cutTestProduct_eq_sum_boolean u x]
      rw [Finset.mul_sum]
      apply Fintype.sum_congr
      intro b
      ring
    _ = ∑ b : BooleanCutAssignment G r,
        mean (fun x : Fin r → G =>
          bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            ((f (∑ i, x i) - g (∑ i, x i)) *
              cutTestProduct
                (cutTestFamilyOfBooleanAssignment b) x)) := by
      unfold mean
      exact Finset.expect_sum_comm Finset.univ Finset.univ _
    _ = ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          mean (fun x : Fin r → G =>
            (f (∑ i, x i) - g (∑ i, x i)) *
              cutTestProduct
                (cutTestFamilyOfBooleanAssignment b) x) := by
      apply Fintype.sum_congr
      intro b
      exact mean_smul
        (bernoulliAssignmentWeight
          (cutTestCoordinateValue u) b) _
    _ = _ := by
      rfl

theorem abs_cutCorrelation_le_of_boolean
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} {f g : G → ℝ} {ε : ℝ}
    (u : CutTestFamily G r) (hu : IsBoundedCutTest u)
    (hboolean :
      ∀ b : BooleanCutAssignment G r,
        |cutCorrelation r f g
          (cutTestFamilyOfBooleanAssignment b)| ≤ ε) :
    |cutCorrelation r f g u| ≤ ε := by
  classical
  rw [cutCorrelation_eq_sum_boolean]
  calc
    |∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b *
          cutCorrelation r f g
            (cutTestFamilyOfBooleanAssignment b)| ≤
        ∑ b : BooleanCutAssignment G r,
          |bernoulliAssignmentWeight
              (cutTestCoordinateValue u) b *
            cutCorrelation r f g
              (cutTestFamilyOfBooleanAssignment b)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ b : BooleanCutAssignment G r,
        bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b * ε := by
      apply Finset.sum_le_sum
      intro b _
      have hw :
          0 ≤ bernoulliAssignmentWeight
            (cutTestCoordinateValue u) b :=
        bernoulliAssignmentWeight_nonneg
          (p := cutTestCoordinateValue u)
          (fun q => hu.nonneg q.1 q.2)
          (fun q => hu.le_one q.1 q.2) b
      rw [abs_mul, abs_of_nonneg hw]
      exact mul_le_mul_of_nonneg_left (hboolean b) hw
    _ = ε := by
      rw [← Finset.sum_mul,
        sum_bernoulliAssignmentWeight, one_mul]

noncomputable def booleanCutConvolution
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (b : BooleanCutAssignment G r) : G → ℝ :=
  generalizedConvolution r
    (cutTestFamilyOfBooleanAssignment b)

theorem booleanCutConvolution_unitBounded
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r)
    (b : BooleanCutAssignment G r) :
    IsUnitBounded (booleanCutConvolution r b) := by
  constructor
  · intro z
    exact generalizedConvolution_nonneg hr
      (cutTestFamilyOfBooleanAssignment_bounded b) z
  · intro z
    exact generalizedConvolution_le_one hr
      (cutTestFamilyOfBooleanAssignment_bounded b) z

theorem booleanCutConvolution_unitBoundedFamily
    {G : Type*} [Fintype G] [AddCommGroup G]
    {r : ℕ} (hr : 0 < r) :
    IsUnitBoundedTestFamily
      (booleanCutConvolution (G := G) r) :=
  fun b => booleanCutConvolution_unitBounded hr b

theorem cutCorrelation_boolean_eq_pairing
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f g : G → ℝ)
    (b : BooleanCutAssignment G r) :
    cutCorrelation r f g
        (cutTestFamilyOfBooleanAssignment b) =
      finitePairing (f - g) (booleanCutConvolution r b) := by
  rw [cutCorrelation_eq_mean_mul_generalizedConvolution]
  rfl

theorem exists_cutDiscrepancy_model_of_finiteBooleanModel
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (f : G → ℝ) {ε : ℝ}
    (hmodel :
      HasFiniteDenseModel
        (booleanCutConvolution (G := G) r) f ε) :
    ∃ g : G → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe r f g ε := by
  obtain ⟨g, hg, hmatch⟩ := hmodel
  refine ⟨g, hg, ?_⟩
  intro u hu0 hu1
  apply abs_cutCorrelation_le_of_boolean u ⟨hu0, hu1⟩
  intro b
  rw [cutCorrelation_boolean_eq_pairing]
  exact hmatch b

theorem exists_cutDiscrepancy_model_of_positivePartCorrelationBound
    {G : Type*} [Fintype G] [DecidableEq G] [AddCommGroup G]
    (r : ℕ) {f ν : G → ℝ} {ε : ℝ}
    (hε : 0 ≤ ε)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hpseudo :
      HasPositivePartCorrelationBound
        (booleanCutConvolution (G := G) r) ν ε) :
    ∃ g : G → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe r f g ε := by
  apply exists_cutDiscrepancy_model_of_finiteBooleanModel r f
  exact hasFiniteDenseModel_of_positivePartCorrelationBound
    (booleanCutConvolution (G := G) r)
    hε hf0 hfν hpseudo

theorem exists_cutDiscrepancy_model_of_monomialCorrelationBound
    {G : Type*} [Fintype G] [AddCommGroup G]
    (r : ℕ) (hr : 0 < r)
    {f ν : G → ℝ}
    {p : ℝ[X]} {δ η M : ℝ}
    (hδ : 0 ≤ δ) (hη : 0 ≤ η) (hM0 : 0 ≤ M)
    (hf0 : ∀ x, 0 ≤ f x) (hfν : ∀ x, f x ≤ ν x)
    (hp : ApproximatesPositivePartOnUnitInterval p δ)
    (hM : centeredAbsoluteMean ν ≤ M)
    (hmono :
      HasMonomialCorrelationBound
        (booleanCutConvolution (G := G) r)
        ν p.natDegree η) :
    ∃ g : G → ℝ, IsUnitBounded g ∧
      CutDiscrepancyLe r f g
        (polynomialCoefficientL1 p * η + δ * M) := by
  classical
  apply
    exists_cutDiscrepancy_model_of_positivePartCorrelationBound
      r
  · exact add_nonneg
      (mul_nonneg (polynomialCoefficientL1_nonneg p) hη)
      (mul_nonneg hδ hM0)
  · exact hf0
  · exact hfν
  · exact hasPositivePartCorrelationBound_of_polynomial
      (booleanCutConvolution_unitBoundedFamily hr)
      hδ hp hM hmono

end Erdos3.FixedDensity

end

end OAI
