import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! Separately affine functions on boxes and sparse squarefree polynomials. -/

namespace MoserWorm.Multiaffine

variable {ι : Type*} [instι : DecidableEq ι]

/-- Affine dependence on each coordinate, with the others held fixed. -/
def SeparatelyAffine (f : (ι → ℝ) → ℝ) : Prop :=
  ∀ i x, ∃ a b : ℝ, ∀ t, f (Function.update x i t) = a * t + b

def InBox (lo hi x : ι → ℝ) : Prop :=
  ∀ i, lo i ≤ x i ∧ x i ≤ hi i

def IsCorner (lo hi x : ι → ℝ) : Prop :=
  ∀ i, x i = lo i ∨ x i = hi i

private theorem endpoint_le {f : (ι → ℝ) → ℝ} (hf : SeparatelyAffine f)
    {lo hi x : ι → ℝ} (hx : InBox lo hi x) (i : ι) :
    ∃ t, (t = lo i ∨ t = hi i) ∧ f (Function.update x i t) ≤ f x := by
  obtain ⟨a, b, hab⟩ := hf i x
  have heq : f x = a * x i + b := by simpa using hab (x i)
  by_cases ha : 0 ≤ a
  · refine ⟨lo i, Or.inl rfl, ?_⟩
    rw [hab, heq]
    simpa [add_comm] using add_le_add_right (mul_le_mul_of_nonneg_left (hx i).1 ha) b
  · refine ⟨hi i, Or.inr rfl, ?_⟩
    rw [hab, heq]
    simpa [add_comm] using
      add_le_add_right (mul_le_mul_of_nonpos_left (hx i).2 (le_of_not_ge ha)) b

private theorem exists_partial_corner {f : (ι → ℝ) → ℝ} (hf : SeparatelyAffine f)
    (s : Finset ι) {lo hi x : ι → ℝ} (hx : InBox lo hi x) :
    ∃ y, (∀ i ∈ s, y i = lo i ∨ y i = hi i) ∧
      (∀ i ∉ s, y i = x i) ∧ f y ≤ f x := by
  induction s using Finset.induction_on generalizing x with
  | empty => exact ⟨x, by simp, by simp, le_rfl⟩
  | @insert i s his ih =>
    obtain ⟨t, ht, hle⟩ := endpoint_le hf hx i
    have hbox : InBox lo hi (Function.update x i t) := by
      intro j
      by_cases hji : j = i
      · subst j
        simp only [Function.update_self]
        rcases ht with rfl | rfl
        · exact ⟨le_rfl, (hx i).1.trans (hx i).2⟩
        · exact ⟨(hx i).1.trans (hx i).2, le_rfl⟩
      · simpa [Function.update_of_ne hji] using hx j
    obtain ⟨y, hy, hyout, hyf⟩ := ih hbox
    refine ⟨y, ?_, ?_, hyf.trans hle⟩
    · intro j hj
      rcases Finset.mem_insert.mp hj with hji | hjs
      · subst j
        simpa [hyout i his] using ht
      · exact hy j hjs
    · intro j hj
      have hji : j ≠ i := by
        intro h
        subst j
        exact hj (Finset.mem_insert_self i s)
      simpa [Function.update_of_ne hji] using hyout j (fun h => hj (Finset.mem_insert_of_mem h))

/-- Moving coordinates to endpoints produces a corner of no greater value.
No continuity, nondegeneracy, or compactness assumption is needed. -/
theorem exists_corner_le [Finite ι] {f : (ι → ℝ) → ℝ} (hf : SeparatelyAffine f)
    {lo hi x : ι → ℝ} (hx : InBox lo hi x) :
    ∃ y, IsCorner lo hi y ∧ f y ≤ f x := by
  let := Fintype.ofFinite ι
  obtain ⟨y, hy, -, hle⟩ := exists_partial_corner hf Finset.univ hx
  exact ⟨y, fun i => hy i (Finset.mem_univ i), hle⟩

theorem lower_bound [Finite ι] {f : (ι → ℝ) → ℝ} (hf : SeparatelyAffine f)
    {lo hi x : ι → ℝ} {b : ℝ} (hx : InBox lo hi x)
    (hcorners : ∀ y, IsCorner lo hi y → b ≤ f y) : b ≤ f x := by
  obtain ⟨y, hy, hle⟩ := exists_corner_le hf hx
  exact (hcorners y hy).trans hle

theorem strict_lower_bound [Finite ι] {f : (ι → ℝ) → ℝ} (hf : SeparatelyAffine f)
    {lo hi x : ι → ℝ} {b : ℝ} (hx : InBox lo hi x)
    (hcorners : ∀ y, IsCorner lo hi y → b < f y) : b < f x := by
  obtain ⟨y, hy, hle⟩ := exists_corner_le hf hx
  exact (hcorners y hy).trans_le hle

/-- Boolean coordinates enumerate the corners, including repeated corners of
degenerate boxes. -/
def corner {R : Type*} (lo hi : ι → R) (bits : ι → Bool) : ι → R :=
  fun i => if bits i then hi i else lo i

omit instι in
theorem exists_bits {lo hi y : ι → ℝ} (hy : IsCorner lo hi y) :
    ∃ bits : ι → Bool, corner lo hi bits = y := by
  classical
  refine ⟨fun i => decide (y i = hi i), ?_⟩
  funext i
  by_cases h : y i = hi i
  · simp [corner, h]
  · change (if decide (y i = hi i) then hi i else lo i) = y i
    rw [if_neg (by simpa using h)]
    exact ((hy i).resolve_right h).symm

theorem lower_bound_of_corners [Finite ι] {f : (ι → ℝ) → ℝ}
    (hf : SeparatelyAffine f) {lo hi x : ι → ℝ} {b : ℝ} (hx : InBox lo hi x)
    (hcorners : ∀ bits : ι → Bool, b ≤ f (corner lo hi bits)) : b ≤ f x := by
  apply lower_bound hf hx
  intro y hy
  obtain ⟨bits, rfl⟩ := exists_bits hy
  exact hcorners bits

theorem strict_lower_bound_of_corners [Finite ι] {f : (ι → ℝ) → ℝ}
    (hf : SeparatelyAffine f) {lo hi x : ι → ℝ} {b : ℝ} (hx : InBox lo hi x)
    (hcorners : ∀ bits : ι → Bool, b < f (corner lo hi bits)) : b < f x := by
  apply strict_lower_bound hf hx
  intro y hy
  obtain ⟨bits, rfl⟩ := exists_bits hy
  exact hcorners bits

/-- A sparse sum of squarefree monomials. Coefficients may be rational for
execution or real for semantics. Duplicate terms are allowed. -/
abbrev Polynomial (ι R : Type*) := List (Finset ι × R)

namespace Polynomial

variable {R S : Type*}
omit instι

/-- Evaluation is a list traversal; every variable occurs at most once per term. -/
def eval [CommSemiring R] (p : Polynomial ι R) (x : ι → R) : R :=
  (p.map fun t => t.2 * ∏ i ∈ t.1, x i).sum

def constant (a : R) : Polynomial ι R := [(∅, a)]

def coord [One R] (i : ι) : Polynomial ι R := [({i}, 1)]

def add (p q : Polynomial ι R) : Polynomial ι R := p ++ q

def sum (ps : List (Polynomial ι R)) : Polynomial ι R := ps.flatten

def scale [Mul R] (a : R) (p : Polynomial ι R) : Polynomial ι R :=
  p.map fun t => (t.1, a * t.2)

/-- Squarefree multiplication. `eval_mul` requires disjoint variables between
each pair of terms, so this operation never silently asserts `x² = x`. -/
def mul [Mul R] (p q : Polynomial ι R) : Polynomial ι R :=
  p.flatMap fun t => q.map fun u => (t.1 ∪ u.1, t.2 * u.2)

def Separated (p q : Polynomial ι R) : Prop :=
  ∀ t ∈ p, ∀ u ∈ q, Disjoint t.1 u.1

def SupportedOn (p : Polynomial ι R) (s : Set ι) : Prop :=
  ∀ t ∈ p, ∀ i ∈ t.1, i ∈ s

@[simp] theorem eval_nil [CommSemiring R] (x : ι → R) :
    eval ([] : Polynomial ι R) x = 0 := rfl

@[simp] theorem eval_cons [CommSemiring R] (t : Finset ι × R)
    (p : Polynomial ι R) (x : ι → R) :
    eval (t :: p) x = t.2 * ∏ i ∈ t.1, x i + eval p x := rfl

@[simp] theorem eval_constant [CommSemiring R] (a : R) (x : ι → R) :
    (constant a).eval x = a := by simp [constant, eval]

@[simp] theorem eval_coord [CommSemiring R] (i : ι) (x : ι → R) :
    (coord i).eval x = x i := by simp [coord, eval]

@[simp] theorem eval_add [CommSemiring R] (p q : Polynomial ι R) (x : ι → R) :
    (p.add q).eval x = p.eval x + q.eval x := by simp [add, eval]

@[simp] theorem eval_sum [CommSemiring R] (ps : List (Polynomial ι R)) (x : ι → R) :
    (sum ps).eval x = (ps.map fun p => p.eval x).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change eval (add p (sum ps)) x = _
    rw [eval_add, ih]
    rfl

@[simp] theorem eval_scale [CommSemiring R] (a : R) (p : Polynomial ι R) (x : ι → R) :
    (p.scale a).eval x = a * p.eval x := by
  induction p with
  | nil => simp [scale]
  | cons t p ih =>
    change (a * t.2) * (∏ i ∈ t.1, x i) + eval (scale a p) x = _
    rw [ih, eval_cons, mul_add, mul_assoc]

include instι in
private theorem eval_mul_term [CommSemiring R] (t : Finset ι × R)
    (q : Polynomial ι R) (h : ∀ u ∈ q, Disjoint t.1 u.1) (x : ι → R) :
    eval (q.map fun u => (t.1 ∪ u.1, t.2 * u.2)) x =
      (t.2 * ∏ i ∈ t.1, x i) * q.eval x := by
  induction q with
  | nil => simp
  | cons u q ih =>
    have htu := h u (by simp)
    have htq : ∀ u ∈ q, Disjoint t.1 u.1 := fun v hv => h v (by simp [hv])
    simp only [List.map_cons, eval_cons, Finset.prod_union htu, ih htq]
    ring

include instι in
theorem eval_mul [CommSemiring R] {p q : Polynomial ι R} (h : Separated p q)
    (x : ι → R) : (p.mul q).eval x = p.eval x * q.eval x := by
  induction p with
  | nil => simp [mul]
  | cons t p ih =>
    have ht : ∀ u ∈ q, Disjoint t.1 u.1 := fun u hu => h t (by simp) u hu
    have hp : Separated p q := fun v hv u hu => h v (by simp [hv]) u hu
    have hrow := eval_mul_term t q ht x
    change eval ((q.map fun u => (t.1 ∪ u.1, t.2 * u.2)) ++ mul p q) x = _
    rw [show ∀ a b : Polynomial ι R, eval (a ++ b) x = eval a x + eval b x from
      fun a b => eval_add a b x, hrow, ih hp, eval_cons, add_mul]

theorem supportedOn_constant (a : R) (s : Set ι) : SupportedOn (constant a) s := by
  simp [SupportedOn, constant]

theorem supportedOn_coord [One R] {i : ι} {s : Set ι} (hi : i ∈ s) :
    SupportedOn (coord (R := R) i) s := by simpa [SupportedOn, coord] using hi

theorem supportedOn_add {p q : Polynomial ι R} {s : Set ι}
    (hp : p.SupportedOn s) (hq : q.SupportedOn s) : (p.add q).SupportedOn s := by
  intro t ht i hi
  rcases List.mem_append.mp ht with ht | ht
  · exact hp t ht i hi
  · exact hq t ht i hi

theorem supportedOn_scale [Mul R] (a : R) {p : Polynomial ι R} {s : Set ι}
    (hp : p.SupportedOn s) : (p.scale a).SupportedOn s := by
  rintro t ht i hi
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp ht
  exact hp u hu i hi

theorem separated_of_support {p q : Polynomial ι R} {s t : Set ι}
    (hp : p.SupportedOn s) (hq : q.SupportedOn t) (hst : Disjoint s t) :
    p.Separated q := by
  intro u hu v hv
  apply Finset.disjoint_left.mpr
  intro i hi hj
  exact Set.disjoint_left.mp hst (hp u hu i hi) (hq v hv i hj)

include instι in
theorem separatelyAffine (p : Polynomial ι ℝ) : SeparatelyAffine p.eval := by
  intro i x
  induction p with
  | nil => exact ⟨0, 0, by simp⟩
  | cons t p ih =>
    obtain ⟨a, b, hab⟩ := ih
    by_cases hi : i ∈ t.1
    · refine ⟨t.2 * ∏ j ∈ t.1.erase i, x j + a, b, ?_⟩
      intro z
      rw [eval_cons, Finset.prod_update_of_mem hi, Finset.sdiff_singleton_eq_erase, hab]
      ring
    · refine ⟨a, t.2 * ∏ j ∈ t.1, x j + b, ?_⟩
      intro z
      rw [eval_cons, Finset.prod_update_of_notMem hi, hab]
      ring

theorem lower_bound [Finite ι] (p : Polynomial ι ℝ)
    {lo hi x : ι → ℝ} {b : ℝ} (hx : InBox lo hi x)
    (hcorners : ∀ bits : ι → Bool, b ≤ p.eval (corner lo hi bits)) :
    b ≤ p.eval x := by
  classical
  exact lower_bound_of_corners p.separatelyAffine hx hcorners

theorem strict_lower_bound [Finite ι] (p : Polynomial ι ℝ)
    {lo hi x : ι → ℝ} {b : ℝ} (hx : InBox lo hi x)
    (hcorners : ∀ bits : ι → Bool, b < p.eval (corner lo hi bits)) :
    b < p.eval x := by
  classical
  exact strict_lower_bound_of_corners p.separatelyAffine hx hcorners

/-- An interval evaluator need only supply a sound lower endpoint at each
corner. Its representation and rounding method do not enter the box proof. -/
theorem lower_bound_of_enclosures [Finite ι] (p : Polynomial ι ℝ)
    {lo hi x : ι → ℝ} {b : ℝ} (hx : InBox lo hi x)
    (lower : (ι → Bool) → ℝ)
    (hsound : ∀ bits, lower bits ≤ p.eval (corner lo hi bits))
    (hcheck : ∀ bits, b ≤ lower bits) : b ≤ p.eval x :=
  p.lower_bound hx fun bits => (hcheck bits).trans (hsound bits)

/-- Change coefficients without changing monomials. -/
def mapCoeffs (f : R → S) (p : Polynomial ι R) : Polynomial ι S :=
  p.map fun t => (t.1, f t.2)

theorem eval_mapCoeffs [CommSemiring R] [CommSemiring S] (f : R →+* S)
    (p : Polynomial ι R) (x : ι → R) :
    (p.mapCoeffs f).eval (fun i => f (x i)) = f (p.eval x) := by
  induction p with
  | nil => simp [mapCoeffs]
  | cons t p ih =>
    change f t.2 * (∏ i ∈ t.1, f (x i)) +
      eval (mapCoeffs f p) (fun i => f (x i)) = _
    rw [ih, eval_cons, map_add, map_mul, map_prod]

/-- Exact rational corner checks imply the corresponding real bound. -/
theorem rat_lower_bound [Finite ι] (p : Polynomial ι ℚ)
    {lo hi : ι → ℚ} {x : ι → ℝ} {b : ℚ}
    (hx : InBox (fun i => (lo i : ℝ)) (fun i => (hi i : ℝ)) x)
    (hcorners : ∀ bits : ι → Bool, b ≤ p.eval (corner lo hi bits)) :
    (b : ℝ) ≤ (p.mapCoeffs (Rat.castHom ℝ)).eval x := by
  apply Polynomial.lower_bound _ hx
  intro bits
  have heq :
      corner (fun i => (lo i : ℝ)) (fun i => (hi i : ℝ)) bits =
        fun i => ((corner lo hi bits i : ℚ) : ℝ) := by
    funext i
    simp only [corner]
    split <;> rfl
  rw [heq]
  have heval := eval_mapCoeffs (Rat.castHom ℝ) p (corner lo hi bits)
  simp only [Rat.coe_castHom] at heval ⊢
  rw [heval]
  exact_mod_cast hcorners bits

/-- Combine a term with an existing monomial before applying coefficient
enclosures. Zero coefficients are retained to avoid coefficient equality tests. -/
def insertTerm [Add R] (t : Finset ι × R) : Polynomial ι R → Polynomial ι R
  | [] => [t]
  | u :: p =>
      if t.1 = u.1 then (u.1, t.2 + u.2) :: p else u :: insertTerm t p

/-- Collect equal monomials. For twelve variables and degree two there are
only 79 possible monomials, independent of the number of polygon edges. -/
def collect [Add R] : Polynomial ι R → Polynomial ι R
  | [] => []
  | t :: p => insertTerm t (collect p)

include instι in
theorem eval_insertTerm [CommSemiring R] (t : Finset ι × R)
    (p : Polynomial ι R) (x : ι → R) :
    (insertTerm t p).eval x = t.2 * (∏ i ∈ t.1, x i) + p.eval x := by
  induction p with
  | nil => rfl
  | cons u p ih =>
    by_cases h : t.1 = u.1
    · simp only [insertTerm, h, ↓reduceIte, eval_cons]
      ring
    · simp only [insertTerm, if_neg h, eval_cons, ih]
      ring

include instι in
theorem eval_collect [CommSemiring R] (p : Polynomial ι R) (x : ι → R) :
    p.collect.eval x = p.eval x := by
  induction p with
  | nil => rfl
  | cons t p ih => rw [collect, eval_insertTerm, ih, eval_cons]

/-- A linear-time lower bound on the unit box. Collect equal monomials first
to retain coefficient cancellation. No corner enumeration is performed. -/
def unitLowerBound [AddGroup R] [LinearOrder R] (p : Polynomial ι R) : R :=
  (p.map fun t => if t.1 = ∅ then t.2 else -|t.2|).sum

include instι in
theorem unitLowerBound_le [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (p : Polynomial ι R) (x : ι → R) (hx : ∀ i, |x i| ≤ 1) :
    p.unitLowerBound ≤ p.eval x := by
  induction p with
  | nil => exact le_rfl
  | cons t p ih =>
    have hterm : (if t.1 = ∅ then t.2 else -|t.2|) ≤ t.2 * ∏ i ∈ t.1, x i := by
      by_cases h : t.1 = ∅
      · simp [h]
      · rw [if_neg h]
        have hp : |∏ i ∈ t.1, x i| ≤ 1 := by
          rw [Finset.abs_prod]
          exact Finset.prod_le_one (fun i _ => abs_nonneg (x i)) (fun i _ => hx i)
        have ha : |t.2 * ∏ i ∈ t.1, x i| ≤ |t.2| := by
          rw [abs_mul]
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (abs_nonneg t.2)
        exact (neg_le_neg ha).trans (neg_abs_le _)
    exact add_le_add hterm ih

include instι in
theorem collected_unitLowerBound_le [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (p : Polynomial ι R) (x : ι → R) (hx : ∀ i, |x i| ≤ 1) :
    p.collect.unitLowerBound ≤ p.eval x := by
  simpa only [eval_collect] using p.collect.unitLowerBound_le x hx

/-- Coefficientwise outward enclosures, with identical monomials. -/
def EnclosedBy [LE R] (p : Polynomial ι R) (bounds : Polynomial ι (R × R)) : Prop :=
  List.Forall₂ (fun t u => t.1 = u.1 ∧ u.2.1 ≤ t.2 ∧ t.2 ≤ u.2.2) p bounds

/-- The cheap interval check: constant lower endpoints minus the maximum
absolute endpoint of each nonconstant coefficient interval. -/
def unitEnclosureLowerBound [AddGroup R] [LinearOrder R]
    (bounds : Polynomial ι (R × R)) : R :=
  (bounds.map fun t => if t.1 = ∅ then t.2.1 else -max |t.2.1| |t.2.2|).sum

include instι in
theorem unitEnclosureLowerBound_le [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    {p : Polynomial ι R} {bounds : Polynomial ι (R × R)}
    (h : p.EnclosedBy bounds) (x : ι → R) (hx : ∀ i, |x i| ≤ 1) :
    unitEnclosureLowerBound bounds ≤ p.eval x := by
  induction h with
  | nil => exact le_rfl
  | @cons t u p bounds h hrest ih =>
    obtain ⟨hs, hl, hu⟩ := h
    apply add_le_add _ ih
    change (if u.1 = ∅ then u.2.1 else -max |u.2.1| |u.2.2|) ≤
      t.2 * ∏ i ∈ t.1, x i
    by_cases hz : u.1 = ∅
    · simpa [hz, hs] using hl
    · rw [if_neg hz]
      have ha : |t.2| ≤ max |u.2.1| |u.2.2| := by
        apply abs_le.mpr
        exact ⟨((neg_le_neg (le_max_left _ _)).trans (neg_abs_le _)).trans hl,
          hu.trans ((le_abs_self _).trans (le_max_right _ _))⟩
      have hp : |∏ i ∈ t.1, x i| ≤ 1 := by
        rw [Finset.abs_prod]
        exact Finset.prod_le_one (fun i _ => abs_nonneg (x i)) (fun i _ => hx i)
      have hmul : |t.2 * ∏ i ∈ t.1, x i| ≤ max |u.2.1| |u.2.2| := by
        rw [abs_mul]
        have hterm : |t.2| * |∏ i ∈ t.1, x i| ≤ |t.2| := by
          simpa only [mul_one] using mul_le_mul_of_nonneg_left hp (abs_nonneg t.2)
        exact hterm.trans ha
      exact (neg_le_neg hmul).trans (neg_abs_le _)

/-- Substitute `xᵢ = a + b yᵢ`. Each affected monomial splits into two
squarefree terms; this avoids enumerating polynomial or box corners. -/
def affineUpdate [CommSemiring R] (i : ι) (a b : R) (p : Polynomial ι R) :
    Polynomial ι R :=
  p.flatMap fun t =>
    if i ∈ t.1 then [(t.1.erase i, a * t.2), (t.1, b * t.2)] else [t]

include instι in
theorem eval_affineUpdate [CommSemiring R] (i : ι) (a b : R)
    (p : Polynomial ι R) (x : ι → R) :
    (affineUpdate i a b p).eval x = p.eval (Function.update x i (a + b * x i)) := by
  induction p with
  | nil => rfl
  | cons t p ih =>
    change eval (add
      (if i ∈ t.1 then [(t.1.erase i, a * t.2), (t.1, b * t.2)] else [t])
      (affineUpdate i a b p)) x = _
    rw [eval_add, ih, eval_cons]
    congr 1
    by_cases hi : i ∈ t.1
    · simp only [if_pos hi, eval_cons, eval_nil, add_zero,
        Finset.prod_update_of_mem hi, Finset.sdiff_singleton_eq_erase]
      rw [← Finset.mul_prod_erase t.1 x hi]
      ring
    · simp [hi, Finset.prod_update_of_notMem hi]

/-- Translate and scale the listed coordinates. Use a duplicate-free list
covering all coordinates for a complete change of variables. -/
def recenter [CommSemiring R] (p : Polynomial ι R) (vars : List ι)
    (center radius : ι → R) : Polynomial ι R :=
  vars.foldr (fun i q => affineUpdate i (center i) (radius i) q) p

include instι in
theorem eval_recenter [CommSemiring R] (p : Polynomial ι R) (vars : List ι)
    (center radius : ι → R) (hvars : vars.Nodup) (x : ι → R) :
    (p.recenter vars center radius).eval x =
      p.eval (fun i => if i ∈ vars then center i + radius i * x i else x i) := by
  induction vars generalizing x with
  | nil => simp [recenter]
  | cons i vars ih =>
    obtain ⟨hi, hvars⟩ := List.nodup_cons.mp hvars
    change eval (affineUpdate i (center i) (radius i) (recenter p vars center radius)) x = _
    rw [eval_affineUpdate, ih hvars]
    congr 1
    funext j
    by_cases hji : j = i
    · subst j
      simp [hi]
    · simp [hji]

include instι in
theorem eval_recenter_all [CommSemiring R] (p : Polynomial ι R) (vars : List ι)
    (center radius : ι → R) (hvars : vars.Nodup) (hcover : ∀ i, i ∈ vars) (x : ι → R) :
    (p.recenter vars center radius).eval x =
      p.eval (fun i => center i + radius i * x i) := by
  simp only [eval_recenter p vars center radius hvars, hcover, ↓reduceIte]

include instι in
theorem recentered_unitLowerBound_le [CommRing R] [LinearOrder R] [IsStrictOrderedRing R]
    (p : Polynomial ι R) (vars : List ι) (center radius : ι → R)
    (hvars : vars.Nodup) (hcover : ∀ i, i ∈ vars) (x : ι → R) (hx : ∀ i, |x i| ≤ 1) :
    (p.recenter vars center radius).collect.unitLowerBound ≤
      p.eval (fun i => center i + radius i * x i) := by
  rw [← eval_recenter_all p vars center radius hvars hcover]
  exact (p.recenter vars center radius).collected_unitLowerBound_le x hx

private theorem exists_unit_coordinates {center radius x : ι → ℝ}
    (hx : InBox (fun i => center i - radius i) (fun i => center i + radius i) x) :
    ∃ y : ι → ℝ, (∀ i, |y i| ≤ 1) ∧ x = fun i => center i + radius i * y i := by
  let y : ι → ℝ := fun i => (x i - center i) / radius i
  have h : ∀ i, |y i| ≤ 1 ∧ x i = center i + radius i * y i := by
    intro i
    have hrad : 0 ≤ radius i := by have := hx i; linarith
    by_cases hz : radius i = 0
    · have hxc : x i = center i := by
        have hxi := hx i
        change center i - radius i ≤ x i ∧ x i ≤ center i + radius i at hxi
        rw [hz] at hxi
        linarith
      simp [y, hz, hxc]
    · have hr : 0 < radius i := lt_of_le_of_ne hrad (Ne.symm hz)
      have hd : |x i - center i| ≤ radius i := by
        apply abs_le.mpr
        have := hx i
        constructor <;> linarith
      constructor
      · dsimp [y]
        rw [abs_div, abs_of_pos hr]
        exact (div_le_one hr).mpr hd
      · dsimp [y]
        field_simp [hz]
        ring
  exact ⟨y, fun i => (h i).1, funext fun i => (h i).2⟩

include instι in
/-- Complete fast path for an arbitrary (possibly degenerate) real box.
Enclosures refer to collected coefficients after recentering. -/
theorem lower_bound_of_recentered_enclosures
    (p : Polynomial ι ℝ) (vars : List ι) (center radius : ι → ℝ)
    (hvars : vars.Nodup) (hcover : ∀ i, i ∈ vars)
    {bounds : Polynomial ι (ℝ × ℝ)}
    (hcoeff : (p.recenter vars center radius).collect.EnclosedBy bounds)
    {x : ι → ℝ}
    (hx : InBox (fun i => center i - radius i) (fun i => center i + radius i) x) :
    unitEnclosureLowerBound bounds ≤ p.eval x := by
  obtain ⟨y, hy, rfl⟩ := exists_unit_coordinates hx
  have h := unitEnclosureLowerBound_le hcoeff y hy
  simpa only [eval_collect, eval_recenter_all p vars center radius hvars hcover] using h

end Polynomial
end MoserWorm.Multiaffine
