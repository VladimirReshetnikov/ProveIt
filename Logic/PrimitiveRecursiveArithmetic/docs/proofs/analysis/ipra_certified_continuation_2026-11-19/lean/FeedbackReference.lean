import Mathlib

/-!
# A finite weighted contraction reference model

STATUS: fully written Lean candidate, NOT compiled in the delivery environment.
There are no `sorry` placeholders or new axioms. This file is an ambient Lean
reference model over rationals, NOT an object-theory `Prf PRAAx` derivation.
See OBJECT_PORT.md for the distinct, still-open object-theory obligations.

All inputs are finite rational vectors/matrices; the function parameter `f`
must become one fixed PR template (or a fixed finite instruction language)
before the numerical algorithm is claimed to be primitive recursive.
-/

namespace FiniteFeedback

abbrev Vec (m : Nat) := Fin m → ℚ
abbrev Mat (m : Nat) := Fin m → Fin m → ℚ

def rowApply {m : Nat} (A : Mat m) (x : Vec m) (i : Fin m) : ℚ :=
  ∑ j, A i j * x j

def Within {m : Nat} (w : Vec m) (r : ℚ) (x y : Vec m) : Prop :=
  ∀ i, |x i - y i| ≤ r * w i

structure HalfCertificate (m : Nat) where
  A : Mat m
  w : Vec m
  weight_pos : ∀ i, 0 < w i
  entry_nonneg : ∀ i j, 0 ≤ A i j
  row_bound : ∀ i, 2 * rowApply A w i ≤ w i

theorem row_domination {m : Nat} (A : Mat m) (w x : Vec m) (r : ℚ)
    (hA : ∀ i j, 0 ≤ A i j) (hx : ∀ j, x j ≤ r * w j) (i : Fin m) :
    rowApply A x i ≤ r * rowApply A w i := by
  unfold rowApply
  calc
    (∑ j, A i j * x j) ≤ ∑ j, A i j * (r * w j) :=
      Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (hx j) (hA i j))
    _ = r * ∑ j, A i j * w j := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

theorem within_refl {m : Nat} (w : Vec m) (x : Vec m) : Within w 0 x x := by
  intro i
  simp

theorem within_symm {m : Nat} {w : Vec m} {r : ℚ} {x y : Vec m}
    (h : Within w r x y) : Within w r y x := by
  intro i
  simpa only [abs_sub_comm] using h i

theorem within_triangle {m : Nat} {w : Vec m} {r s : ℚ} {x y z : Vec m}
    (hxy : Within w r x y) (hyz : Within w s y z) : Within w (r+s) x z := by
  intro i
  calc
    |x i-z i| = |(x i-y i)+(y i-z i)| := by congr 1 <;> ring
    _ ≤ |x i-y i|+|y i-z i| := abs_add _ _
    _ ≤ r*w i+s*w i := add_le_add (hxy i) (hyz i)
    _ = (r+s)*w i := by ring

theorem within_mono {m : Nat} {w : Vec m} (hw : ∀ i, 0 ≤ w i)
    {r s : ℚ} (hrs : r ≤ s) {x y : Vec m} (h : Within w r x y) :
    Within w s x y := by
  intro i
  exact le_trans (h i) (mul_le_mul_of_nonneg_right hrs (hw i))

structure LocalMap {m : Nat} (C : HalfCertificate m) where
  good : Vec m → Prop
  f : Vec m → Vec m
  closed : ∀ x, good x → good (f x)
  gain : ∀ x y, good x → good y → ∀ i,
    |f x i-f y i| ≤ rowApply C.A (fun j => |x j-y j|) i

theorem half_contract {m : Nat} {C : HalfCertificate m} (T : LocalMap C)
    {x y : Vec m} (hx : T.good x) (hy : T.good y) {r : ℚ}
    (hr : 0 ≤ r) (hxy : Within C.w r x y) : Within C.w (r/2) (T.f x) (T.f y) := by
  intro i
  have hrow := row_domination C.A C.w (fun j => |x j-y j|) r C.entry_nonneg hxy i
  have hcert := C.row_bound i
  have hscaled : r * rowApply C.A C.w i ≤ (r/2) * C.w i := by
    have hmul := mul_le_mul_of_nonneg_left hcert hr
    nlinarith
  exact le_trans (T.gain x y hx hy i) (le_trans hrow hscaled)

def orbit {m : Nat} (f : Vec m → Vec m) (x : Vec m) : Nat → Vec m
  | 0 => x
  | n+1 => f (orbit f x n)

theorem orbit_good {m : Nat} {C : HalfCertificate m} (T : LocalMap C)
    (x : Vec m) (hx : T.good x) : ∀ n, T.good (orbit T.f x n) := by
  intro n
  induction n with
  | zero => exact hx
  | succ n ih => exact T.closed _ ih

theorem increment_bound {m : Nat} {C : HalfCertificate m} (T : LocalMap C)
    (x : Vec m) (hx : T.good x) (D : ℚ) (hD : 0 ≤ D)
    (hfirst : Within C.w D (T.f x) x) :
    ∀ n, Within C.w (D*(1/2:ℚ)^n) (orbit T.f x (n+1)) (orbit T.f x n) := by
  intro n
  induction n with
  | zero => simpa [orbit] using hfirst
  | succ n ih =>
    have hr : 0 ≤ D*(1/2:ℚ)^n := mul_nonneg hD (pow_nonneg (by norm_num) _)
    have h := half_contract T (orbit_good T x hx (n+1)) (orbit_good T x hx n) hr ih
    have he : (D*(1/2:ℚ)^n)/2 = D*(1/2:ℚ)^(n+1) := by rw [pow_succ]; ring
    rw [he] at h
    simpa only [orbit] using h

/-- The exact finite geometric tail, before any interpretation by real numbers. -/
theorem finite_segment {m : Nat} {C : HalfCertificate m} (T : LocalMap C)
    (x : Vec m) (hx : T.good x) (D : ℚ) (hD : 0 ≤ D)
    (hfirst : Within C.w D (T.f x) x) (n : Nat) :
    ∀ j, Within C.w (2*D*(1/2:ℚ)^n*(1-(1/2:ℚ)^j))
      (orbit T.f x (n+j)) (orbit T.f x n) := by
  intro j
  induction j with
  | zero => simpa using within_refl C.w (orbit T.f x n)
  | succ j ih =>
    have hinc := increment_bound T x hx D hD hfirst (n+j)
    have h := within_triangle hinc ih
    have he : D*(1/2:ℚ)^(n+j)+2*D*(1/2:ℚ)^n*(1-(1/2:ℚ)^j) =
        2*D*(1/2:ℚ)^n*(1-(1/2:ℚ)^(j+1)) := by
      rw [pow_add, pow_succ]
      ring
    rw [he] at h
    simpa only [Nat.add_assoc] using h

theorem finite_tail {m : Nat} {C : HalfCertificate m} (T : LocalMap C)
    (x : Vec m) (hx : T.good x) (D : ℚ) (hD : 0 ≤ D)
    (hfirst : Within C.w D (T.f x) x) (n j : Nat) :
    Within C.w (2*D*(1/2:ℚ)^n) (orbit T.f x (n+j)) (orbit T.f x n) := by
  apply within_mono (fun i => le_of_lt (C.weight_pos i)) _
    (finite_segment T x hx D hD hfirst n j)
  have hp : 0 ≤ (1/2:ℚ)^j := pow_nonneg (by norm_num) _
  have hc : 0 ≤ 2*D*(1/2:ℚ)^n := by positivity
  nlinarith

/-- A finite maximum witness is explicit data, not a choice of a real maximizer. -/
structure MaxWitness {m : Nat} (w x y : Vec m) where
  E : ℚ
  nonneg : 0 ≤ E
  index : Fin m
  upper : Within w E x y
  attains : |x index-y index| = E*w index

theorem maxWitness_exists {m : Nat} (hm : 0 < m) (w x y : Vec m)
    (hw : ∀ i, 0 < w i) : Nonempty (MaxWitness w x y) := by
  let ratio := fun i : Fin m => |x i-y i| / w i
  let S : Finset ℚ := Finset.univ.image ratio
  let i0 : Fin m := ⟨0,hm⟩
  have hS : S.Nonempty := ⟨ratio i0, by simp [S]⟩
  let E := S.max' hS
  have hmem : E ∈ S := Finset.max'_mem S hS
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hmem
  have upper (j : Fin m) : ratio j ≤ E :=
    Finset.le_max' S (ratio j) (by simp [S])
  refine ⟨⟨E, ?_, i, ?_, ?_⟩⟩
  · exact le_trans (div_nonneg (abs_nonneg _) (le_of_lt (hw i0))) (upper i0)
  · intro j
    exact (div_le_iff₀ (hw j)).mp (upper j)
  · exact (div_eq_iff (ne_of_gt (hw i))).mp hi

/-- Finite residual comparison: two approximate fixed points are close. -/
theorem residual_comparison {m : Nat} {C : HalfCertificate m} (T : LocalMap C)
    {x y : Vec m} (hx : T.good x) (hy : T.good y) {r s : ℚ}
    (rx : Within C.w r (T.f x) x) (ry : Within C.w s (T.f y) y)
    (M : MaxWitness C.w x y) : Within C.w (2*(r+s)) x y := by
  have mid := half_contract T hx hy M.nonneg M.upper
  have whole := within_triangle (within_triangle (within_symm rx) mid) ry
  have at := whole M.index
  rw [M.attains] at at
  have hE : M.E ≤ (r+M.E/2)+s := (mul_le_mul_right (C.weight_pos M.index)).mp at
  have hb : M.E ≤ 2*(r+s) := by linarith
  exact within_mono (fun i => le_of_lt (C.weight_pos i)) hb M.upper

end FiniteFeedback
