import Mathlib.Data.List.Nodup
import Mathlib.Data.Nat.Sqrt

/-!
# Transparent enumeration of positive reduced quadratic forms

The discriminant is `-D`. The inequalities of a reduced form imply
`3a² ≤ D`, and once `a,b` are chosen the third coefficient is
determined. The list enumerator has a proved membership criterion
and contains each triple only once.
-/

namespace GRHArticle.ClassGroups

/-- The coefficients of a positive definite integral binary quadratic form. -/
@[ext] structure ReducedQuadraticForm where
  a : ℕ
  b : ℤ
  c : ℕ
  deriving DecidableEq, Repr

/-- A primitive reduced form of discriminant `-D`, with nonnegative
middle coefficient when either reduction inequality is an equality. -/
def PrimitiveReducedAt (D : ℕ) (f : ReducedQuadraticForm) : Prop :=
  0 < f.a ∧ f.b.natAbs ≤ f.a ∧ f.a ≤ f.c ∧
  f.b.natAbs^2+D = 4*f.a*f.c ∧ Nat.gcd f.a (Nat.gcd f.b.natAbs f.c) = 1 ∧
  (0 ≤ f.b ∨ (f.b.natAbs < f.a ∧ f.a < f.c))

instance (D : ℕ) (f : ReducedQuadraticForm) : Decidable (PrimitiveReducedAt D f) := by
  unfold PrimitiveReducedAt
  infer_instance

/-- The natural discriminant bound on the leading coefficient. -/
theorem leading_le_sqrt_of_primitiveReducedAt {D : ℕ} {f : ReducedQuadraticForm}
    (h : PrimitiveReducedAt D f) : f.a ≤ (D/3).sqrt := by
  obtain ⟨_,hb,hc,hd,_,_⟩ := h
  have hb' := Nat.pow_le_pow_left hb 2
  have hc' := Nat.mul_le_mul_left f.a hc
  rw [Nat.mul_assoc] at hd
  apply Nat.le_sqrt'.mpr
  apply (Nat.le_div_iff_mul_le (by decide : 0 < 3)).mpr
  calc
    f.a^2 * 3 ≤ 4*(f.a*f.c) - f.b.natAbs^2 := by
      simp only [Nat.pow_two] at hb' ⊢
      omega
    _ = D := by omega

private def quadraticFormCandidate (D a i : ℕ) : ReducedQuadraticForm :=
  let b := (i:ℤ)-a
  ⟨a,b,(b.natAbs^2+D)/(4*a)⟩

/-- Primitive reduced forms of the given discriminant with specified `a`. -/
def reducedQuadraticFormsAt (D a : ℕ) : List ReducedQuadraticForm :=
  ((List.range (2*a+1)).map (quadraticFormCandidate D a)).filter
    (fun f ↦ decide (PrimitiveReducedAt D f))

theorem mem_reducedQuadraticFormsAt {D a : ℕ} {f : ReducedQuadraticForm} :
    f ∈ reducedQuadraticFormsAt D a ↔ f.a = a ∧ PrimitiveReducedAt D f := by
  constructor
  · intro h
    obtain ⟨hm,h⟩ := List.mem_filter.mp h
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hm
    exact ⟨rfl,of_decide_eq_true h⟩
  · rintro ⟨rfl,h⟩
    have hvalid := h
    obtain ⟨ha,hb,_,hdisc,_,_⟩ := h
    have hba : (f.b.natAbs : ℤ) ≤ f.a := Int.ofNat_le.mpr hb
    have hbb : -(f.a:ℤ) ≤ f.b ∧ f.b ≤ f.a := by
      by_cases hb₀ : 0 ≤ f.b
      · rw [Int.ofNat_natAbs_of_nonneg hb₀] at hba
        omega
      · rw [Int.ofNat_natAbs_of_nonpos (by omega : f.b ≤ 0)] at hba
        omega
    let i := (f.b+(f.a:ℤ)).toNat
    have hi : (i:ℤ) = f.b+(f.a:ℤ) := Int.toNat_of_nonneg (by omega)
    have hib : i < 2*f.a+1 := by omega
    have hc : quadraticFormCandidate D f.a i = f := by
      have hB : (i:ℤ) - f.a = f.b := by omega
      ext
      · rfl
      · exact hB
      · change (((i:ℤ)-f.a).natAbs^2+D)/(4*f.a) = _
        rw [hB,hdisc,Nat.mul_div_cancel_left _ (Nat.mul_pos (by decide) ha)]
    exact List.mem_filter.mpr ⟨List.mem_map.mpr ⟨i,List.mem_range.mpr hib,hc⟩,decide_eq_true hvalid⟩

theorem nodup_reducedQuadraticFormsAt (D a : ℕ) : (reducedQuadraticFormsAt D a).Nodup := by
  apply List.Nodup.filter
  apply (List.nodup_range).map
  intro i j h
  have he := congrArg ReducedQuadraticForm.b h
  change (i:ℤ)-a = (j:ℤ)-a at he
  omega

/-- List of forms with leading coefficient in `[a,a+len)`. -/
def reducedQuadraticFormsWindow (D a len : ℕ) : List ReducedQuadraticForm :=
  (List.range' a len).flatMap (reducedQuadraticFormsAt D)

/-- All primitive reduced forms of discriminant `-D`. -/
def reducedQuadraticForms (D : ℕ) : List ReducedQuadraticForm :=
  reducedQuadraticFormsWindow D 1 (D/3).sqrt

theorem mem_reducedQuadraticForms {D : ℕ} {f : ReducedQuadraticForm} :
    f ∈ reducedQuadraticForms D ↔ PrimitiveReducedAt D f := by
  constructor
  · intro hf
    obtain ⟨a,_,ha⟩ := List.mem_flatMap.mp hf
    exact (mem_reducedQuadraticFormsAt.mp ha).2
  · intro h
    have hA := leading_le_sqrt_of_primitiveReducedAt h
    have ha : 0 < f.a := h.1
    apply List.mem_flatMap.mpr
    exact ⟨f.a, List.mem_range'_1.mpr (by omega), mem_reducedQuadraticFormsAt.mpr ⟨rfl,h⟩⟩

theorem nodup_reducedQuadraticForms (D : ℕ) : (reducedQuadraticForms D).Nodup := by
  apply List.nodup_flatMap.mpr
  refine ⟨fun a _ ↦ nodup_reducedQuadraticFormsAt D a, ?_⟩
  apply (List.nodup_range' (s := 1) (n := (D/3).sqrt)).imp
  intro a b h
  apply List.disjoint_left.mpr
  intro f ha hb
  exact h ((mem_reducedQuadraticFormsAt.mp ha).1.symm.trans (mem_reducedQuadraticFormsAt.mp hb).1)

/-- Number of forms in a consecutive range of leading coefficients. -/
def reducedQuadraticFormCountWindow (D a len : ℕ) : ℕ :=
  (reducedQuadraticFormsWindow D a len).length

theorem reducedQuadraticFormCountWindow_append (D a m n : ℕ) :
    reducedQuadraticFormCountWindow D a (m+n) =
      reducedQuadraticFormCountWindow D a m + reducedQuadraticFormCountWindow D (a+m) n := by
  simp only [reducedQuadraticFormCountWindow, reducedQuadraticFormsWindow,
    ← List.range'_append_1 (s := a) (m := m) (n := n), List.flatMap_append, List.length_append]

/-- Exact reduced-form count at the specified negative discriminant. -/
def reducedQuadraticFormCount (D : ℕ) : ℕ :=
  reducedQuadraticFormCountWindow D 1 (D/3).sqrt

end GRHArticle.ClassGroups
