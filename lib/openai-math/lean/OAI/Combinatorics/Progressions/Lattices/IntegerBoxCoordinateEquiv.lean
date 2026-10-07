import OAI.Combinatorics.Progressions.Estimates.RelativePatchAmplification

namespace OAI

section

namespace Erdos3

open scoped BigOperators

variable {X Y : Type*}

def coordinateReindexedSides (e : X ≃ Y) (N : X → ℕ) : Y → ℕ :=
  fun y => N (e.symm y)

def coordinateReindexedFunction (e : X ≃ Y) (f : (X → ℤ) → ℝ) : (Y → ℤ) → ℝ :=
  fun y => f (fun x => y (e x))

variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

theorem coordinateReindexedSides_mem_integerBox (e : X ≃ Y) (N : X → ℕ) (y : Y → ℤ) :
    y ∈ integerBox (coordinateReindexedSides e N) ↔
      (fun x => y (e x)) ∈ integerBox N := by
  simp only [mem_integerBox, coordinateReindexedSides]
  constructor
  · intro hy x
    simpa only [e.symm_apply_apply] using hy (e x)
  · intro hy j
    simpa only [e.apply_symm_apply] using hy (e.symm j)

theorem coordinateReindexedFunction_expect (e : X ≃ Y) (N : X → ℕ)
    (f : (X → ℤ) → ℝ) :
    (𝔼 y ∈ integerBox (coordinateReindexedSides e N), coordinateReindexedFunction e f y) =
      𝔼 x ∈ integerBox N, f x := by
  apply Finset.expect_bij (fun y _ x => y (e x))
  · intro y hy
    exact (coordinateReindexedSides_mem_integerBox e N y).mp hy
  · intro y _
    rfl
  · intro y _ z _ he
    funext j
    simpa only [e.apply_symm_apply] using congrFun he (e.symm j)
  · intro x hx
    refine ⟨fun j => x (e.symm j), ?_, ?_⟩
    · apply (coordinateReindexedSides_mem_integerBox e N _).mpr
      simpa only [e.symm_apply_apply] using hx
    · funext i
      simp only [e.symm_apply_apply]

theorem coordinateReindexedFunction_bounds (e : X ≃ Y) (N : X → ℕ)
    (f : (X → ℤ) → ℝ) (hf : ∀ x ∈ integerBox N, f x ∈ Set.Icc (0 : ℝ) 1) :
    ∀ y ∈ integerBox (coordinateReindexedSides e N),
      coordinateReindexedFunction e f y ∈ Set.Icc (0 : ℝ) 1 := by
  intro y hy
  exact hf _ ((coordinateReindexedSides_mem_integerBox e N y).mp hy)

theorem coordinateReindexedFunction_apFree (e : X ≃ Y) (N : X → ℕ)
    (f : (X → ℤ) → ℝ) {k : ℕ}
    (hfree : IntegerVectorAPFree {x | x ∈ integerBox N ∧ f x ≠ 0} k) :
    IntegerVectorAPFree
      {y | y ∈ integerBox (coordinateReindexedSides e N) ∧
        coordinateReindexedFunction e f y ≠ 0} k := by
  intro a d hd
  have hd' : (fun x => d (e x)) ≠ 0 := by
    intro hzero
    apply hd
    funext j
    simpa only [e.apply_symm_apply, Pi.zero_apply] using congrFun hzero (e.symm j)
  obtain ⟨i, hi⟩ := hfree (fun x => a (e x)) (fun x => d (e x)) hd'
  refine ⟨i, ?_⟩
  rintro ⟨hbox, hnonzero⟩
  apply hi
  refine ⟨?_, ?_⟩
  · exact (coordinateReindexedSides_mem_integerBox e N _).mp hbox
  · exact hnonzero

end Erdos3

end

section

namespace Erdos3

variable {X Y : Type*}

def integerPointCoordinateEquiv (e : X ≃ Y) : (X → ℤ) ≃ (Y → ℤ) where
  toFun x y := x (e.symm y)
  invFun y x := y (e x)
  left_inv x := by funext i; simp only [e.symm_apply_apply]
  right_inv y := by funext j; simp only [e.apply_symm_apply]

@[simp] theorem integerPointCoordinateEquiv_apply (e : X ≃ Y) (x : X → ℤ) (y : Y) :
    integerPointCoordinateEquiv e x y = x (e.symm y) := rfl

@[simp] theorem integerPointCoordinateEquiv_symm_apply (e : X ≃ Y) (y : Y → ℤ) (x : X) :
    (integerPointCoordinateEquiv e).symm y x = y (e x) := rfl

@[simp] theorem integerPointCoordinateEquiv_symm (e : X ≃ Y) :
    integerPointCoordinateEquiv e.symm = (integerPointCoordinateEquiv e).symm := rfl

variable [Fintype X] [Fintype Y] [DecidableEq X] [DecidableEq Y]

@[simp] theorem integerPointCoordinateEquiv_mem_integerBox (e : X ≃ Y)
    (N : X → ℕ) (x : X → ℤ) :
    integerPointCoordinateEquiv e x ∈ integerBox (coordinateReindexedSides e N) ↔
      x ∈ integerBox N := by
  rw [coordinateReindexedSides_mem_integerBox]
  simp only [integerPointCoordinateEquiv_apply, e.symm_apply_apply]

def integerBoxCoordinateEquiv (e : X ≃ Y) (N : X → ℕ) :
    integerBox N ≃ integerBox (coordinateReindexedSides e N) where
  toFun x := ⟨integerPointCoordinateEquiv e x.val,
    (integerPointCoordinateEquiv_mem_integerBox e N x.val).mpr x.property⟩
  invFun y := ⟨(integerPointCoordinateEquiv e).symm y.val,
    (coordinateReindexedSides_mem_integerBox e N y.val).mp y.property⟩
  left_inv x := by apply Subtype.ext; exact (integerPointCoordinateEquiv e).left_inv x.val
  right_inv y := by apply Subtype.ext; exact (integerPointCoordinateEquiv e).right_inv y.val

@[simp] theorem integerBoxCoordinateEquiv_val (e : X ≃ Y) (N : X → ℕ)
    (x : integerBox N) :
    (integerBoxCoordinateEquiv e N x).val = integerPointCoordinateEquiv e x.val := rfl

@[simp] theorem integerBoxCoordinateEquiv_symm_val (e : X ≃ Y) (N : X → ℕ)
    (y : integerBox (coordinateReindexedSides e N)) :
    ((integerBoxCoordinateEquiv e N).symm y).val =
      (integerPointCoordinateEquiv e).symm y.val := rfl

theorem integerBox_map_coordinateEquiv (e : X ≃ Y) (N : X → ℕ) :
    (integerBox N).map (integerPointCoordinateEquiv e).toEmbedding =
      integerBox (coordinateReindexedSides e N) := by
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := Finset.mem_map.mp hy
    exact (integerPointCoordinateEquiv_mem_integerBox e N x).mpr hx
  · intro hy
    refine Finset.mem_map.mpr ⟨(integerPointCoordinateEquiv e).symm y, ?_, ?_⟩
    · exact (coordinateReindexedSides_mem_integerBox e N y).mp hy
    · exact (integerPointCoordinateEquiv e).apply_symm_apply y

theorem integerBox_image_coordinateEquiv (e : X ≃ Y) (N : X → ℕ) :
    (integerBox N).image (integerPointCoordinateEquiv e) =
      integerBox (coordinateReindexedSides e N) := by
  classical
  exact (Finset.map_eq_image (integerPointCoordinateEquiv e).toEmbedding (integerBox N)).symm.trans
    (integerBox_map_coordinateEquiv e N)

end Erdos3

end

end OAI
