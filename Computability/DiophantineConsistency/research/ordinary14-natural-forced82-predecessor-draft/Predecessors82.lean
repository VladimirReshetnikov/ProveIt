import Natural82Model

/-! Source-only conditional arithmetic helper. None of these declarations
has been elaborated, and the hypotheses must be obtained from the factors. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.Predecessors82Draft
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ModelDifferenceRing Natural82ModelDraft
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- For a nonnegative `a`, the auxiliary discriminant exceeds one. -/
theorem delta_gt_one (a : DiffRing V) (ha : 0 ≤ a) :
    1 < a*a + 4*a + 3 := by
  nlinarith [sq_nonneg a]

/-- A positive strong factor excludes f=0. -/
theorem f_nonzero (a f I : DiffRing V) (ha : 0 ≤ a)
    (hstrong : 1 + I*I - (a*a + 4*a + 3)*(f*f - 1) = 1) : f ≠ 0 := by
  intro hf
  rw [hf] at hstrong
  have hd := delta_gt_one a ha
  nlinarith [sq_nonneg I]

/-- A positive auxiliary factor excludes y=0 in a discrete ordered ring of
differences. The square term may itself be any signed ring value. -/
theorem y_nonzero (a f y v : DiffRing V) (ha : 0 ≤ a)
    (haux : y*y - (a*a + 4*a + 3)*(f*f - 1)*(y*y - v*v) = 1) : y ≠ 0 := by
  intro hy
  rw [hy] at haux
  let delta := a*a + 4*a + 3
  let t := (f*f - 1)*(v*v)
  have hd : 1 < delta := delta_gt_one a ha
  have hproduct : delta*t = 1 := by dsimp [delta, t]; nlinarith [haux]
  have ht : 0 < t := by nlinarith [hproduct]
  have ht1 : 1 ≤ t := ModelDifferenceRing.one_le_of_pos
    (fun x hx => pos_iff_one_le.mp hx) ht
  have hbound : delta ≤ delta*t := by nlinarith [mul_nonneg (show 0 ≤ delta by linarith)
    (show 0 ≤ t-1 by linarith)]
  linarith

/-- The abstract factor equations suffice for three natural predecessors.
The graph-to-equation obligations are intentionally explicit hypotheses. -/
theorem predecessors_of_factor_equations (w : Fin 14 → V)
    (a I v ellPart : DiffRing V)
    (ha : 0 ≤ a) (hell : 0 ≤ ellPart)
    (hfirst : ι (w 8)*ι (w 8) = ellPart + 1)
    (hstrong : 1 + I*I - (a*a + 4*a + 3)*(ι (w 3)*ι (w 3) - 1) = 1)
    (haux : ι (w 11)*ι (w 11) -
      (a*a + 4*a + 3)*(ι (w 3)*ι (w 3) - 1)*
        (ι (w 11)*ι (w 11) - v*v) = 1) : HasThreePredecessors w := by
  have hr : w 8 ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hfirst
    nlinarith
  have hf : w 3 ≠ 0 := by
    intro hz
    apply f_nonzero a (ι (w 3)) I ha hstrong
    rw [hz, map_zero]
  have hy : w 11 ≠ 0 := by
    intro hz
    apply y_nonzero a (ι (w 3)) (ι (w 11)) v ha haux
    rw [hz, map_zero]
  obtain ⟨f, hf⟩ := exists_add_of_le (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hf))
  obtain ⟨r, hr⟩ := exists_add_of_le (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hr))
  obtain ⟨y, hy⟩ := exists_add_of_le (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hy))
  exact ⟨f, r, y, hf, hr, hy⟩

end DiophantineConsistency.Predecessors82Draft
