import GowersSzemeredi.Proofs16FreimanFamilyRestriction
import GowersSzemeredi.Proofs16CubicCoverControls

/-! Dimension-one stackability as an algebra of Freiman covers.

`RelFreimanCover q R` says that a dimension-one relation `R` lies in a
union of `q` graphs of Freiman 8-homomorphisms. These relations are closed
under subsets, translation and finite unions (counts add). Every member
has the cubic `MultiplyLinearWith` cover with count `3q` and exponent
`cubicBaseExponent q`, which is polynomial in `q`. This is exactly what
the simultaneous union of pieces needs in dimension two: spectra, face
remainders and stacked slices of many pieces are all such unions.
* `RelFreimanCover.mono`, `.pad`, `.translate`, `relFreimanCover_union`.
* `relFreimanCover_of_familyCover` (from `Section16FreimanFamilyCover`).
* `RelFreimanCover.cubic_cover`. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- A dimension-one relation inside a union of `q` Freiman graphs. -/
def RelFreimanCover {N : Nat} [NeZero N] (q : Nat) (R : Finset (Point N 1 × ZMod N)) : Prop :=
  ∃ (D : Fin q → Finset (Point N 1)) (f : Fin q → Point N 1 → ZMod N),
    (∀ i, FreimanHom 8 (pointOneDomain (D i)) (pointOneMap (f i))) ∧
    R ⊆ section16FinsetUnion (fun i => partialGraph (D i) (f i))

theorem RelFreimanCover.mono {N q : Nat} [NeZero N] {R R' : Finset (Point N 1 × ZMod N)}
    (h : RelFreimanCover q R) (hsub : R' ⊆ R) : RelFreimanCover q R' := by
  obtain ⟨D, f, hf, hc⟩ := h
  exact ⟨D, f, hf, hsub.trans hc⟩

theorem relFreimanCover_of_familyCover {N q : Nat} [NeZero N]
    {B : Finset (Point N 1)} {phi : Point N 1 → ZMod N}
    (h : Section16FreimanFamilyCover q B phi) : RelFreimanCover q (partialGraph B phi) :=
  h

/-- More graphs may be allowed: pad with empty graphs. -/
theorem RelFreimanCover.pad {N q q' : Nat} [NeZero N] {R : Finset (Point N 1 × ZMod N)}
    (h : RelFreimanCover q R) (hqq' : q ≤ q') : RelFreimanCover q' R := by
  classical
  obtain ⟨D, f, hf, hc⟩ := h
  let D' : Fin q' → Finset (Point N 1) := fun i => if hi : i.val < q then D ⟨i.val, hi⟩ else ∅
  let f' : Fin q' → Point N 1 → ZMod N := fun i => if hi : i.val < q then f ⟨i.val, hi⟩ else 0
  refine ⟨D', f', ?_, ?_⟩
  · intro i
    by_cases hi : i.val < q
    · simp only [D', f', dif_pos hi]
      exact hf _
    · simp only [D', f', dif_neg hi]
      show IsAddFreimanHom 8 _ Set.univ (fun _ => (0 : ZMod N))
      exact isAddFreimanHom_const (Set.mem_univ _)
  · intro z hz
    have hz' := hc hz
    unfold section16FinsetUnion at hz' ⊢
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp hz'
    apply Finset.mem_biUnion.mpr
    refine ⟨⟨i.val, i.isLt.trans_le hqq'⟩, Finset.mem_univ _, ?_⟩
    simp only [D', f', dif_pos i.isLt]
    exact hi

/-- Translation of the base point. -/
theorem RelFreimanCover.translate {N q : Nat} [NeZero N] {R : Finset (Point N 1 × ZMod N)}
    (h : RelFreimanCover q R) (t : Point N 1) :
    RelFreimanCover q (R.image (fun z => (z.1 + t, z.2))) := by
  classical
  obtain ⟨D, f, hf, hc⟩ := h
  let D' := fun i => (D i).image (fun x => x + t)
  let f' := fun i x => f i (x - t)
  refine ⟨D', f', ?_, ?_⟩
  · intro i
    have hh := (hf i).translate_input (-(t 0)) (J := pointOneDomain (D' i)) (by
      intro z hz
      rw [mem_pointOneDomain] at hz ⊢
      obtain ⟨x, hx, heq⟩ := Finset.mem_image.mp hz
      have heval := congrFun heq 0
      have hpoint : (pointOneEquiv N).symm (-t 0 + z) = x := by
        funext j
        fin_cases j
        change -t 0 + z = x 0
        change x 0 + t 0 = z at heval
        rw [← heval]
        abel
      rwa [hpoint])
    convert hh using 1
    funext z
    change f i ((pointOneEquiv N).symm z - t) = f i ((pointOneEquiv N).symm (-t 0 + z))
    congr 1
    funext j
    fin_cases j
    change z - t 0 = -t 0 + z
    abel
  · intro z hz
    obtain ⟨⟨x, y⟩, hxy, rfl⟩ := Finset.mem_image.mp hz
    have horig := hc hxy
    unfold section16FinsetUnion at horig ⊢
    obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp horig
    obtain ⟨w, hw, heq⟩ := Finset.mem_image.mp hi
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj heq
    apply Finset.mem_biUnion.mpr
    refine ⟨i, Finset.mem_univ _, Finset.mem_image.mpr ⟨w + t, ?_, ?_⟩⟩
    · exact Finset.mem_image.mpr ⟨w, hw, rfl⟩
    · simp [f', add_sub_cancel_right]

/-- **Finite unions add the counts.** -/
theorem relFreimanCover_union {N q m : Nat} [NeZero N]
    (R : Fin m → Finset (Point N 1 × ZMod N)) (h : ∀ c, RelFreimanCover q (R c)) :
    RelFreimanCover (m * q) (Finset.univ.biUnion R) := by
  classical
  choose D f hf hc using h
  let e : Fin (m * q) ≃ Fin m × Fin q := finProdFinEquiv.symm
  refine ⟨fun i => D (e i).1 (e i).2, fun i => f (e i).1 (e i).2, fun i => hf _ _, ?_⟩
  intro z hz
  obtain ⟨c, -, hzc⟩ := Finset.mem_biUnion.mp hz
  have h1 := hc c hzc
  unfold section16FinsetUnion at h1 ⊢
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp h1
  apply Finset.mem_biUnion.mpr
  refine ⟨e.symm (c, i), Finset.mem_univ _, ?_⟩
  simpa only [Equiv.apply_symm_apply] using hi

/-- **The cubic cover of a Freiman union.** -/
theorem RelFreimanCover.cubic_cover {N q : Nat} [NeZero N] [Fact N.Prime]
    {R : Finset (Point N 1 × ZMod N)} (h : RelFreimanCover q R) (hq : 0 < q) :
    MultiplyLinearWith (fun _ => ((3 * q : Nat) : Real)) (cubicBaseExponent q) R := by
  obtain ⟨D, f, hf, hc⟩ := h
  exact section16_freiman_family_cubic_cover hq D f hf R hc

end LeanProofs.GowersSzemeredi
