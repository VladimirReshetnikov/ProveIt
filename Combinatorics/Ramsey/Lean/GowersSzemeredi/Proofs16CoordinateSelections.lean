import GowersSzemeredi.Proofs16FaceLifts
import GowersSzemeredi.Proofs16SlabProductProperty

/-! Vertex maps as product functions of `k` coordinates (Notes L.6, E3).

In the original frame `w = z + (x₀, 0)`, the translated vertex `φ_e` of
Gowers's identity reads `w` on the coordinates where `e` is true and on the
last one, and reads the base point `x₀` elsewhere:
`φ_e(w) = φ(selectPt (snoc e true) (snoc x₀ 0) w)` (`translatedVertex_point`).
For `e ≠ 1` pick `i` with `e i = false`. Then `φ_e(w) = faceSel φ x₀ e i
(dropAt (castSucc i) w)`, a function of `k` coordinates
(`selectPt_vertex_eq_face`). Its graph is a `k`-dimensional product relation
(`faceSel_product`), so the uniform class of dimension `k` covers it.

The product property passes through any coordinate map whose input
coordinates each move one output coordinate or nothing
(`HasProductProperty.comp_of_coordinates`). An ignored input gives constant
restrictions, and constant parallel maps have the full additive energy
`N⁻¹(Σθ)⁴` (`weightedSimultaneousAdditiveEnergy_constants`). This covers
coordinate faces, frozen coordinates and dummy coordinates at once. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- **The product property passes through coordinate maps.** Every input
coordinate `j` either moves the single output coordinate `r j = some m`, or
(`r j = none`) leaves the image unchanged. -/
theorem HasProductProperty.comp_of_coordinates {N d l : Nat} [NeZero N]
    {B : Finset (Point N d)} {phi : Point N d → ZMod N} {gamma : Real}
    (h : HasProductProperty B phi gamma) (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1)
    (A : Point N l → Point N d) (r : Fin l → Option (Fin d))
    (hsome : ∀ y j m x, r j = some m → A (replaceCoordinate y j x) = replaceCoordinate (A y) m x)
    (hnone : ∀ y j x, r j = none → A (replaceCoordinate y j x) = A y) :
    HasProductProperty ((Finset.univ : Finset (Point N l)).filter fun y => A y ∈ B)
      (fun y => phi (A y)) gamma := by
  classical
  intro p j y E theta htheta hE
  cases hr : r j with
  | none =>
    have hfun : (fun i : Fin p => coordinateRestriction (fun y => phi (A y)) (y i) j) =
        (fun i _ => phi (A (y i))) := by
      funext i x
      show phi (A (replaceCoordinate (y i) j x)) = _
      rw [hnone _ _ _ hr]
    rw [hfun, weightedSimultaneousAdditiveEnergy_constants]
    have hz := section16_zero_parallel_energy (p := p) E theta
    have hpow : gamma ^ (8 * p) ≤ 1 := pow_le_one₀ hg0 hg1
    have hnn : 0 ≤ (N : Real)⁻¹ * (∑ x ∈ E, theta x) ^ 4 := by positivity
    calc gamma ^ (8 * p) * (N : Real)⁻¹ * (∑ x ∈ E, theta x) ^ 4
        = gamma ^ (8 * p) * ((N : Real)⁻¹ * (∑ x ∈ E, theta x) ^ 4) := by ring
      _ ≤ 1 * ((N : Real)⁻¹ * (∑ x ∈ E, theta x) ^ 4) := mul_le_mul_of_nonneg_right hpow hnn
      _ = (N : Real)⁻¹ * (∑ x ∈ E, theta x) ^ 4 := one_mul _
      _ ≤ _ := hz
  | some m =>
    have hh := h p m (fun i => A (y i)) E theta htheta (by
      intro i x hx
      have hmem := (Finset.mem_filter.mp (hE i x hx)).2
      rw [hsome _ _ _ _ hr] at hmem
      exact hmem)
    have hfun : (fun i => coordinateRestriction (fun y => phi (A y)) (y i) j) =
        (fun i => coordinateRestriction phi (A (y i)) m) := by
      funext i x
      show phi (A (replaceCoordinate (y i) j x)) = _
      rw [hsome _ _ _ _ hr]
      rfl
    rw [hfun]
    exact hh

/-! ### Masked selections -/

/-- Read `w` where the mask is true and the anchor `a` elsewhere. -/
def selectPt {N d : Nat} (mask : Fin d → Bool) (a w : Point N d) : Point N d :=
  fun m => if mask m then w m else a m

theorem selectPt_update_true {N d : Nat} {mask : Fin d → Bool} (a w : Point N d) {m : Fin d}
    (hm : mask m = true) (x : ZMod N) :
    selectPt mask a (Function.update w m x) = Function.update (selectPt mask a w) m x := by
  funext m'
  by_cases h : m' = m
  · subst h; simp [selectPt, hm]
  · simp [selectPt, Function.update_of_ne h]

theorem selectPt_update_false {N d : Nat} {mask : Fin d → Bool} (a w : Point N d) {m : Fin d}
    (hm : mask m = false) (x : ZMod N) :
    selectPt mask a (Function.update w m x) = selectPt mask a w := by
  funext m'
  by_cases h : m' = m
  · subst h; simp [selectPt, hm]
  · simp [selectPt, Function.update_of_ne h]

/-- **The translated vertex in the original frame.** -/
theorem translatedVertex_point {N k : Nat} (x0 : Point N k) (e : Fin k → Bool) (z : Point N (k + 1)) :
    appendCoordinate (fun i => x0 i + if e i then section16Init z i else 0) (section16Last z) =
      selectPt (Fin.snoc e true) (Fin.snoc x0 0) (z + appendCoordinate x0 0) := by
  funext m
  rw [appendCoordinate_eq_snoc, appendCoordinate_eq_snoc]
  refine Fin.lastCases ?_ (fun j => ?_) m
  · simp [selectPt, section16Last]
  · cases hj : e j
    · simp [selectPt, hj]
    · simp [selectPt, hj, section16Init, add_comm]

/-- The vertex map `w ↦ φ(selectPt … w)` as a function of the coordinates
other than `castSucc i`. -/
def faceSel {N k : Nat} (phi : Point N (k + 1) → ZMod N) (x0 : Point N k) (e : Fin k → Bool)
    (i : Fin k) (y : Point N k) : ZMod N :=
  phi (selectPt (Fin.snoc e true) (Fin.snoc x0 0) (Fin.insertNth i.castSucc 0 y))

/-- The domain of `faceSel` inside `B`. -/
def faceSelDomain {N k : Nat} [NeZero N] (B : Finset (Point N (k + 1))) (x0 : Point N k)
    (e : Fin k → Bool) (i : Fin k) : Finset (Point N k) := by
  classical
  exact Finset.univ.filter fun y =>
    selectPt (Fin.snoc e true) (Fin.snoc x0 0) (Fin.insertNth i.castSucc 0 y) ∈ B

theorem mask_castSucc {k : Nat} (e : Fin k → Bool) (i : Fin k) :
    (Fin.snoc e true : Fin (k + 1) → Bool) i.castSucc = e i := by
  simp

/-- **When `e i = false`, the selection ignores coordinate `castSucc i`.** -/
theorem selectPt_vertex_eq_drop {N k : Nat} (x0 : Point N k) {e : Fin k → Bool} {i : Fin k}
    (hi : e i = false) (w : Point N (k + 1)) :
    selectPt (Fin.snoc e true) (Fin.snoc x0 0) w =
      selectPt (Fin.snoc e true) (Fin.snoc x0 0)
        (Fin.insertNth i.castSucc 0 (dropAt i.castSucc w)) := by
  unfold dropAt
  rw [Fin.insertNth_removeNth, selectPt_update_false]
  rw [mask_castSucc, hi]

theorem selectPt_vertex_eq_face {N k : Nat} (phi : Point N (k + 1) → ZMod N) (x0 : Point N k)
    {e : Fin k → Bool} {i : Fin k} (hi : e i = false) (w : Point N (k + 1)) :
    phi (selectPt (Fin.snoc e true) (Fin.snoc x0 0) w) = faceSel phi x0 e i (dropAt i.castSucc w) := by
  unfold faceSel
  rw [← selectPt_vertex_eq_drop x0 hi]

theorem mem_faceSelDomain {N k : Nat} [NeZero N] {B : Finset (Point N (k + 1))} {x0 : Point N k}
    {e : Fin k → Bool} {i : Fin k} (hi : e i = false) {w : Point N (k + 1)}
    (hw : selectPt (Fin.snoc e true) (Fin.snoc x0 0) w ∈ B) :
    dropAt i.castSucc w ∈ faceSelDomain B x0 e i := by
  classical
  unfold faceSelDomain
  refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
  rw [← selectPt_vertex_eq_drop x0 hi]
  exact hw

/-- **A vertex face is a `k`-dimensional product function.** -/
theorem faceSel_product {N k : Nat} [NeZero N] {B : Finset (Point N (k + 1))}
    {phi : Point N (k + 1) → ZMod N} {gamma : Real} (h : HasProductProperty B phi gamma)
    (hg0 : 0 ≤ gamma) (hg1 : gamma ≤ 1) (x0 : Point N k) (e : Fin k → Bool) (i : Fin k) :
    HasProductProperty (faceSelDomain B x0 e i) (faceSel phi x0 e i) gamma := by
  classical
  have hmain := h.comp_of_coordinates hg0 hg1
    (fun y => selectPt (Fin.snoc e true) (Fin.snoc x0 0) (Fin.insertNth i.castSucc 0 y))
    (fun j => if (Fin.snoc e true : Fin (k + 1) → Bool) (i.castSucc.succAbove j) = true
      then some (i.castSucc.succAbove j) else none)
    (by
      intro y j m x hr
      by_cases hm : (Fin.snoc e true : Fin (k + 1) → Bool) (i.castSucc.succAbove j) = true
      · simp only [hm, if_true, Option.some.injEq] at hr
        subst hr
        simp only [replaceCoordinate]
        rw [Fin.insertNth_update, selectPt_update_true _ _ hm]
      · simp [hm] at hr)
    (by
      intro y j x hr
      by_cases hm : (Fin.snoc e true : Fin (k + 1) → Bool) (i.castSucc.succAbove j) = true
      · simp [hm] at hr
      · have hf : (Fin.snoc e true : Fin (k + 1) → Bool) (i.castSucc.succAbove j) = false := by
          simpa using hm
        simp only [replaceCoordinate]
        rw [Fin.insertNth_update, selectPt_update_false _ _ hf])
  have hdom : faceSelDomain B x0 e i = (Finset.univ : Finset (Point N k)).filter fun y =>
      selectPt (Fin.snoc e true) (Fin.snoc x0 0) (Fin.insertNth i.castSucc 0 y) ∈ B := by
    unfold faceSelDomain; rfl
  rw [hdom]
  exact hmain

end LeanProofs.GowersSzemeredi
