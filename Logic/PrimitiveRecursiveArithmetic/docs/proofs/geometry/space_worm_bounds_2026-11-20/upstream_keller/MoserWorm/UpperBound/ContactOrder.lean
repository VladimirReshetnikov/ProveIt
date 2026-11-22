import MoserWorm.UpperBound.NormalForm
import MoserWorm.UpperBound.Certificate.RealSound

/-!
# Actual support contacts for the upper certificate

Strict unit normals in the two open half-planes determine weak cyclic
contact order, even when a support face has two vertices. Certificate labels
store the top before the right contacts; the geometric boundary order puts
the top after them.
-/

open Set

noncomputable section

namespace MoserWorm.UpperBound

open Certificate

/-- On the right unit semicircle, increasing height is increasing angle. -/
theorem cross_pos_of_right_unit {u v : Plane}
    (hu : 0 < u.re) (hv : 0 < v.re)
    (hunitu : u.re ^ 2 + u.im ^ 2 = 1)
    (hunitv : v.re ^ 2 + v.im ^ 2 = 1) (hy : u.im < v.im) :
    0 < cross u v := by
  have hx : 0 < u.re + v.re := add_pos hu hv
  have hs : 0 < (u.re + v.re) ^ 2 + (u.im + v.im) ^ 2 :=
    add_pos_of_pos_of_nonneg (sq_pos_of_pos hx) (sq_nonneg _)
  have hid :
      2 * (u.re + v.re) * cross u v =
        (v.im - u.im) * ((u.re + v.re) ^ 2 + (u.im + v.im) ^ 2) := by
    unfold cross
    linear_combination (u.im + v.im) * hunitu - (u.im + v.im) * hunitv
  have hprod := mul_pos (sub_pos.mpr hy) hs
  have hc : 0 < 2 * (u.re + v.re) * cross u v := hid ▸ hprod
  exact (mul_pos_iff_of_pos_left (mul_pos (by norm_num) hx)).mp hc

/-- On the left unit semicircle, decreasing height is increasing angle. -/
theorem cross_pos_of_left_unit {u v : Plane}
    (hu : u.re < 0) (hv : v.re < 0)
    (hunitu : u.re ^ 2 + u.im ^ 2 = 1)
    (hunitv : v.re ^ 2 + v.im ^ 2 = 1) (hy : v.im < u.im) :
    0 < cross u v := by
  have h := cross_pos_of_right_unit (u := -u) (v := -v)
    (by simpa using neg_pos.mpr hu) (by simpa using neg_pos.mpr hv)
    (by simpa using hunitu) (by simpa using hunitv)
    (by simpa using neg_lt_neg hy)
  simpa [cross] using h

namespace Certificate.LabelTables

def rightNormal (T : LabelTables) (i : Fin T.kR) : Plane :=
  qPlane (T.right.getD i.val (0, 0))

def leftNormal (T : LabelTables) (j : Fin T.kL) : Plane :=
  qPlane (T.left.getD j.val (0, 0))

theorem rightNormal_re_pos (T : LabelTables) (hT : labelsOK T = true) (i : Fin T.kR) :
    0 < (T.rightNormal i).re := by
  change 0 < ((T.right.getD i.val (0, 0)).1 : ℝ)
  exact_mod_cast ((labelsOK_props T hT).2.2.1 i.val i.isLt).1

theorem leftNormal_re_neg (T : LabelTables) (hT : labelsOK T = true) (j : Fin T.kL) :
    (T.leftNormal j).re < 0 := by
  change ((T.left.getD j.val (0, 0)).1 : ℝ) < 0
  exact_mod_cast ((labelsOK_props T hT).2.2.2.2.1 j.val j.isLt).1

private theorem qPlane_unit_coords {u : Q2} (hu : qnorm2 u = 1) :
    (qPlane u).re ^ 2 + (qPlane u).im ^ 2 = 1 := by
  change (u.1 : ℝ) ^ 2 + (u.2 : ℝ) ^ 2 = 1
  norm_cast
  simpa [qnorm2, sq] using hu

theorem rightNormal_unit_coords (T : LabelTables) (hT : labelsOK T = true)
    (i : Fin T.kR) : (T.rightNormal i).re ^ 2 + (T.rightNormal i).im ^ 2 = 1 :=
  qPlane_unit_coords ((labelsOK_props T hT).2.2.1 i.val i.isLt).2

theorem leftNormal_unit_coords (T : LabelTables) (hT : labelsOK T = true)
    (j : Fin T.kL) : (T.leftNormal j).re ^ 2 + (T.leftNormal j).im ^ 2 = 1 :=
  qPlane_unit_coords ((labelsOK_props T hT).2.2.2.2.1 j.val j.isLt).2

theorem rightNormal_im_strictMono (T : LabelTables) (hT : labelsOK T = true) :
    StrictMono (fun i => (T.rightNormal i).im) := by
  have hadj := (labelsOK_props T hT).2.2.2.1
  have hh : ∀ n, T.kR = n → StrictMono (fun i : Fin n =>
      (T.right.getD i.val (0, 0)).2) := by
    intro n hn
    cases n with
    | zero => intro i; exact Fin.elim0 i
    | succ n =>
      apply Fin.strictMono_iff_lt_succ.mpr
      intro i
      exact hadj i.val (by omega)
  intro i j hij
  change ((T.right.getD i.val (0, 0)).2 : ℝ) <
    ((T.right.getD j.val (0, 0)).2 : ℝ)
  exact_mod_cast hh T.kR rfl hij

theorem leftNormal_im_strictAnti (T : LabelTables) (hT : labelsOK T = true) :
    StrictAnti (fun j => (T.leftNormal j).im) := by
  have hadj := (labelsOK_props T hT).2.2.2.2.2
  have hh : ∀ n, T.kL = n → StrictAnti (fun i : Fin n =>
      (T.left.getD i.val (0, 0)).2) := by
    intro n hn
    cases n with
    | zero => intro i; exact Fin.elim0 i
    | succ n =>
      apply Fin.strictAnti_iff_succ_lt.mpr
      intro i
      exact hadj i.val (by omega)
  intro i j hij
  change ((T.left.getD j.val (0, 0)).2 : ℝ) <
    ((T.left.getD i.val (0, 0)).2 : ℝ)
  exact_mod_cast hh T.kL rfl hij

theorem rightNormal_cross_pos (T : LabelTables) (hT : labelsOK T = true)
    (i j : Fin T.kR) (hij : i < j) :
    0 < cross (T.rightNormal i) (T.rightNormal j) :=
  cross_pos_of_right_unit (T.rightNormal_re_pos hT i) (T.rightNormal_re_pos hT j)
    (T.rightNormal_unit_coords hT i) (T.rightNormal_unit_coords hT j)
    (T.rightNormal_im_strictMono hT hij)

theorem leftNormal_cross_pos (T : LabelTables) (hT : labelsOK T = true)
    (i j : Fin T.kL) (hij : i < j) :
    0 < cross (T.leftNormal i) (T.leftNormal j) :=
  cross_pos_of_left_unit (T.leftNormal_re_neg hT i) (T.leftNormal_re_neg hT j)
    (T.leftNormal_unit_coords hT i) (T.leftNormal_unit_coords hT j)
    (T.leftNormal_im_strictAnti hT hij)

/-- Boundary-order labels reindexed into the certificate's anchor-first array. -/
def boundaryEquiv (T : LabelTables) : ContactIndex T.kR T.kL ≃ Fin T.nLab where
  toFun a := ⟨if a.val < 2 then a.val
    else if a.val < T.kR + 2 then a.val + 1
    else if a.val = T.kR + 2 then 2 else a.val, by
      have := a.isLt
      unfold nLab
      split_ifs <;> omega⟩
  invFun a := ⟨if a.val < 2 then a.val
    else if a.val = 2 then T.kR + 2
    else if a.val < T.kR + 3 then a.val - 1 else a.val, by
      have := a.isLt
      unfold nLab at *
      split_ifs <;> omega⟩
  left_inv a := by
    apply Fin.ext
    dsimp only
    split_ifs <;> omega
  right_inv a := by
    apply Fin.ext
    dsimp only
    split_ifs <;> omega

@[simp] theorem boundaryEquiv_minus (T : LabelTables) :
    T.boundaryEquiv (floorMinus T.kR T.kL) = ⟨0, by unfold nLab; omega⟩ := by
  apply Fin.ext
  simp [boundaryEquiv, floorMinus]

@[simp] theorem boundaryEquiv_plus (T : LabelTables) :
    T.boundaryEquiv (floorPlus T.kR T.kL) = ⟨1, by unfold nLab; omega⟩ := by
  apply Fin.ext
  simp [boundaryEquiv, floorPlus]

@[simp] theorem boundaryEquiv_top (T : LabelTables) :
    T.boundaryEquiv (topIndex T.kR T.kL) = ⟨2, by unfold nLab; omega⟩ := by
  apply Fin.ext
  simp [boundaryEquiv, topIndex]

@[simp] theorem boundaryEquiv_right (T : LabelTables) (i : Fin T.kR) :
    T.boundaryEquiv (rightIndex T.kL i) =
      ⟨3 + i.val, by have := i.isLt; unfold nLab; omega⟩ := by
  apply Fin.ext
  simp only [boundaryEquiv, rightIndex, Equiv.coe_fn_mk, Fin.val_mk]
  split_ifs <;> omega

@[simp] theorem boundaryEquiv_left (T : LabelTables) (j : Fin T.kL) :
    T.boundaryEquiv (leftIndex T.kR j) =
      ⟨3 + T.kR + j.val, by have := j.isLt; unfold nLab; omega⟩ := by
  apply Fin.ext
  simp only [boundaryEquiv, leftIndex, Equiv.coe_fn_mk, Fin.val_mk]
  split_ifs <;> omega

theorem label_cases (T : LabelTables) (l : Fin T.nLab) :
    l.val = 0 ∨ l.val = 1 ∨ l.val = 2 ∨
      (∃ i : Fin T.kR, l.val = 3 + i.val) ∨
      (∃ j : Fin T.kL, l.val = 3 + T.kR + j.val) := by
  have := l.isLt
  unfold nLab at *
  by_cases h0 : l.val = 0
  · exact Or.inl h0
  by_cases h1 : l.val = 1
  · exact Or.inr (Or.inl h1)
  by_cases h2 : l.val = 2
  · exact Or.inr (Or.inr (Or.inl h2))
  by_cases hR : l.val < 3 + T.kR
  · exact Or.inr (Or.inr (Or.inr (Or.inl
      ⟨⟨l.val - 3, by omega⟩, by simp only; omega⟩)))
  exact Or.inr (Or.inr (Or.inr (Or.inr
    ⟨⟨l.val - (3 + T.kR), by omega⟩, by simp only; omega⟩)))

@[simp] theorem normalOf_right (T : LabelTables) (i : Fin T.kR) :
    qPlane (T.normalOf (3 + i.val)) = T.rightNormal i := by
  have hi := i.isLt
  simp [normalOf, rightNormal,
    show 3 + i.val ≠ 1 by omega, show 3 + i.val ≠ 2 by omega,
    show 3 + i.val < 3 + T.kR by omega]

@[simp] theorem normalOf_left (T : LabelTables) (j : Fin T.kL) :
    qPlane (T.normalOf (3 + T.kR + j.val)) = T.leftNormal j := by
  simp [normalOf, leftNormal,
    show 3 + T.kR + j.val ≠ 1 by omega, show 3 + T.kR + j.val ≠ 2 by omega,
    show ¬3 + T.kR + j.val < 3 + T.kR by omega,
    show 3 + T.kR + j.val - 3 - T.kR = j.val by omega]

end Certificate.LabelTables

namespace FloorPolygon

variable {n : ℕ} (F : FloorPolygon n)

/-- Actual maximizing vertices. No tie-breaking assumption is required. -/
def certificateContact (top : Fin n) (T : LabelTables) (l : Fin T.nLab) : Fin n :=
  if l.val = 0 then F.base
  else if l.val = 1 then F.tip
  else if l.val = 2 then top
  else Classical.choose (F.exists_support (qPlane (T.normalOf l.val)))

@[simp] theorem certificateContact_minus (top : Fin n) (T : LabelTables) :
    F.certificateContact top T (T.boundaryEquiv (floorMinus T.kR T.kL)) = F.base := by
  simp [certificateContact]

@[simp] theorem certificateContact_plus (top : Fin n) (T : LabelTables) :
    F.certificateContact top T (T.boundaryEquiv (floorPlus T.kR T.kL)) = F.tip := by
  simp [certificateContact]

@[simp] theorem certificateContact_top (top : Fin n) (T : LabelTables) :
    F.certificateContact top T (T.boundaryEquiv (topIndex T.kR T.kL)) = top := by
  simp [certificateContact]

/-- Every selected label really maximizes its named normal. -/
theorem certificateContact_support (top : Fin n)
    (hmax : ∀ i, (F.vertex i).im ≤ (F.vertex top).im)
    (T : LabelTables) (l : Fin T.nLab) :
    F.Supports (qPlane (T.normalOf l.val)) (F.certificateContact top T l) := by
  unfold certificateContact
  split_ifs with h0 h1 h2
  · intro j
    simpa [h0, LabelTables.normalOf, qPlane, F.base_zero] using F.nonneg j
  · intro j
    simpa [h1, LabelTables.normalOf, qPlane, F.tip_im] using F.nonneg j
  · intro j
    simpa [h2, LabelTables.normalOf, qPlane] using hmax j
  · exact Classical.choose_spec (F.exists_support _)

theorem certificateContact_right_support (top : Fin n)
    (hmax : ∀ i, (F.vertex i).im ≤ (F.vertex top).im)
    (T : LabelTables) (i : Fin T.kR) :
    F.Supports (T.rightNormal i)
      (F.certificateContact top T (T.boundaryEquiv (rightIndex T.kL i))) := by
  have h := F.certificateContact_support top hmax T
    (T.boundaryEquiv (rightIndex T.kL i))
  simpa only [LabelTables.boundaryEquiv_right, LabelTables.normalOf_right] using h

theorem certificateContact_left_support (top : Fin n)
    (hmax : ∀ i, (F.vertex i).im ≤ (F.vertex top).im)
    (T : LabelTables) (j : Fin T.kL) :
    F.Supports (T.leftNormal j)
      (F.certificateContact top T (T.boundaryEquiv (leftIndex T.kR j))) := by
  have h := F.certificateContact_support top hmax T
    (T.boundaryEquiv (leftIndex T.kR j))
  simpa only [LabelTables.boundaryEquiv_left, LabelTables.normalOf_left] using h

/-- Vertex maxima extend to the entire convex hull by convexity of a half-space. -/
theorem Supports.hull {u : Plane} {i : Fin n} (h : F.Supports u i)
    {x : Plane} (hx : x ∈ convexHull ℝ (Set.range F.vertex)) :
    inner ℝ u x ≤ inner ℝ u (F.vertex i) := by
  apply convexHull_min ?_ (convex_halfSpace_le (innerSL ℝ u).isLinear _) hx
  rintro _ ⟨j, rfl⟩
  exact (F.supports_iff_inner u i).mp h j

theorem certificateContact_support_eq (top : Fin n)
    (hmax : ∀ i, (F.vertex i).im ≤ (F.vertex top).im)
    (T : LabelTables) (l : Fin T.nLab) :
    support (convexHull ℝ (Set.range F.vertex)) (qPlane (T.normalOf l.val)) =
      inner ℝ (qPlane (T.normalOf l.val)) (F.vertex (F.certificateContact top T l)) := by
  have hc := (Set.finite_range F.vertex).isCompact_convexHull ℝ
  have hm : F.vertex (F.certificateContact top T l) ∈
      convexHull ℝ (Set.range F.vertex) :=
    subset_convexHull ℝ _ (Set.mem_range_self _)
  apply le_antisymm
  · exact (support_le_iff hc ⟨_, hm⟩ _ _).mpr fun x hx =>
      (F.certificateContact_support top hmax T l).hull F hx
  · exact le_support hc hm _

/-- The actual contact choice satisfies the geometric boundary-prefix property. -/
theorem certificateContact_completed_prefix {V : Set Plane} (P : ShortestVertexPath V)
    (F : FloorPolygon (P.edges + 1)) (hvertex : ∀ i, P.vertex i = F.vertex i)
    (top : Fin (P.edges + 1)) (htop : 0 < (F.vertex top).im)
    (hmax : ∀ i, (F.vertex i).im ≤ (F.vertex top).im)
    (T : LabelTables) (hT : labelsOK T = true) (r : ℕ) :
    IsBoundaryInterval (completedPrefix
      (fun l => (F.certificateContact top T (T.boundaryEquiv l)).val) r) := by
  exact F.support_completed_prefix P hvertex top htop hmax
    (fun l => F.certificateContact top T (T.boundaryEquiv l))
    (F.certificateContact_minus top T) (F.certificateContact_plus top T)
    (F.certificateContact_top top T) T.rightNormal T.leftNormal
    (T.rightNormal_re_pos hT) (T.leftNormal_re_neg hT)
    (T.rightNormal_cross_pos hT) (T.leftNormal_cross_pos hT)
    (F.certificateContact_right_support top hmax T)
    (F.certificateContact_left_support top hmax T) r

end FloorPolygon

namespace Certificate.LabelTables

/-- The four sets actually enumerated by `familyMaxNorm2`, in certificate
array order. The first interval is nonempty; the other three may have no
right/left labels. The anchor in families (ii) and (iii) is always present. -/
def FourFamily (T : LabelTables) (pLo pHi qLo qHi : ℕ) (S : Set (Fin T.nLab)) : Prop :=
  (∃ a b : ℕ, qLo ≤ a ∧ a < b ∧ b ≤ T.kL ∧
    S = {l | 3 + T.kR + a ≤ l.val ∧ l.val < 3 + T.kR + b}) ∨
  (∃ j : ℕ, j ≤ qHi ∧ j ≤ T.kL ∧
    S = {l | l.val = 0 ∨ 3 + T.kR + j ≤ l.val}) ∨
  (∃ s : ℕ, pLo ≤ s ∧ s ≤ T.kR ∧
    S = {l | l.val = 1 ∨ 3 ≤ l.val ∧ l.val < 3 + s}) ∨
  (∃ a b : ℕ, a ≤ b ∧ b ≤ pHi ∧
    S = {l | 3 + a ≤ l.val ∧ l.val < 3 + b})

/-- Reindex the cyclic family into the exact checker family. Nonemptiness
removes the unchecked empty left run; a left suffix is clamped to `kL`. -/
theorem fourFamily_reindex (T : LabelTables) {pLo pHi qLo qHi : ℕ}
    (hpHi : pHi ≤ T.kR) {S : Set (Fin T.nLab)} (hne : S.Nonempty)
    (hS : UpperBound.FourFamily T.kR T.kL pLo pHi qLo qHi
      (T.boundaryEquiv ⁻¹' S)) :
    T.FourFamily pLo pHi qLo qHi S := by
  rcases hS with ⟨a, b, hqa, hab, hbm, he⟩ | ⟨j, hjq, he⟩ |
    ⟨s, hps, hsk, he⟩ | ⟨a, b, hab, hbp, he⟩
  · have hab' : a < b := by
      obtain ⟨l, hl⟩ := hne
      have hh : T.boundaryEquiv.symm l ∈ T.boundaryEquiv ⁻¹' S := by simpa using hl
      rw [he] at hh
      change _ ≤ _ ∧ _ < _ at hh
      omega
    refine Or.inl ⟨a, b, hqa, hab', hbm, ?_⟩
    ext l
    obtain ⟨c, rfl⟩ := T.boundaryEquiv.surjective l
    have hh : T.boundaryEquiv c ∈ S ↔
        T.kR + 3 + a ≤ c.val ∧ c.val < T.kR + 3 + b := by
      change c ∈ T.boundaryEquiv ⁻¹' S ↔ _
      rw [he]; rfl
    rw [hh]
    simp only [mem_ofPred_eq]
    rcases contactIndex_cases c with rfl | rfl | ⟨i, rfl⟩ | rfl | ⟨j, rfl⟩ <;>
      simp only [boundaryEquiv_minus, boundaryEquiv_plus, boundaryEquiv_right,
        boundaryEquiv_top, boundaryEquiv_left, Fin.val_mk] <;>
      dsimp only [floorMinus, floorPlus, topIndex, rightIndex, leftIndex] <;> omega
  · refine Or.inr (Or.inl ⟨min j T.kL, (min_le_left _ _).trans hjq,
      min_le_right _ _, ?_⟩)
    ext l
    obtain ⟨c, rfl⟩ := T.boundaryEquiv.surjective l
    have hh : T.boundaryEquiv c ∈ S ↔ c.val = 0 ∨ T.kR + 3 + j ≤ c.val := by
      change c ∈ T.boundaryEquiv ⁻¹' S ↔ _
      rw [he]; rfl
    rw [hh]
    simp only [mem_ofPred_eq]
    rcases contactIndex_cases c with rfl | rfl | ⟨i, rfl⟩ | rfl | ⟨i, rfl⟩ <;>
      simp only [boundaryEquiv_minus, boundaryEquiv_plus, boundaryEquiv_right,
        boundaryEquiv_top, boundaryEquiv_left, Fin.val_mk] <;>
      dsimp only [floorMinus, floorPlus, topIndex, rightIndex, leftIndex] <;>
      (first | omega | simp only [eq_self, true_or])
  · refine Or.inr (Or.inr (Or.inl ⟨s, hps, hsk, ?_⟩))
    ext l
    obtain ⟨c, rfl⟩ := T.boundaryEquiv.surjective l
    have hh : T.boundaryEquiv c ∈ S ↔ c.val = 1 ∨ 2 ≤ c.val ∧ c.val < 2 + s := by
      change c ∈ T.boundaryEquiv ⁻¹' S ↔ _
      rw [he]; rfl
    rw [hh]
    simp only [mem_ofPred_eq]
    rcases contactIndex_cases c with rfl | rfl | ⟨i, rfl⟩ | rfl | ⟨j, rfl⟩ <;>
      simp only [boundaryEquiv_minus, boundaryEquiv_plus, boundaryEquiv_right,
        boundaryEquiv_top, boundaryEquiv_left, Fin.val_mk] <;>
      dsimp only [floorMinus, floorPlus, topIndex, rightIndex, leftIndex] <;>
      (first | omega | simp only [eq_self, true_or])
  · refine Or.inr (Or.inr (Or.inr ⟨a, b, hab, hbp, ?_⟩))
    ext l
    obtain ⟨c, rfl⟩ := T.boundaryEquiv.surjective l
    have hh : T.boundaryEquiv c ∈ S ↔ 2 + a ≤ c.val ∧ c.val < 2 + b := by
      change c ∈ T.boundaryEquiv ⁻¹' S ↔ _
      rw [he]; rfl
    rw [hh]
    simp only [mem_ofPred_eq]
    rcases contactIndex_cases c with rfl | rfl | ⟨i, rfl⟩ | rfl | ⟨j, rfl⟩ <;>
      simp only [boundaryEquiv_minus, boundaryEquiv_plus, boundaryEquiv_right,
        boundaryEquiv_top, boundaryEquiv_left, Fin.val_mk] <;>
      dsimp only [floorMinus, floorPlus, topIndex, rightIndex, leftIndex] <;> omega

/-- Complete table, including the empty/full prefixes, in certificate order. -/
def CompletionProperty (T : LabelTables) (rank : Fin T.nLab → ℕ)
    (pLo pHi qLo qHi : ℕ) : Prop :=
  ∀ r, completedPrefix rank r = ∅ ∨ completedPrefix rank r = Set.univ ∨
    T.FourFamily pLo pHi qLo qHi (completedPrefix rank r) ∨
    T.FourFamily pLo pHi qLo qHi (completedPrefix rank r)ᶜ

/-- The complete table yields all prefix-force bounds. Empty/full prefixes
use zero/balance, and complements use the same norm by balance. -/
theorem CompletionProperty.prefixForce_le {T : LabelTables}
    {rank : Fin T.nLab → ℕ} {pLo pHi qLo qHi : ℕ}
    (hcomp : T.CompletionProperty rank pLo pHi qLo qHi)
    (f : Fin T.nLab → Plane) (hbalance : ∑ l, f l = 0)
    (hfamily : ∀ S : Finset (Fin T.nLab), T.FourFamily pLo pHi qLo qHi (S : Set _) →
      ‖∑ l ∈ S, f l‖ ≤ 1) (r : ℕ) :
    ‖prefixForce f rank r‖ ≤ 1 := by
  classical
  let S := Finset.univ.filter (fun l => rank l ≤ r)
  have hS : (S : Set _) = completedPrefix rank r := by
    ext l
    simp [S, completedPrefix]
  change ‖∑ l ∈ S, f l‖ ≤ 1
  rcases hcomp r with he | he | hf | hf
  · have heS : S = ∅ := Finset.coe_injective (by simpa using hS.trans he)
    simp [heS]
  · have heS : S = Finset.univ := Finset.coe_injective (by simpa using hS.trans he)
    simp [heS, hbalance]
  · exact hfamily S (hS ▸ hf)
  · have hh := hfamily Sᶜ (by simpa only [Finset.coe_compl, hS] using hf)
    rw [norm_sum_compl f S hbalance] at hh
    exact hh

end Certificate.LabelTables

namespace NormalizedWitness

variable {K : Set Plane} (W : NormalizedWitness K)

/-- Contact indices are actual indices of the shortest visiting path. -/
def contactVertex (T : LabelTables) : Fin T.nLab → Fin (W.path.edges + 1) :=
  W.polygon.certificateContact W.top T

def contactPoint (T : LabelTables) (l : Fin T.nLab) : Plane :=
  W.polygon.vertex (W.contactVertex T l)

def contactRank (T : LabelTables) (l : Fin T.nLab) : ℕ :=
  (W.contactVertex T l).val

def boundaryRank (T : LabelTables) : ContactIndex T.kR T.kL → ℕ :=
  W.contactRank T ∘ T.boundaryEquiv

@[simp] theorem contactVertex_minus (T : LabelTables) :
    W.contactVertex T ⟨0, by unfold LabelTables.nLab; omega⟩ = W.polygon.base := by
  simp [contactVertex, FloorPolygon.certificateContact]

@[simp] theorem contactVertex_plus (T : LabelTables) :
    W.contactVertex T ⟨1, by unfold LabelTables.nLab; omega⟩ = W.polygon.tip := by
  simp [contactVertex, FloorPolygon.certificateContact]

@[simp] theorem contactVertex_top (T : LabelTables) :
    W.contactVertex T ⟨2, by unfold LabelTables.nLab; omega⟩ = W.top := by
  simp [contactVertex, FloorPolygon.certificateContact]

theorem contactPoint_eq_path (T : LabelTables) (l : Fin T.nLab) :
    W.contactPoint T l = W.path.vertex (W.contactVertex T l) :=
  (W.vertex_eq _).symm

theorem contactRank_le (T : LabelTables) (l : Fin T.nLab) :
    W.contactRank T l ≤ W.path.edges := Nat.le_of_lt_succ (W.contactVertex T l).isLt

/-- Coincident contacts always complete together, including ties at anchors. -/
theorem contactRank_tied (T : LabelTables) {a b : Fin T.nLab}
    (h : W.contactPoint T a = W.contactPoint T b) :
    W.contactRank T a = W.contactRank T b :=
  congrArg Fin.val (W.polygon.injective h)

theorem completedPrefix_tied (T : LabelTables) {a b : Fin T.nLab}
    (h : W.contactPoint T a = W.contactPoint T b) (r : ℕ) :
    a ∈ completedPrefix (W.contactRank T) r ↔ b ∈ completedPrefix (W.contactRank T) r := by
  change W.contactRank T a ≤ r ↔ W.contactRank T b ≤ r
  rw [W.contactRank_tied T h]

/-- Exact support values, for the entire normalized witness hull. -/
theorem contact_support_eq (T : LabelTables) (l : Fin T.nLab) :
    support (convexHull ℝ W.vertices) (qPlane (T.normalOf l.val)) =
      inner ℝ (qPlane (T.normalOf l.val)) (W.contactPoint T l) := by
  have hF : Set.range W.polygon.vertex = W.vertices := by
    exact (congrArg Set.range (funext fun i => (W.vertex_eq i).symm)).trans W.path.range_eq
  simpa only [hF, contactPoint, contactVertex] using
    W.polygon.certificateContact_support_eq W.top W.top_max T l

theorem boundaryRank_minus_lt_top (T : LabelTables) :
    W.boundaryRank T (floorMinus T.kR T.kL) <
      W.boundaryRank T (topIndex T.kR T.kL) := by
  simpa [boundaryRank, contactRank] using W.base_before_top

theorem boundaryRank_top_lt_plus (T : LabelTables) :
    W.boundaryRank T (topIndex T.kR T.kL) <
      W.boundaryRank T (floorPlus T.kR T.kL) := by
  simpa [boundaryRank, contactRank] using W.top_before_tip

theorem contact_prefix (T : LabelTables) (hT : labelsOK T = true) (r : ℕ) :
    IsBoundaryInterval (completedPrefix (W.boundaryRank T) r) :=
  FloorPolygon.certificateContact_completed_prefix W.path W.polygon W.vertex_eq
    W.top W.top_pos W.top_max T hT r

/-- The splits used by the checker are consequences of the actual contacts.
The right split includes a tie with F+; the left split excludes a tie with F-. -/
theorem contact_splits (T : LabelTables) (hT : labelsOK T = true) :
    ∃ p q, p ≤ T.kR ∧ q ≤ T.kL ∧
      (∀ i : Fin T.kR, i.val < p ↔
        W.boundaryRank T (floorPlus T.kR T.kL) ≤ W.boundaryRank T (rightIndex T.kL i)) ∧
      (∀ j : Fin T.kL, j.val < q ↔
        W.boundaryRank T (floorMinus T.kR T.kL) < W.boundaryRank T (leftIndex T.kR j)) :=
  exists_contact_split (W.boundaryRank T) (W.contact_prefix T hT)
    (W.boundaryRank_minus_lt_top T) (W.boundaryRank_top_lt_plus T)

/-- Completion table for any rectangle containing the actual splits. The
only geometric inputs are a constructed normalized witness and checked normals. -/
theorem certificate_contacts (T : LabelTables) (hT : labelsOK T = true) :
    ∃ p q, p ≤ T.kR ∧ q ≤ T.kL ∧
      (∀ i : Fin T.kR, i.val < p ↔
        W.boundaryRank T (floorPlus T.kR T.kL) ≤ W.boundaryRank T (rightIndex T.kL i)) ∧
      (∀ j : Fin T.kL, j.val < q ↔
        W.boundaryRank T (floorMinus T.kR T.kL) < W.boundaryRank T (leftIndex T.kR j)) ∧
      ∀ pLo pHi qLo qHi, pLo ≤ p → p ≤ pHi → pHi ≤ T.kR →
        qLo ≤ q → q ≤ qHi → T.CompletionProperty (W.contactRank T) pLo pHi qLo qHi := by
  obtain ⟨p, q, hp, hq, hR, hL⟩ := W.contact_splits T hT
  refine ⟨p, q, hp, hq, hR, hL, ?_⟩
  intro pLo pHi qLo qHi hpLo hpHi hpK hqLo hqHi r
  let S := completedPrefix (W.contactRank T) r
  by_cases hne : S.Nonempty
  · by_cases hcne : Sᶜ.Nonempty
    · have hcyc : (completedPrefix (W.boundaryRank T) r).Nonempty := by
        obtain ⟨l, hl⟩ := hne
        exact ⟨T.boundaryEquiv.symm l, by simpa [boundaryRank, completedPrefix, S] using hl⟩
      have hccyc : (completedPrefix (W.boundaryRank T) r)ᶜ.Nonempty := by
        obtain ⟨l, hl⟩ := hcne
        exact ⟨T.boundaryEquiv.symm l, by simpa [boundaryRank, completedPrefix, S] using hl⟩
      have hh := completedPrefix_four_families (W.boundaryRank T) (W.contact_prefix T hT)
        (W.boundaryRank_minus_lt_top T) (W.boundaryRank_top_lt_plus T)
        hp hq hpLo hpHi hqLo hqHi hR hL r hcyc hccyc
      rcases hh with hh | hh
      · exact Or.inr (Or.inr (Or.inl (T.fourFamily_reindex hpK hne hh)))
      · exact Or.inr (Or.inr (Or.inr (T.fourFamily_reindex hpK hcne hh)))
    · exact Or.inr (Or.inl (Set.eq_univ_iff_forall.mpr fun l => by
        by_contra hl; exact hcne ⟨l, hl⟩))
  · exact Or.inl (Set.not_nonempty_iff_eq_empty.mp hne)

end NormalizedWitness

namespace Certificate

/-- Membership in the checker's natural-number block, including empty blocks. -/
theorem mem_labelBlock_iff (o a b l : ℕ) :
    l ∈ labelBlock o a b ↔ o + a ≤ l ∧ l < o + b := by
  simp only [labelBlock, Finset.mem_image, Finset.mem_Ico]
  constructor
  · rintro ⟨i, hi, rfl⟩
    omega
  · intro h
    exact ⟨l - o, by omega, by omega⟩

/-- Convert the finite-type completion family to `RealSound`'s actual
natural-number label sets. The set bound also fixes the complement universe. -/
theorem LabelTables.fourFamily_prefixFamily (T : LabelTables) {p q : ℕ}
    (hp : p ≤ T.kR) {S : Finset ℕ} (hS : S ⊆ Finset.range T.nLab)
    (hf : T.FourFamily p p q q {l | l.val ∈ S}) : PrefixFamily T p q S := by
  have hin (l : ℕ) (hl : ¬l < T.nLab) : l ∉ S := by
    intro hm
    exact hl (Finset.mem_range.mp (hS hm))
  rcases hf with ⟨a, b, hqa, hab, hbk, he⟩ | ⟨j, hjq, hjk, he⟩ |
    ⟨j, hpj, hjk, he⟩ | ⟨a, b, hab, hbp, he⟩
  · refine Or.inl ⟨a, b, hqa, hab.le, hbk, ?_⟩
    ext l
    rw [mem_labelBlock_iff]
    by_cases hl : l < T.nLab
    · have hh := Set.ext_iff.mp he ⟨l, hl⟩
      exact hh
    · have hh := hin l hl
      unfold LabelTables.nLab at hl
      simp only [hh, false_iff]
      omega
  · refine Or.inr (Or.inl ⟨j, hjq, ?_⟩)
    ext l
    simp only [Finset.mem_insert, mem_labelBlock_iff]
    by_cases hl : l < T.nLab
    · have hh := Set.ext_iff.mp he ⟨l, hl⟩
      change (l ∈ S ↔ l = 0 ∨ 3 + T.kR + j ≤ l) at hh
      unfold LabelTables.nLab at hl
      simpa only [hl, and_true] using hh
    · have hh := hin l hl
      unfold LabelTables.nLab at hl
      simp only [hh, false_iff]
      omega
  · refine Or.inr (Or.inr (Or.inl ⟨j, hpj, hjk, ?_⟩))
    ext l
    simp only [Finset.mem_insert, mem_labelBlock_iff]
    by_cases hl : l < T.nLab
    · have hh := Set.ext_iff.mp he ⟨l, hl⟩
      change (l ∈ S ↔ l = 1 ∨ 3 ≤ l ∧ l < 3 + j) at hh
      omega
    · have hh := hin l hl
      unfold LabelTables.nLab at hl
      simp only [hh, false_iff]
      omega
  · refine Or.inr (Or.inr (Or.inr ⟨a, b, hab, hbp, ?_⟩))
    ext l
    rw [mem_labelBlock_iff]
    by_cases hl : l < T.nLab
    · have hh := Set.ext_iff.mp he ⟨l, hl⟩
      exact hh
    · have hh := hin l hl
      unfold LabelTables.nLab at hl
      simp only [hh, false_iff]
      omega

/-- Exact adapter to the `ContactPrefixes` field consumed by `ContactModel`.
The rank extension outside the valid label range is irrelevant. -/
theorem LabelTables.CompletionProperty.contactPrefixes {T : LabelTables}
    {p q : ℕ} (hp : p ≤ T.kR) {rank : Fin T.nLab → ℕ} {rankNat : ℕ → ℕ}
    (hrank : ∀ l : Fin T.nLab, rankNat l.val = rank l)
    (hc : T.CompletionProperty rank p p q q) (m : ℕ) :
    ContactPrefixes T p q rankNat m := by
  intro r _
  let S := (Finset.range T.nLab).filter (fun l => rankNat l ≤ r)
  have hS : S ⊆ Finset.range T.nLab := Finset.filter_subset _ _
  have hset : {l : Fin T.nLab | l.val ∈ S} = completedPrefix rank r := by
    ext l
    simp [S, completedPrefix, hrank l]
  change S = ∅ ∨ S = Finset.range T.nLab ∨ PrefixFamily T p q S ∨
    PrefixFamily T p q (Finset.range T.nLab \ S)
  rcases hc r with he | he | hf | hf
  · left
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro l hl
    have hh : (⟨l, Finset.mem_range.mp (hS hl)⟩ : Fin T.nLab) ∈
        completedPrefix rank r := hset ▸ hl
    simp only [he, Set.mem_empty_iff_false] at hh
  · right; left
    apply Finset.Subset.antisymm hS
    intro l hl
    have hh : (⟨l, Finset.mem_range.mp hl⟩ : Fin T.nLab) ∈
        completedPrefix rank r := by rw [he]; trivial
    rw [← hset] at hh
    exact hh
  · exact Or.inr (Or.inr (Or.inl (T.fourFamily_prefixFamily hp hS (hset ▸ hf))))
  · have hcompl :
        {l : Fin T.nLab | l.val ∈ Finset.range T.nLab \ S} =
          (completedPrefix rank r)ᶜ := by
      rw [← hset]
      ext l
      simp
    exact Or.inr (Or.inr (Or.inr
      (T.fourFamily_prefixFamily hp Finset.sdiff_subset (hcompl ▸ hf))))

end Certificate

namespace NormalizedWitness

variable {K : Set Plane} (W : NormalizedWitness K)

/-- Natural-number rank interface for `RealSound`. Invalid labels are unused. -/
def contactRankNat (T : LabelTables) (l : ℕ) : ℕ :=
  if h : l < T.nLab then W.contactRank T ⟨l, h⟩ else 0

@[simp] theorem contactRankNat_coe (T : LabelTables) (l : Fin T.nLab) :
    W.contactRankNat T l.val = W.contactRank T l := by
  simp [contactRankNat, l.isLt]

theorem contactRankNat_le (T : LabelTables) (l : ℕ) (hl : l < T.nLab) :
    W.contactRankNat T l ≤ W.path.edges := by
  simpa only [contactRankNat, dif_pos hl] using W.contactRank_le T ⟨l, hl⟩

theorem contact_natExt (T : LabelTables) (l : Fin T.nLab) :
    natExt W.path.vertex (W.contactRankNat T l.val) = W.contactPoint T l := by
  rw [W.contactRankNat_coe, natExt_of_le _ (W.contactRank_le T l)]
  exact (W.contactPoint_eq_path T l).symm

/-- Actual contacts in precisely the hull/path representation of `ContactModel`. -/
theorem certificate_contactData (T : LabelTables) :
    ContactData T (convexHull ℝ W.vertices)
      (fun l => natExt W.path.vertex (W.contactRankNat T l)) := by
  constructor
  · intro l hl
    rw [W.contact_natExt T ⟨l, hl⟩, W.contactPoint_eq_path]
    exact subset_convexHull ℝ _ (W.path.range_eq.subset (Set.mem_range_self _))
  · intro l hl
    rw [W.contact_natExt T ⟨l, hl⟩]
    exact (W.contact_support_eq T ⟨l, hl⟩).symm

/-- Construct the actual split and the exact `ContactPrefixes` model field. -/
theorem certificate_contactPrefixes (T : LabelTables) (hT : labelsOK T = true) :
    ∃ p q, p ≤ T.kR ∧ q ≤ T.kL ∧
      ContactPrefixes T p q (W.contactRankNat T) W.path.edges := by
  obtain ⟨p, q, hp, hq, _, _, hc⟩ := W.certificate_contacts T hT
  refine ⟨p, q, hp, hq, ?_⟩
  exact Certificate.LabelTables.CompletionProperty.contactPrefixes hp
    (W.contactRankNat_coe T)
    (hc p p q q le_rfl le_rfl hp le_rfl le_rfl) W.path.edges

end NormalizedWitness

end MoserWorm.UpperBound
