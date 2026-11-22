import Mathlib.Data.Fintype.Card
import Mathlib.Data.List.FinRange

/-!
# Function sheaves on finite spaces

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/05_algebraic.tex`, Proposition A12
("function sheaves, continuity, and rings"), with Proposition A14's local-equality criterion, for coded covers
`(U_i)_{i<r}` of a finite carrier (decidable membership):

* `glue`: "For matching local functions `f_i`, define `f(x) = f_{i(x)}(x)` using the least covering index";
* `glue_restrict`: "Agreement on overlaps proves … that `f|_{U_i} = f_i`";
* `glue_unique`: "Any other gluing has the same value at each point";
* `glue_mono`: for a preorder in which the `U_i` are upward closed (open), the gluing of monotone, i.e.
  continuous, local maps is monotone on the union ("Each inverse image on the right is open in `U_i`, hence in
  `U`");
* `glue_add`, `glue_mul`: gluing commutes with pointwise ring operations ("restrictions preserve these
  operations");
* `local_eq` (A14 for function sheaves): sections agreeing on every least neighbourhood `↑x` of a point of `U`
  are equal on `U`.
-/

namespace LeanProofs.IPRA.Topology.FiniteSheaves

variable {k r : ℕ} {A : Type*} (U : Fin r → Fin k → Prop) [∀ i, DecidablePred (U i)]

/-- The least covering index of `x`, if any. -/
def idx (x : Fin k) : Option (Fin r) := (List.finRange r).find? fun i => decide (U i x)

theorem idx_spec {x : Fin k} {i : Fin r} (h : idx U x = some i) : U i x := by
  simpa using List.find?_some h

theorem idx_some {x : Fin k} {i : Fin r} (hx : U i x) : ∃ j, idx U x = some j := by
  cases h : idx U x with
  | none =>
    have := List.find?_eq_none.mp h i (List.mem_finRange i)
    simp [hx] at this
  | some j => exact ⟨j, rfl⟩

/-- The gluing `f(x) = f_{i(x)}(x)` (with a default value off the cover). -/
def glue (f : Fin r → Fin k → A) (d : A) (x : Fin k) : A :=
  match idx U x with
  | some i => f i x
  | none => d

/-- Matching: the local functions agree on overlaps. -/
def Matching (f : Fin r → Fin k → A) : Prop := ∀ i j x, U i x → U j x → f i x = f j x

theorem glue_restrict {f : Fin r → Fin k → A} (hf : Matching U f) (d : A) {i : Fin r} {x : Fin k}
    (hx : U i x) : glue U f d x = f i x := by
  obtain ⟨j, hj⟩ := idx_some U hx
  simp only [glue, hj]
  exact hf j i x (idx_spec U hj) hx

theorem glue_unique {f : Fin r → Fin k → A} (hf : Matching U f) (d : A) {g : Fin k → A}
    (hg : ∀ i x, U i x → g x = f i x) {x : Fin k} {i : Fin r} (hx : U i x) : g x = glue U f d x := by
  rw [hg i x hx, glue_restrict U hf d hx]

/-- The gluing of continuous local maps over an open cover is continuous on the union. -/
theorem glue_mono {f : Fin r → Fin k → A} (hf : Matching U f) (d : A) {rel : Fin k → Fin k → Prop}
    {relA : A → A → Prop} (hopen : ∀ i x y, rel x y → U i x → U i y)
    (hmono : ∀ i x y, U i x → U i y → rel x y → relA (f i x) (f i y)) {x y : Fin k} {i : Fin r}
    (hx : U i x) (hxy : rel x y) : relA (glue U f d x) (glue U f d y) := by
  have hy := hopen i x y hxy hx
  rw [glue_restrict U hf d hx, glue_restrict U hf d hy]
  exact hmono i x y hx hy hxy

theorem glue_add [Add A] {f g : Fin r → Fin k → A} (hf : Matching U f) (hg : Matching U g) (d e : A)
    {i : Fin r} {x : Fin k} (hx : U i x) :
    glue U (fun j y => f j y + g j y) (d + e) x = glue U f d x + glue U g e x := by
  have hfg : Matching U (fun j y => f j y + g j y) := fun a b z ha hb => by
    show f a z + g a z = f b z + g b z
    rw [hf a b z ha hb, hg a b z ha hb]
  rw [glue_restrict U hfg _ hx, glue_restrict U hf _ hx, glue_restrict U hg _ hx]

theorem glue_mul [Mul A] {f g : Fin r → Fin k → A} (hf : Matching U f) (hg : Matching U g) (d e : A)
    {i : Fin r} {x : Fin k} (hx : U i x) :
    glue U (fun j y => f j y * g j y) (d * e) x = glue U f d x * glue U g e x := by
  have hfg : Matching U (fun j y => f j y * g j y) := fun a b z ha hb => by
    show f a z * g a z = f b z * g b z
    rw [hf a b z ha hb, hg a b z ha hb]
  rw [glue_restrict U hfg _ hx, glue_restrict U hf _ hx, glue_restrict U hg _ hx]

/-- A14 for function sheaves: sections agreeing on every least neighbourhood of the points of `V` agree on
`V` (with a reflexive preorder, `x ∈ ↑x`). -/
theorem local_eq {rel : Fin k → Fin k → Prop} (hrefl : ∀ x, rel x x) {V : Fin k → Prop} {s t : Fin k → A}
    (h : ∀ x, V x → ∀ y, rel x y → s y = t y) : ∀ x, V x → s x = t x :=
  fun x hx => h x hx x (hrefl x)

end LeanProofs.IPRA.Topology.FiniteSheaves
