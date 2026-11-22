import IPRADerivations.Topology.FiniteInteriorClosure
import IPRADerivations.Foundations.RichardsonLogic
import Mathlib.Logic.Relation

/-!
# Products, quotients and the `T₀` quotient of finite spaces

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/03_finite.tex`, in the framework of
`Topology/FiniteInteriorClosure` (a finite preorder, subsets given by arbitrary iPRA formulas, open = upward
closed by derived implications):

* F10 (`thm:finite-products`): boxes `U × V` of opens are open for the coordinatewise preorder (`box_open`),
  the projections are continuous (`proj₁_open`, `proj₂_open`), every product-open `W` is the union of the
  boxes below its points, `W(x, y) ↔ ⋁_{a ≼ x, b ≼ y} W(a, b)` (`open_union`), and a map into the product with
  monotone components pulls product-opens back to opens (`pair_preimage_open`);
* F11 (`thm:finite-quotients`): for `q : X → Y` and the reflexive transitive closure of the generating edges
  `q(x) → q(x')` (`x ≼ x'`), a family `V` on `Y` is upward along that closure exactly when `q⁻¹V` is open
  (`quotient_open`, `quotient_open_of`), and `g` preserves the closure exactly when `g ∘ q` is monotone
  (`quotient_map_mono`);
* F12 (`thm:finite-tzero`): every open set is constant on the classes of `x ∼ y ⇔ x ≼ y ∧ y ≼ x`
  (`open_const`), principal upward sets are open (`up_open`) and separate inequivalent points
  (`up_separates`), and a monotone map into an antisymmetric preorder is constant on classes (`mono_const`).
-/

namespace LeanProofs.IPRA.Topology.FiniteProductsQuotients

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Foundations.IntersectionEnumeration (disjFin disjFin_intro disjFin_imp)
open LeanProofs.IPRA.Topology.FiniteInteriorClosure
open LeanProofs.IPRA.Foundations.RichardsonLogic (iffF)
open Syn
open scoped Fm

variable {n k l m : ℕ} {Γ : List (Fm PTm n)}
variable {relX : Fin k → Fin k → Prop} [DecidableRel relX] {relY : Fin l → Fin l → Prop} [DecidableRel relY]

/-! ## F10 -/

/-- `W ⊆ X × Y` is open for the coordinatewise preorder. -/
def IsOpen2 (relX : Fin k → Fin k → Prop) (relY : Fin l → Fin l → Prop) (G : List (Fm PTm n))
    (W : Fin k → Fin l → Fm PTm n) : Prop :=
  ∀ x x' y y', relX x x' → relY y y' → Prf PRAAx G (W x y ⟶ W x' y')

theorem box_open {U : Fin k → Fm PTm n} {V : Fin l → Fm PTm n} (hU : IsOpen relX Γ U) (hV : IsOpen relY Γ V) :
    IsOpen2 relX relY Γ (fun x y => U x ⋏ V y) := fun x x' y y' hx hy =>
  .impI (.andI (.impE (hU x x' hx).wk Prf.hyp0.andE₁) (.impE (hV y y' hy).wk Prf.hyp0.andE₂))

theorem proj₁_open {U : Fin k → Fm PTm n} (hU : IsOpen relX Γ U) :
    IsOpen2 relX relY Γ (fun x _ => U x) := fun x x' _ _ hx _ => hU x x' hx

theorem proj₂_open {V : Fin l → Fm PTm n} (hV : IsOpen relY Γ V) :
    IsOpen2 relX relY Γ (fun _ y => V y) := fun _ _ y y' _ hy => hV y y' hy

/-- Every product-open set is the union of the boxes `↑a × ↑b` over its points. -/
theorem open_union (hreflX : ∀ x, relX x x) (hreflY : ∀ y, relY y y) {W : Fin k → Fin l → Fm PTm n}
    (hW : IsOpen2 relX relY Γ W) (x : Fin k) (y : Fin l) :
    (Γ ⊢[PRAAx] W x y ⟶ disjFin fun a => disjFin fun b => if relX a x ∧ relY b y then W a b else Fm.bot) ∧
    (Γ ⊢[PRAAx] (disjFin fun a => disjFin fun b => if relX a x ∧ relY b y then W a b else Fm.bot) ⟶ W x y) := by
  refine ⟨.impI (disjFin_intro x (disjFin_intro y ?_)), disjFin_imp fun a => disjFin_imp fun b => ?_⟩
  · beta_reduce
    rw [if_pos ⟨hreflX x, hreflY y⟩]
    exact Prf.hyp0
  · beta_reduce
    by_cases h : relX a x ∧ relY b y
    · rw [if_pos h]; exact hW a x b y h.1 h.2
    · rw [if_neg h]; exact .impI (.botE _ Prf.hyp0)

/-- A map `z ↦ (f z, g z)` with monotone components pulls product-opens back to opens. -/
theorem pair_preimage_open {relZ : Fin m → Fin m → Prop} {f : Fin m → Fin k} {g : Fin m → Fin l}
    (hf : ∀ z z', relZ z z' → relX (f z) (f z')) (hg : ∀ z z', relZ z z' → relY (g z) (g z'))
    {W : Fin k → Fin l → Fm PTm n} (hW : IsOpen2 relX relY Γ W) :
    IsOpen relZ Γ (fun z => W (f z) (g z)) := fun z z' h => hW _ _ _ _ (hf z z' h) (hg z z' h)

/-- The universal property: a map into the product is monotone exactly when both components are. -/
theorem pair_mono_iff {relZ : Fin m → Fin m → Prop} (f : Fin m → Fin k) (g : Fin m → Fin l) :
    (∀ z z', relZ z z' → relX (f z) (f z') ∧ relY (g z) (g z')) ↔
      (∀ z z', relZ z z' → relX (f z) (f z')) ∧ (∀ z z', relZ z z' → relY (g z) (g z')) :=
  ⟨fun h => ⟨fun z z' e => (h z z' e).1, fun z z' e => (h z z' e).2⟩,
   fun h z z' e => ⟨h.1 z z' e, h.2 z z' e⟩⟩

/-! ## F11 -/

/-- The generating edges `q(x) → q(x')` for `x ≼ x'`. -/
def qEdge (relX : Fin k → Fin k → Prop) (q : Fin k → Fin l) (a b : Fin l) : Prop :=
  ∃ x x', q x = a ∧ q x' = b ∧ relX x x'

/-- If `q⁻¹V` is open, `V` is upward along every path of generating edges. -/
theorem quotient_open {q : Fin k → Fin l} {V : Fin l → Fm PTm n} (hV : IsOpen relX Γ (fun x => V (q x)))
    {a b : Fin l} (h : Relation.ReflTransGen (qEdge relX q) a b) : Γ ⊢[PRAAx] V a ⟶ V b := by
  induction h with
  | refl => exact .impI Prf.hyp0
  | tail _ e ih =>
    obtain ⟨x, x', rfl, rfl, hxx'⟩ := e
    exact .impI (.impE (hV x x' hxx').wk (.impE ih.wk Prf.hyp0))

/-- Conversely, upwardness along the closure makes `q⁻¹V` open. -/
theorem quotient_open_of {q : Fin k → Fin l} {V : Fin l → Fm PTm n}
    (h : ∀ a b, Relation.ReflTransGen (qEdge relX q) a b → (Γ ⊢[PRAAx] V a ⟶ V b)) :
    IsOpen relX Γ (fun x => V (q x)) := fun x x' hxx' =>
  h _ _ (Relation.ReflTransGen.single ⟨x, x', rfl, rfl, hxx'⟩)

/-- `g` preserves the generated preorder exactly when `g ∘ q` is monotone. -/
theorem quotient_map_mono {relZ : Fin m → Fin m → Prop} (hreflZ : ∀ z, relZ z z)
    (htransZ : ∀ z z' z'', relZ z z' → relZ z' z'' → relZ z z'') (q : Fin k → Fin l) (g : Fin l → Fin m) :
    (∀ a b, Relation.ReflTransGen (qEdge relX q) a b → relZ (g a) (g b)) ↔
      (∀ x x', relX x x' → relZ (g (q x)) (g (q x'))) := by
  refine ⟨fun h x x' e => h _ _ (Relation.ReflTransGen.single ⟨x, x', rfl, rfl, e⟩), fun h a b p => ?_⟩
  induction p with
  | refl => exact hreflZ _
  | tail _ e ih =>
    obtain ⟨x, x', rfl, rfl, hxx'⟩ := e
    exact htransZ _ _ _ ih (h x x' hxx')

/-! ## F12 -/

/-- Open sets are constant on the classes of `x ∼ y`. -/
theorem open_const {U : Fin k → Fm PTm n} (hU : IsOpen relX Γ U) {x y : Fin k} (h : relX x y ∧ relX y x) :
    Γ ⊢[PRAAx] iffF (U x) (U y) :=
  .andI (hU x y h.1) (hU y x h.2)

/-- The principal upward set `↑x`. -/
def up (relX : Fin k → Fin k → Prop) [DecidableRel relX] (x : Fin k) (z : Fin k) : Fm PTm n :=
  if relX x z then truth else Fm.bot

theorem up_open (htrans : ∀ x y z, relX x y → relX y z → relX x z) (x : Fin k) :
    IsOpen relX Γ (up relX x) := fun z z' hzz' => by
  unfold up
  by_cases h : relX x z
  · rw [if_pos h, if_pos (htrans x z z' h hzz')]; exact .impI Prf.hyp0
  · rw [if_neg h]; exact .impI (.botE _ Prf.hyp0)

/-- If `y ⋠ x`, the open set `↑y` contains `y` and not `x`. -/
theorem up_separates (hrefl : ∀ x, relX x x) {x y : Fin k} (h : ¬ relX y x) :
    (Γ ⊢[PRAAx] up relX y y) ∧ (Γ ⊢[PRAAx] up relX y x ⟶ Fm.bot) := by
  unfold up
  rw [if_pos (hrefl y), if_neg h]
  exact ⟨.eqRefl _, .impI Prf.hyp0⟩

/-- A monotone map into an antisymmetric preorder is constant on classes, so it descends to the quotient. -/
theorem mono_const {relZ : Fin m → Fin m → Prop} (hanti : ∀ z z', relZ z z' → relZ z' z → z = z')
    {f : Fin k → Fin m} (hf : ∀ x x', relX x x' → relZ (f x) (f x')) {x y : Fin k} (h : relX x y ∧ relX y x) :
    f x = f y :=
  hanti _ _ (hf x y h.1) (hf y x h.2)

end LeanProofs.IPRA.Topology.FiniteProductsQuotients
