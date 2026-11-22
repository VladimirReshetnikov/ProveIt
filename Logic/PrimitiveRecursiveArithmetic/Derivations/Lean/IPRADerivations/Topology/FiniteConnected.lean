import IPRADerivations.Topology.FiniteClosureMaps

/-!
# Connected images and products of finite spaces

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/03_finite.tex`, Theorem F14
(`thm:finite-connected`): "The image of a connected finite space under a continuous map is connected …
The product of two nonempty connected finite spaces is connected. More generally, the components of a finite
product of nonempty factors are exactly the products of their components."

Connectedness is reachability in the comparability graph (`Topology/FiniteClosureMaps.comp`, walks of
`Foundations/ObservationCut`), and by F13 (`FiniteClosureMaps.clopen_walk`) clopen sets are constant along
walks:

* `walk_map`: a monotone map sends comparability walks to comparability walks ("A monotone map takes a
  comparability edge to a comparability edge");
* `image_clopen_const`: a clopen set of the target takes the same truth value at the images of two connected
  points;
* `walk_fst`, `walk_snd`, `walk_prod`: walks in the factors give a walk in the product ("hold the second
  coordinate fixed and follow a path in the first coordinate; then hold the first fixed");
* `walk_proj₁`, `walk_proj₂`: a product walk projects to walks in the factors ("a path cannot leave either
  coordinate component");
* `prod_clopen_const`: a clopen family on the product is constant on products of components.
-/

namespace LeanProofs.IPRA.Topology.FiniteConnected

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Topology.FiniteInteriorClosure
open LeanProofs.IPRA.Topology.FiniteClosureMaps (comp clopen_walk)
open LeanProofs.IPRA.Foundations.RichardsonLogic (iffF)
open LeanProofs.IPRA.Foundations.ObservationCut.Finality (Walk pathDerivation)
open Syn
open scoped Fm

variable {n k l m : ℕ} {Γ : List (Fm PTm n)}
variable {relX : Fin k → Fin k → Prop} {relY : Fin l → Fin l → Prop} {relZ : Fin m → Fin m → Prop}

theorem walk_map {f : Fin k → Fin m} (hf : ∀ x x', relX x x' → relZ (f x) (f x')) {x y : Fin k}
    (w : Walk (comp relX) x y) : Walk (comp relZ) (f x) (f y) := by
  induction w with
  | trivial => exact .trivial _
  | edge e =>
    rcases e with e | e
    · exact .edge (.inl (hf _ _ e))
    · exact .edge (.inr (hf _ _ e))
  | reverse _ ih => exact .reverse ih
  | join _ _ ih₁ ih₂ => exact .join ih₁ ih₂

/-- The image of a connected set meets each clopen set of the target in all or nothing. -/
theorem image_clopen_const [DecidableRel relZ] {f : Fin k → Fin m} (hf : ∀ x x', relX x x' → relZ (f x) (f x'))
    {U : Fin m → Fm PTm n} (hO : IsOpen relZ Γ U) (hC : IsClosed relZ Γ U) {x y : Fin k}
    (w : Walk (comp relX) x y) : Γ ⊢[PRAAx] iffF (U (f x)) (U (f y)) :=
  clopen_walk hO hC (walk_map hf w)

/-- Comparability on an arbitrary carrier (the product carrier is not a `Fin`). -/
def pcomp {V : Type} (R : V → V → Prop) (p q : V) : Prop := R p q ∨ R q p

/-- The product preorder. -/
def relP (relX : Fin k → Fin k → Prop) (relY : Fin l → Fin l → Prop) (p q : Fin k × Fin l) : Prop :=
  relX p.1 q.1 ∧ relY p.2 q.2

theorem walk_fst (hreflY : ∀ y, relY y y) {x x' : Fin k} (w : Walk (comp relX) x x') (y : Fin l) :
    Walk (pcomp (relP relX relY)) (x, y) (x', y) := by
  induction w with
  | trivial => exact .trivial _
  | edge e =>
    rcases e with e | e
    · exact .edge (.inl ⟨e, hreflY y⟩)
    · exact .edge (.inr ⟨e, hreflY y⟩)
  | reverse _ ih => exact .reverse ih
  | join _ _ ih₁ ih₂ => exact .join ih₁ ih₂

theorem walk_snd (hreflX : ∀ x, relX x x) (x : Fin k) {y y' : Fin l} (w : Walk (comp relY) y y') :
    Walk (pcomp (relP relX relY)) (x, y) (x, y') := by
  induction w with
  | trivial => exact .trivial _
  | edge e =>
    rcases e with e | e
    · exact .edge (.inl ⟨hreflX x, e⟩)
    · exact .edge (.inr ⟨hreflX x, e⟩)
  | reverse _ ih => exact .reverse ih
  | join _ _ ih₁ ih₂ => exact .join ih₁ ih₂

/-- Products of connected sets are connected. -/
theorem walk_prod (hreflX : ∀ x, relX x x) (hreflY : ∀ y, relY y y) {x x' : Fin k} {y y' : Fin l}
    (w₁ : Walk (comp relX) x x') (w₂ : Walk (comp relY) y y') :
    Walk (pcomp (relP relX relY)) (x, y) (x', y') :=
  .join (walk_fst hreflY w₁ y) (walk_snd hreflX x' w₂)

theorem walk_proj₁ {p q : Fin k × Fin l} (w : Walk (pcomp (relP relX relY)) p q) :
    Walk (comp relX) p.1 q.1 := by
  induction w with
  | trivial => exact .trivial _
  | edge e =>
    rcases e with e | e
    · exact .edge (.inl e.1)
    · exact .edge (.inr e.1)
  | reverse _ ih => exact .reverse ih
  | join _ _ ih₁ ih₂ => exact .join ih₁ ih₂

theorem walk_proj₂ {p q : Fin k × Fin l} (w : Walk (pcomp (relP relX relY)) p q) :
    Walk (comp relY) p.2 q.2 := by
  induction w with
  | trivial => exact .trivial _
  | edge e =>
    rcases e with e | e
    · exact .edge (.inl e.2)
    · exact .edge (.inr e.2)
  | reverse _ ih => exact .reverse ih
  | join _ _ ih₁ ih₂ => exact .join ih₁ ih₂

/-- A clopen family on the product is constant on every product of components. -/
theorem prod_clopen_const (hreflX : ∀ x, relX x x) (hreflY : ∀ y, relY y y) {W : Fin k × Fin l → Fm PTm n}
    (hO : ∀ p q, relP relX relY p q → (Γ ⊢[PRAAx] W p ⟶ W q))
    (hC : ∀ p q, relP relX relY p q → (Γ ⊢[PRAAx] W q ⟶ W p))
    {x x' : Fin k} {y y' : Fin l} (w₁ : Walk (comp relX) x x') (w₂ : Walk (comp relY) y y') :
    Γ ⊢[PRAAx] iffF (W (x, y)) (W (x', y')) :=
  pathDerivation Γ (pcomp (relP relX relY)) (fun a b => iffF (W a) (W b))
    (fun a => .andI (.impI Prf.hyp0) (.impI Prf.hyp0))
    (fun a b h => .andI h.andE₂ h.andE₁)
    (fun a b c h₁ h₂ => .andI (.impI (.impE h₂.andE₁.wk (.impE h₁.andE₁.wk Prf.hyp0)))
      (.impI (.impE h₁.andE₂.wk (.impE h₂.andE₂.wk Prf.hyp0))))
    (fun a b e => by
      rcases e with e | e
      · exact .andI (hO a b e) (hC a b e)
      · exact .andI (hC b a e) (hO b a e))
    (walk_prod hreflX hreflY w₁ w₂)

end LeanProofs.IPRA.Topology.FiniteConnected
