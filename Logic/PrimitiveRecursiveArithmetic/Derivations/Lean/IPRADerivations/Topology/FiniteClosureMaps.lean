import IPRADerivations.Topology.FiniteInteriorClosure
import IPRADerivations.Foundations.ObservationCut.PathDerivation
import IPRADerivations.Foundations.RichardsonLogic

/-!
# Closure maps, subspaces and clopen sets of finite spaces

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/03_finite.tex`, in the framework of
`Topology/FiniteInteriorClosure` (a finite preorder with subsets given by arbitrary iPRA formulas):

* F07 (`thm:finite-closuremap`, the forward implication): a continuous, i.e. monotone, map `f` satisfies
  `f(Cl A) ⊆ Cl f(A)` (`closure_map`), with the image `f(A)(y') = ⋁_{f x = y'} A x`;
* F09 (`thm:finite-subspace`): for a subset `S` and `A ⊆ S`, the closure in the restricted preorder agrees
  with the ambient closure at the points of `S` (`subspace_closure`), and restrictions of open sets are open
  (`subspace_open`);
* F13 (`thm:finite-components`): a clopen family is constant along every walk of the comparability graph
  (`clopen_walk`, by `Foundations/ObservationCut.pathDerivation`), and conversely a family constant along
  comparability edges is open and closed (`clopen_of_edges`).
-/

namespace LeanProofs.IPRA.Topology.FiniteClosureMaps

open_ipra
open LeanProofs.IPRA.Foundations.IntersectionEnumeration (disjFin disjFin_intro disjFin_imp)
open LeanProofs.IPRA.Topology.FiniteInteriorClosure
open LeanProofs.IPRA.Foundations.RichardsonLogic (iffF)
open LeanProofs.IPRA.Foundations.ObservationCut.Finality (Walk pathDerivation)

variable {n k l : ℕ} {Γ : List (Fm PTm n)}

/-! ## F07 -/

/-- The image `f(A)(y') = ⋁_{f x = y'} A x`. -/
def image (f : Fin k → Fin l) (A : Fin k → Fm PTm n) (y' : Fin l) : Fm PTm n :=
  disjFin fun x => if f x = y' then A x else Fm.bot

/-- F07: a monotone map takes `Cl A` into `Cl f(A)`. -/
theorem closure_map {rel : Fin k → Fin k → Prop} [DecidableRel rel] {rel' : Fin l → Fin l → Prop}
    [DecidableRel rel'] {f : Fin k → Fin l} (hf : ∀ x y, rel x y → rel' (f x) (f y))
    (A : Fin k → Fm PTm n) (x : Fin k) :
    Γ ⊢[PRAAx] Cl rel A x ⟶ Cl rel' (image f A) (f x) :=
  cl_imp fun y hxy => .impI (cl_intro (hf x y hxy) (disjFin_intro y (by rw [if_pos rfl]; exact Prf.hyp0)))

/-! ## F09 -/

variable {rel : Fin k → Fin k → Prop} [DecidableRel rel] (S : Fin k → Prop) [DecidablePred S]

/-- The restricted preorder. -/
def relS (rel : Fin k → Fin k → Prop) (S : Fin k → Prop) (x y : Fin k) : Prop := S x ∧ S y ∧ rel x y

instance [DecidableRel rel] [DecidablePred S] : DecidableRel (relS rel S) := fun _ _ => by
  unfold relS; infer_instance

/-- Restrictions of open sets are open. -/
theorem subspace_open {U : Fin k → Fm PTm n} (hU : IsOpen rel Γ U) : IsOpen (relS rel S) Γ U :=
  fun x y h => hU x y h.2.2

/-- F09: for `A ⊆ S` and `x ∈ S`, `Cl_S A x ↔ Cl_X A x`. -/
theorem subspace_closure {A : Fin k → Fm PTm n} (hA : ∀ y, ¬ S y → (Γ ⊢[PRAAx] A y ⟶ Fm.bot))
    {x : Fin k} (hx : S x) :
    (Γ ⊢[PRAAx] Cl (relS rel S) A x ⟶ Cl rel A x) ∧ (Γ ⊢[PRAAx] Cl rel A x ⟶ Cl (relS rel S) A x) := by
  refine ⟨cl_imp fun y h => .impI (cl_intro h.2.2 Prf.hyp0), cl_imp fun y hxy => ?_⟩
  by_cases hy : S y
  · exact .impI (cl_intro ⟨hx, hy, hxy⟩ Prf.hyp0)
  · exact .impI (.botE _ (.impE (hA y hy).wk Prf.hyp0))

/-! ## F13 -/

variable {S}

/-- Comparability. -/
def comp (rel : Fin k → Fin k → Prop) (x y : Fin k) : Prop := rel x y ∨ rel y x

/-- Forward and backward implications on the edges give an equivalence along a comparability walk. -/
theorem clopen_walk_of_relation {V : Type} {R : V → V → Prop} {U : V → Fm PTm n}
    (hO : ∀ a b, R a b → (Γ ⊢[PRAAx] U a ⟶ U b))
    (hC : ∀ a b, R a b → (Γ ⊢[PRAAx] U b ⟶ U a))
    {x y : V} (w : Walk (fun a b => R a b ∨ R b a) x y) : Γ ⊢[PRAAx] iffF (U x) (U y) :=
  pathDerivation Γ (fun a b => R a b ∨ R b a) (fun a b => iffF (U a) (U b))
    (fun a => .andI (.impI Prf.hyp0) (.impI Prf.hyp0))
    (fun a b h => .andI h.andE₂ h.andE₁)
    (fun a b c h₁ h₂ => .andI (.impI (.impE h₂.andE₁.wk (.impE h₁.andE₁.wk Prf.hyp0)))
      (.impI (.impE h₁.andE₂.wk (.impE h₂.andE₂.wk Prf.hyp0))))
    (fun a b e => by
      rcases e with e | e
      · exact .andI (hO a b e) (hC a b e)
      · exact .andI (hC b a e) (hO b a e))
    w

/-- F13: a clopen family is constant along every comparability walk. -/
theorem clopen_walk {U : Fin k → Fm PTm n} (hO : IsOpen rel Γ U) (hC : IsClosed rel Γ U) {x y : Fin k}
    (w : Walk (comp rel) x y) : Γ ⊢[PRAAx] iffF (U x) (U y) :=
  clopen_walk_of_relation hO hC w

/-- F13, converse: a family constant along comparability edges is open and closed. -/
theorem clopen_of_edges {U : Fin k → Fm PTm n} (h : ∀ a b, comp rel a b → (Γ ⊢[PRAAx] iffF (U a) (U b))) :
    IsOpen rel Γ U ∧ IsClosed rel Γ U :=
  ⟨fun a b e => (h a b (.inl e)).andE₁, fun a b e => (h a b (.inl e)).andE₂⟩

end LeanProofs.IPRA.Topology.FiniteClosureMaps
