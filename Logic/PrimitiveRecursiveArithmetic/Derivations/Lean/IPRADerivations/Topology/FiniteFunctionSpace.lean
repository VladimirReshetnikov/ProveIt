import IPRADerivations.Topology.FiniteInteriorClosure

/-!
# The finite compact-open topology and the exponential law

Packet: `topology/general_topology_ipra_2026-11-19`, `paper/sections/03_finite.tex`, Theorem F23
(`thm:finite-exponential`), in the framework of `Topology/FiniteInteriorClosure`. Tables `f : X → Y` carry the
pointwise preorder `f ≼ g ⇔ ∀ x, f(x) ≼_Y g(x)`; subsets of the function space are families of iPRA formulas
indexed by tables.

* `eval_open`: the point-evaluation set `[{x}, U] = {f : f(x) ∈ U}` is upward for the pointwise order when
  `U` is open ("Each condition is upward for pointwise order");
* `co_open`: the compact-open set `[K, U] = ⋀_{x ∈ K} [{x}, U]` is upward ("a finite intersection of
  point-evaluation conditions");
* `upF`: the least pointwise neighbourhood `↑f` as the compact-open set `⋀_x [{x}, ↑f(x)]`; it is upward
  (`upF_open`) and a table lies in it exactly when it lies above `f` (`up_co_iff`);
* `eval_continuous`: evaluation `C(X, Y) × X → Y` pulls opens back to sets that are upward in both arguments
  for monotone tables ("`f(x) ≼ g(x) ≼ g(y)`");
* `exponential_law`: `H : Z × X → Y` is monotone exactly when its sections are monotone in `x` and its
  curried table is pointwise monotone in `z` ("`H(z, x) ≼ H(z', x) ≼ H(z', x')`").
-/

namespace LeanProofs.IPRA.Topology.FiniteFunctionSpace

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Topology.FiniteInteriorClosure
open LeanProofs.IPRA.Algebra.AdjugateInverse (conjFin_elim)
open Syn
open scoped Fm

variable {n k l m : ℕ} {Γ : List (Fm PTm n)}
variable {relX : Fin k → Fin k → Prop} {relY : Fin l → Fin l → Prop} [DecidableRel relY]

/-- The pointwise preorder on tables. -/
def ptw (relY : Fin l → Fin l → Prop) (f g : Fin k → Fin l) : Prop := ∀ x, relY (f x) (g x)

/-- `[{x}, U] = {f : f(x) ∈ U}` is upward for the pointwise order. -/
theorem eval_open {U : Fin l → Fm PTm n} (hU : IsOpen relY Γ U) (x : Fin k) {f g : Fin k → Fin l}
    (h : ptw relY f g) : Γ ⊢[PRAAx] U (f x) ⟶ U (g x) :=
  hU _ _ (h x)

/-- The compact-open set `[K, U] = ⋀_{x ∈ K} U(f x)`. -/
def co (K : Fin k → Prop) [DecidablePred K] (U : Fin l → Fm PTm n) (f : Fin k → Fin l) : Fm PTm n :=
  conjFin fun x => if K x then U (f x) else truth

/-- `[K, U]` is upward for the pointwise order. -/
theorem co_open (K : Fin k → Prop) [DecidablePred K] {U : Fin l → Fm PTm n} (hU : IsOpen relY Γ U)
    {f g : Fin k → Fin l} (h : ptw relY f g) : Γ ⊢[PRAAx] co K U f ⟶ co K U g := by
  refine .impI (conjFin_intro fun x => ?_)
  have e := conjFin_elim (Prf.hyp0 : (co K U f :: Γ) ⊢[PRAAx] co K U f) x
  by_cases hx : K x
  · simp only [hx, ↓reduceIte] at e ⊢
    exact .impE (hU _ _ (h x)).wk e
  · simp only [hx, ↓reduceIte] at e ⊢
    exact .eqRefl _

/-- The principal upward set `↑y` of `Y`. -/
def upY (relY : Fin l → Fin l → Prop) [DecidableRel relY] (y z : Fin l) : Fm PTm n :=
  if relY y z then truth else Fm.bot

/-- `↑f = ⋀_x [{x}, ↑f(x)]`, evaluated at a table `g`. -/
def upF (relY : Fin l → Fin l → Prop) [DecidableRel relY] (f g : Fin k → Fin l) : Fm PTm n :=
  conjFin fun x => upY relY (f x) (g x)

/-- `↑f` is upward for the pointwise order. -/
theorem upF_open (htransY : ∀ a b c, relY a b → relY b c → relY a c) (f : Fin k → Fin l)
    {g g' : Fin k → Fin l} (h : ptw relY g g') : Γ ⊢[PRAAx] upF relY f g ⟶ upF relY f g' := by
  refine .impI (conjFin_intro fun x => ?_)
  have e := conjFin_elim (Prf.hyp0 : (upF relY f g :: Γ) ⊢[PRAAx] upF relY f g) x
  by_cases hx : relY (f x) (g x)
  · simp only [upY, hx, htransY _ _ _ hx (h x), ↓reduceIte]; exact .eqRefl _
  · simp only [upY, hx, ↓reduceIte] at e
    exact .botE _ e

/-- A table lies in the compact-open set `⋀_x [{x}, ↑f(x)]` exactly when it lies pointwise above `f`. -/
theorem up_co_iff (f g : Fin k → Fin l) :
    (ptw relY f g → (Γ ⊢[PRAAx] upF relY f g)) ∧
    (∀ x, ¬ relY (f x) (g x) → (Γ ⊢[PRAAx] upF relY f g ⟶ Fm.bot)) := by
  refine ⟨fun h => conjFin_intro fun x => ?_, fun x hx => ?_⟩
  · simp only [upY, h x, ↓reduceIte]; exact .eqRefl _
  · refine .impI ?_
    have e := conjFin_elim (Prf.hyp0 : (upF relY f g :: Γ) ⊢[PRAAx] upF relY f g) x
    simp only [upY, hx, ↓reduceIte] at e
    exact e

/-- Evaluation is continuous: for a monotone table `g`, `f ≼ g` and `x ≼ y` give `U(f x) → U(g y)`. -/
theorem eval_continuous (htransY : ∀ a b c, relY a b → relY b c → relY a c) {U : Fin l → Fm PTm n}
    (hU : IsOpen relY Γ U) {f g : Fin k → Fin l} (hg : ∀ x y, relX x y → relY (g x) (g y))
    (hfg : ptw relY f g) {x y : Fin k} (hxy : relX x y) : Γ ⊢[PRAAx] U (f x) ⟶ U (g y) :=
  hU _ _ (htransY _ _ _ (hfg x) (hg x y hxy))

/-- The exponential law: `H` is monotone on `Z × X` exactly when its sections are monotone and its curried
table is pointwise monotone. -/
theorem exponential_law {relZ : Fin m → Fin m → Prop} (hreflZ : ∀ z, relZ z z) (hreflX : ∀ x, relX x x)
    (htransY : ∀ a b c, relY a b → relY b c → relY a c) (H : Fin m → Fin k → Fin l) :
    (∀ z z' x x', relZ z z' → relX x x' → relY (H z x) (H z' x')) ↔
      ((∀ z x x', relX x x' → relY (H z x) (H z x')) ∧ (∀ z z', relZ z z' → ptw relY (H z) (H z'))) :=
  ⟨fun h => ⟨fun z x x' e => h z z x x' (hreflZ z) e, fun z z' e x => h z z' x x e (hreflX x)⟩,
   fun h z z' x x' ez ex => htransY _ _ _ (h.2 z z' ez x) (h.1 z' x x' ex)⟩

end LeanProofs.IPRA.Topology.FiniteFunctionSpace
