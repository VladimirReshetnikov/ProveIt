import IPRADerivations.Topology.FinitePreorder
import IPRADerivations.Foundations.CoherentTower

/-!
# Selections of a strong carrier are simplicial and contiguous

Packet: `topology/ipra_topology_framework_2026-11-15`, `paper/sections/05_carrier_theorems.tex`, Theorem
`thm:selection` ("Selection theorem"): every selection `f` of a strong carrier `C : K ⊸ L` is simplicial, and
any two selections `f`, `g` are contiguous, i.e. `f(σ) ∪ g(σ)` is a simplex of `L` for every simplex `σ` of
`K`.

Finite vertex sets are presented by codes with membership relations: `A(v, p)` says that `v` belongs to the
set coded by `p` on the `K` side, `B(w, q)` on the `L` side. The simplices are given by formulas `SK(p)`,
`SL(q)`, and the carrier by a relation `C(v, w)` ("`w ∈ C(v)`"). All of these are arbitrary formulas; nothing
is assumed bounded or decidable, and the derivation is first-order logic in iPRA.

* `Carried A B C p q`: `∀ w, B(w, q) → ∃ v, A(v, p) ∧ C(v, w)`, i.e. `q ⊆ C(p) = ⋃_{v ∈ p} C(v)`;
* `InImages A B f g p q`: `∀ w, B(w, q) → ∃ v, A(v, p) ∧ (w = f(v) ∨ w = g(v))`, i.e. `q ⊆ f(p) ∪ g(p)`;
* the strong-carrier property enters as the rule `hcar`: a set carried by a simplex of `K` is a simplex of
  `L` (the carrier condition "`C(σ)` is a simplex" together with "a subset of a simplex is a simplex");
* `carried_of_images`: if `f` and `g` are selections (`C(v, f(v))`, `C(v, g(v))`), then
  `q ⊆ f(p) ∪ g(p)` gives `q ⊆ C(p)`;
* `contiguous` (`thm:selection`, second statement): for a simplex `p` of `K`, every `q ⊆ f(p) ∪ g(p)` is a
  simplex of `L`;
* `simplicial` (`thm:selection`, first statement): the case `g = f`, every `q ⊆ f(p)` is a simplex of `L`.

Carrier composition, the prism identity and the homology statements of the section are not derived here.
-/

namespace LeanProofs.IPRA.Topology.Carriers

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Topology.FinitePreorder (App)
open LeanProofs.IPRA.Foundations.CoherentTower (ex_mono)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {m : ℕ} {Γ : List (Fm PTm m)}

/-- `S(p)` for a formula `S` in one variable. -/
abbrev At {m : ℕ} (S : Fm PTm 1) (p : PTm m) : Fm PTm m := S.subst ![p]

/-- `q ⊆ C(p)`: every member of `q` is carried by a member of `p`. -/
abbrev Carried {m : ℕ} (A B C : Fm PTm 2) (p q : PTm m) : Fm PTm m :=
  Fm.all (App B (var 0) (Syn.shift q) ⟶
    Fm.ex (App A (var 0) (Syn.shift (Syn.shift p)) ⋏ App C (var 0) (var 1)))

/-- `q ⊆ f(p) ∪ g(p)`. -/
abbrev InImages {m : ℕ} (A B : Fm PTm 2) (f g : PTm 1) (p q : PTm m) : Fm PTm m :=
  Fm.all (App B (var 0) (Syn.shift q) ⟶
    Fm.ex (App A (var 0) (Syn.shift (Syn.shift p)) ⋏
      ((var 1 ≐ inst1 f (var 0)) ⋎ (var 1 ≐ inst1 g (var 0)))))

/-- Congruence of a binary relation in its second argument. -/
theorem App_congr (C : Fm PTm 2) {s t t' : PTm m} (h : Γ ⊢[PRAAx] t ≐ t') (hC : Γ ⊢[PRAAx] App C s t) :
    Γ ⊢[PRAAx] App C s t' :=
  Prf.eqSubst C ![s, t] ![s, t'] (fun i => by
    fin_cases i
    · exact .eqRefl s
    · exact h) hC

section Selection

variable {A B C : Fm PTm 2} {SK SL : Fm PTm 1} {f g : PTm 1} {p q : PTm m}

/-- For selections `f`, `g` of `C`: `q ⊆ f(p) ∪ g(p)` gives `q ⊆ C(p)`. -/
theorem carried_of_images
    (hf : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (v : PTm k), Δ ⊢[PRAAx] App C v (inst1 f v))
    (hg : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (v : PTm k), Δ ⊢[PRAAx] App C v (inst1 g v))
    (h : Γ ⊢[PRAAx] InImages A B f g p q) : Γ ⊢[PRAAx] Carried A B C p q := by
  refine .allI (.impI ?_)
  refine ex_mono (Prf.impE (Prf.allOpen h).wk Prf.hyp0) ?_
  refine .andI (Prf.andE₁ Prf.hyp0) ?_
  refine .orE (Prf.andE₂ Prf.hyp0) ?_ ?_
  · exact App_congr C (Prf.eqSymm Prf.hyp0) (hf (var 0))
  · exact App_congr C (Prf.eqSymm Prf.hyp0) (hg (var 0))

/-- `thm:selection`: two selections of a strong carrier are contiguous. -/
theorem contiguous
    (hcar : ∀ {k : ℕ} {Δ : List (Fm PTm k)} {p q : PTm k},
      (Δ ⊢[PRAAx] At SK p) → (Δ ⊢[PRAAx] Carried A B C p q) → (Δ ⊢[PRAAx] At SL q))
    (hf : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (v : PTm k), Δ ⊢[PRAAx] App C v (inst1 f v))
    (hg : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (v : PTm k), Δ ⊢[PRAAx] App C v (inst1 g v))
    (hp : Γ ⊢[PRAAx] At SK p) (hq : Γ ⊢[PRAAx] InImages A B f g p q) : Γ ⊢[PRAAx] At SL q :=
  hcar hp (carried_of_images hf hg hq)

/-- `thm:selection`: a selection of a strong carrier is simplicial. -/
theorem simplicial
    (hcar : ∀ {k : ℕ} {Δ : List (Fm PTm k)} {p q : PTm k},
      (Δ ⊢[PRAAx] At SK p) → (Δ ⊢[PRAAx] Carried A B C p q) → (Δ ⊢[PRAAx] At SL q))
    (hf : ∀ {k : ℕ} {Δ : List (Fm PTm k)} (v : PTm k), Δ ⊢[PRAAx] App C v (inst1 f v))
    (hp : Γ ⊢[PRAAx] At SK p) (hq : Γ ⊢[PRAAx] InImages A B f f p q) : Γ ⊢[PRAAx] At SL q :=
  contiguous hcar hf hf hp hq

end Selection

end LeanProofs.IPRA.Topology.Carriers
