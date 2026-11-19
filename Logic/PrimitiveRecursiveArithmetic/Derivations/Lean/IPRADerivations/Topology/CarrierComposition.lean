import IPRADerivations.Topology.Carriers

/-!
# Composition of carriers: associativity and identities

Packet: `topology/ipra_topology_framework_2026-11-15`, `paper/sections/05_carrier_theorems.tex`, Theorem
`thm:carrier-composition` ("Carrier composition"), second sentence: "Composition is associative, and
singleton identity clouds are identities." (The carrier property of the composite is `comp_carrier` of
`Topology/Carriers`.)

A carrier is a relation `C(v, w)` ("`w ∈ C(v)`"), an arbitrary formula in two variables. Carrier
composition is relational composition, `(D ∘ C)(v, u) :⟺ ∃ w. C(v, w) ∧ D(w, u)`, i.e.
`(D ∘ C)(v) = ⋃_{w ∈ C(v)} D(w)`; here it is written in diagrammatic order as `Comp C D`.

* `Comp C D`, `CompAt`, `app_comp`: the composite relation and its instances;
* `comp_intro`, `comp_elim`: the introduction and elimination rules, which hide the bound variable;
* `comp_assoc`: `Comp (Comp C D) E ⟺ Comp C (Comp D E)` at every pair of vertices;
* `Id`, `comp_id_left`, `comp_id_right`: the singleton cloud `Id(v) = {v}` is a two-sided identity.

Everything is first-order logic in iPRA; nothing is assumed bounded or decidable.
-/

namespace LeanProofs.IPRA.Topology.CarrierComposition

open LeanProofs.ConciseIPRA LeanProofs.IPRA
open LeanProofs.IPRA.Topology.FinitePreorder (App subst_App subst_up_shift)
open LeanProofs.IPRA.Topology.Carriers (App_congr)
open Syn
open scoped Fm
open ConciseIPRA.PTm (app zero succ)

variable {m : ℕ} {Γ : List (Fm PTm m)} {C D E : Fm PTm 2}

/-- `∃ w. C(a, w) ∧ D(w, b)`. -/
def CompAt {m : ℕ} (C D : Fm PTm 2) (a b : PTm m) : Fm PTm m :=
  Fm.ex (App C (Syn.shift a) (var 0) ⋏ App D (var 0) (Syn.shift b))

theorem subst_CompAt {j k : ℕ} (σ : Fin j → PTm k) (C D : Fm PTm 2) (a b : PTm j) :
    (CompAt C D a b).subst σ = CompAt C D (Syn.subst σ a) (Syn.subst σ b) := by
  simp only [CompAt, Fm.subst_ex, Fm.subst_and, subst_App, subst_up_shift, Syn.subst_var, Syn.up_zero]

/-- The composite relation, in diagrammatic order: first `C`, then `D`. -/
def Comp (C D : Fm PTm 2) : Fm PTm 2 := CompAt C D (var 0) (var 1)

theorem app_comp (C D : Fm PTm 2) (a b : PTm m) : App (Comp C D) a b = CompAt C D a b := by
  show (CompAt C D (var 0) (var 1)).subst ![a, b] = _
  rw [subst_CompAt]
  simp

theorem shift_App (R : Fm PTm 2) (s t : PTm m) :
    Fm.shift (App R s t) = App R (Syn.shift s) (Syn.shift t) := by
  unfold Fm.shift
  rw [subst_App]
  rfl

/-- Congruence of a binary relation in its first argument. -/
theorem App_congr₁ (R : Fm PTm 2) {s s' t : PTm m} (h : Γ ⊢[PRAAx] s ≐ s') (hR : Γ ⊢[PRAAx] App R s t) :
    Γ ⊢[PRAAx] App R s' t :=
  Prf.eqSubst R ![s, t] ![s', t] (fun i => by
    fin_cases i
    · exact h
    · exact .eqRefl t) hR

/-! ## The rules of composition -/

theorem comp_intro {a w b : PTm m} (h₁ : Γ ⊢[PRAAx] App C a w) (h₂ : Γ ⊢[PRAAx] App D w b) :
    Γ ⊢[PRAAx] App (Comp C D) a b := by
  rw [app_comp]
  unfold CompAt
  refine .exI w ?_
  simp only [Fm.subst_and, subst_App, Syn.subst_var, Syn.inst_zero, Syn.subst_inst_shift]
  exact .andI h₁ h₂

theorem comp_elim {a b : PTm m} {φ : Fm PTm m} (h : Γ ⊢[PRAAx] App (Comp C D) a b)
    (k : ((App C (Syn.shift a) (var 0) ⋏ App D (var 0) (Syn.shift b)) :: Γ.map Fm.shift) ⊢[PRAAx]
      Fm.shift φ) : Γ ⊢[PRAAx] φ := by
  rw [app_comp] at h
  unfold CompAt at h
  exact .exE h k

/-! ## Associativity -/

theorem assoc_fwd_core {a b u : PTm m} (hl : Γ ⊢[PRAAx] App (Comp C D) a u) (hr : Γ ⊢[PRAAx] App E u b) :
    Γ ⊢[PRAAx] App (Comp C (Comp D E)) a b := by
  refine comp_elim hl ?_
  rw [shift_App]
  have hr' := hr.shift
  rw [shift_App] at hr'
  exact comp_intro (Prf.andE₁ Prf.hyp0) (comp_intro (Prf.andE₂ Prf.hyp0) hr'.wk)

theorem assoc_fwd {a b : PTm m} (h : Γ ⊢[PRAAx] App (Comp (Comp C D) E) a b) :
    Γ ⊢[PRAAx] App (Comp C (Comp D E)) a b := by
  refine comp_elim h ?_
  rw [shift_App]
  exact assoc_fwd_core (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0)

theorem assoc_bwd_core {a b w : PTm m} (hl : Γ ⊢[PRAAx] App C a w) (hr : Γ ⊢[PRAAx] App (Comp D E) w b) :
    Γ ⊢[PRAAx] App (Comp (Comp C D) E) a b := by
  refine comp_elim hr ?_
  rw [shift_App]
  have hl' := hl.shift
  rw [shift_App] at hl'
  exact comp_intro (comp_intro hl'.wk (Prf.andE₁ Prf.hyp0)) (Prf.andE₂ Prf.hyp0)

theorem assoc_bwd {a b : PTm m} (h : Γ ⊢[PRAAx] App (Comp C (Comp D E)) a b) :
    Γ ⊢[PRAAx] App (Comp (Comp C D) E) a b := by
  refine comp_elim h ?_
  rw [shift_App]
  exact assoc_bwd_core (Prf.andE₁ Prf.hyp0) (Prf.andE₂ Prf.hyp0)

/-- `thm:carrier-composition`: composition of carriers is associative. -/
theorem comp_assoc (C D E : Fm PTm 2) (a b : PTm m) :
    Γ ⊢[PRAAx] Fm.iff (App (Comp (Comp C D) E) a b) (App (Comp C (Comp D E)) a b) :=
  Prf.iffI (.impI (assoc_fwd Prf.hyp0)) (.impI (assoc_bwd Prf.hyp0))

/-! ## Identities -/

/-- The singleton cloud: `Id(v) = {v}`. -/
def Id : Fm PTm 2 := var 0 ≐ var 1

theorem app_id (a b : PTm m) : App Id a b = (a ≐ b) := by
  simp [App, Id]

theorem id_left_fwd {a b : PTm m} (h : Γ ⊢[PRAAx] App (Comp Id C) a b) : Γ ⊢[PRAAx] App C a b := by
  refine comp_elim h ?_
  rw [shift_App]
  have e : ((App Id (Syn.shift a) (var 0) ⋏ App C (var 0) (Syn.shift b)) :: Γ.map Fm.shift) ⊢[PRAAx]
      App Id (Syn.shift a) (var 0) := Prf.andE₁ Prf.hyp0
  rw [app_id] at e
  exact App_congr₁ C (Prf.eqSymm e) (Prf.andE₂ Prf.hyp0)

theorem id_left_bwd {a b : PTm m} (h : Γ ⊢[PRAAx] App C a b) : Γ ⊢[PRAAx] App (Comp Id C) a b := by
  refine comp_intro (w := a) ?_ h
  rw [app_id]
  exact .eqRefl a

theorem id_right_fwd {a b : PTm m} (h : Γ ⊢[PRAAx] App (Comp C Id) a b) : Γ ⊢[PRAAx] App C a b := by
  refine comp_elim h ?_
  rw [shift_App]
  have e : ((App C (Syn.shift a) (var 0) ⋏ App Id (var 0) (Syn.shift b)) :: Γ.map Fm.shift) ⊢[PRAAx]
      App Id (var 0) (Syn.shift b) := Prf.andE₂ Prf.hyp0
  rw [app_id] at e
  exact App_congr C e (Prf.andE₁ Prf.hyp0)

theorem id_right_bwd {a b : PTm m} (h : Γ ⊢[PRAAx] App C a b) : Γ ⊢[PRAAx] App (Comp C Id) a b := by
  refine comp_intro (w := b) h ?_
  rw [app_id]
  exact .eqRefl b

/-- `thm:carrier-composition`: the singleton cloud is a left identity. -/
theorem comp_id_left (C : Fm PTm 2) (a b : PTm m) :
    Γ ⊢[PRAAx] Fm.iff (App (Comp Id C) a b) (App C a b) :=
  Prf.iffI (.impI (id_left_fwd Prf.hyp0)) (.impI (id_left_bwd Prf.hyp0))

/-- `thm:carrier-composition`: the singleton cloud is a right identity. -/
theorem comp_id_right (C : Fm PTm 2) (a b : PTm m) :
    Γ ⊢[PRAAx] Fm.iff (App (Comp C Id) a b) (App C a b) :=
  Prf.iffI (.impI (id_right_fwd Prf.hyp0)) (.impI (id_right_bwd Prf.hyp0))

end LeanProofs.IPRA.Topology.CarrierComposition
