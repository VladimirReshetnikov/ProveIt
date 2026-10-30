import ZFCinPA.NativeGicDelta1
import ZFCinPA.ZFDelta1
import ZFCinPA.Translation
import BusyBeaver.ZFC.ProfileModel

set_option autoImplicit false
noncomputable section

/-!
# The native theory as a `Δ₁` Foundation theory (`R1`)

The native numerical calculus (`Code254.C254`) is equiconsistent with the
first-order theory `NativeTheory254.NativeAx`: the sealed container axiom,
global-image collection (GIC) for every matrix, and irreflexivity. For the
represented reverse comparison (plan doc
`Computability/BusyBeaver/Research/ZFC/pa_internalization.md`, "Proposed
decomposition of the reverse ZF-to-validator translation") the same theory
is needed over Foundation's `ℒₛₑₜ`, as a `Δ₁` theory whose provability
predicate is available in every model of `𝗜𝚺₁`:

`nativeTheory = 𝗘𝗤 ℒₛₑₜ ∪ {containerAx, irAx} ∪ gicTheory`.

The container axiom and irreflexivity are the `toSet` translations of the
native `containerForm` and `irForm`; the GIC schema (`NativeGicDelta1`) ranges
over all Foundation two-variable cores. `models_cpgic` reads every model of
`nativeTheory` as a native CP/GIC model with raw irreflexivity, via
`eval_toSet`; this is the semantic side used by the WF interpretation
(`R3`).
-/

namespace LeanProofs.ZFCinPA.NativeSet

open LO LO.FirstOrder LO.FirstOrder.SetTheory
open LeanProofs.ZFCinPA

/-- Raw irreflexivity, as in `NativeTheory254.irForm`. -/
def irForm : SetTheory.Form := .fAll (.fImp (.fMem 0 0) .fBot)

/-- The container axiom, translated. -/
def containerAx : SetTheorySentence :=
  (toSet 0 SetTheory.BusyBeaver.ZFC.ProfileModel.containerForm).univCl

/-- Irreflexivity, translated. -/
def irAx : SetTheorySentence := (toSet 0 irForm).univCl

/-- The two fixed native axioms. -/
def nativeFixed : SetTheory := {containerAx, irAx}

noncomputable instance nativeFixed_delta1 : nativeFixed.Δ₁ :=
  (Theory.Δ₁.ofList [containerAx, irAx]).ofEq (by ext φ; simp [nativeFixed])

/-- **The native theory** over `ℒₛₑₜ`. -/
abbrev nativeTheory : SetTheory := 𝗘𝗤 ℒₛₑₜ ∪ nativeFixed ∪ gicTheory

noncomputable instance nativeTheory_delta1 : nativeTheory.Δ₁ := inferInstance

instance : 𝗘𝗤 ℒₛₑₜ ⪯ nativeTheory :=
  LO.Entailment.WeakerThan.ofSubset (fun _ h => Or.inl (Or.inl h))

/-! ## Semantics: every model of `nativeTheory` is a native CP/GIC model -/

section Semantics

open SetTheory.BusyBeaver.ZFC

variable {M : Type} [Nonempty M] [SetStructure M] [M↓[ℒₛₑₜ] ⊧* nativeTheory]

theorem models_containerAx : M↓[ℒₛₑₜ] ⊧ containerAx :=
  models_of_mem (T := nativeTheory) (Or.inl (Or.inr (Or.inl rfl)))

theorem models_irAx : M↓[ℒₛₑₜ] ⊧ irAx :=
  models_of_mem (T := nativeTheory) (Or.inl (Or.inr (Or.inr rfl)))

theorem models_gic (ψ : SetTheorySemiproposition 2) :
    M↓[ℒₛₑₜ] ⊧ (gicBodyMeta ψ).univCl :=
  models_of_mem (T := nativeTheory) (Or.inr ⟨ψ, rfl⟩)

/-- A translated closed native formula holds at every environment. -/
theorem sat_of_models_toSet (φ : SetTheory.Form) (h : M↓[ℒₛₑₜ] ⊧ (toSet 0 φ).univCl)
    (e : ℕ → M) : SetTheory.Sat (memRel M) e φ :=
  (eval_toSet φ 0 ![] e e (fun i => i.elim0) (fun j => by rw [Nat.zero_add])).mp
    (models_iff_proposition.mp h e)

theorem containers : ProfileCollection.Containers (memRel M) :=
  (ProfileModel.sat_containerForm (memRel M) (fun _ => Classical.arbitrary M)).mp
    (sat_of_models_toSet _ models_containerAx _)

theorem irreflexive (x : M) : ¬ x ∈ x := by
  have h := sat_of_models_toSet irForm models_irAx (fun _ => x)
  exact fun hx => h x hx

/-- Every native matrix has its global-image collection instance. -/
theorem collection (phi : SetTheory.Form) (env : ℕ → M) :
    ProfileCollection.CollectionInstance (memRel M)
      (DeepPositiveClosure.MatrixRelation (memRel M) phi env) := by
  have h := models_iff_proposition.mp (models_gic (M := M) (toSet 2 phi)) env
  have key : ∀ x y : M, (toSet 2 phi).Eval ![x, y] env ↔
      DeepPositiveClosure.MatrixRelation (memRel M) phi env x y := fun x y =>
    eval_toSet phi 2 ![x, y] env _ (fun i => by
      match i with
      | 0 => rfl
      | 1 => rfl) (fun j => by rw [Nat.add_comm]; rfl)
  simp [gicBodyMeta, gicAtomYB3, gicAtomXA3, gicAtomYB4, Semiformula.eval_substs,
    Matrix.comp_vecCons', Matrix.constant_eq_singleton] at h
  intro a
  obtain ⟨b, h1, h2⟩ := h a
  refine ⟨b, fun y hy => ?_, fun x hx ⟨y, hy⟩ => ?_⟩
  · obtain ⟨x, hx⟩ := h1 y hy
    exact ⟨x, (key x y).1 hx⟩
  · obtain ⟨y', hy', h'⟩ := h2 x hx y ((key x y).2 hy)
    exact ⟨y', hy', (key x y').1 h'⟩

/-- **Every model of the native theory is an irreflexive CP/GIC model.** -/
theorem models_cpgic : ProfileModel.ModelsCPGIC (memRel M) ∧ ∀ x : M, ¬ x ∈ x :=
  ⟨⟨fun env => (ProfileModel.sat_containerForm (memRel M) env).mpr containers,
    fun phi _ env => (ProfileSyntax.sat_gicForm (memRel M) phi env).mpr (collection phi env)⟩,
    irreflexive⟩

end Semantics

end LeanProofs.ZFCinPA.NativeSet
