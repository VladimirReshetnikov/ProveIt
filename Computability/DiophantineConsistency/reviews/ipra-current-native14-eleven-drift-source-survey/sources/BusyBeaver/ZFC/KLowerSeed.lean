import BusyBeaver.ZFC.KSeedInterface222
import BusyBeaver.ZFC.Code254GIC

/-!
The seed property for every first-order `Form` (De Bruijn, with literal equality), the interface
of the semantic lower chain of the 222/221 calculus.

`FormSeed mem`: for every formula `φ`, parameters `env` and input `A`, the relation
`R x y := φ(y, x, env)` (output in slot 0, input in slot 1) has Elliot Glazer's seed property at
`A`. It follows from `FullSeed` through `Code254GIC.toNamed`, which puts slot `i` at name `2i+1`;
the wrapper `∀v₃ (v₃ = v₀ → …)` moves the input from name 3 to the seed's input name 0.
-/

namespace SetTheory.BusyBeaver.ZFC.KLower

open SetTheory.BusyBeaver.ZFC.KSeed222 SetTheory.BusyBeaver.ZFC.KIndisc222 Form

universe u
variable {V : Type u}

/-- The seed property for every first-order relation (output slot 0, input slot 1). -/
def FormSeed (mem : V → V → Prop) : Prop :=
  ∀ (φ : Form) (env : Nat → V) (A : V),
    SeedProp mem (fun x y => Sat mem (scons y (scons x env)) φ) A

theorem seedProp_congr {mem : V → V → Prop} {R R' : V → V → Prop} {A : V}
    (h : ∀ x y, R x y ↔ R' x y) (hs : SeedProp mem R A) : SeedProp mem R' A := by
  have e : R = R' := funext fun x => funext fun y => propext (h x y)
  exact e ▸ hs

/-- **Every full seed model has the seed property for every `Form`.** -/
theorem formSeed_of_fullSeed {mem : V → V → Prop} (h : FullSeed mem) : FormSeed mem := by
  intro φ env A
  let ψ : Tarski.NF := .all 3 (.imp (.eq 3 0) (Code254GIC.toNamed 0 φ))
  let e : Nat → V := fun n => if n = 0 then A else env ((n - 5) / 2)
  have key : ∀ x y, Tarski.Sat mem (Tarski.update (Tarski.update e 0 x) 1 y) ψ ↔
      Sat mem (scons y (scons x env)) φ := by
    intro x y
    have hT : Tarski.Sat mem (Tarski.update (Tarski.update (Tarski.update e 0 x) 1 y) 3 x)
        (Code254GIC.toNamed 0 φ) ↔ Sat mem (scons y (scons x env)) φ := by
      apply Code254GIC.sat_toNamed mem h.irr
      intro i
      match i with
      | 0 => simp [Code254GIC.names, Tarski.update, scons]
      | 1 => simp [Code254GIC.names, Tarski.update, scons]
      | k + 2 =>
          have h1 : 2 * (k + 2) + 1 ≠ 3 := by omega
          have h2 : 2 * (k + 2) + 1 ≠ 1 := by omega
          have h3 : 2 * (k + 2) + 1 ≠ 0 := by omega
          have h4 : (2 * (k + 2) + 1 - 5) / 2 = k := by omega
          simp only [Code254GIC.names, Tarski.update, h1, h2, h3, if_false, e, h4, scons]
    constructor
    · intro hall
      refine hT.mp (hall x ?_)
      simp [Tarski.Sat, Tarski.update]
    · intro hφ d hd
      have hd' : d = x := by simpa [Tarski.Sat, Tarski.update] using hd
      subst hd'
      exact hT.mpr hφ
  have hs := h.seed ψ e
  have he0 : e 0 = A := by simp [e]
  rw [he0] at hs
  exact seedProp_congr key hs

#print axioms formSeed_of_fullSeed

end SetTheory.BusyBeaver.ZFC.KLower
