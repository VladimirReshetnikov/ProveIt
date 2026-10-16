import BusyBeaver.ZFC.L2AxiomsEval254

/-!
L2: one run of the root of the 219-node program is one enumerator step.

`ax_eval` evaluates the generated `axioms()` composite symbolically: the
stack becomes `Enum254.axStack` and the current formula the gated bundle.
-/

namespace SetTheory.BusyBeaver.ZFC.L2

open RMDag Dag254 Code254

attribute [local irreducible] Code254.P

theorem ax_eval (np t S c a h pl : Nat) :
    f1 ⟨np, t, S, c, a, h, 0, 0, pl⟩ =
      ⟨np, Enum254.gate a (h + (Cantor.ofNat pl).1) c,
        Enum254.axStack a h (h + (Cantor.ofNat pl).1) c (Cantor.ofNat (Cantor.ofNat pl).2).1 t S,
        0, 0, 0, 0, 0, (Cantor.ofNat (Cantor.ofNat pl).2).2⟩ := by
  rw [e1]
  simp only [Enum254.gate, Enum254.axStack, bundle, bundleC, bundleG, rho1, rho2, rho3, rho4, rho5,
    rho6, rho7, rho8, Nat.zero_add, Nat.add_zero]

end SetTheory.BusyBeaver.ZFC.L2
