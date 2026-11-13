import Absorb88Forward

/-! Reverse the 88 map when the absorbed witness exceeds ell+k. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Absorb88Inverse
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency FreeJAbsorb88 Absorb88First Absorb88Forward
open AdaptiveEquationSyntax2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def threshold (p : Fin 4 → ℕ) (v : Fin 12 → V) : V :=
  let q : V := 1+v 0*(p 0:V)
  let X : V := q*v 5
  let Y : V := (q*(q*q))*v 6
  let k : V := v 8+v 9
  (X*Y)*(Y*k)+k

def inverse (p : Fin 4 → ℕ) (v : Fin 12 → V) : Fin 12 → V :=
  Function.update v 7 (v 7-threshold p v)

theorem inverse_pos (p : Fin 4 → ℕ) (v : Fin 12 → V) (hv : ∀j,0<v j)
    (h : threshold p v<v 7) : ∀j,0 < inverse p v j := by
  intro j
  by_cases hj : j=7
  · subst j
    simpa [inverse] using tsub_pos_iff_lt.mpr h
  · simpa [inverse,hj] using hv j

theorem transform_inverse (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (h : threshold p v≤v 7) : transform p (inverse p v)=v := by
  funext i
  by_cases hi : i=7
  · subst i
    simp only [transform,inverse,Function.update_self]
    simp only [Function.update_noteq (show (0:Fin 12) ≠ 7 by decide),
      Function.update_noteq (show (5:Fin 12) ≠ 7 by decide),
      Function.update_noteq (show (6:Fin 12) ≠ 7 by decide),
      Function.update_noteq (show (8:Fin 12) ≠ 7 by decide),
      Function.update_noteq (show (9:Fin 12) ≠ 7 by decide)]
    change threshold p v+(v 7-threshold p v)=v 7
    rw [add_comm,tsub_add_cancel_of_le h]
  · simp [transform,inverse,hi]

theorem exists_89_of_gap (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hv : ∀j,0<v j) (hgap : threshold p v<v 7)
    (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃w : Fin 12 → V, (∀j,0<w j) ∧
      InternalZero (FreeJAbsorb89.graph (integerPorts p)).output w := by
  refine ⟨inverse p v,inverse_pos p v hv hgap,?_⟩
  apply (Absorb88Forward.zero_iff p (inverse p v)).mp
  rw [transform_inverse p v (le_of_lt hgap)]
  exact hz

#print axioms Absorb88Inverse.exists_89_of_gap
end Absorb88Inverse
