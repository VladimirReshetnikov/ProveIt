import DiophantineConsistency.FreeJFirstTransport
import DiophantineConsistency.ArithmeticAdaptiveRankWindow2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FreeJEarlyWindow
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.Ordinary12FreeJ
open DiophantineConsistency.ArithmeticAdaptiveRankWindow2011
open FreeJFirstTransport
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Early scalar window from the first-factor transport and explicit mask
bounds, with no strong norm or Pell rank hypothesis. -/
theorem early_window (p : Fin 4 → ℕ) (v : Fin 12 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀ j, 0<v j) (hz : InternalZero (literal (fun j => (p j:ℤ))) v) :
    let q : V := 1+v 0*(p 0:V)
    let R : V := ((q-1)*(q-v 1)+v 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*v 0
    24≤R ∧ R+q^3+q+1≤q^4 := by
  have hg := (freej_first_factor_transport p v hb hv hz).2
  have hgap : v 1+v 2<1+v 0*(p 0:V) := tsub_pos_iff_lt.mp hg
  exact scalar_rank_window _ _ _ _ _ _ _ hb (hv 0) (hv 1) (hv 2) hl hh (by ring) hgap
end FreeJEarlyWindow
#print axioms FreeJEarlyWindow.early_window
