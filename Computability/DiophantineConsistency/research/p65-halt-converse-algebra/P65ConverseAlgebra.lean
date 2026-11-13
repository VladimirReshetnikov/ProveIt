import P65GraphShim
import Mathlib.Tactic.LinearCombination

/-! Halt-side residual assembly for the package-65 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
set_option maxRecDepth 16384
noncomputable section
namespace P65ConverseAlgebra
open DiophantineConsistency AdaptiveEquationSyntax2011 P65Graph
variable {R : Type*} [CommRing R]

/-- The five P65 residuals vanish from the displayed halt-side algebraic
relations. This does not assert that the relations are inhabited. -/
theorem residuals_zero (p : Fin 4 → ℤ) (v : Fin 14 → R)
    (tau sy tx gamma0 t4 wa yy g : R)
    (hY : v 8=sy*(vals p v).q3)
    (hfirst : v 9+(vals p v).ell+sy=tau)
    (htau : tau*tau=1+(vals p v).ell*((vals p v).ell+(vals p v).k))
    (htransport : (vals p v).C*((vals p v).X+(p 1:R)*(vals p v).q)-v 1*(vals p v).q=
      (vals p v).bJ*(vals p v).q*v 3)
    (hk : (vals p v).k=(vals p v).RR+1+(vals p v).M*t4)
    (hX : (vals p v).X=(vals p v).q*tx)
    (hgamma : v 13+tx=gamma0+t4)
    (hg : g=(vals p v).X+(vals p v).c*(vals p v).a+gamma0*(vals p v).H)
    (hmain : g*g=1+(vals p v).Delta*((vals p v).c*(vals p v).c))
    (hT : (v 4*v 4)*(v 6*(vals p v).c)=wa+(vals p v).c+(v 4*v 4)*(vals p v).RR)
    (hy : yy=wa+v 12)
    (hstrong : (vals p v).U=(v 5*((vals p v).c*(vals p v).c))*(v 5*((vals p v).c*(vals p v).c)))
    (haux : ((vals p v).U)*wa*wa+yy*yy=1+((vals p v).U)*yy*yy) :
    (graph p).A0.evalRing v=0 ∧ (graph p).Nm.evalRing v=0 ∧
    (graph p).At.evalRing v=0 ∧ (graph p).Aa.evalRing v=0 ∧
    (graph p).As.evalRing v=0 := by
  let z := vals p v
  have hM : z.M=z.S*z.q := rfl
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [A0_eval]
    have hshape : v 8+z.q3*(v 9+z.ell)=z.q3*tau := by
      rw [hY]
      linear_combination z.q3*hfirst
    change (v 8+z.q3*(v 9+z.ell))*(v 8+z.q3*(v 9+z.ell))-
      (z.q3*z.q3)*(1+z.ell*(z.ell+z.k))=0
    rw [hshape]
    linear_combination (z.q3*z.q3)*htau
  · rw [Nm_eval]
    have hshape : z.Dstar=z.M*g := by
      change z.M*(z.c*z.a+z.X)+z.H*((v 13*z.M-((z.k-z.RR)-1))+z.S*z.X)=z.M*g
      change z.k=z.RR+1+z.M*t4 at hk
      rw [hM] at hk
      rw [hM]
      linear_combination z.H*(z.S*z.q*hgamma+z.S*hX-hk)-z.S*z.q*hg
    change z.Dstar*z.Dstar-(z.M*z.M)*(1+z.Delta*(z.c*z.c))=0
    rw [hshape]
    linear_combination (z.M*z.M)*hmain
  · rw [At_eval]
    change z.C*z.X+z.q*((p 1:R)*z.C-v 1-z.bJ*v 3)=0
    linear_combination htransport
  · rw [Aa_eval]
    have hV : z.V=wa := by
      change (v 4*v 4)*(v 6*z.c-z.RR)-z.c=wa
      linear_combination hT
    change (v 12+z.V)*(v 12+z.V)-(v 12*z.U)*(v 12+(z.V+z.V))-1=0
    rw [hV]
    rw [hy] at haux
    linear_combination haux
  · rw [As_eval]
    exact sub_eq_zero.mpr hstrong.symm

#print axioms P65ConverseAlgebra.residuals_zero
end P65ConverseAlgebra
