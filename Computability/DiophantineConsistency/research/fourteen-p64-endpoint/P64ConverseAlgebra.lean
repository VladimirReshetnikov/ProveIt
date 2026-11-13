import P64GraphShim

/-! Ring-level assembly of the five P64 converse residuals. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace P64ConverseAlgebra
open DiophantineConsistency AdaptiveEquationSyntax2011 P64Graph
variable {R : Type*} [CommRing R]

/-- The displayed canonical witness relations force the exact P64
residuals to be `0, 0, 0, 1, 0`, respectively. -/
theorem residuals (p : Fin 4 → ℤ) (w : Fin 14 → R) (s tau t gammaOld g aux : R)
    (hY : w 7=s*(vals p w).q3)
    (htau_input : (vals p w).ell+w 9+s=tau)
    (htau : tau*tau=1+(vals p w).ell*((vals p w).ell+(vals p w).k))
    (hk : (vals p w).k=(vals p w).RR+1+4*(vals p w).X*(vals p w).U*t)
    (hgamma : w 13=gammaOld+4*(vals p w).X*t)
    (hg : g=(vals p w).X+(vals p w).a*(vals p w).c+gammaOld*(vals p w).H)
    (hmain : g*g=1+(vals p w).Delta*(vals p w).c*(vals p w).c)
    (hstrong : (w 5*((vals p w).c*(vals p w).c))*(w 5*((vals p w).c*(vals p w).c))=
      (vals p w).Aaux)
    (hV : (vals p w).V=aux)
    (haux : (vals p w).Aaux*aux*aux+(aux+w 12)*(aux+w 12)=
      1+(vals p w).Aaux*(aux+w 12)*(aux+w 12))
    (htransport : ((p 1:R)+w 8)*(vals p w).C=w 1+w 3*(vals p w).qm) :
    (graph p).A0.evalRing w=0 ∧ (graph p).M.evalRing w=0 ∧
    (graph p).W.evalRing w=0 ∧ (graph p).Na.evalRing w=1 ∧
    (graph p).Lt.evalRing w=0 := by
  have hD : (vals p w).Dstar=(vals p w).U*g := by
    change (vals p w).U*((vals p w).X+(vals p w).a*(vals p w).c)+
      (vals p w).H*((vals p w).U*w 13-((vals p w).k-(vals p w).RR-1)) = _
    rw [hgamma,hk,hg]
    ring
  refine ⟨?_,?_,?_,?_,?_⟩
  · rw [A0_eval]
    linear_combination ((vals p w).q3*((vals p w).ell+w 9)+w 7+(vals p w).q3*tau)*hY +
      ((vals p w).q3*((vals p w).ell+w 9)+w 7+(vals p w).q3*tau)*(vals p w).q3*htau_input +
      (vals p w).q3*(vals p w).q3*htau
  · rw [M_eval,hD]
    linear_combination (vals p w).U*(vals p w).U*hmain
  · rw [W_eval,hstrong]
    ring
  · rw [Na_eval]
    change (vals p w).Aaux*((vals p w).V*(vals p w).V-
      ((vals p w).V+w 12)*((vals p w).V+w 12))+
      ((vals p w).V+w 12)*((vals p w).V+w 12)=1
    rw [hV]
    linear_combination haux
  · rw [Lt_eval,htransport]
    ring

#print axioms P64ConverseAlgebra.residuals
end P64ConverseAlgebra
