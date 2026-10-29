import DiophantineConsistency.ArithmeticCarrierRadix2011
import DiophantineConsistency.ArithmeticPellRecurrence
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPellRecurrence
attribute [local irreducible] DiophantineConsistency.CurrentKernel2011.K DiophantineConsistency.CurrentMasks2011.radix DiophantineConsistency.CurrentMasks2011.beta
  DiophantineConsistency.CurrentMasks2011.lowPort DiophantineConsistency.CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
example (J F alpha z f i t yq w n eta zeta y gamma q : V)
    (hq : (DiophantineConsistency.CurrentMasks2011.beta : V)*J+1=q) :
    DiophantineConsistency.ArithmeticCarrierRadix2011.rank
        ![J, F, alpha, z, f, i, t, yq, w, n, eta, zeta, y, gamma] =
      ((q-1)*(q-F)+alpha)*(q^2-1)+
        ((DiophantineConsistency.CurrentMasks2011.lowPort:V)+q*
          ((DiophantineConsistency.CurrentMasks2011.highPort+
            DiophantineConsistency.CurrentMasks2011.beta:ℕ):V))*J := by
  have hqfull : DiophantineConsistency.ArithmeticCarrierRadix2011.q
      ![J, F, alpha, z, f, i, t, yq, w, n, eta, zeta, y, gamma] = q := by
    change (DiophantineConsistency.CurrentMasks2011.beta:V)*J+1=q
    exact hq
  unfold DiophantineConsistency.ArithmeticCarrierRadix2011.rank
  rw [hqfull]
  rfl
example (J F alpha z f i t yq w n eta zeta y gamma q R b : V)
    (hq : (DiophantineConsistency.CurrentMasks2011.beta : V)*J+1=q)
    (hR : R = ((q-1)*(q-F)+alpha)*(q^2-1)+
        ((DiophantineConsistency.CurrentMasks2011.lowPort:V)+q*
          ((DiophantineConsistency.CurrentMasks2011.highPort+
            DiophantineConsistency.CurrentMasks2011.beta:ℕ):V))*J)
    (hphase : R%4=3) (hy : y=ycoord R b) :
    let v : Fin 14 → V := ![J,F,alpha,z,f,i,t,yq,w,n,eta,zeta,y,gamma]
    DiophantineConsistency.ArithmeticCarrierRadix2011.rank v%4=3 ∧
      ∃ b, v 12=ycoord (DiophantineConsistency.ArithmeticCarrierRadix2011.rank v) b := by
  have hqfull : DiophantineConsistency.ArithmeticCarrierRadix2011.q
      ![J,F,alpha,z,f,i,t,yq,w,n,eta,zeta,y,gamma] = q := by
    change (DiophantineConsistency.CurrentMasks2011.beta:V)*J+1=q
    exact hq
  have hrank : DiophantineConsistency.ArithmeticCarrierRadix2011.rank
      ![J,F,alpha,z,f,i,t,yq,w,n,eta,zeta,y,gamma] = R := by
    unfold DiophantineConsistency.ArithmeticCarrierRadix2011.rank
    rw [hqfull, hR]
    rfl
  dsimp only
  constructor
  · rw [hrank]
    exact hphase
  · refine ⟨b, ?_⟩
    rw [hrank]
    exact hy
