import DiophantineConsistency.ArithmeticOuterSeed
import DiophantineConsistency.ArithmeticCarrierRadix2011
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency DiophantineConsistency.ArithmeticPellRecurrence
  DiophantineConsistency.ArithmeticOuterSeed
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.radix CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Projection of the enriched facts on the Assembly's concrete vector;
all construction facts are explicit hypotheses. -/
theorem seed_projection (J F alpha z f i T s w n eta zeta y gamma q R u b : V)
    (hq : (CurrentMasks2011.beta:V)*J+1=q)
    (hrank : R=((q-1)*(q-F)+alpha)*(q^2-1)+
      ((CurrentMasks2011.lowPort:V)+q*((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V))*J)
    (hphase : R%4=3) (hy : y=ycoord R b)
    (hqexp : q=Exp.exp u) (hX : Exp.exp R=q*w) (hbig : 2*u≤R)
    (hseed : SeedRelations u R s n eta zeta gamma)
    (hlit : let c := (eta+zeta)*(s*q^3)+eta
      let a := f*f*c*T
      let b := f*f*R+c
      a=(a-b)+(b-a)+c+f*f*R) :
    let v : Fin 14 → V := ![J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma]
    ArithmeticCarrierRadix2011.rank v%4=3 ∧
      (∃ b, v 12=ycoord (ArithmeticCarrierRadix2011.rank v) b) ∧
      ∃ u, ArithmeticCarrierRadix2011.q v=Exp.exp u ∧
        Exp.exp (ArithmeticCarrierRadix2011.rank v)=ArithmeticCarrierRadix2011.q v*v 8 ∧
        2*u≤ArithmeticCarrierRadix2011.rank v ∧
        SeedRelations u (ArithmeticCarrierRadix2011.rank v) (v 7) (v 9) (v 10) (v 11) (v 13) ∧
        let q := ArithmeticCarrierRadix2011.q v
        let Y := v 7*q^3
        let c := (v 10+v 11)*Y+v 10
        let R := ArithmeticCarrierRadix2011.rank v
        let a := v 4*v 4*c*v 6
        let b := v 4*v 4*R+c
        a=(a-b)+(b-a)+c+v 4*v 4*R := by
  have hqfull : ArithmeticCarrierRadix2011.q
      ![J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma]=q := by
    change (CurrentMasks2011.beta:V)*J+1=q
    exact hq
  have hrankfull : ArithmeticCarrierRadix2011.rank
      ![J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma]=R := by
    unfold ArithmeticCarrierRadix2011.rank
    rw [hqfull,hrank]
    rfl
  dsimp only
  refine ⟨?_, ?_, u, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hrankfull]; exact hphase
  · refine ⟨b,?_⟩
    rw [hrankfull]; exact hy
  · rw [hqfull]; exact hqexp
  · change Exp.exp (ArithmeticCarrierRadix2011.rank ![J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma]) =
      ArithmeticCarrierRadix2011.q ![J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma]*w
    rw [hqfull,hrankfull]; exact hX
  · rw [hrankfull]; exact hbig
  · change SeedRelations u (ArithmeticCarrierRadix2011.rank ![J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma]) s n eta zeta gamma
    rw [hrankfull]; exact hseed
  · change f*f*((eta+zeta)*(s*(ArithmeticCarrierRadix2011.q
      ![J,F,alpha,z,f,i,T,s,w,n,eta,zeta,y,gamma])^3)+eta)*T = _
    rw [hqfull,hrankfull]
    let c := (eta+zeta)*(s*q^3)+eta
    change f*f*c*T=(f*f*c*T-(f*f*R+c))+(f*f*R+c-f*f*c*T)+c+f*f*R
    exact hlit
#print axioms seed_projection
