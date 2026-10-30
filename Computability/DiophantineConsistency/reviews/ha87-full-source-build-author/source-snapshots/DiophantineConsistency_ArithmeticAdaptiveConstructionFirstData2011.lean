import DiophantineConsistency.ArithmeticAdaptiveConstructionFirstScalar2011
import DiophantineConsistency.ArithmeticAdaptiveConstructionFirstActual2011

/-! Actual first-carrier data before the literal-factor application. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionFirstData2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticCarrierSoundness2011 ArithmeticCarrierRadix2011 ArithmeticOuterSeed
  ArithmeticAdaptiveConstructionFirstActual2011 ArithmeticAdaptiveConstructionTransport2011
  ArithmeticAdaptiveConstructionFirstScalar2011
attribute [local irreducible] CurrentKernel2011.K CurrentMasks2011.beta
  CurrentMasks2011.lowPort CurrentMasks2011.highPort
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem transport_first_difference (q K w F alpha C z : V)
    (hsum : C+F+alpha=q)
    (ht : (q*K+q*w)*C=q*F+(q-1)*(q*(z-1))) :
    q*(q*w+K*q)=(F+alpha)*(q*w+K*q)+F*q+(q-1)*(q*(z-1)) := by
  calc q*(q*w+K*q)=(C+F+alpha)*(q*w+K*q) := by rw [hsum]
       _=(F+alpha)*(q*w+K*q)+(q*K+q*w)*C := by ring
       _=(F+alpha)*(q*w+K*q)+F*q+(q-1)*(q*(z-1)) := by rw [ht]; ring

def FirstData (v : Fin 14 → V) (r : V) : Prop :=
  let q := ArithmeticCarrierRadix2011.q v
  let X := q*v 8
  let Y := v 7*q^3
  let k := v 10+v 11
  let ell := (X*Y)*(Y*k)
  let tau := X*Y*v 9+k-rank v
  let A := X+(CurrentKernel2011.K:V)*q
  let Bp := q*A
  let Bn := (v 1+v 2)*A+v 1*q
  let M := q*(q*q)*(q-1)
  let W := 1+k*(q-1)
  M*(ell+k+r)+Y*(q-1)+Bn*(W*(q*(q*q))) = Bp*(W*(q*(q*q)))+M*tau ∧
    tau*tau=1+ell*(ell+k)

/-- The actual vector and seed provide positive r and the precise additive
carrier data, independently of the syntax-level factor application. -/
theorem actual_first_data (v : Fin 14 → V) (u : V)
    (hv : ∀ j, 0<v j)
    (he : Equations (CurrentMasks2011.beta:V) (CurrentKernel2011.K:V)
      (CurrentMasks2011.lowPort:V) ((CurrentMasks2011.highPort+CurrentMasks2011.beta:ℕ):V) v)
    (hphase : rank v%4=3)
    (hq : ArithmeticCarrierRadix2011.q v=Exp.exp u)
    (hX : Exp.exp (rank v)=ArithmeticCarrierRadix2011.q v*v 8)
    (hR : 2*u≤rank v)
    (hseed : SeedRelations u (rank v) (v 7) (v 9) (v 10) (v 11) (v 13)) :
    ∃ r : V, 0<r ∧ FirstData v r := by
  let q := ArithmeticCarrierRadix2011.q v
  let X := q*v 8
  let Y := v 7*q^3
  let k := v 10+v 11
  let ell := (X*Y)*(Y*k)
  let R := rank v
  let tau := X*Y*v 9+k-R
  let b := q*(v 3-1)
  let C := q-v 1-v 2
  let A := X+(CurrentKernel2011.K:V)*q
  let Bp := q*A
  let Bn := (v 1+v 2)*A+v 1*q
  let M := q*(q*q)*(q-1)
  let W := 1+k*(q-1)
  obtain ⟨r,hr,_,hcar⟩ := positive_first_of_actual v u hv he hphase hq hX hR hseed
  have hcar' : M*(ell+k+r)+Y*(q-1)=M*tau+W*(q*(q*q))*((q-1)*b) := by
    rw [←hq,hX] at hcar
    change (q^3*(q-1))*((X*Y*Y)*k+k+r)+(q^3*v 7)*(q-1) =
      (q^3*(q-1))*tau+(1+(q-1)*k)*q^3*((q-1)*b) at hcar
    exact first_carrier_scalar q X Y k (v 7) r tau b rfl hcar
  have hnorm : tau*tau=1+ell*(ell+k) := by
    have hh := hseed.1
    rw [←hq,hX] at hh
    change tau*tau=1+(X*Y*Y)*((X*Y*Y)+1)*k*k at hh
    exact first_norm_scalar X Y k tau hh
  have ht := adaptive_transport_of_equations v hv he
  change 0<C ∧ (q*(CurrentKernel2011.K:V)+q*v 8)*C=q*v 1+(q-1)*b at ht
  have hlt : v 1+v 2<q := by
    have h := ht.1
    change 0<q-v 1-v 2 at h
    rw [tsub_tsub] at h
    exact tsub_pos_iff_lt.mp h
  have hsum : C+v 1+v 2=q := by
    have h := add_tsub_cancel_of_le (le_of_lt hlt)
    change v 1+v 2+(q-(v 1+v 2))=q at h
    dsimp only [C]
    rw [tsub_tsub]
    calc _=(v 1+v 2)+(q-(v 1+v 2)) := by ring
         _=q := h
  have hbp : Bp=Bn+(q-1)*b := by
    dsimp only [Bp,Bn,A,X]
    exact transport_first_difference q (CurrentKernel2011.K:V) (v 8) (v 1) (v 2) C (v 3) hsum ht.2
  have hcut : M*(ell+k+r)+Y*(q-1)+Bn*(W*(q*(q*q))) =
      Bp*(W*(q*(q*q)))+M*tau := by
    calc _=M*tau+W*(q*(q*q))*((q-1)*b)+Bn*(W*(q*(q*q))) := by rw [hcar']
         _=(Bn+(q-1)*b)*(W*(q*(q*q)))+M*tau := by ring
         _=Bp*(W*(q*(q*q)))+M*tau := by rw [hbp]
  exact ⟨r,hr,hcut,hnorm⟩
end DiophantineConsistency.ArithmeticAdaptiveConstructionFirstData2011
