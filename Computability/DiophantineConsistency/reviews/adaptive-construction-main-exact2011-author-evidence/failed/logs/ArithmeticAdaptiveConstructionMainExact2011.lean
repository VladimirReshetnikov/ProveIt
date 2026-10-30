import DiophantineConsistency.ArithmeticAdaptiveConstructionCarrier2011

/-! Exact natural main-carrier factorization from additive correction data. -/
set_option autoImplicit false
set_option Elab.async false
namespace DiophantineConsistency.ArithmeticAdaptiveConstructionMainExact2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticAdaptiveConstructionCarrier2011
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- Additive quotient and correction equalities justify the truncated
subtraction and recover exactly the old main carrier at scale Y*q². -/
theorem main_shift_exact (q X Y w gamma gammaOld t R k : V)
    (hX : X=q*w) (hk : k=R+1+(Y*q^2)*t)
    (hg : gamma+w=gammaOld+t) :
    (Y*q^2)*gamma+q*(X*Y)-(k-R-1)=(Y*q^2)*gammaOld := by
  have hv : k-R-1=(Y*q^2)*t := by
    rw [hk]
    simp [add_assoc]
  have hs : (Y*q^2)*gamma+q*(X*Y)=(Y*q^2)*gammaOld+(Y*q^2)*t := by
    calc _=(Y*q^2)*(gamma+w) := by rw [hX]; ring
         _=(Y*q^2)*(gammaOld+t) := by rw [hg]
         _=_ := by ring
  rw [hv,hs]
  simp

/-- The exact shift restores the old norm, scaled by the square of Y*q². -/
theorem main_norm_exact (q X Y w gamma gammaOld t R k a c H delta : V)
    (hX : X=q*w) (hk : k=R+1+(Y*q^2)*t)
    (hg : gamma+w=gammaOld+t)
    (hnorm : (X+a*c+H*gammaOld)*(X+a*c+H*gammaOld)=1+delta*c*c) :
    let D := (Y*q^2)*(X+a*c)+H*((Y*q^2)*gamma+q*(X*Y)-(k-R-1))
    D*D=(Y*q^2)*(Y*q^2)*(1+delta*c*c) := by
  dsimp only
  rw [main_shift_exact q X Y w gamma gammaOld t R k hX hk hg]
  calc
    ((Y*q^2)*(X+a*c)+H*((Y*q^2)*gammaOld))^2 =
        (Y*q^2)*(Y*q^2)*((X+a*c+H*gammaOld)*(X+a*c+H*gammaOld)) := by ring
    _=(Y*q^2)*(Y*q^2)*(1+delta*c*c) := by rw [hnorm]
end DiophantineConsistency.ArithmeticAdaptiveConstructionMainExact2011
