import Direct80UnweightedProjection
import Direct80NaturalProjection
import DiophantineConsistency.ArithmeticPellPowerRecovery

/-! Positive projection quotient without an 80 graph-zero assumption. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositiveScaledKappaGeneric
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
open ArithmeticPellRecurrence ArithmeticPellPowerRecovery TenPositive80NaturalProjection
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive_kappa (a R X : V) (hX : X=Exp.exp R)
    (hsize : X<ycoord R a) :
    let C:=ycoord R a
    ∃ kappa : V, 0<kappa ∧
      X*(3*C-2*X)+2=(4*a+3)*kappa := by
  let C:=ycoord R a
  let H:=4*a+3
  let K:=X*(3*C-2*X)+2
  have hC : 0<C := lt_of_le_of_lt (by simp) hsize
  have h2 : 2*X<2*C := mul_lt_mul_of_pos_left hsize (by simp)
  have h23 : 2*C≤3*C := by
    have hh : 2*C≤2*C+C := by simp
    simpa only [show 2*C+C=3*C by ring] using hh
  have hgap : 2*X<3*C := lt_of_lt_of_le h2 h23
  have hcast : (ι (3*C-2*X):DiffRing V)=3*ι C-2*ι X := by
    apply eq_sub_iff_add_eq.mpr
    have he : (2:DiffRing V)*ι X=ι (2*X) := by rw [map_mul,map_ofNat]
    rw [he,←map_add]
    change ι ((3*C-2*X)+2*X)=3*ι C
    rw [tsub_add_cancel_of_le (le_of_lt hgap),map_mul,map_ofNat]
  have hKcast : (ι K:DiffRing V)=(4*ι a+3)*ι X*ι C-
      2*(ι X*ι X+2*ι a*ι X*ι C-1) := by
    dsimp [K]
    rw [map_add,map_mul,map_ofNat,hcast]
    ring
  obtain ⟨z,hz⟩ := projection_quotient a R
  have hd : xcoord R a=X+a*C+H*z := by
    rw [hX]
    exact hz
  have hnorm : xcoord R a*xcoord R a=1+(a*a+H)*C*C := by
    have hh := norm R a
    unfold ArithmeticPellRecurrence.delta at hh
    change xcoord R a*xcoord R a=1+(a*a+(4*a+3))*C*C
    convert hh using 1; ring
  have hdR := congrArg (ι : V →+* DiffRing V) hd
  have hnR := congrArg (ι : V →+* DiffRing V) hnorm
  simp only [map_add,map_mul,map_one] at hdR hnR
  have hHcast : (ι H:DiffRing V)=4*ι a+3 := by dsimp [H]; simp only [map_add,map_mul,map_ofNat]
  rw [hHcast] at hdR hnR
  have hu := Direct80UnweightedProjection.unweighted (ι a:DiffRing V) (ι C) (ι (xcoord R a)) (ι X) (ι z) hdR hnR
  have hdiv : (ι H:DiffRing V) ∣ ι K := by
    rw [hKcast]
    rw [hHcast]
    exact hu
  obtain ⟨kap,hkap⟩ := natural_dvd_of_signed H K hdiv
  have hKpos : 0<K := by dsimp [K]; simp
  have hkpos : 0<kap := pos_of_mul_pos_right (by rw [←hkap]; exact hKpos) (by simp)
  exact ⟨kap,hkpos,hkap⟩

#print axioms TenPositiveScaledKappaGeneric.positive_kappa
end TenPositiveScaledKappaGeneric
