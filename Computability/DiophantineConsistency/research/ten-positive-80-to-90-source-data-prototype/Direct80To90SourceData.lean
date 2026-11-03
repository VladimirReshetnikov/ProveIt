import Direct80FreshFirstCoordinate
import Direct90FirstFactor
import Direct90MainFactor

/-! A positive 80 zero yields a positive valuation zeroing the 90 main factor. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80To90SourceData
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open ArithmeticPellRecurrence
open CompactFixedBeta CompactSymbolicPorts
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank
open TenPositive80FreshFirstCoordinate TenPositive80NaturalTransport TenPositive80SymbolicPortBounds
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def valuation (v : Fin 10 → V) (eta zeta direct t T n s : V) : Fin 12 → V :=
  ![v 0,v 1,v 2,t,T,v 5,v 6,s,eta,zeta,n,direct]

theorem graph_source_data (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ r eta zeta gamma h s : V, 0 < r ∧ 0 < eta ∧ 0 < zeta ∧ 0 < gamma ∧ 0 < s ∧
      rankNat p v=2*r+1 ∧
      (let K:=2*ycoord (r+1) (2*(X p v*Y p v*Y p v-1)+1)
       let C:=ycoord (2*r+1) (Y p v*(X p v+1))
       C=K*Y p v+eta ∧ K=eta+zeta) ∧
      ∀ t0 T n : V, 0 < t0 → 0 < T → 0 < n →
      (∀j,0<valuation v eta zeta (gamma+h) t0 T n s j) ∧
      ((FreeJDirectMainGraph.graph (integerPorts p)).first).evalRing
        (fun j => ι (valuation v eta zeta (gamma+h) t0 T n s j))=0 ∧
      ((FreeJDirectMainGraph.graph (integerPorts p)).main).evalRing
        (fun j => ι (valuation v eta zeta (gamma+h) t0 T n s j))=0 := by
  obtain ⟨r,eta,zeta,gamma,h,t,s,tau,hr,heta,hzeta,hgamma,ht,hs,htau,hR,
    hC,hK,hproj,hoff,htransport,htauEq,hfirstnorm,hcoord⟩ :=
    graph_fresh_first_coordinate p v hp0 hp2 hp3 hv hz
  obtain ⟨h31,_hl,_hh,_hodd⟩ := fixed_bounds (V:=V) p hp0 hp2 hp3
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num) h31
  let a:=Y p v*(X p v+1)
  let K:=2*ycoord (r+1) (2*(X p v*Y p v*Y p v-1)+1)
  let C:=ycoord (2*r+1) a
  let d:=xcoord (2*r+1) a
  have hnorm : d*d=1+(a*a+(4*a+3))*C*C := by
    have h := norm (2*r+1) a
    unfold ArithmeticPellRecurrence.delta at h
    convert h using 1; ring
  have hnat := (graph_natural_rank p v hb hv hz).1
  have hRank :
      (ι (rankNat p v):DiffRing V)=
        (ι (v 2)+(1+ι (v 0)*ι (p 0:V)-ι (v 1))*(ι (v 0)*ι (p 0:V)))*
          ((1+ι (v 0)*ι (p 0:V))*(1+ι (v 0)*ι (p 0:V))-1)+
            ι (v 0)*(ι (p 2:V)+ι (p 3:V)*(1+ι (v 0)*ι (p 0:V))) := by
    rw [←hnat]
    simp only [TenPositive80ResidueBinding.rExpr,integerPorts,Expr.evalRing_mul,
      Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_var,Expr.evalRing_constant,
      Expr.evalRing_ofNat,Int.cast_natCast,Nat.cast_one,map_natCast]
    ring
  have hqcast : (1+ι (v 0)*(p 0:DiffRing V))=ι (q p v) := by
    simp only [q,b,map_add,map_mul,map_one,map_natCast]
    ring
  have hYcast : (ι (q p v):DiffRing V)*(ι (q p v)*ι (q p v))*ι (v 6)=ι (Y p v) := by
    simp only [Y,map_mul]
    ring
  have hXcast : (ι (q p v):DiffRing V)*ι (v 5)=ι (X p v) := by
    simp only [X,map_mul]
    ring
  have hCcast : (ι C:DiffRing V)=ι eta+ι (Y p v)*(ι eta+ι zeta) := by
    change (ι (ycoord (2*r+1) (Y p v*(X p v+1))):DiffRing V)=_
    rw [hC,hK]
    simp only [map_add,map_mul]
    ring
  have hacast : (ι a:DiffRing V)=ι (X p v)*ι (Y p v)+ι (Y p v) := by
    dsimp [a]
    simp only [map_mul,map_add,map_one]
    ring
  have hbcast : (ι (v 0)*(p 0:DiffRing V))=ι (b p v) := by
    simp only [b,map_mul,map_natCast]
    ring
  have hmask := (graph_natural_rank p v hb hv hz).2.2
  have hFle : v 1≤q p v := le_trans (by simp) (le_of_lt hmask)
  have hAle : v 2≤q p v-v 1 := by
    apply (le_tsub_iff_right hFle).mpr
    change v 2+v 1≤q p v
    rw [add_comm]
    exact le_of_lt hmask
  have hsub {x y : V} (hy : y≤x) : (ι (x-y):DiffRing V)=ι x-ι y := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add,tsub_add_cancel_of_le hy]
  have hMaskCast : (ι (Cnat p v):DiffRing V)=ι (q p v)-ι (v 1)-ι (v 2) := by
    dsimp [Cnat]
    rw [hsub hAle,hsub hFle]
  have htransCast : (ι (Cnat p v):DiffRing V)*((p 1:DiffRing V)+ι (v 5))-ι (v 1)=ι (b p v)*ι t := by
    have he := congrArg (ι : V →+* DiffRing V) htransport
    simp only [map_add,map_mul,map_natCast] at he
    linear_combination he
  have hcNat : tau+q p v*t*(b p v*(eta+zeta)+1)=
      (X p v*Y p v*Y p v)*(eta+zeta)+(eta+zeta)+s+v 6 := by
    rw [←hK]
    exact hcoord
  have hnNat : tau*tau=1+(X p v*Y p v*Y p v)*
      ((X p v*Y p v*Y p v)+1)*(eta+zeta)*(eta+zeta) := by
    rw [←hK]
    exact hfirstnorm
  refine ⟨r,eta,zeta,gamma,h,s,hr,heta,hzeta,hgamma,hs,hR,⟨hC,hK⟩,?_⟩
  intro t0 T n ht0 hT hn
  constructor
  · intro j
    fin_cases j <;> simp [valuation,hv,heta,hzeta,hgamma,ht0,hT,hn,hs]
  · constructor
    · rw [TenPositive90FirstFactor.first_recipe]
      simp [valuation,integerPorts]
      rw [hqcast,hYcast,hXcast,hbcast,←hMaskCast,htransCast]
      have hc := congrArg (ι : V →+* DiffRing V) hcNat
      simp only [map_add,map_mul,map_one] at hc
      have hn := congrArg (ι : V →+* DiffRing V) hnNat
      simp only [map_add,map_mul,map_one] at hn
      exact TenPositive90FirstFactor.residual_zero (ι (b p v)) (ι (q p v))
        (ι (X p v)) (ι (Y p v)) (ι eta+ι zeta) (ι (v 6)) (ι s) (ι t) (ι tau) hc hn
    · apply TenPositive90MainFactor.main_zero (integerPorts p)
        (fun j => ι (valuation v eta zeta (gamma+h) t0 T n s j)) (ι gamma) (ι h) (ι d)
      · simp [valuation]
      · dsimp only
        simp [valuation,integerPorts]
        simp only [map_natCast] at hRank
        rw [←hRank,hqcast,hYcast]
        have he := congrArg (ι : V →+* DiffRing V) (hK.symm.trans hoff)
        simp only [map_add,map_mul,map_one] at he
        exact he
      · simp [valuation,integerPorts]
        rw [hqcast,hYcast,hXcast,←hCcast,←hacast]
        have heNat : d=X p v+a*C+(4*a+3)*gamma := hproj
        have he := congrArg (ι : V →+* DiffRing V) heNat
        simp only [map_add,map_mul,map_ofNat] at he
        exact he
      · simp [valuation,integerPorts]
        rw [hqcast,hYcast,hXcast,←hCcast,←hacast]
        have he := congrArg (ι : V →+* DiffRing V) hnorm
        simp only [map_mul,map_add,map_one,map_ofNat] at he
        exact he
#print axioms TenPositive80To90SourceData.graph_source_data
end TenPositive80To90SourceData
