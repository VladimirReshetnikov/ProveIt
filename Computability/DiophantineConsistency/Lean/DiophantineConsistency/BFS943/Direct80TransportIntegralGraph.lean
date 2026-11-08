import DiophantineConsistency.BFS943.TransportIntegral
import DiophantineConsistency.BFS943.Direct80GraphUnweighted
import DiophantineConsistency.BFS943.Direct80OffsetExact
import DiophantineConsistency.BFS943.Direct80TransportModel

/-! The exact graph transport has a natural quotient after projection. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80TransportIntegralGraph
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80CarrierIdentity TenPositive80SignedCarrier
open TenPositive80NaturalProjection TenPositive80OffsetExact TenPositive80TransportModel TenPositiveTransportIntegral
open Direct80GraphUnweighted Direct80Kpos
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_integral_transport (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hbeta31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbetaodd : ∃u : V, (p 0:V)=2*u+1) :
    ∃ t : V, (BExpr (integerPorts p)).evalRing (fun j => ι (v j))=ι (b p v*t) := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hbeta31
  obtain ⟨_tau,_f,_V0,_y,z,_ht,_hf,_hV,_hy,_he,_hf2,_hVs,hZ,_hsign,_hzle,_haux⟩ := graph_signed_carrier p v hb hv hz
  let w : Fin 10 → DiffRing V := fun j => ι (v j)
  let h := (hExpr (integerPorts p)).evalRing w
  let u := (muExpr (integerPorts p)).evalRing w
  let m := u*u
  let H := (HExpr (integerPorts p)).evalRing w
  let B := (BExpr (integerPorts p)).evalRing w
  let k := (KExpr (integerPorts p)).evalRing w
  let e := (eExpr (integerPorts p)).evalRing w
  let L := (graph (integerPorts p)).v.evalRing w*(graph (integerPorts p)).v.evalRing w
  let Z := (graph (integerPorts p)).z.evalRing w
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hmu : 0<mu p v := add_pos (mul_pos hq hq) (by simp)
  have hA : 0<A p v := mul_pos (mul_pos hmu hY) (add_pos hX (by simp))
  have h4A : 1≤4*A p v := le_trans (pos_iff_one_le.mp hA) (by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right (by norm_num : (1:V)≤4) (by simp : (0:V)≤A p v))
  have hHcast : (ι (Hnat p v):DiffRing V)=4*ι (A p v)-1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_one (ι : V →+* DiffRing V),←map_add]
    change ι ((4*A p v-1)+1)=4*ι (A p v)
    rw [tsub_add_cancel_of_le h4A,map_mul,map_ofNat]
  have hgap := (graph_positive_gap p v hb hv hz).1
  have hKcast : (ι (3*c p v-2*X p v):DiffRing V)=3*ι (c p v)-2*ι (X p v) := by
    apply eq_sub_iff_add_eq.mpr
    have h2 : (2:DiffRing V)*ι (X p v)=ι (2*X p v) := by rw [map_mul,map_ofNat]
    rw [h2,←map_add]
    change ι ((3*c p v-2*X p v)+2*X p v)=3*ι (c p v)
    rw [tsub_add_cancel_of_le (le_of_lt hgap),map_mul,map_ofNat]
  have hHeval : H=ι (Hnat p v) := by
    rw [hHcast]
    simp only [H,HExpr,muExpr,qExpr,hExpr,w,A,mu,Y,X,q,b,integerPorts,
      Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_sub,Expr.evalRing_constant,
      Expr.evalRing_var,Expr.evalRing_ofNat,Int.cast_natCast,Nat.cast_one,Nat.cast_ofNat,
      map_mul,map_add,map_one,map_natCast]
  have hheval : h=ι (b p v) := by
    simp only [h,hExpr,w,b,integerPorts,Expr.evalRing_mul,Expr.evalRing_constant,
      Expr.evalRing_var,Int.cast_natCast,map_mul,map_natCast]
  have hKeval : k=ι (Knat p v) := by
    simp only [Knat,map_add,map_mul,map_ofNat,hKcast]
    simp only [k,KExpr,w,Expr.evalRing_mul,Expr.evalRing_add,Expr.evalRing_sub,
      Expr.evalRing_var,Expr.evalRing_ofNat,Nat.cast_ofNat,TenPositive80ResidueBinding.c_eval]
    have hx : ((.var 5 : Expr (Fin 10))*qExpr (integerPorts p)).evalRing w=ι (X p v) := by
      simp only [qExpr,hExpr,w,X,q,b,integerPorts,Expr.evalRing_mul,Expr.evalRing_add,
        Expr.evalRing_constant,Expr.evalRing_var,Expr.evalRing_ofNat,Int.cast_natCast,
        Nat.cast_one,map_mul,map_add,map_one,map_natCast]
    simp only [Expr.evalRing_mul,Expr.evalRing_var] at hx
    rw [hx]
  have hueval : u=ι (mu p v) := by
    simp only [u,muExpr,qExpr,hExpr,w,mu,q,b,integerPorts,Expr.evalRing_mul,Expr.evalRing_add,
      Expr.evalRing_constant,Expr.evalRing_var,Expr.evalRing_ofNat,Int.cast_natCast,
      Nat.cast_one,map_mul,map_add,map_one,map_natCast]
  have hmpos : 0<m := by
    dsimp [m]; rw [hueval]
    have hu : (0:DiffRing V)<ι (mu p v) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hmu
    exact mul_pos hu hu
  have hHpos : 0<H := by
    rw [hHeval,hHcast]
    have hA1 : (1:DiffRing V)≤ι (A p v) := by rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact pos_iff_one_le.mp hA
    linarith
  obtain ⟨kappa,hkappa⟩ := graph_unweighted p v hbeta31 hl hh hv hz hbetaodd
  have hK : k=H*ι kappa := by rw [hKeval,hHeval,hkappa,map_mul]
  have hediv := TenPositive80OffsetDivisibility.graph_offset_divisible p v hb hl hh hv hz hbetaodd
  change m∣e at hediv
  obtain ⟨rho,hrho⟩ := hediv
  have hM : (graph (integerPorts p)).m.evalRing w=h*m*H := m_eval (integerPorts p) w
  have hZ' : Z=h*m*H*z := by
    rw [M_eval p v hb hv] at hM
    rw [hM] at hZ
    exact hZ
  have hcar : Z=h*m*(H*(w 7-L*B)+k)-H*(m*B+h*e) := z_eval (integerPorts p) w
  have hdiv : h∣B := transport_divisor h m H L B k e z (w 7) Z (ι kappa) rho
    (ne_of_gt hmpos) (ne_of_gt hHpos) hZ' hK hrho hcar
  have hB : 0≤B := (graph_transport_and_mask p v hb hv hz).1
  obtain ⟨B0,hB0⟩ := nonneg_iff.mp hB
  rw [hheval,hB0] at hdiv
  have hnat : b p v∣B0 := natural_dvd_of_signed (b p v) B0 hdiv
  obtain ⟨t,ht⟩ := hnat
  refine ⟨t,?_⟩
  change B=ι (b p v*t)
  rw [hB0,ht]

#print axioms TenPositive80TransportIntegralGraph.graph_integral_transport
end TenPositive80TransportIntegralGraph
