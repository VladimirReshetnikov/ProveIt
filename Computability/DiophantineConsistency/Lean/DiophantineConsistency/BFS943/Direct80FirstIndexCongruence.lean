import DiophantineConsistency.BFS943.Direct80OffsetDivisibility

/-! The signed carrier offset yields a natural congruence. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace TenPositive80FirstIndexCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ModelDifferenceRing
open TenPositive80Graph TenPositive80Factors TenPositive80ResidueBinding TenPositive80CarrierIdentity
open TenPositive80NaturalRank TenPositive80OffsetDivisibility
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem mod_eq_of_signed_dvd (m x y : V) (hm : 0<m)
    (hd : (ι m : DiffRing V)∣ι x-ι y) : x%m=y%m := by
  obtain ⟨t,ht⟩ := hd
  rcases nonneg_or_nonpos t with ⟨a,ha⟩|⟨a,ha⟩
  · have he : x=y+m*a := by
      apply ι_injective
      calc
        (ι x:DiffRing V)=((ι x:DiffRing V)-ι y)+ι y := by ring
        _=ι m*ι a+ι y := by rw [ht,ha]
        _=ι (y+m*a) := by rw [map_add,map_mul]; ring
    rw [he,mod_add_mul' _ _ hm]
  · have he : x+m*a=y := by
      apply ι_injective
      calc
        (ι (x+m*a):DiffRing V)=ι x+ι m*ι a := by rw [map_add,map_mul]
        _=((ι x:DiffRing V)-ι y)+ι y+ι m*ι a := by ring
        _=ι m*(-ι a)+ι y+ι m*ι a := by rw [ht,ha]
        _=ι y := by ring
    have h := congrArg (fun z : V => z%m) he
    rwa [mod_add_mul' _ _ hm] at h

theorem graph_first_index_congruence (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v)
    (hbeta : ∃u : V, (p 0:V)=2*u+1) :
    k v%(mu p v*mu p v)=(rankNat p v+1)%(mu p v*mu p v) := by
  let w : Fin 10 → DiffRing V := fun j => ι (v j)
  let m : V := mu p v*mu p v
  have hq : 0<q p v := add_pos (mul_pos hb (hv 0)) (by simp)
  have hmu : 0<mu p v := add_pos (mul_pos hq hq) (by simp)
  have hm : 0<m := mul_pos hmu hmu
  have hnat := (graph_natural_rank p v hb hv hz).1
  have heval : (eExpr (integerPorts p)).evalRing w=ι (k v)-ι (rankNat p v+1) := by
    dsimp [eExpr,w,k]
    simp only [Expr.evalRing_ofNat,Nat.cast_one,map_add,map_one]
    rw [hnat]
    ring
  have hmuval : (muExpr (integerPorts p)).evalRing w=ι (mu p v) := by
    simp only [muExpr,qExpr,hExpr,w,mu,q,b,integerPorts,Expr.evalRing_mul,Expr.evalRing_add,
      Expr.evalRing_constant,Expr.evalRing_var,Expr.evalRing_ofNat,Int.cast_natCast,
      Nat.cast_one,map_mul,map_add,map_one,map_natCast]
  have hd := graph_offset_divisible p v hb hl hh hv hz hbeta
  change (muExpr (integerPorts p)).evalRing w*(muExpr (integerPorts p)).evalRing w∣
    (eExpr (integerPorts p)).evalRing w at hd
  rw [hmuval,←map_mul,heval] at hd
  exact mod_eq_of_signed_dvd m (k v) (rankNat p v+1) hm hd

#print axioms TenPositive80FirstIndexCongruence.graph_first_index_congruence
end TenPositive80FirstIndexCongruence
