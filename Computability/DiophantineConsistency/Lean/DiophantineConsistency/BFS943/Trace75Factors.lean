import DiophantineConsistency.BFS943.Trace75RootNonzero

/-! Positive natural representatives for the actual trace75 registers. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace75Factors
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 Trace75RootNonzero
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def b (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := (p 0:V)*v 0
def q (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := b p v+1
def Y (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := (q p v*q p v*q p v)*v 6
def X (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := v 5*q p v
def k (v : Fin 10 → V) : V := v 8+v 9
def c (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := k v*Y p v+v 8
def A (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := X p v*Y p v+Y p v
def delta (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := A p v*(A p v+2)
def U (p : Fin 4 → ℕ) (v : Fin 10 → V) : V := v 3*(c p v*c p v)
def E (p : Fin 4 → ℕ) (v : Fin 10 → V) : V :=
  (X p v*Y p v)*(k v*Y p v)*((X p v*Y p v)*(k v*Y p v)+k v)+1
def M (p : Fin 4 → ℕ) (v : Fin 10 → V) : V :=
  (b p v*(X p v*Y p v))*(4*A p v-1)
def ports (p : Fin 4 → ℕ) : Fin 4 → DiffRing V := fun j => ((p j:ℕ):DiffRing V)

theorem delta_eval (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    (regs (ports p) (fun j => ι (v j))).Delta = ι (delta p v) := by
  simp only [delta,A,Y,X,q,b,ports,regs,map_mul,map_add,map_one,map_natCast,map_ofNat]

theorem U_eval (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    (regs (ports p) (fun j => ι (v j))).U = ι (U p v) := by
  simp only [U,c,k,Y,q,b,ports,regs,map_mul,map_add,map_one,map_natCast]

theorem E_eval (p : Fin 4 → ℕ) (v : Fin 10 → V) :
    (regs (ports p) (fun j => ι (v j))).E = ι (E p v) := by
  simp only [E,k,Y,X,q,b,ports,regs,map_mul,map_add,map_one,map_natCast]

theorem factors_positive (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j) :
    0<delta p v ∧ 0<U p v ∧ 0<E p v ∧ 0<M p v := by
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hx : 0<X p v := mul_pos (hv 5) hq
  have hk : 0<k v := add_pos (hv 8) (hv 9)
  have hc : 0<c p v := add_pos (mul_pos hk hy) (hv 8)
  have hA : 0<A p v := add_pos (mul_pos hx hy) hy
  have hA1 : 1≤A p v := pos_iff_one_le.mp hA
  have h4A : 1<4*A p v := lt_of_lt_of_le (by simp : (1:V)<4)
    (by simpa using mul_le_mul_of_nonneg_left hA1 (by simp : (0:V)≤4))
  have hHp : 0<4*A p v-1 := tsub_pos_iff_lt.mpr h4A
  refine ⟨mul_pos hA (add_pos hA (by simp)),
    mul_pos (hv 3) (mul_pos hc hc),?_,mul_pos (mul_pos hb0 (mul_pos hx hy)) hHp⟩
  dsimp [E]
  simp

theorem M_eval (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j) :
    (regs (ports p) (fun j => ι (v j))).M = ι (M p v) := by
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hy : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hx : 0<X p v := mul_pos (hv 5) hq
  have hA : 0<A p v := add_pos (mul_pos hx hy) hy
  have hA1 : 1≤A p v := pos_iff_one_le.mp hA
  have h4A : 1<4*A p v := lt_of_lt_of_le (by simp : (1:V)<4)
    (by simpa using mul_le_mul_of_nonneg_left hA1 (by simp : (0:V)≤4))
  have hsub : 4*A p v-1+1=4*A p v := tsub_add_cancel_of_le (le_of_lt h4A)
  have hcast : ι (4*A p v-1) = 4*ι (A p v)-1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [← map_one (ι : V →+* DiffRing V), ← map_add, hsub,map_mul,map_ofNat]
  simp only [M,map_mul]
  rw [hcast]
  simp only [A,Y,X,q,b,ports,regs,map_mul,map_add,map_one,map_natCast]

theorem graph_roots (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb : 0<(p 0:V)) (hv : ∀j,0<v j)
    (hz : value75 (ports p) (fun j => ι (v j)) = 0) :
    ∃ tau f : V, 0<tau ∧ 0<f ∧ E p v=tau*tau ∧
      1+delta p v*U p v*U p v*E p v=f*f := by
  obtain ⟨hd,hu,he,hm⟩ := factors_positive p v hb hv
  exact roots_of_positive_representatives (ports p) v (delta p v) (U p v) (E p v) (M p v)
    hd hu he hm (delta_eval p v) (U_eval p v) (E_eval p v) (M_eval p v hb hv) hz

#print axioms Trace75Factors.graph_roots
end Trace75Factors
