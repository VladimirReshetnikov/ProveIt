import DiophantineConsistency.FieldWindowGeometry
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FieldExactZero
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticBinaryCarry ArithmeticStandardCasts CompactSymbolicPorts
open FieldWindowGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_sub (a b : ℕ) (h : b≤a) : ((a-b:ℕ):V)=(a:V)-(b:V) := by
  apply eq_tsub_of_add_eq
  exact_mod_cast (Nat.sub_add_cancel h)
private theorem cyc_cast (t q : ℕ) :
    cyc (8807:V) (t:V) (q:V) = ((phase t q:ℕ):V) := by
  have hle : q%8807≤t+8807 := by have := Nat.mod_lt q (by omega : 0<8807); omega
  have hc : ((t+8807-q%8807:ℕ):V)=(t:V)+8807-((q%8807:ℕ):V) := by
    rw [cast_sub _ _ hle, Nat.cast_add]; simp only [Nat.cast_ofNat]
  have hm : (q:V)%8807 = ((q%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cast_mod (V:=V) q 8807).symm
  unfold cyc phase
  rw [hm, ←hc]
  simpa only [Nat.cast_ofNat] using (cast_mod (V:=V) (t+8807-q%8807) 8807).symm

theorem source_zero (N C x : V) (j : ℕ) (hx : x<8807*N) (hj : j<8807)
    (hphase : x%8807=(j:V)) (ha : absent j)
    (hslots : ∀ k<8807*N, 0<k → NoCarry (dig 67 C k) (dig 67 (lowNat:V) (k%8807))) :
    dig 67 C x=0 := by
  have hj0 : j≠0 := by
    intro he
    subst j
    have hz : (0:ℕ)∈CompactConcreteMask.support := by decide
    exact ha.1 hz
  have hx0 : 0<x := by
    by_contra hn
    have he : x=0 := nonpos_iff_eq_zero.mp (not_lt.mp hn)
    rw [he,zero_mod] at hphase
    have hjz : j=0 := by exact_mod_cast hphase.symm
    exact hj0 hjz
  have hm := CleanMaskClasses.absent_mask_digit j hj ha.1 ha.2
  have hh := hslots x hx hx0
  rw [hphase,hm] at hh
  exact CompactDummyBound.forbidden_zero _ (dig_lt 67 C x) hh

theorem rotated_zero (N C k : V) (t off : ℕ) (hN : 0<N) (hk : k<8807*N)
    (hC : C<Exp.exp (67*(8807*N))) (hp : k%8807=(t:V)) (ha : absent (phase t off))
    (hslots : ∀ x<8807*N, 0<x → NoCarry (dig 67 C x) (dig 67 (lowNat:V) (x%8807))) :
    dig 67 (rot 67 (8807*N) C ((off:V)%(8807*N))) k=0 := by
  have hn : 0<(8807:V)*N := mul_pos (by norm_num) hN
  rw [dig_rot 67 (8807*N) C _ k (mod_lt _ hn) hk hC,cyc_mod _ _ _ hn]
  apply source_zero N C _ (phase t off) (cyc_lt hn _ _) (by unfold phase; exact Nat.mod_lt _ (by norm_num)) _ ha hslots
  rw [CyclicAnyPhase.cyc_period 8807 N k (off:V) (by norm_num) hN,hp]
  exact cyc_cast t off
#print axioms FieldExactZero.source_zero
#print axioms FieldExactZero.rotated_zero
end FieldExactZero
