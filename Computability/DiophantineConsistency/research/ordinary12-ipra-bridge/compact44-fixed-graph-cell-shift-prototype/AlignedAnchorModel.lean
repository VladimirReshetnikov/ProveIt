import DiophantineConsistency.AlignedTemporalAnchor
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace AlignedAnchorModel
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticStandardCasts
open CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem cast_sub (a b : ℕ) (h : b≤a) : ((a-b:ℕ):V)=(a:V)-(b:V) := by
  apply eq_tsub_of_add_eq
  exact_mod_cast (Nat.sub_add_cancel h)
private theorem cyc_cast (t q : ℕ) :
    cyc (8807:V) (t:V) (q:V) = (((t+8807-q%8807)%8807:ℕ):V) := by
  have hle : q%8807≤t+8807 := by have := Nat.mod_lt q (by omega : 0<8807); omega
  have hc : ((t+8807-q%8807:ℕ):V)=(t:V)+8807-((q%8807:ℕ):V) := by
    rw [cast_sub _ _ hle, Nat.cast_add]; simp only [Nat.cast_ofNat]
  have hm : (q:V)%8807 = ((q%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat] using (cast_mod (V:=V) q 8807).symm
  unfold cyc
  rw [hm, ←hc]
  simpa only [Nat.cast_ofNat] using (cast_mod (V:=V) (t+8807-q%8807) 8807).symm

theorem model_zero (D : V) (h1 : Bad (cyc 8807 2195 D)) (h2 : Bad (cyc 8807 3296 D)) :
    D%8807=0 := by
  have hdlt : D%8807<8807 := mod_lt _ (by norm_num)
  obtain ⟨d,hd,hdv⟩ := bounded_standard 8807 (D%8807) hdlt
  rw [←cyc_mod 8807 2195 D (by norm_num), hdv] at h1
  rw [←cyc_mod 8807 3296 D (by norm_num), hdv] at h2
  have hc1 : cyc (8807:V) 2195 (d:V)=(((2195+8807-d)%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat,Nat.mod_eq_of_lt hd] using (cyc_cast (V:=V) 2195 d)
  have hc2 : cyc (8807:V) 3296 (d:V)=(((3296+8807-d)%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat,Nat.mod_eq_of_lt hd] using (cyc_cast (V:=V) 3296 d)
  rw [hc1,bad_cast] at h1
  rw [hc2,bad_cast] at h2
  have hz := AlignedAnchorPhase.nat_zero d hd h1 h2
  simpa only [hz,Nat.cast_zero] using hdv
#print axioms AlignedAnchorModel.model_zero
end AlignedAnchorModel
