import DiophantineConsistency.FractionalBooleanWindows
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ParityAdjacentPhase
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord ArithmeticStandardCasts
open CleanGeometry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def badNat (x : ℕ) : Prop := x=1063 ∨ x=1064

theorem nat_choice (d : ℕ) (hd : d<8807) :
    ¬badNat ((2194+8807-d)%8807) ∨ ¬badNat ((3295+8807-d)%8807) := by
  unfold badNat
  omega

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

theorem choose_two_ordinary (N D : V) (hN : 0<N) :
    let a := (cyc (8807*N) 2194 D)%8807
    let b := (cyc (8807*N) 3295 D)%8807
    (a≠1063 ∧ a≠1064) ∨ (b≠1063 ∧ b≠1064) := by
  have hdlt : D%8807<8807 := mod_lt _ (by norm_num)
  obtain ⟨d,hd,hdv⟩ := bounded_standard 8807 (D%8807) hdlt
  have h1 := CyclicAnyPhase.cyc_period 8807 N 2194 D (by norm_num) hN
  have h2 := CyclicAnyPhase.cyc_period 8807 N 3295 D (by norm_num) hN
  rw [mod_eq_self_of_lt (by norm_num : (2194:V)<8807)] at h1
  rw [mod_eq_self_of_lt (by norm_num : (3295:V)<8807)] at h2
  rw [←cyc_mod 8807 2194 D (by norm_num), ←cyc_mod 8807 3295 D (by norm_num), hdv] at h1 h2
  have hc1 : cyc (8807:V) 2194 (d:V)=(((2194+8807-d)%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat,Nat.mod_eq_of_lt hd] using (cyc_cast (V:=V) 2194 d)
  have hc2 : cyc (8807:V) 3295 (d:V)=(((3295+8807-d)%8807:ℕ):V) := by
    simpa only [Nat.cast_ofNat,Nat.mod_eq_of_lt hd] using (cyc_cast (V:=V) 3295 d)
  rw [hc1] at h1
  rw [hc2] at h2
  have h := nat_choice d hd
  rcases h with h | h
  · left
    constructor <;> intro he <;> apply h <;> unfold badNat
    · left; exact_mod_cast (h1.symm.trans he)
    · right; exact_mod_cast (h1.symm.trans he)
  · right
    constructor <;> intro he <;> apply h <;> unfold badNat
    · left; exact_mod_cast (h2.symm.trans he)
    · right; exact_mod_cast (h2.symm.trans he)
#print axioms ParityAdjacentPhase.nat_choice
#print axioms ParityAdjacentPhase.choose_two_ordinary
end ParityAdjacentPhase
