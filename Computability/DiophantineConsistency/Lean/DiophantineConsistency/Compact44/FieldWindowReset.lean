import DiophantineConsistency.Compact44.FieldHighModel
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace FieldWindowReset
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency ArithmeticWindowDigits ArithmeticCyclicWord CompactHeterogeneousCarry CompactBitRotation
variable {V ι : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [Fintype ι]

theorem reset (N C E F k : V) (t : ℕ) (a e : ι→V)
    (hN : 0<N) (hk : k<8807*N) (hC : C<Exp.exp (67*(8807*N)))
    (haligned : E%67=0) (hcell : ((E/67)%(8807*N))%8807=0)
    (ht0 : 1≤t) (htmax : t<8807) (htspecial : t-1≠1063)
    (hp : k%8807=(t:V))
    (hbool : ∀ j<8807*N, j%8807≠1063 → dig 67 C j≤1)
    (hcarry : CarryInput 67 (8807*N) F 1 (GenericBandCarryFamily.cap (ι:=ι))
      (GenericBandCarryFamily.coefficient a) (GenericBandCarryFamily.word (8807*N) C e (temporalWord (8807*N) E C)))
    (hroom : (∑ j, a j*3)+1<Exp.exp 66) :
    dig 67 (temporalWord (8807*N) E C) (cyc (8807*N) k 1)≤1 ∧
      carry 67 (8807*N) (GenericBandCarryFamily.coefficient a)
        (GenericBandCarryFamily.word (8807*N) C e (temporalWord (8807*N) E C)) (cyc (8807*N) k 1)=0 := by
  let n : V := 8807*N
  let D : V := (E/67)%n
  let kp : V := cyc n k 1
  let src : V := cyc n kp D
  have hn : 0<n := mul_pos (by norm_num) hN
  have hkpl : kp<n := cyc_lt hn _ _
  have hsrc : src<n := cyc_lt hn _ _
  have hpredphase : kp%8807=((t-1:ℕ):V) := by
    dsimp only [kp]
    rw [CyclicAnyPhase.cyc_period 8807 N k 1 (by norm_num) hN,hp]
    have htv : (t:V)<8807 := by exact_mod_cast htmax
    have htone : (1:V)≤(t:V) := by exact_mod_cast ht0
    rw [cyc_of_le htv (by norm_num) htone]
    have hs : (((t-1:ℕ):V)+1)=(t:V) := by exact_mod_cast (Nat.sub_add_cancel ht0)
    exact (eq_tsub_of_add_eq hs).symm
  have hsrcphase : src%8807=((t-1:ℕ):V) := by
    dsimp only [src]
    rw [WholeBlockPhase.shift_phase N kp D hN hcell,hpredphase]
  have hspecial : src%8807≠1063 := by
    rw [hsrcphase]
    intro he
    have hn : t-1=1063 := by exact_mod_cast he
    exact htspecial hn
  have hpred : dig 67 (temporalWord n E C) kp≤1 := by
    rw [AlignedTemporalAnchor.digit C n E kp hn hkpl hC haligned]
    exact hbool src hsrc hspecial
  have h1 : (1:V)≤Exp.exp 66 := one_le_exp _
  have hreset := (TemporalCarryReset.clean n C (temporalWord n E C) F a e hcarry k hk hroom (le_trans hpred h1)).1
  exact ⟨hpred,hreset⟩
#print axioms FieldWindowReset.reset
end FieldWindowReset
