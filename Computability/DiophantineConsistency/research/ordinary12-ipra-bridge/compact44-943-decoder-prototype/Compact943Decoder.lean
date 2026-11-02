import DiophantineConsistency.Compact943Data
import DiophantineConsistency.CompactTilePayload
import DiophantineConsistency.CompactDecoderIff
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Compact943Decoder
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic BigOperators
open DiophantineConsistency.ArithmeticBinaryCarry
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def tileValue (i : Fin 943) : V :=
  CompactTilePayload.value ((Compact943Data.row i).1:V) ((Compact943Data.row i).2.1:V)
    ((Compact943Data.row i).2.2.1:V) ((Compact943Data.row i).2.2.2:V)

theorem tileValue_bounds (i : Fin 943) : 0<tileValue (V:=V) i ∧ tileValue (V:=V) i<Exp.exp 41 := by
  obtain ⟨hw,hn,he,hs⟩ := Compact943Data.row_bounds i
  have hw' : ((Compact943Data.row i).1:V)<256 := by exact_mod_cast hw
  have hn' : ((Compact943Data.row i).2.1:V)<512 := by exact_mod_cast hn
  have he' : ((Compact943Data.row i).2.2.1:V)<256 := by exact_mod_cast he
  have hs' : ((Compact943Data.row i).2.2.2:V)<512 := by exact_mod_cast hs
  exact CompactTilePayload.value_bounds _ _ _ _ hw' hn' he' hs'

private theorem exp_nat_cast (n : ℕ) : Exp.exp (n:V)=(2:V)^n := by
  induction n with
  | zero => simp
  | succ n ih => rw [Nat.cast_add,Nat.cast_one,exp_succ,ih,pow_succ,mul_comm]

theorem count_bound (f : Fin 943 → V) (hf : ∀ i,f i≤1) : (∑ i,f i)<Exp.exp 10 := by
  have hsum : (∑ i,f i)≤(943:V) := calc
    _≤∑ _i : Fin 943, (1:V) := Finset.sum_le_sum (fun i _ => hf i)
    _=943 := by simp
  have hexp : Exp.exp (10:V)=1024 := by
    have he := exp_nat_cast (V:=V) 10
    norm_num only [Nat.cast_ofNat] at he
    rw [he]
  rw [hexp]
  exact lt_of_le_of_lt hsum (by norm_num)

theorem decode_iff (f : Fin 943 → V) (W : V) (hf : ∀ i,f i≤1) (hW : W<Exp.exp 41) :
    NoCarry ((∑ i,f i)+Exp.exp 10*((∑ i,(Exp.exp 41-tileValue (V:=V) i)*f i)+W)) (Exp.exp 51-2) ↔
    ((∀ i,f i=0) ∧ W=0) ∨ ∃ i,CompactSelectorSum.Selected f i ∧ W=tileValue (V:=V) i :=
  CompactDecoderIff.decode_iff f tileValue W (count_bound f hf) hW tileValue_bounds
end Compact943Decoder
#print axioms Compact943Decoder.tileValue_bounds
#print axioms Compact943Decoder.count_bound
#print axioms Compact943Decoder.decode_iff
