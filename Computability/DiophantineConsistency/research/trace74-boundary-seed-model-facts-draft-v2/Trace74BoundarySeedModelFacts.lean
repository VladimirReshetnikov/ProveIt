import Trace74BoundarySeedSpecialization
import DiophantineConsistency.ArithmeticStandardCasts

/-! UNCHECKED DRAFT. Proposed cast-based discharges for the explicit model
hypotheses of the conditional finite-seed theorem. No zero is asserted here. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace Trace74BoundarySeedModelFacts
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing
open Trace75Factors Trace74BoundarySeedParametric
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def WNat : ℕ := 2^30
def W : V := (WNat:V)
def S : V := (Trace74BoundaryNaturalSeed.S:V)

theorem model_facts :
    0<W (V:=V) ∧ 0<S (V:=V) ∧
    X ports31 (source31 (W (V:=V)) (S (V:=V))) = (Trace74BoundaryNaturalSeed.X:V) ∧
    Y ports31 (source31 (W (V:=V)) (S (V:=V))) = (Trace74BoundaryNaturalSeed.Y:V) ∧
    ((2*(Trace74BoundaryNaturalSeed.X*Trace74BoundaryNaturalSeed.Y*Trace74BoundaryNaturalSeed.Y-1)+1 : ℕ):V) =
      2*((Trace74BoundaryNaturalSeed.X:V)*(Trace74BoundaryNaturalSeed.Y:V)*(Trace74BoundaryNaturalSeed.Y:V)-1)+1 ∧
    (2*(15:V)+1)%4=3 ∧
    X ports31 (source31 (W (V:=V)) (S (V:=V)))=Exp.exp (2*(15:V)+1) ∧
    72*(15:V)<X ports31 (source31 (W (V:=V)) (S (V:=V)))+1 := by
  have hWNat : 0<WNat := by decide
  have hSNat : 0<Trace74BoundaryNaturalSeed.S := by decide
  have hXNat : 0<Trace74BoundaryNaturalSeed.X := by decide
  have hYNat : 0<Trace74BoundaryNaturalSeed.Y := by
    exact mul_pos (by decide) hSNat
  have hle : 1≤Trace74BoundaryNaturalSeed.X*Trace74BoundaryNaturalSeed.Y*Trace74BoundaryNaturalSeed.Y :=
    Nat.succ_le_of_lt (mul_pos (mul_pos hXNat hYNat) hYNat)
  have hdouble : WNat*2=Trace74BoundaryNaturalSeed.X := by decide
  have hW : 0<W (V:=V) := Nat.cast_pos.mpr hWNat
  have hS : 0<S (V:=V) := Nat.cast_pos.mpr hSNat
  have hX : X ports31 (source31 (W (V:=V)) (S (V:=V))) = (Trace74BoundaryNaturalSeed.X:V) := by
    have hcast := congrArg (fun n : ℕ => (n:V)) hdouble
    simp only [Nat.cast_mul, Nat.cast_ofNat] at hcast
    have htwo : (1:V)+1=2 := by norm_num
    simpa [X,q,b,ports31,source31,W,htwo] using hcast
  have hY : Y ports31 (source31 (W (V:=V)) (S (V:=V))) = (Trace74BoundaryNaturalSeed.Y:V) := by
    have htwo : (1:V)+1=2 := by norm_num
    have height : (2:V)*2*2=8 := by norm_num
    simp [Y,q,b,ports31,source31,S,Trace74BoundaryNaturalSeed.Y,Nat.cast_mul,htwo,height]
  have hbase : ((2*(Trace74BoundaryNaturalSeed.X*Trace74BoundaryNaturalSeed.Y*Trace74BoundaryNaturalSeed.Y-1)+1 : ℕ):V) =
      2*((Trace74BoundaryNaturalSeed.X:V)*(Trace74BoundaryNaturalSeed.Y:V)*(Trace74BoundaryNaturalSeed.Y:V)-1)+1 := by
    have hsum : ((Trace74BoundaryNaturalSeed.X*Trace74BoundaryNaturalSeed.Y*Trace74BoundaryNaturalSeed.Y-1:ℕ):V)+1 =
        ((Trace74BoundaryNaturalSeed.X*Trace74BoundaryNaturalSeed.Y*Trace74BoundaryNaturalSeed.Y:ℕ):V) := by
      exact_mod_cast Nat.sub_add_cancel hle
    have hsub : ((Trace74BoundaryNaturalSeed.X*Trace74BoundaryNaturalSeed.Y*Trace74BoundaryNaturalSeed.Y-1:ℕ):V) =
        ((Trace74BoundaryNaturalSeed.X*Trace74BoundaryNaturalSeed.Y*Trace74BoundaryNaturalSeed.Y:ℕ):V)-1 :=
      eq_tsub_of_add_eq hsum
    simp only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one,hsub]
  have h31 : 2*(15:V)+1=31 := by ring
  have hpNat : (31:ℕ)%4=3 := by decide
  have hpV := congrArg (fun n : ℕ => (n:V)) hpNat
  have hphase : (2*(15:V)+1)%4=3 := by
    rw [h31]
    simpa only [ArithmeticStandardCasts.cast_mod,Nat.cast_ofNat] using hpV
  have exp_cast (n : ℕ) : Exp.exp (n:V) = (2:V)^n := by
    induction n with
    | zero => rw [Nat.cast_zero,exp_zero,pow_zero]
    | succ n ih => rw [Nat.cast_succ,exp_succ,ih,pow_succ,mul_comm]
  have hExp : Exp.exp (31:V)=(Trace74BoundaryNaturalSeed.X:V) := by
    have he := exp_cast 31
    simpa only [Nat.cast_ofNat,Nat.cast_pow,Trace74BoundaryNaturalSeed.X] using he
  have hXeq : X ports31 (source31 (W (V:=V)) (S (V:=V)))=Exp.exp (2*(15:V)+1) := by
    rw [hX,h31,hExp]
  have hgNat : (72*15:ℕ)<Trace74BoundaryNaturalSeed.X+1 := by decide
  have hgV := (Nat.cast_lt.mpr hgNat : ((72*15:ℕ):V)<((Trace74BoundaryNaturalSeed.X+1:ℕ):V))
  have h72 : 72*(15:V)<X ports31 (source31 (W (V:=V)) (S (V:=V)))+1 := by
    rw [hX]
    simpa only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat,Nat.cast_one] using hgV
  exact ⟨hW,hS,hX,hY,hbase,hphase,hXeq,h72⟩

#print axioms Trace74BoundarySeedModelFacts.model_facts
end Trace74BoundarySeedModelFacts
