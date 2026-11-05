import FreeMainFirstOrdinateUnique
import FreeMainFirstIndexExtraction
import FreeMainConditionalRank

/-! Unchecked draft: actual positive 72 zeros at common X,Y,c have the same k. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainActualFirstOrdinateUnique
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011 ArithmeticPellRecurrence
open FreeMainConditionalRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem same_k (p : Fin 4 → ℕ) (v w : Fin 14 → V)
    (hv : ∀ i,0<v i) (hw : ∀ i,0<w i)
    (hzv : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v)
    (hzw : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output w)
    (hX : v 8*qval p v=w 8*qval p w)
    (hY : yval p v=yval p w)
    (hc : cval p v=cval p w) : v 10+v 11=w 10+w 11 := by
  let q : V := qval p v
  let Y : V := yval p v
  let X : V := v 8*q
  let P : V := (X*Y)*Y
  let B : V := 2*(P-1)+1
  let k : V := v 10+v 11
  let k' : V := w 10+w 11
  let c : V := cval p v
  have hq : 0<q := by dsimp [q,qval]; simp
  have hYpos : 0<Y := by dsimp [Y,yval]; exact mul_pos (mul_pos (mul_pos hq hq) hq) (hv 7)
  have hY1 : 1≤Y := pos_iff_one_le.mp hYpos
  obtain ⟨n,_,_,hny⟩ := FreeMainFirstIndexExtraction.first_index p v hv hzv
  change 2*ycoord n B=k at hny
  obtain ⟨n',_,_,hny'⟩ := FreeMainFirstIndexExtraction.first_index p w hw hzw
  change 2*ycoord n' (2*((w 8*qval p w*yval p w)*yval p w-1)+1)=k' at hny'
  rw [←hX,←hY] at hny'
  change 2*ycoord n' B=k' at hny'
  have hcv : c=k*Y+v 10 := rfl
  have hcw : c=k'*Y+w 10 := by
    change (v 10+v 11)*yval p v+v 10=(w 10+w 11)*yval p w+w 10 at hc
    rw [←hY] at hc
    exact hc
  have hkv : v 10<k := lt_add_of_pos_right _ (hv 11)
  have hkw : w 10<k' := lt_add_of_pos_right _ (hw 11)
  have h := FreeMainFirstOrdinateUnique.first_index_unique B Y c k k' (v 10) (w 10) n n'
    hY1 (hv 10) hkv (hw 10) hkw hcv hcw hny.symm hny'.symm
  exact h.2

#print axioms same_k
end FreeMainActualFirstOrdinateUnique
