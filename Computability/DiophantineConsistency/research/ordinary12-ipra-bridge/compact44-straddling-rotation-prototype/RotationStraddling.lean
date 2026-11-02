import DiophantineConsistency.RotationAdjacent
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
noncomputable section
namespace RotationStraddling
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticWindowDigits DiophantineConsistency.ArithmeticCyclicWord
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem mod_low_high (Q v A B : V) (hA : 0<A) (hB : 0<B) (hv : v<A) :
    (Q*A+v) % (A*B) = (Q%B)*A+v := by
  rw [mod_mul_split _ _ _ hA hB, mod_mul_add_of_lt _ _ hv, div_mul_add _ _ hv]
  rw [add_comm]

theorem straddling (X L e k a t : V)
    (ha : a<67) (he : e=67*k+a) (hL : L=e+((67-a)+t))
    (hX : X<Exp.exp L) :
    dig 67 (rot 1 L X e) k =
      (X % Exp.exp (67-a))*Exp.exp a +
      (X / Exp.exp (L-e+67*k)) % Exp.exp a := by
  let P := Exp.exp (67*k)
  let A := Exp.exp a
  let B := Exp.exp (67-a)
  let H := X / Exp.exp (L-e)
  let Q := X % Exp.exp (L-e)
  have hcut : L-e=(67-a)+t := by rw [hL, add_tsub_cancel_left]
  have hfull : Exp.exp 67=A*B := by
    dsimp [A,B]
    rw [← exp_add, add_tsub_cancel_of_le (le_of_lt ha)]
  have hp : Exp.exp e=P*A := by dsimp [P,A]; rw [he, exp_add]
  have hhigh : H<Exp.exp e := by
    dsimp [H]
    apply div_lt_of_lt_mul
    rw [mul_comm, ← exp_add, tsub_add_cancel_of_le]
    · exact hX
    · rw [hL]; exact le_add_of_nonneg_right (by simp)
  have hlow : H/P<A := by
    apply div_lt_of_lt_mul
    rw [mul_comm, ← hp]
    exact hhigh
  have hdiv : (Q*Exp.exp e+H)/P = Q*A+H/P := by
    rw [hp]
    have hz : Q*(P*A)+H=H+(Q*A)*P := by ring
    rw [hz, div_add_mul_self _ _ (exp_pos _)]
    ring
  have hcutexp : Exp.exp (L-e)=B*Exp.exp t := by dsimp [B]; rw [hcut,exp_add]
  have hmod : Q%B=X%B := by
    dsimp [Q]
    rw [hcutexp]
    exact AdjacentDigits.mod_factor X B (Exp.exp t) (exp_pos _)
  have hHdiv : H/P = X / Exp.exp (L-e+67*k) := by
    dsimp [H,P]
    rw [← Arithmetic.div_mul, ← exp_add]
  have hrem : (X / Exp.exp (L-e+67*k)) % Exp.exp a = X / Exp.exp (L-e+67*k) := by
    apply mod_eq_self_of_lt
    rw [← hHdiv]
    exact hlow
  unfold dig rot
  simp only [one_mul]
  change (Q*Exp.exp e+H)/P % Exp.exp 67 = _
  rw [hdiv, hfull, mod_low_high _ _ _ _ (exp_pos _) (exp_pos _) hlow, hmod, hHdiv]
  rw [hrem]
#print axioms RotationStraddling.mod_low_high
#print axioms RotationStraddling.straddling
end RotationStraddling
