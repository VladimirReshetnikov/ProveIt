import DiophantineConsistency.ArithmeticPellPowerRecovery
import DiophantineConsistency.ArithmeticPellResidueClasses
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 12000000
noncomputable section
namespace DiophantineConsistency.AdaptiveGap85AllIndicesModular
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellRecurrence ArithmeticPellResidueClasses
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- General-index positive Pell congruence at modulus 4a+3. -/
theorem pell_minus_congruence (a n : V) :
    (xcoord n a)%(4*a+3)=(a*ycoord n a+Exp.exp n)%(4*a+3) := by
  induction n using ISigma1.sigma1_succ_induction
  · definability
  case zero => simp
  case succ n ih =>
    let H : V := 4*a+3
    have hH : 0<H := by dsimp [H]; simp
    change xcoord n a%H=(a*ycoord n a+Exp.exp n)%H at ih
    change xcoord (n+1) a%H=(a*ycoord (n+1) a+Exp.exp (n+1))%H
    have h2 : (2*xcoord n a)%H=(2*(a*ycoord n a+Exp.exp n))%H := by
      rw [mod_mul hH,mod_mul (a:=(2:V)) (b:=a*ycoord n a+Exp.exp n) hH,ih]
    have hsum := mod_add_congr (2*xcoord n a) (2*(a*ycoord n a+Exp.exp n)) (a*ycoord (n+1) a) H hH h2
    apply mod_add_cancel _ _ (2*a*ycoord n a) H hH
    calc
      _ = (2*xcoord n a+a*ycoord (n+1) a+H*ycoord n a)%H := by
        congr 1
        rw [x_succ,y_succ]
        dsimp [H,delta]
        ring
      _ = (2*xcoord n a+a*ycoord (n+1) a)%H := mod_add_mul' _ _ hH
      _ = (2*(a*ycoord n a+Exp.exp n)+a*ycoord (n+1) a)%H := hsum
      _ = _ := by rw [exp_succ]; congr 1; ring

/-- The opposite signed Pell combination has reciprocal power residue. -/
theorem pell_plus_congruence (a n : V) :
    (Exp.exp n*(xcoord n a+a*ycoord n a))%(4*a+3)=1%(4*a+3) := by
  let H : V := 4*a+3
  let x : V := xcoord n a
  let y : V := ycoord n a
  let E : V := Exp.exp n
  have hH : 0<H := by dsimp [H]; simp
  have hminus : x%H=(a*y+E)%H := pell_minus_congruence a n
  have hmul : (x*(x+a*y))%H=((a*y+E)*(x+a*y))%H := by
    rw [mod_mul hH,mod_mul (a:=a*y+E) (b:=x+a*y) hH,hminus]
  have he : x*(x+a*y)=a*y*(x+a*y)+1+H*(y*y) := by
    have hn : x*x=1+delta a*y*y := norm n a
    calc
      _ = x*x+a*y*x := by ring
      _ = (1+delta a*y*y)+a*y*x := by rw [hn]
      _ = _ := by dsimp [H,delta]; ring
  apply mod_add_cancel _ _ (a*y*(x+a*y)) H hH
  calc
    _ = ((a*y+E)*(x+a*y))%H := by congr 1; ring
    _ = (x*(x+a*y))%H := hmul.symm
    _ = (a*y*(x+a*y)+1+H*(y*y))%H := by rw [he]
    _ = (a*y*(x+a*y)+1)%H := mod_add_mul' _ _ hH
    _ = _ := by congr 1; ring
end DiophantineConsistency.AdaptiveGap85AllIndicesModular
