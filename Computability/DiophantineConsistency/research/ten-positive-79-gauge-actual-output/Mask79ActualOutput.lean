import Mask79ActualRowsV3

/-! Bind the corrected gauge to the actual 79-ring evaluator. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Mask79ActualOutput
open DiophantineConsistency AdaptiveEquationSyntax2011 TenPositive79Mask Mask79ActualRows
variable {R : Type*} [CommRing R]

def rankTerm (p : Fin 4 → ℤ) (v : Fin 10 → R) : R :=
  let q := (p 0:R)*v 0 + ((1:ℤ):R)
  q*(q-v 1)-v 2

def move (v : Fin 10 → R) (s : Shared R) (t : R) : Fin 10 → R :=
  let D := s.q*(s.k+s.w)+1
  ![v 0, v 1+s.b*t, v 2-s.q*s.b*t, v 3, v 4, v 5, v 6,
    v 7-(s.b*s.sq+1)*D*t, v 8, v 9]

theorem shared_move (p : Fin 4 → ℤ) (v : Fin 10 → R) (s : Shared R) (G t : R) :
    shared p (move v s t) G = shared p v G := by
  rfl

theorem output_move (p : Fin 4 → ℤ) (v : Fin 10 → R) (t : R) :
    let G := rankTerm p v
    let s := shared p v G
    (output79 p).evalRing (move v s t) = (output79 p).evalRing v := by
  dsimp only
  let G := rankTerm p v
  let s := shared p v G
  have hgauge := Mask79Carrier.preserve_rank_and_main s.q s.b s.k s.w
    (v 1) (v 2) (v 7) s.sq s.u s.H s.Z s.P t
  have hrank : rankTerm p (move v s t) = rankTerm p v := by
    change s.q*(s.q-(v 1+s.b*t))-(v 2-s.q*s.b*t) = s.q*(s.q-v 1)-v 2
    exact hgauge.1
  rw [TenPositive79Mask.new_core, TenPositive79Mask.new_core]
  change core p (move v s t) ((move v s t) 2) (rankTerm p (move v s t)) =
    core p v (v 2) (rankTerm p v)
  rw [hrank, core_decompose, core_decompose, shared_move]
  change output s (v 1+s.b*t) (v 2-s.q*s.b*t)
    (v 7-(s.b*s.sq+1)*(s.q*(s.k+s.w)+1)*t) = output s (v 1) (v 2) (v 7)
  have hmain : main s (v 1+s.b*t) (v 2-s.q*s.b*t)
      (v 7-(s.b*s.sq+1)*(s.q*(s.k+s.w)+1)*t) = main s (v 1) (v 2) (v 7) := by
    exact hgauge.2
  unfold output
  rw [hmain]

#print axioms Mask79ActualOutput.output_move
end Mask79ActualOutput
