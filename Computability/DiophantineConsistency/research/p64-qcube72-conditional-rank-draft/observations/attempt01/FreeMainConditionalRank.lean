import FreeMainActualLarge
import DiophantineConsistency.AdaptiveGap85GenericSignedHalfIndex

/-! Unchecked draft: actual zero plus explicit strong/auxiliary norms and half-window. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeMainConditionalRank
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open ArithmeticPellRecurrence ArithmeticPellHalfIndex
open AdaptiveGap85GenericSignedHalfIndex
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

def qval (p : Fin 4 → ℕ) (v : Fin 14 → V) : V := (p 0:V)*v 0+1
def yval (p : Fin 4 → ℕ) (v : Fin 14 → V) : V := qval p v*qval p v*qval p v*v 7
def aval (p : Fin 4 → ℕ) (v : Fin 14 → V) : V := (v 8*qval p v)*yval p v+yval p v
def cval (p : Fin 4 → ℕ) (v : Fin 14 → V) : V := (v 10+v 11)*yval p v+v 10

theorem main_index_eq_rank (p : Fin 4 → ℕ) (v : Fin 14 → V) (R : V)
    (hv : ∀ i, 0 < v i)
    (hz : InternalZero (P64QCube72Free.graph (fun j => (p j:ℤ))).output v)
    (hq : 33≤qval p v) (hR : 0<R) (hhalf : 2*R<cval p v)
    (hstrong : (v 5*cval p v*cval p v)*(v 5*cval p v*cval p v)+delta (aval p v) =
      delta (aval p v)*(v 4*v 4))
    (haux : let z := absdiff ((v 4*v 4)*(v 6*cval p v)) ((v 4*v 4)*R+cval p v)
      (v 5*cval p v*cval p v)*(v 5*cval p v*cval p v)*z*z+v 12*v 12 =
        1+(v 5*cval p v*cval p v)*(v 5*cval p v*cval p v)*v 12*v 12) :
    ∃ g : V, g*g=1+delta (aval p v)*(cval p v)*(cval p v) ∧
      xcoord R (aval p v)=g ∧ ycoord R (aval p v)=cval p v := by
  let a : V := aval p v
  let c : V := cval p v
  obtain ⟨g,m,hg,_,hx,hy,hm,hbig⟩ := FreeMainActualLarge.main_index_large p v hv hz hq
  change g*g=1+delta a*c*c at hg
  change xcoord m a=g at hx
  change ycoord m a=c at hy
  change (a+2)*delta a*delta a<c at hbig
  have hc : 0<c := by
    dsimp [c,cval]
    exact add_pos_of_nonneg_of_pos (Arithmetic.zero_le _) (hv 10)
  have hm0 : 0<m := lt_of_lt_of_le (by norm_num) hm
  have hRabs : absdiff R 0=R := by simp [absdiff]
  have haux' : let z := absdiff ((v 4*v 4)*(v 6*c+0)) ((v 4*v 4)*R+c)
      (v 5*c*c)*(v 5*c*c)*z*z+v 12*v 12 =
        1+(v 5*c*c)*(v 5*c*c)*v 12*v 12 := by
    simpa only [add_zero] using haux
  have h := signed_half_index_of_facts a c g (v 4) (v 5) (v 6) R 0 (v 12) m
    hc (hv 5) (hv 4) hm0 (hv 12) hy (by rw [hRabs]; exact hR)
    (by rw [hRabs]; exact hhalf) hg hstrong hbig haux'
  have hmR : m=R := by simpa only [hRabs] using h
  refine ⟨g,hg,?_,?_⟩
  · simpa only [←hmR] using hx
  · simpa only [←hmR] using hy

#print axioms FreeMainConditionalRank.main_index_eq_rank
end FreeMainConditionalRank
