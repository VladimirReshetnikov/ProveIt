import PA194BFinite
import PA194BModelSteps

/-! Replays the four exceptional primary-to-PA194B tape segments. -/

set_option autoImplicit false
set_option maxRecDepth 25000
set_option maxHeartbeats 1300000

namespace PA194BExceptions
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open PA194BRows PA194BModelSteps

abbrev machine := table actions

private theorem s39zero : action 39 0 = (0,0,52) := by decide +kernel
private theorem s39one : action 39 1 = (1,1,53) := by decide +kernel
private theorem s52zero : action 52 0 = (0,1,72) := by decide +kernel
private theorem s52one : action 52 1 = (1,1,52) := by decide +kernel
private theorem s72zero : action 72 0 = (0,0,95) := by decide +kernel
private theorem s95zero : action 95 0 = (0,1,84) := by decide +kernel
private theorem s84zero : action 84 0 = (0,1,106) := by decide +kernel

section models
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

noncomputable abbrev bStep (x : V) : V := ConPA.Machine.step machine x

private theorem goRight (q b w dest : Nat) (hq : q < 194) (hb : b < 2)
    (l r : V) (act : action q b = (w,1,dest)) :
    bStep (config q l (stack r (b : V))) = config dest (stack l (w : V)) r :=
  right actions counts.1 q b w dest hq hb l r act

private theorem goLeft (q a b w dest : Nat) (hq : q < 194) (ha : a < 2) (hb : b < 2)
    (l r : V) (act : action q b = (w,0,dest)) :
    bStep (config q (stack l (a : V)) (stack r (b : V))) =
      config dest l (stack (stack r (w : V)) (a : V)) :=
  left actions counts.1 q a b w dest hq ha hb l r act

theorem readOne (l r : V) :
    bStep (config 39 l (stack r 1)) = config 53 (stack l 1) r := by
  simpa only [Nat.cast_one] using goRight 39 1 1 53 (by decide) (by decide) l r s39one

theorem historyOne (l r : V) :
    bStep^[3] (config 39 (stack l 1) (stack r 0)) = config 72 (stack (stack l 1) 0) r := by
  have h1 := goLeft 39 1 0 0 52 (by decide) (by decide) (by decide) l r s39zero
  have h2 := goRight 52 1 1 52 (by decide) (by decide) l (stack r 0) s52one
  have h3 := goRight 52 0 0 72 (by decide) (by decide) (stack l 1) r s52zero
  simp only [Nat.cast_zero,Nat.cast_one] at h1 h2 h3
  rw [show 3 = 2+1 by decide,Function.iterate_succ_apply',
    show 2 = 1+1 by decide,Function.iterate_succ_apply',Function.iterate_one,
    h1,h2,h3]

theorem historyZero (l r : V) :
    bStep^[5] (config 39 (stack l 0) (stack r 0)) = config 106 (stack (stack l 0) 0) r := by
  have h1 := goLeft 39 0 0 0 52 (by decide) (by decide) (by decide) l r s39zero
  have h2 := goRight 52 0 0 72 (by decide) (by decide) l (stack r 0) s52zero
  have h3 := goLeft 72 0 0 0 95 (by decide) (by decide) (by decide) l r s72zero
  have h4 := goRight 95 0 0 84 (by decide) (by decide) l (stack r 0) s95zero
  have h5 := goRight 84 0 0 106 (by decide) (by decide) (stack l 0) r s84zero
  simp only [Nat.cast_zero] at h1 h2 h3 h4 h5
  rw [show 5 = 4+1 by decide,Function.iterate_succ_apply',
    show 4 = 3+1 by decide,Function.iterate_succ_apply',
    show 3 = 2+1 by decide,Function.iterate_succ_apply',
    show 2 = 1+1 by decide,Function.iterate_succ_apply',Function.iterate_one,
    h1,h2,h3,h4,h5]

#print axioms readOne
#print axioms historyOne
#print axioms historyZero
end models
end PA194BExceptions
