import DiophantineConsistency.ThirteenCarrier
import Mathlib.Tactic.LinearCombination

/-! Source-only generic graph cut. This is copied from the standard-integer
completeness development, but it uses only commutative-ring hypotheses. It
has not yet been checked against a coherent provider overlay or connected to
an actual model zero. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Model69GraphCutDraft
open DiophantineConsistency
variable {R : Type*} [CommRing R]

/-- Preserve J,F,alpha,s,w,n,eta,zeta,gamma and replace only f,i,T,m. -/
def replace (v : Fin 14 → R) (f i T m : R) (j : Fin 13) : R :=
  match j.val with
  | 0 => v 0
  | 1 => v 1
  | 2 => v 2
  | 3 => f
  | 4 => i
  | 5 => T
  | 6 => v 7
  | 7 => v 8
  | 8 => v 9
  | 9 => v 10
  | 10 => v 11
  | 11 => m
  | _ => v 13

/-- Outer parent blocks, defined solely by retained coordinates. -/
structure ParentView (R : Type*) where
  C : R
  c : R
  rank : R
  a : R
  delta : R
  P : R
  Q : R

def parentView (p : Fin 4 → R) (v : Fin 14 → R) : ParentView R :=
  let b := p 0 * v 0
  let q := b + 1
  let C := q - v 1 - v 2
  let X := v 8 * q
  let Y := v 7 * q ^ 3
  let E := X * Y
  let k := v 10 + v 11
  let ell := E * k * Y
  let c := k * Y + v 10
  let a := E + Y
  let H := 4 * a + 3
  let delta := a ^ 2 + H
  let D := X + a * c + v 13 * H
  let rank := (b * (q - v 1) + v 2) * (q ^ 2 - 1) + (p 2 + q * p 3) * v 0
  let tau := E * v 9 + k - rank
  ⟨C,c,rank,a,delta,tau ^ 2 - ell * (ell+k), D ^ 2 - delta * c ^ 2⟩

def transport (p : Fin 4 → R) (v : Fin 14 → R) : R :=
  (p 1 + v 8) * (parentView p v).C - v 1

/-- The complete literal core, including the retained first-root carrier n. -/
theorem core_replace (p : Fin 4 → R) (v : Fin 14 → R) (f i T m : R) :
    let b := parentView p v
    let V := f ^ 2 * (b.c * T - b.rank) - b.c
    let y := 1 + 4 * (p 0 * v 0 * (m - V ^ 2 * transport p v) - transport p v)
    ThirteenCarrier.core p (replace v f i T m) =
      ⟨b.a, b.delta, p 0 * v 0 * i * b.c ^ 2, f, V ^ 2 - y ^ 2, y, b.P, b.Q⟩ := rfl

/-- The two fresh norms and the two retained norms give the actual69 evaluator. -/
theorem replace_zero69 (p : Fin 4 → R) (v : Fin 14 → R) (f i T m : R)
    (hP : (parentView p v).P = 1) (hQ : (parentView p v).Q = 1)
    (hs : f ^ 2 - (parentView p v).delta *
      (p 0 * v 0 * i * (parentView p v).c ^ 2) ^ 2 = 1)
    (hu : let b := parentView p v
      let S := b.delta * (p 0 * v 0 * i * b.c ^ 2)
      let V := f ^ 2 * (b.c * T - b.rank) - b.c
      let y := 1 + 4 * (p 0 * v 0 * (m - V ^ 2 * transport p v) - transport p v)
      S ^ 2 * (V ^ 2 - y ^ 2) + y ^ 2 = 1) :
    ThirteenCarrier.value69 p (replace v f i T m) = 0 := by
  have hz : (parentView p v).delta * f ^ 2 -
      ((parentView p v).delta * (p 0 * v 0 * i * (parentView p v).c ^ 2)) ^ 2 =
      (parentView p v).delta := by
    linear_combination (parentView p v).delta * hs
  dsimp only [ThirteenCarrier.value69]
  rw [core_replace]
  dsimp only
  rw [hP, hQ, hu, hz]
  ring


end Model69GraphCutDraft
#print axioms Model69GraphCutDraft.replace_zero69
