import DiophantineConsistency.NativeQuadraticParent
import Mathlib.Tactic.LinearCombination

/-!
# The seven ordinary native arithmetic equations behind report52

This file eliminates exactly the fifteen lifting registers of the literal
31-coordinate parent. All coefficient ports remain parameters. No Wang-language,
blank-machine, or consistency interpretation is assumed or concluded here.
-/

namespace DiophantineConsistency.NativeArithmetic52

open NativeQuadraticParent

set_option maxRecDepth 12000
set_option maxHeartbeats 100000

variable {R : Type*} [CommRing R]

/-- The source's first sixteen coordinates, in its unchanged delivered order:
J,F,alpha,z,f,h,i,o,j,s,w,tau,eta,zeta,y,gamma. -/
def restrict (x : Fin 31 → R) (i : Fin 16) : R := x ⟨i, by omega⟩

structure Registers (R : Type*) where
  q : R
  k : R
  N : R
  E : R
  P : R
  c : R
  a : R
  X : R
  D : R
  C2 : R
  L : R
  F2 : R
  V : R
  g : R
  I : R
  Baux : R
  delta : R
  Y : R
  target : R

/-- Ordinary strong arithmetic: in particular `Baux = (i*c²)²`, without
inserting or canceling a discriminant in the supplied coordinate. -/
def registers (ports : Fin 4 → R) (v : Fin 16 → R) : Registers R :=
  let q := 1 + v 0 * ports 0
  let k := v 12 + v 13
  let L := q * q - 1
  let N := q * (1 + L)
  let X := q * v 10
  let Y := N * v 9
  let E := X * Y
  let a := E + Y
  let c := v 12 + k * Y
  let P := k + E * (c - v 12)
  let delta := a*a + (3 + 4*a)
  let D := X + a*c + (3 + 4*a)*v 15
  let V := v 4 * v 7 - c
  let I := c*c*v 6
  let target := ((q-1)*(q-v 1)+v 2)*L + (ports 2+ports 3*q)*v 0
  {q, k, N, E, P, c, a, X, D, C2 := c*c, L, F2 := v 4*v 4,
   V, g := v 14*v 14-V*V, I, Baux := I*I, delta, Y, target}

/-- The fifteen original auxiliary coordinates, in their original order. -/
def auxiliaries (ports : Fin 4 → R) (v : Fin 16 → R) : Fin 15 → R :=
  let c := registers ports v
  ![c.N, c.E, c.P, c.c, c.a, c.X, c.D, c.C2, c.L, c.F2,
    c.V, c.g, c.I, c.Baux, c.delta]

/-- Explicit reconstruction, with no choice of intermediate witnesses. -/
def lift (ports : Fin 4 → R) (v : Fin 16 → R) : Fin 31 → R :=
  let c := registers ports v
  ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7,v 8,v 9,v 10,v 11,v 12,v 13,v 14,v 15,
    c.N,c.E,c.P,c.c,c.a,c.X,c.D,c.C2,c.L,c.F2,c.V,c.g,c.I,c.Baux,c.delta]

@[simp] theorem restrict_lift (ports : Fin 4 → R) (v : Fin 16 → R) :
    restrict (lift ports v) = v := by
  funext i
  fin_cases i <;> rfl

/-- The seven nondefinitional residuals: first norm, main norm, index,
quotient compatibility, shifted transport, ordinary strong norm, auxiliary norm. -/
def residuals (ports : Fin 4 → R) (v : Fin 16 → R) : Fin 7 → R :=
  let c := registers ports v
  ![v 11*v 11-(1+c.P*(c.P-c.k)),
    c.D*c.D-(1+c.C2*c.delta),
    c.k-(1+c.target+c.E*v 5),
    c.c*v 8-c.V-c.target,
    (ports 1+v 10)*(c.q-v 1-v 2)-(v 1+(c.q-1)*v 3),
    c.Baux-c.delta*(c.F2-1),
    v 14*v 14-c.Baux*c.g-1]

private theorem lifted_row0 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 0 = 0 := by
  let c := registers ports v
  change 1+(c.q*c.q-1)-c.q*c.q=0
  ring

private theorem lifted_row1 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 1 = 0 := by
  let c := registers ports v
  exact sub_self c.N

private theorem lifted_row2 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 2 = 0 := by
  let c := registers ports v
  exact sub_self c.X

private theorem lifted_row3 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 3 = 0 := by
  let c := registers ports v
  change (c.E+c.Y-c.E)-c.Y=0
  ring

private theorem lifted_row4 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 4 = 0 := by
  let c := registers ports v
  change c.X*c.Y-c.X*(c.E+c.Y-c.E)=0
  ring

private theorem lifted_row5 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 5 = 0 := by
  let c := registers ports v
  change (v 12+c.k*c.Y-v 12)-c.k*(c.E+c.Y-c.E)=0
  ring

private theorem lifted_row6 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 6 = 0 := by
  let c := registers ports v
  change (c.k+c.E*(c.c-v 12)-c.k)-c.E*(c.c-v 12)=0
  ring

private theorem lifted_row7 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 7 = residuals ports v 0 := by
  let c := registers ports v
  rfl

private theorem lifted_row8 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 8 = 0 := by
  let c := registers ports v
  exact sub_self c.D

private theorem lifted_row9 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 9 = 0 := by
  let c := registers ports v
  exact sub_self c.delta

private theorem lifted_row10 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 10 = 0 := by
  let c := registers ports v
  exact sub_self c.C2

private theorem lifted_row11 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 11 = residuals ports v 1 := by
  let c := registers ports v
  rfl

private theorem lifted_row12 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 12 = residuals ports v 2-residuals ports v 3 := by
  let c := registers ports v
  change c.k-(1+(c.c*v 8-c.V)+c.E*v 5)=
    (c.k-(1+c.target+c.E*v 5))-(c.c*v 8-c.V-c.target)
  ring

private theorem lifted_row13 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 13 = residuals ports v 3 := by
  let c := registers ports v
  change (c.c*v 8-c.V)-
    ((c.q*(1+c.L)-c.q)*(c.q-v 1)-c.L*(c.q-v 1-v 2)+v 0*(ports 2+ports 3*c.q))=
      c.c*v 8-c.V-(((c.q-1)*(c.q-v 1)+v 2)*c.L+
        (ports 2+ports 3*c.q)*v 0)
  ring

private theorem lifted_row14 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 14 = residuals ports v 4 := by
  let c := registers ports v
  change (ports 1+v 10)*(c.q-v 1-v 2)-(v 1+v 0*ports 0*v 3)=
    (ports 1+v 10)*(c.q-v 1-v 2)-(v 1+(1+v 0*ports 0-1)*v 3)
  ring

private theorem lifted_row15 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 15 = 0 := by
  let c := registers ports v
  exact sub_self c.F2

private theorem lifted_row16 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 16 = 0 := by
  let c := registers ports v
  exact sub_self c.V

private theorem lifted_row17 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 17 = 0 := by
  let c := registers ports v
  exact sub_self c.g

private theorem lifted_row18 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 18 = 0 := by
  let c := registers ports v
  exact sub_self c.I

private theorem lifted_row19 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 19 = 0 := by
  let c := registers ports v
  exact sub_self c.Baux

private theorem lifted_row20 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 20 = residuals ports v 5 := by
  let c := registers ports v
  rfl

private theorem lifted_row21 (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) 21 = residuals ports v 6 := by
  let c := registers ports v
  rfl

private theorem lifted_rows (ports : Fin 4 → R) (v : Fin 16 → R) :
    sourceRows ports (lift ports v) =
      ![0,0,0,0,0,0,0,residuals ports v 0,0,0,0,residuals ports v 1,
        residuals ports v 2-residuals ports v 3,residuals ports v 3,
        residuals ports v 4,0,0,0,0,0,residuals ports v 5,residuals ports v 6] := by
  funext k
  fin_cases k
  · exact lifted_row0 ports v
  · exact lifted_row1 ports v
  · exact lifted_row2 ports v
  · exact lifted_row3 ports v
  · exact lifted_row4 ports v
  · exact lifted_row5 ports v
  · exact lifted_row6 ports v
  · exact lifted_row7 ports v
  · exact lifted_row8 ports v
  · exact lifted_row9 ports v
  · exact lifted_row10 ports v
  · exact lifted_row11 ports v
  · exact lifted_row12 ports v
  · exact lifted_row13 ports v
  · exact lifted_row14 ports v
  · exact lifted_row15 ports v
  · exact lifted_row16 ports v
  · exact lifted_row17 ports v
  · exact lifted_row18 ports v
  · exact lifted_row19 ports v
  · exact lifted_row20 ports v
  · exact lifted_row21 ports v


/-- The literal parent at explicitly reconstructed registers has exactly the
seven displayed arithmetic equations. -/
theorem lift_zero_iff (ports : Fin 4 → R) (v : Fin 16 → R) :
    (∀ k, sourceRows ports (lift ports v) k = 0) ↔ ∀ j, residuals ports v j = 0 := by
  rw [lifted_rows]
  constructor
  · intro h
    have hq := h 13
    have hi := h 12
    intro j
    fin_cases j
    · exact h 7
    · exact h 11
    · have hi' : residuals ports v 2-residuals ports v 3=0 := hi
      exact (sub_eq_zero.mp hi').trans hq
    · exact hq
    · exact h 14
    · exact h 20
    · exact h 21
  · intro h k
    fin_cases k <;> simp [h]

/-- Every zero fixes all fifteen lifting registers uniquely. -/
theorem eq_lift_of_zero (ports : Fin 4 → R) (x : Fin 31 → R)
    (h : ∀ k, sourceRows ports x k = 0) : x = lift ports (restrict x) := by
  have h0 := h 0
  have h1 := h 1
  have h2 := h 2
  have h3 := h 3
  have h4 := h 4
  have h5 := h 5
  have h6 := h 6
  have h8 := h 8
  have h9 := h 9
  have h10 := h 10
  have h15 := h 15
  have h16 := h 16
  have h17 := h 17
  have h18 := h 18
  have h19 := h 19
  change 1+x 24-(1+x 0*ports 0)*(1+x 0*ports 0)=0 at h0
  change x 16-(1+x 0*ports 0)*(1+x 24)=0 at h1
  change x 21-(1+x 0*ports 0)*x 10=0 at h2
  change (x 20-x 17)-x 16*x 9=0 at h3
  change x 17-x 21*(x 20-x 17)=0 at h4
  change (x 19-x 12)-(x 12+x 13)*(x 20-x 17)=0 at h5
  change (x 18-(x 12+x 13))-x 17*(x 19-x 12)=0 at h6
  change x 22-(x 21+x 20*x 19+(3+4*x 20)*x 15)=0 at h8
  change x 30-(x 20*x 20+(3+4*x 20))=0 at h9
  change x 23-x 19*x 19=0 at h10
  change x 25-x 4*x 4=0 at h15
  change x 26-(x 4*x 7-x 19)=0 at h16
  change x 27-(x 14*x 14-x 26*x 26)=0 at h17
  change x 28-x 23*x 6=0 at h18
  change x 29-x 28*x 28=0 at h19
  let c := registers ports (restrict x)
  have hL : x 24 = c.L := by
    change x 24 = (1+x 0*ports 0)*(1+x 0*ports 0)-1
    linear_combination h0
  have hN : x 16 = c.N := by
    rw [hL] at h1
    exact sub_eq_zero.mp h1
  have hX : x 21 = c.X := sub_eq_zero.mp h2
  have hY : x 20-x 17 = c.Y := by
    rw [hN] at h3
    exact sub_eq_zero.mp h3
  have hE : x 17 = c.E := by
    rw [hX,hY] at h4
    exact sub_eq_zero.mp h4
  have ha : x 20 = c.a := by
    rw [hE] at hY
    change x 20 = c.E+c.Y
    linear_combination hY
  have hc : x 19 = c.c := by
    rw [hY] at h5
    change x 19 = x 12+(x 12+x 13)*c.Y
    linear_combination h5
  have hP : x 18 = c.P := by
    rw [hE,hc] at h6
    change x 18 = (x 12+x 13)+c.E*(c.c-x 12)
    linear_combination h6
  have hD : x 22 = c.D := by
    rw [hX,ha,hc] at h8
    exact sub_eq_zero.mp h8
  have hdelta : x 30 = c.delta := by
    rw [ha] at h9
    exact sub_eq_zero.mp h9
  have hC2 : x 23 = c.C2 := by
    rw [hc] at h10
    exact sub_eq_zero.mp h10
  have hF2 : x 25 = c.F2 := sub_eq_zero.mp h15
  have hV : x 26 = c.V := by
    rw [hc] at h16
    exact sub_eq_zero.mp h16
  have hg : x 27 = c.g := by
    rw [hV] at h17
    exact sub_eq_zero.mp h17
  have hI : x 28 = c.I := by
    rw [hC2] at h18
    exact sub_eq_zero.mp h18
  have hB : x 29 = c.Baux := by
    rw [hI] at h19
    exact sub_eq_zero.mp h19
  funext i
  fin_cases i
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hN
  · exact hE
  · exact hP
  · exact hc
  · exact ha
  · exact hX
  · exact hD
  · exact hC2
  · exact hL
  · exact hF2
  · exact hV
  · exact hg
  · exact hI
  · exact hB
  · exact hdelta

/-- Exact algebraic elimination, over every commutative ring. -/
theorem source_zero_iff (ports : Fin 4 → R) (x : Fin 31 → R) :
    (∀ k, sourceRows ports x k = 0) ↔
      x = lift ports (restrict x) ∧ ∀ j, residuals ports (restrict x) j = 0 := by
  constructor
  · intro h
    refine ⟨eq_lift_of_zero ports x h, ?_⟩
    apply (lift_zero_iff ports (restrict x)).mp
    simpa only [← eq_lift_of_zero ports x h] using h
  · rintro ⟨hx,h⟩
    simpa only [← hx] using (lift_zero_iff ports (restrict x)).mpr h

/-- Existence equivalence with sixteen quantified ring coordinates. -/
theorem exists_zero_iff (ports : Fin 4 → R) :
    (∃ x : Fin 31 → R, ∀ k, sourceRows ports x k = 0) ↔
      ∃ v : Fin 16 → R, ∀ j, residuals ports v j = 0 := by
  constructor
  · rintro ⟨x,hx⟩
    exact ⟨restrict x, ((source_zero_iff ports x).mp hx).2⟩
  · rintro ⟨v,hv⟩
    exact ⟨lift ports v, (lift_zero_iff ports v).mpr hv⟩

/-- Positive existence, retaining every reconstructed coordinate's positivity.
In particular, neither `V>0` nor `g>0` is silently discarded. -/
theorem exists_positive_zero_iff (ports : Fin 4 → ℤ) :
    (∃ x : Fin 31 → ℤ, (∀ i, 0 < x i) ∧ ∀ k, sourceRows ports x k = 0) ↔
      ∃ v : Fin 16 → ℤ, (∀ i, 0 < lift ports v i) ∧ ∀ j, residuals ports v j = 0 := by
  constructor
  · rintro ⟨x,hp,hx⟩
    obtain ⟨he,hr⟩ := (source_zero_iff ports x).mp hx
    refine ⟨restrict x, ?_, hr⟩
    simpa only [← he] using hp
  · rintro ⟨v,hp,hv⟩
    exact ⟨lift ports v,hp,(lift_zero_iff ports v).mpr hv⟩

end DiophantineConsistency.NativeArithmetic52
