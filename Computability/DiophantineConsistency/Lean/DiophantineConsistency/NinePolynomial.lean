import DiophantineConsistency.JonesIndex
import DiophantineConsistency.Polynomial

/-!
# Jones's actual nine-variable polynomial without a polynomiality choice

The formula below substitutes literal multivariate polynomials into the
already explicit refined relation-combining core. Its coefficient data are
specified by arithmetic and polynomial evaluation, with no selection from
`PolyFn` or an existential polynomial representation.

As with `JonesIndex`, imported polynomial operations remain noncomputable
library definitions. The construction is a choice-free mathematical recipe
from the supplied quartic, rather than an executable sparse-polynomial
compiler or a new way to obtain that starting quartic.
-/

namespace DiophantineConsistency.NinePolynomial

open MvPolynomial
open Jones1982

/-- The free Jones quantities with their coefficient ring made explicit. -/
structure RingVars (A : Type*) where
  (R N b g G h s w φ i j : A)

namespace RingVars

variable {R : Type*} [Add R] [Sub R] [Mul R] [Pow R ℕ]
  [OfNat R 1] [OfNat R 2] [OfNat R 3] [OfNat R 4] [OfNat R 5] [OfNat R 8]
  (v : RingVars R)

def U : R := v.N ^ 2 * v.w
def Y : R := v.N ^ 2 * v.s
def M : R := v.R * v.Y
def P : R := 2 * v.M ^ 2 * v.U
def K : R := v.R + 1 + v.h * (v.P - 1)
def A : R := v.M * (v.U + 1)
def B' : R := 2 * v.R + 1
def W : R := v.b * v.w
def C : R := v.B' + v.W + v.φ
def J : R := 4 * v.A - 5
def Q : R := 3 * v.W * v.C - 2 * (v.W ^ 2 - 1)
def D : R := (v.A ^ 2 - 1) * v.C ^ 2 + 1
def E : R := v.i * v.J * v.D * v.C ^ 2
def F : R := (v.A ^ 2 - 1) * v.E ^ 2 + 1
def Gp : R := v.A + v.F * (v.C * v.D + 1 - v.A)
def H : R := v.B' + v.j * v.C
def I : R := (v.Gp ^ 2 - 1) * v.H ^ 2 + 1

def rad : Fin 2 → R := ![(v.P ^ 2 - 1) * v.K ^ 2 + 1, v.D * v.F * v.I]
def wt : Fin 2 → R := fun k => v.rad k ^ 2 + 2
def dvsr : R := (v.J * v.F) ^ 2
def dvnd : R := (v.Q * v.F + v.J * (v.H - v.C)) ^ 2
def marg : R := v.K ^ 2 * v.G - 4 * (v.C - v.K * v.Y) ^ 2 * v.G - 8 * v.g * v.K ^ 2

end RingVars

/-- Evaluate every polynomial free quantity into the original integer record. -/
noncomputable def evalVars {σ : Type*} (a : σ → ℤ) (v : RingVars (MvPolynomial σ ℤ)) :
    Jones1982.Nine.Vars :=
  ⟨eval a v.R, eval a v.N, eval a v.b, eval a v.g, eval a v.G,
    eval a v.h, eval a v.s, eval a v.w, eval a v.φ, eval a v.i, eval a v.j⟩

private theorem eval_rad {σ : Type*} (a : σ → ℤ)
    (v : RingVars (MvPolynomial σ ℤ)) (k : Fin 2) :
    eval a (v.rad k) = Jones1982.Nine.rad (evalVars a v) k := by
  fin_cases k <;>
    simp [RingVars.rad, Jones1982.Nine.rad, evalVars,
      RingVars.U, RingVars.Y, RingVars.M, RingVars.P, RingVars.K,
      RingVars.A, RingVars.B', RingVars.W, RingVars.C, RingVars.J,
      RingVars.D, RingVars.E, RingVars.F, RingVars.Gp,
      RingVars.H, RingVars.I,
      Jones1982.Nine.Vars.U, Jones1982.Nine.Vars.Y, Jones1982.Nine.Vars.M,
      Jones1982.Nine.Vars.P, Jones1982.Nine.Vars.K, Jones1982.Nine.Vars.A,
      Jones1982.Nine.Vars.B', Jones1982.Nine.Vars.W, Jones1982.Nine.Vars.C,
      Jones1982.Nine.Vars.J, Jones1982.Nine.Vars.D,
      Jones1982.Nine.Vars.E, Jones1982.Nine.Vars.F, Jones1982.Nine.Vars.Gp,
      Jones1982.Nine.Vars.H, Jones1982.Nine.Vars.I]

private theorem eval_wt {σ : Type*} (a : σ → ℤ)
    (v : RingVars (MvPolynomial σ ℤ)) (k : Fin 2) :
    eval a (v.wt k) = Jones1982.Nine.wt (evalVars a v) k := by
  simp only [RingVars.wt, Jones1982.Nine.wt, map_add, map_pow, map_ofNat, eval_rad]

private theorem eval_dvsr {σ : Type*} (a : σ → ℤ)
    (v : RingVars (MvPolynomial σ ℤ)) :
    eval a v.dvsr = Jones1982.Nine.dvsr (evalVars a v) := by
  simp [RingVars.dvsr, Jones1982.Nine.dvsr, evalVars,
    RingVars.U, RingVars.Y, RingVars.M, RingVars.A, RingVars.B', RingVars.W,
    RingVars.C, RingVars.J, RingVars.D, RingVars.E, RingVars.F,
    Jones1982.Nine.Vars.U, Jones1982.Nine.Vars.Y, Jones1982.Nine.Vars.M,
    Jones1982.Nine.Vars.A, Jones1982.Nine.Vars.B', Jones1982.Nine.Vars.W,
    Jones1982.Nine.Vars.C, Jones1982.Nine.Vars.J, Jones1982.Nine.Vars.D,
    Jones1982.Nine.Vars.E, Jones1982.Nine.Vars.F]

private theorem eval_dvnd {σ : Type*} (a : σ → ℤ)
    (v : RingVars (MvPolynomial σ ℤ)) :
    eval a v.dvnd = Jones1982.Nine.dvnd (evalVars a v) := by
  simp [RingVars.dvnd, Jones1982.Nine.dvnd, evalVars,
    RingVars.U, RingVars.Y, RingVars.M, RingVars.A, RingVars.B', RingVars.W,
    RingVars.C, RingVars.J, RingVars.Q, RingVars.D, RingVars.E, RingVars.F, RingVars.H,
    Jones1982.Nine.Vars.U, Jones1982.Nine.Vars.Y, Jones1982.Nine.Vars.M,
    Jones1982.Nine.Vars.A, Jones1982.Nine.Vars.B', Jones1982.Nine.Vars.W,
    Jones1982.Nine.Vars.C, Jones1982.Nine.Vars.J, Jones1982.Nine.Vars.Q,
    Jones1982.Nine.Vars.D, Jones1982.Nine.Vars.E, Jones1982.Nine.Vars.F, Jones1982.Nine.Vars.H]

private theorem eval_marg {σ : Type*} (a : σ → ℤ)
    (v : RingVars (MvPolynomial σ ℤ)) :
    eval a v.marg = Jones1982.Nine.marg (evalVars a v) := by
  simp [RingVars.marg, Jones1982.Nine.marg, evalVars,
    RingVars.U, RingVars.Y, RingVars.M, RingVars.P, RingVars.K,
    RingVars.B', RingVars.W, RingVars.C,
    Jones1982.Nine.Vars.U, Jones1982.Nine.Vars.Y, Jones1982.Nine.Vars.M,
    Jones1982.Nine.Vars.P, Jones1982.Nine.Vars.K, Jones1982.Nine.Vars.B',
    Jones1982.Nine.Vars.W, Jones1982.Nine.Vars.C]

/-- The rank coding polynomial, written over any commutative coefficient ring. -/
def rankCode {R : Type*} [Add R] [Sub R] [Mul R] [Pow R ℕ] [OfNat R 1] [OfNat R 2] (x z b e g l n q θ lam : R) : R :=
  (g + e * q ^ 3 + l * q ^ 5 +
    (2 * (e - z * lam) * (1 + x * b ^ 5 + g) ^ 4 + lam * b ^ 5 + lam * b ^ 5 * q ^ 4) * q ^ 7) *
      (n ^ 2 - n) +
  (q ^ 3 - b * l + l + θ * lam * q ^ 3 + (b ^ 5 - 2) * q ^ 8) * (n ^ 2 - 1)

/-- Literal multivariate polynomials for all Jones free quantities. -/
noncomputable def polynomialVars (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ) (z y : ℕ) :
    RingVars (MvPolynomial (Fin 10) ℤ) :=
  let x : MvPolynomial (Fin 10) ℤ := X 0
  let b := x * C (y : ℤ) + 1 + X 1
  let q := (b ^ 5) ^ L4 ν
  let n := q ^ 16
  let e := Polynomial.aeval (b ^ 5) (epoly ν 4 P z)
  let l := Polynomial.aeval (b ^ 5) (lpoly ν 4)
  let lam := Polynomial.aeval (b ^ 5) (lampoly ν 4)
  let g := X 2 + 1
  let θ := b ^ 5 - 2 * C (z : ℤ)
  ⟨rankCode x (C (z : ℤ)) b e g l n q θ lam,
    n, b, g, 32 * b * (b ^ 5) ^ (5 ^ ν),
    X 3 + 1, X 4 + 1, X 5 + 1, X 6, X 7 + 1, X 8 + 1⟩

theorem eval_variables (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (z y : ℕ) (a : Fin 10 → ℤ) :
    evalVars a (polynomialVars ν P z y) = Jones1982.Nine.varsOf ν P z y a := by
  simp [polynomialVars, evalVars, Jones1982.Nine.varsOf, rankCode, Jones1982.Nine.rZ,
    Diophantine.PolyFn.eval_aeval]

/-- The explicit polynomial before its distinguished input is fixed. -/
noncomputable def withInput (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ) (z y : ℕ) :
    MvPolynomial (Fin 10) ℤ :=
  let v := polynomialVars ν P z y
  Diophantine.RefinedRelationCombiningPolynomial.compose 2 v.rad v.wt
    (X 9) v.dvsr v.dvnd v.marg

theorem eval_withInput (ν : ℕ) (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (z y : ℕ) (a : Fin 10 → ℤ) :
    eval a (withInput ν P z y) = Jones1982.Nine.nineValue ν P z y a := by
  rw [withInput, Diophantine.RefinedRelationCombiningPolynomial.eval_compose]
  simp only [eval_rad, eval_wt, eval_dvsr, eval_dvnd, eval_marg, eval_X, eval_variables]
  rfl

/-- A fixed nine-variable polynomial, with the index computed by `JonesIndex`. -/
noncomputable def polynomial {ν : ℕ} (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (bound : ℕ := 0) : MvPolynomial (Fin 9) ℤ :=
  specializeOne (withInput ν P (JonesIndex.indexZ P bound) (JonesIndex.indexY P bound))

private theorem natCast_cons_one (a : Fin 9 → ℕ) :
    (fun i => ((Fin.cons 1 a : Fin 10 → ℕ) i : ℤ)) =
      Fin.cons 1 (fun i => (a i : ℤ)) := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- The only semantic premises concern the supplied starting quartic. No
existential polynomial witness is chosen at the nine-variable stage. -/
theorem hasNaturalZero_polynomial {ν : ℕ} (P : MvPolynomial (Fin (ν + 1)) ℤ)
    (hν : 1 ≤ ν) (hP : P.totalDegree ≤ 4) (hnorm : Normalized P) (bound : ℕ) :
    HasNaturalZero (polynomial P bound) ↔ Wset P 1 := by
  have h := Jones1982.Nine.wset_iff_nine hν hP hnorm
    (JonesIndex.index_correct P bound) (by decide : 0 < (1 : ℕ))
  simp only [natCast_cons_one] at h
  have hv (a : Fin 9 → ℕ) :
      eval (fun i => (a i : ℤ)) (polynomial P bound) =
        Jones1982.Nine.nineValue ν P (JonesIndex.indexZ P bound) (JonesIndex.indexY P bound)
          (Fin.cons 1 (fun i => (a i : ℤ))) := by
    calc
      _ = eval (Fin.cons 1 (fun i => (a i : ℤ)))
          (withInput ν P (JonesIndex.indexZ P bound) (JonesIndex.indexY P bound)) :=
        eval_specializeOne _ _
      _ = _ := eval_withInput _ _ _ _ _
  constructor
  · rintro ⟨a, ha⟩
    apply h.mpr
    refine ⟨a, ?_⟩
    rwa [← hv a]
  · intro hW
    obtain ⟨a, ha⟩ := h.mp hW
    refine ⟨a, ?_⟩
    rwa [hv a]

#print axioms hasNaturalZero_polynomial

end DiophantineConsistency.NinePolynomial
