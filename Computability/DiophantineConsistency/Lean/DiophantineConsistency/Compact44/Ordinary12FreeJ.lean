import DiophantineConsistency.Compact44.Ordinary12Patterns
import DiophantineConsistency.Compact44.Ordinary12FactorSplit
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.Ordinary12FreeJ
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ArithmeticSignedPairs
open DiophantineConsistency.ArithmeticAdaptiveFactorMagnitude2011
open DiophantineConsistency.ArithmeticAdaptiveFactorUnits2011
open DiophantineConsistency.Ordinary12Patterns
open DiophantineConsistency.Ordinary12FactorSplit

structure Core where
  first : Expr (Fin 12)
  main : Expr (Fin 12)
  ordinary : Expr (Fin 12)
  output : Expr (Fin 12)
  qm : Expr (Fin 12)
  z : Expr (Fin 12)
  n : Expr (Fin 12)
  u : Expr (Fin 12)
  a : Expr (Fin 12)
  c : Expr (Fin 12)
  d : Expr (Fin 12)
  pa : Expr (Fin 12)
  pd : Expr (Fin 12)
  pt : Expr (Fin 12)
  pc : Expr (Fin 12)

set_option linter.unusedVariables false in
def core (p : Fin 4 → ℤ) : Core :=
  let J : Expr (Fin 12) := .var 0
  let F : Expr (Fin 12) := .var 1
  let alpha : Expr (Fin 12) := .var 2
  let t : Expr (Fin 12) := .var 3
  let T : Expr (Fin 12) := .var 4
  let X : Expr (Fin 12) := .var 5
  let Y : Expr (Fin 12) := .var 6
  let r : Expr (Fin 12) := .var 7
  let eta : Expr (Fin 12) := .var 8
  let zeta : Expr (Fin 12) := .var 9
  let n : Expr (Fin 12) := .var 10
  let gamma : Expr (Fin 12) := .var 11
  let beta : Expr (Fin 12) := .constant (p 0)
  let K0 : Expr (Fin 12) := .constant (p 1)
  let MC : Expr (Fin 12) := .constant (p 2)
  let MF : Expr (Fin 12) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
  let qm := J * beta
  let q := 1 + qm
  let q2 := q * q
  let q3 := q * q2
  let U := Y * q2
  let qF := q - F
  let C := qF - alpha
  let E := X * Y
  let k := eta + zeta
  let kY := Y * k
  let c := eta + kY
  let c2 := c * c
  let a := E + Y
  let g15 := 4 * a
  let H := 3 + g15
  let g17 := a * a
  let Delta := H + g17
  let g19 := a * c
  let b0 := X + g19
  let ell := E * kY
  let M := q3 * qm
  let g25 := K0 * q
  let g26 := X + g25
  let g27 := C * g26
  let g28 := F * q
  let Bt := g27 - g28
  let g30 := ell + k
  let g31 := g30 + r
  let folded_kBt := k * Bt
  let folded_g31 := g31 - folded_kBt
  let g32 := M * folded_g31
  let g33 := Y * qm
  let g34 := g32 + g33
  let folded_q3Bt := q3 * Bt
  let Z := g34 - folded_q3Bt
  let g38 := Z * Z
  let g39 := M * M
  let g40 := ell * g30
  let g41 := 1 + g40
  let g42 := g39 * g41
  let A0 := g38 - g42
  let g44 := qF * qm
  let G := alpha + g44
  let g46 := q2 - 1
  let g47 := G * g46
  let g48 := MF * q
  let g49 := MC + g48
  let g50 := J * g49
  let R := g47 + g50
  let g52 := k - R
  let r0 := g52 - 1
  let g54 := U * gamma
  let g55 := E * q
  let g56 := g54 + g55
  let shift := g56 - r0
  let g58 := U * b0
  let g59 := H * shift
  let Dstar := g58 + g59
  let g61 := Dstar * Dstar
  let g62 := U * U
  let g63 := Delta * c2
  let g64 := 1 + g63
  let g65 := g62 * g64
  let A1 := g61 - g65
  let f := 1 + t
  let f2 := f * f
  let rho := f2 - 1
  let Q := Delta * rho
  let oneQ := 1 - Q
  let den := c2 * c2
  let g73 := T * c
  let g74 := g73 - R
  let g75 := f2 * g74
  let V := g75 - c
  let vn := V + n
  let vn2 := vn * vn
  let polarV2 := V * V
  let polarQV2 := Q * polarV2
  let polarCy := polarQV2 - 1
  let polarHpart := oneQ * vn2
  let h := polarHpart + polarCy
  let polarT := Q * oneQ
  let polarDh := den * h
  let polarA := polarDh - polarT
  let polarA2 := polarA * polarA
  let polarDT := den * polarT
  let polar4DT := 4 * polarDT
  let polarCorrection := polar4DT * polarCy
  let N := polarA2 + polarCorrection
  let g94 := 1 + A0
  let g95 := 1 + A1
  let g96 := g94 * g95
  let g97 := 1 + N
  let g98 := g96 * g97
  let P12 := g98 - 1
  -- END LITERAL GRAPH
  ⟨g94,g95,g97,P12,qm,Z,g41,U,a,c,Dstar,polarA,den,polarT,polarCy⟩

def literal (p : Fin 4 → ℤ) : Expr (Fin 12) := (core p).output

def polarized (a d t c : Expr (Fin 12)) : Expr (Fin 12) :=
  1+(a*a+((4*(d*t))*c))

private theorem polarized_mod : ∀ a d t c : ZMod 4,
    1+(a*a+((4*(d*t))*c)) ≠ -1 := by decide

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem polarized_ne (a d t c : Expr (Fin 12)) (v : Fin 12 → V) :
    (pairEval (polarized a d t c) v).1 + 1 ≠ (pairEval (polarized a d t c) v).2 := by
  intro h
  have hn := negative_residue h
  rw [pairEval_residue] at hn
  apply polarized_mod (syntaxEval (fun i => residue (v i)) a)
    (syntaxEval (fun i => residue (v i)) d) (syntaxEval (fun i => residue (v i)) t)
    (syntaxEval (fun i => residue (v i)) c)
  simpa only [polarized, syntax_add, syntax_mul, syntax_ofNat, Nat.cast_one, Nat.cast_ofNat] using hn

theorem first_eq (p : Fin 4 → ℤ) : (core p).first =
    firstPattern (core p).qm (core p).z (core p).n := by rfl

theorem main_eq (p : Fin 4 → ℤ) : (core p).main =
    mainPattern (core p).u (core p).a (core p).c (core p).d := by rfl

theorem ordinary_eq (p : Fin 4 → ℤ) : (core p).ordinary =
    polarized (core p).pa (core p).pd (core p).pt (core p).pc := by rfl

theorem literal_eq_factors (p : Fin 4 → ℤ) :
    literal p = (core p).first * (core p).main * (core p).ordinary - 1 := by rfl

theorem product_one_of_internal_zero (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (hz : InternalZero (literal p) v) :
    Equivalent (multiply (multiply (pairEval (core p).first v)
      (pairEval (core p).main v)) (pairEval (core p).ordinary v)) (natural (1:V)) := by
  rw [literal_eq_factors] at hz
  apply equivalent_one.mpr
  change (Expr.sub _ (Expr.constant 1)).splitNatural.1.evalSemiring v =
    (Expr.sub _ (Expr.constant 1)).splitNatural.2.evalSemiring v at hz
  simpa [Expr.splitNatural, NatExpr.evalSemiring, pairEval, multiply] using hz

theorem literal_factor_units (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (h : InternalZero (literal p) v) :
    (pairEval (core p).first v).1 = (pairEval (core p).first v).2 + 1 ∧
    (pairEval (core p).main v).1 = (pairEval (core p).main v).2 + 1 ∧
    (pairEval (core p).ordinary v).1 = (pairEval (core p).ordinary v).2 + 1 := by
  apply three_factor_units (product_one_of_internal_zero p v h)
  · rw [first_eq]; exact first_ne _ _ _ v
  · rw [main_eq]; exact main_ne _ _ _ _ v
  · rw [ordinary_eq]; exact polarized_ne _ _ _ _ v
end DiophantineConsistency.Ordinary12FreeJ
#print axioms DiophantineConsistency.Ordinary12FreeJ.polarized_ne
#print axioms DiophantineConsistency.Ordinary12FreeJ.first_eq
#print axioms DiophantineConsistency.Ordinary12FreeJ.main_eq
#print axioms DiophantineConsistency.Ordinary12FreeJ.ordinary_eq
#print axioms DiophantineConsistency.Ordinary12FreeJ.literal_eq_factors
#print axioms DiophantineConsistency.Ordinary12FreeJ.product_one_of_internal_zero
#print axioms DiophantineConsistency.Ordinary12FreeJ.literal_factor_units
