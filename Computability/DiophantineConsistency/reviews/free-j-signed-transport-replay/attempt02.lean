import DiophantineConsistency.ModelDifferenceRing
import DiophantineConsistency.FreeJNormZero
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace FreeJOrdinaryTransport
open DiophantineConsistency
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency.AdaptiveEquationSyntax2011
open DiophantineConsistency.ModelDifferenceRing
open DiophantineConsistency.Ordinary12FreeJ
open FreeJNormZero

structure Parts where
  q : Expr (Fin 12)
  d : Expr (Fin 12)
  z : Expr (Fin 12)
  n : Expr (Fin 12)

set_option linter.unusedVariables false in
def parts (p : Fin 4 → ℤ) : Parts :=
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
  ⟨Q,den,V,n⟩

def polarizedExpr {σ : Type*} (q d z n : Expr σ) : Expr σ :=
  let w := z+n
  let p := 1-q
  let cy := q*(z*z)-1
  let h := p*(w*w)+cy
  let A := d*h-q*p
  A*A + (4*(d*(q*p)))*cy

theorem graph_residual_shape (p : Fin 4 → ℤ) : ordinaryResidual p =
    polarizedExpr (parts p).q (parts p).d (parts p).z (parts p).n := by rfl

theorem polarized_eval {σ R : Type*} [CommRing R] (q d z n : Expr σ) (v : σ → R) :
    (polarizedExpr q d z n).evalRing v =
      let w := z.evalRing v+n.evalRing v
      let p := 1-q.evalRing v
      let cy := q.evalRing v*z.evalRing v*z.evalRing v-1
      let h := p*w*w+cy
      let A := d.evalRing v*h-q.evalRing v*p
      A*A+4*d.evalRing v*q.evalRing v*p*cy := by
  simp only [polarizedExpr, Expr.evalRing]
  simp only [Expr.evalRing]
  ring

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem actual_unpolarized_zero (p : Fin 4 → ℤ) (v : Fin 12 → V)
    (hz : InternalZero (literal p) v) :
    let ev := fun e : Expr (Fin 12) => e.evalRing (fun i => ι (v i))
    let q := ev (parts p).q
    let d := ev (parts p).d
    let z := ev (parts p).z
    let n := ev (parts p).n
    let w := n+z
    let r := 1-q
    let h := r*w*w+q*z*z-1
    let b := 2*r*w
    let A := d*h+q*r
    A*A-d*q*b*b=0 := by
  have hzero := (internalZero_iff (ordinaryResidual p) v).mp (ordinary_residual_zero p v hz)
  rw [graph_residual_shape,polarized_eval] at hzero
  have hpol := polarization_identity
    ((parts p).q.evalRing (fun i => ι (v i)))
    ((parts p).d.evalRing (fun i => ι (v i)))
    ((parts p).z.evalRing (fun i => ι (v i)))
    ((parts p).n.evalRing (fun i => ι (v i)))
  dsimp only at hpol ⊢ hzero
  have hh : _ := hpol
  convert hh.trans (show _ = 0 by convert hzero using 1 <;> ring) using 1 <;> ring
end FreeJOrdinaryTransport
#print axioms FreeJOrdinaryTransport.graph_residual_shape
#print axioms FreeJOrdinaryTransport.polarized_eval
#print axioms FreeJOrdinaryTransport.actual_unpolarized_zero
