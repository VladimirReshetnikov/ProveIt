import DiophantineConsistency.Compact44.IPRAOrdinary72

/-! # Package 72's P14: fourteen positive unknowns, degree 24, 101 operations

`72-congruence-sextic/positive14/p14_degree24.json` lifts P13's register
`E = XY` to a fourteenth positive input, and adds the residual `AE = E − XY`.
Its output is P13's `A0² + A1² + Aa² + As²` plus `AE²`. The gate block is
generated from the pinned JSON by
`research/ordinary13-p72-endpoint/tools/generate_p14.py`, which also checks it.

At a valuation with `E = XY`, the four P13 residuals evaluate exactly as P13's
at the first thirteen coordinates. Hence, in every model of `𝗜𝚺₁`, P14 has a
positive zero iff P13 has one, iff machine 215 halts. The iPRA endpoints
follow as for P13. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
noncomputable section
namespace P72P14
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open AdaptiveEquationSyntax2011 ModelDifferenceRing

structure Graph where
  A0 : Expr (Fin 14)
  A1 : Expr (Fin 14)
  Aa : Expr (Fin 14)
  As : Expr (Fin 14)
  AE : Expr (Fin 14)
  output : Expr (Fin 14)

set_option linter.unusedVariables false in
def graph (p : Fin 4 → ℤ) : Graph :=
  let F : Expr (Fin 14) := .var 0
  let alpha : Expr (Fin 14) := .var 1
  let C : Expr (Fin 14) := .var 2
  let f0 : Expr (Fin 14) := .var 3
  let i : Expr (Fin 14) := .var 4
  let T : Expr (Fin 14) := .var 5
  let X : Expr (Fin 14) := .var 6
  let Y : Expr (Fin 14) := .var 7
  let r : Expr (Fin 14) := .var 8
  let eta : Expr (Fin 14) := .var 9
  let zeta : Expr (Fin 14) := .var 10
  let u : Expr (Fin 14) := .var 11
  let gamma : Expr (Fin 14) := .var 12
  let E : Expr (Fin 14) := .var 13
  let beta : Expr (Fin 14) := .constant (p 0)
  let K0 : Expr (Fin 14) := .constant (p 1)
  let MC : Expr (Fin 14) := .constant (p 2)
  let MF : Expr (Fin 14) := .constant (p 3)
  -- BEGIN LITERAL GRAPH
  let B : Expr (Fin 14) := .constant ((p 0) + 1)
  let b : Expr (Fin 14) := .constant (3 * (p 0))
  let b2 : Expr (Fin 14) := .constant ((3 * (p 0)) * (3 * (p 0)))
  let L : Expr (Fin 14) := .constant ((p 0) * ((3 * (p 0)) * (3 * (p 0))))
  let Kfinal : Expr (Fin 14) := .constant (((3 * (p 0)) * (3 * (p 0))) * (((p 0) * ((3 * (p 0)) * (3 * (p 0)))) * ((p 0) * ((3 * (p 0)) * (3 * (p 0))))))
  let four_beta : Expr (Fin 14) := .constant (4 * (p 0))
  let qF := C + alpha
  let q := F + qF
  let qm := q - 1
  let q2 := q * q
  let q3 := q * q2
  let k := eta + zeta
  let kY := Y * k
  let c := eta + kY
  let c2 := c * c
  let Eprod := X * Y
  let a := E + Y
  let g11 := 4 * a
  let H := 3 + g11
  let g13 := a * a
  let Delta := H + g13
  let ell := E * kY
  let ac := a * c
  let b0 := X + ac
  let g18 := b * f0
  let g19 := q - B
  let nF := g18 + g19
  let f2 := nF * nF
  let f2m := f2 - b2
  let I := c2 * i
  let g24 := I * I
  let g25 := Delta * g24
  let g26 := b2 * g25
  let As := f2m - g26
  let g28 := qF * qm
  let G := alpha + g28
  let g30 := q2 - 1
  let g31 := G * g30
  let g32 := beta * g31
  let g33 := MF * q
  let g34 := MC + g33
  let g35 := g34 * qm
  let Rhat := g32 + g35
  let M0 := q3 * qm
  let g38 := K0 * q
  let g39 := X + g38
  let g40 := C * g39
  let g41 := F * q
  let Bt := g40 - g41
  let g43 := ell + r
  let g44 := M0 * g43
  let g45 := Y * qm
  let g46 := g44 + g45
  let g47 := Bt * q3
  let Z := g46 - g47
  let g49 := ell + k
  let g50 := ell * g49
  let rad0 := 1 + g50
  let g52 := Z * Z
  let g53 := M0 * M0
  let g54 := g53 * rad0
  let A0 := g52 - g54
  let g56 := Y * q
  let Sb := four_beta * g56
  let Mb := Sb * q
  let g59 := Mb * gamma
  let g60 := Sb * X
  let g61 := g59 + g60
  let g62 := k - 1
  let g63 := beta * g62
  let g64 := g61 - g63
  let shift := Rhat + g64
  let g66 := Mb * b0
  let g67 := H * shift
  let Dhat := g66 + g67
  let g69 := Dhat * Dhat
  let g70 := Mb * Mb
  let g71 := Delta * c2
  let g72 := 1 + g71
  let g73 := g70 * g72
  let A1 := g69 - g73
  let g75 := beta * c
  let g76 := T * g75
  let g77 := g76 - Rhat
  let g78 := f2 * g77
  let g79 := L * c
  let Vhat := g78 - g79
  let g81 := L * u
  let yhat := Vhat + g81
  let yhat2 := yhat * yhat
  let g84 := b2 * yhat2
  let g85 := Delta * f2m
  let g86 := Vhat * Vhat
  let g87 := yhat2 - g86
  let g88 := g85 * g87
  let g89 := g84 - g88
  let Aa := g89 - Kfinal
  let AE := E - Eprod
  let g91 := A0 * A0
  let g92 := A1 * A1
  let g93 := g91 + g92
  let g94 := Aa * Aa
  let g95 := g93 + g94
  let g96 := As * As
  let g97 := g95 + g96
  let AE2 := AE * AE
  let P14 := g97 + AE2
  -- END LITERAL GRAPH
  ⟨A0, A1, Aa, As, AE, P14⟩

theorem output_eq (p : Fin 4 → ℤ) : (graph p).output =
    (graph p).A0 * (graph p).A0 + (graph p).A1 * (graph p).A1 +
      (graph p).Aa * (graph p).Aa + (graph p).As * (graph p).As + (graph p).AE * (graph p).AE := by
  rfl

section Ring
variable {R : Type*}

/-- The first thirteen coordinates. -/
def drop (w : Fin 14 → R) : Fin 13 → R := fun j => w j.castSucc

@[simp] theorem drop_0 (w : Fin 14 → R) : drop w 0 = w 0 := rfl
@[simp] theorem drop_1 (w : Fin 14 → R) : drop w 1 = w 1 := rfl
@[simp] theorem drop_2 (w : Fin 14 → R) : drop w 2 = w 2 := rfl
@[simp] theorem drop_3 (w : Fin 14 → R) : drop w 3 = w 3 := rfl
@[simp] theorem drop_4 (w : Fin 14 → R) : drop w 4 = w 4 := rfl
@[simp] theorem drop_5 (w : Fin 14 → R) : drop w 5 = w 5 := rfl
@[simp] theorem drop_6 (w : Fin 14 → R) : drop w 6 = w 6 := rfl
@[simp] theorem drop_7 (w : Fin 14 → R) : drop w 7 = w 7 := rfl
@[simp] theorem drop_8 (w : Fin 14 → R) : drop w 8 = w 8 := rfl
@[simp] theorem drop_9 (w : Fin 14 → R) : drop w 9 = w 9 := rfl
@[simp] theorem drop_10 (w : Fin 14 → R) : drop w 10 = w 10 := rfl
@[simp] theorem drop_11 (w : Fin 14 → R) : drop w 11 = w 11 := rfl
@[simp] theorem drop_12 (w : Fin 14 → R) : drop w 12 = w 12 := rfl

variable [CommRing R]

theorem AE_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) : (graph p).AE.evalRing w = w 13 - w 6 * w 7 := by
  simp only [graph, Expr.evalRing_sub, Expr.evalRing_mul, Expr.evalRing_var]

theorem residuals_eval (p : Fin 4 → ℤ) (w : Fin 14 → R) (hE : w 13 = w 6 * w 7) :
    (graph p).A0.evalRing w = (P72Graph.graph p).A0.evalRing (drop w) ∧
    (graph p).A1.evalRing w = (P72Graph.graph p).A1.evalRing (drop w) ∧
    (graph p).Aa.evalRing w = (P72Graph.graph p).Aa.evalRing (drop w) ∧
    (graph p).As.evalRing w = (P72Graph.graph p).As.evalRing (drop w) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp only [graph, P72Graph.graph, Expr.evalRing_add, Expr.evalRing_sub, Expr.evalRing_mul,
      Expr.evalRing_var, Expr.evalRing_constant, Expr.evalRing_ofNat, drop_0, drop_1, drop_2, drop_3,
      drop_4, drop_5, drop_6, drop_7, drop_8, drop_9, drop_10, drop_11, drop_12, hE]

end Ring

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

private theorem five_squares {a b c d e : DiffRing V} :
    a * a + b * b + c * c + d * d + e * e = 0 ↔ a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  constructor
  · intro h
    have ha := mul_self_nonneg a; have hb := mul_self_nonneg b; have hc := mul_self_nonneg c
    have hd := mul_self_nonneg d; have he := mul_self_nonneg e
    refine ⟨mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith),
      mul_self_eq_zero.mp (by linarith), mul_self_eq_zero.mp (by linarith),
      mul_self_eq_zero.mp (by linarith)⟩
  · rintro ⟨rfl, rfl, rfl, rfl, rfl⟩; ring

/-- A P14 zero is a P13 zero of the first thirteen coordinates with `E = XY`. -/
theorem zero_iff (p : Fin 4 → ℤ) (v : Fin 14 → V) :
    InternalZero (graph p).output v ↔
      v 13 = v 6 * v 7 ∧ InternalZero (P72Graph.graph p).output (fun j => v j.castSucc) := by
  rw [internalZero_iff, output_eq, P72Graph.zero_iff, internalZero_iff, internalZero_iff,
    internalZero_iff, internalZero_iff]
  simp only [Expr.evalRing_add, Expr.evalRing_mul]
  rw [five_squares, AE_eval]
  constructor
  · rintro ⟨h0, h1, ha, hs, hE⟩
    have hEι : ι (v 13) = ι (v 6) * ι (v 7) := by linear_combination hE
    have hE' : v 13 = v 6 * v 7 := ι_injective (by rw [map_mul]; exact hEι)
    obtain ⟨e0, e1, ea, es⟩ := residuals_eval p (fun j => ι (v j)) hEι
    exact ⟨hE', e0 ▸ h0, e1 ▸ h1, ea ▸ ha, es ▸ hs⟩
  · rintro ⟨hE', h0, h1, ha, hs⟩
    have hEι : ι (v 13) = ι (v 6) * ι (v 7) := by rw [hE', map_mul]
    obtain ⟨e0, e1, ea, es⟩ := residuals_eval p (fun j => ι (v j)) hEι
    exact ⟨e0.trans h0, e1.trans h1, ea.trans ha, es.trans hs, by rw [hEι]; ring⟩

end P72P14

namespace DiophantineConsistency.IPRAOrdinary72P14
open LO LO.FirstOrder LO.FirstOrder.Arithmetic LO.Entailment
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 HAExpressionAssembly
open PRALanguage IPRANativeTheory IPRAFoundationZFCMappedNegation
open IPRAOrdinary12 (PositiveModelBridge)
open IPRAOrdinary12Chain (native_of_positive standard_of_positive reference_of_positive)
open CompactSymbolicKernel CompactSymbolicKernelOpaque CompactSymbolicPorts
attribute [local irreducible] paramKernel rho CompactFixedBeta.betaNat lowNat highNat

def expression : Expr (Fin 14) :=
  (P72P14.graph (CompactSymbolicPortProjections.portsInt (paramKernel rho))).output

theorem positiveBridge : PositiveModelBridge expression := by
  intro V _ _
  refine Iff.trans ?_ (IPRAOrdinary72.positiveBridge V)
  constructor
  · rintro ⟨v, hv, hz⟩
    obtain ⟨_, hz'⟩ := (P72P14.zero_iff _ v).mp hz
    exact ⟨fun j => v j.castSucc, fun j => hv _, hz'⟩
  · rintro ⟨v, hv, hz⟩
    let w : Fin 14 → V := ![v 0, v 1, v 2, v 3, v 4, v 5, v 6, v 7, v 8, v 9, v 10, v 11, v 12,
      v 6 * v 7]
    have hw : (fun j : Fin 13 => w j.castSucc) = v := by funext j; fin_cases j <;> rfl
    refine ⟨w, ?_, (P72P14.zero_iff _ w).mpr ⟨rfl, by rw [hw]; exact hz⟩⟩
    intro j
    fin_cases j
    exacts [hv 0, hv 1, hv 2, hv 3, hv 4, hv 5, hv 6, hv 7, hv 8, hv 9, hv 10, hv 11, hv 12,
      mul_pos (hv 6) (hv 7)]

theorem native_equivalence : nativeTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  native_of_positive _ positiveBridge
theorem standard_equivalence : IPRAStandardTheory.standardTheory ⊢
    IPRAExpressionNative.nativeNoZero (positiveShift expression) 🡘
      ∼mappedNativeRefutation embedding :=
  standard_of_positive _ positiveBridge
theorem reference_equivalence : IPRAEqualityOnlyReference.referenceTheory ⊢
    IPRAOrderErasure.erase (IPRAExpressionNative.nativeNoZero (positiveShift expression)) 🡘
      ∼IPRAOrderErasure.erase (mappedNativeRefutation embedding) :=
  reference_of_positive _ positiveBridge

#print axioms P72P14.zero_iff
#print axioms positiveBridge
#print axioms native_equivalence
#print axioms standard_equivalence
#print axioms reference_equivalence

end DiophantineConsistency.IPRAOrdinary72P14
