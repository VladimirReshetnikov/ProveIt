import Direct80Graph

/-! Explicit row-register presentation for the ten-variable 80-row graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace TenPositive80DisplayedRows
open DiophantineConsistency AdaptiveEquationSyntax2011 TenPositive80Graph

def output_by_rows (p : Fin 4 → ℤ) : Expr (Fin 10) :=
  let a : Expr (Fin 10) := .var 0
  let b : Expr (Fin 10) := .var 1
  let c : Expr (Fin 10) := .var 2
  let d : Expr (Fin 10) := .var 3
  let e : Expr (Fin 10) := .var 4
  let f : Expr (Fin 10) := .var 5
  let g : Expr (Fin 10) := .var 6
  let h : Expr (Fin 10) := .var 7
  let i : Expr (Fin 10) := .var 8
  let j : Expr (Fin 10) := .var 9
  let port0 : Expr (Fin 10) := .constant (p 0)
  let port1 : Expr (Fin 10) := .constant (p 1)
  let port2 : Expr (Fin 10) := .constant (p 2)
  let port3 : Expr (Fin 10) := .constant (p 3)
  let r01 := port0 * a
  let r02 := r01 + 1
  let r03 := r02 * r02
  let r04 := r03 * r02
  let r05 := r04 * g
  let r06 := r02 - b
  let r07 := r06 - c
  let r08 := f * r02
  let r09 := i + j
  let r10 := r09 * r05
  let r11 := r10 + i
  let r12 := r03 + 1
  let r13 := r08 + 1
  let r14 := r12 * r05
  let r15 := r14 * r13
  let r16 := 4 * r15
  let r17 := r16 - 1
  let r18 := r15 + 2
  let r19 := r14 * r14
  let r20 := r08 * r19
  let r21 := r20 * r09
  let r22 := r21 + r09
  let r23 := r21 * r22
  let r24 := r23 + 1
  let r25 := r01 * r06
  let r26 := r25 + c
  let r27 := r03 - 1
  let r28 := r26 * r27
  let r29 := r02 * port3
  let r30 := port2 + r29
  let r31 := r30 * a
  let r32 := r28 + r31
  let r33 := r09 - r32
  let r34 := r33 - 1
  let r35 := port1 + f
  let r36 := r35 * r07
  let r37 := r36 - b
  let r38 := r11 * r11
  let r39 := d * r38
  let r40 := r39 * r24
  let r41 := r15 * r18
  let r42 := r41 * r40
  let r43 := r42 * r39
  let r44 := r43 + 1
  let r45 := r43 * r44
  let r46 := 4 * r45
  let r47 := r46 + 1
  let r48 := r41 * r46
  let r49 := r11 * e
  let r50 := r49 - r32
  let r51 := r47 * r50
  let r52 := r51 - r11
  let r53 := r52 * r52
  let r54 := r12 * r12
  let r55 := r01 * r54
  let r56 := r53 * r37
  let r57 := h - r56
  let r58 := r17 * r57
  let r59 := 3 * r11
  let r60 := 2 * r08
  let r61 := r59 - r60
  let r62 := r08 * r61
  let r63 := r62 + 2
  let r64 := r58 + r63
  let r65 := r55 * r64
  let r66 := r54 * r37
  let r67 := r01 * r34
  let r68 := r66 + r67
  let r69 := r17 * r68
  let r70 := r65 - r69
  let r71 := r55 * r17
  let r72 := r71 * r71
  let r73 := r24 * r44
  let r74 := r70 * r70
  let r75 := r72 * r73
  let r76 := r75 * r53
  let r77 := r74 - r76
  let r78 := r48 * r77
  let r79 := r75 - r74
  let r80 := r78 + r79
  r80

theorem output_eq (p : Fin 4 → ℤ) : output_by_rows p=(graph p).output := by rfl

#print axioms TenPositive80DisplayedRows.output_eq
end TenPositive80DisplayedRows
