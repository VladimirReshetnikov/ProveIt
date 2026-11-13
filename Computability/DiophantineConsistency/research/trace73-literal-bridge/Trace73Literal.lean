import Trace73CenterV2

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace73Literal
variable {R : Type*} [CommRing R]

def graph73 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let g01 := (p 0) * (v 0)
  let g02 := g01 + 1
  let g03 := g02 * g02
  let g04 := g03 * g02
  let g05 := g04 * (v 6)
  let g06 := g02 - (v 1)
  let g07 := g06 - (v 2)
  let g08 := (v 5) * g02
  let g09 := (v 8) + (v 9)
  let g10 := g09 * g05
  let g11 := g10 + (v 8)
  let g12 := g08 * g05
  let g13 := g12 + g05
  let g14 := 4 * g13
  let g15 := g14 - 1
  let g16 := g13 + 2
  let g17 := g12 * g10
  let g18 := g17 + g09
  let g19 := g17 * g18
  let g20 := g19 + 1
  let g21 := g01 * g06
  let g22 := g21 + (v 2)
  let g23 := g03 - 1
  let g24 := g22 * g23
  let g25 := g02 * (p 3)
  let g26 := (p 2) + g25
  let g27 := g26 * (v 0)
  let g28 := g24 + g27
  let g29 := g09 - g28
  let g30 := g29 - 1
  let g31 := (p 1) + (v 5)
  let g32 := g31 * g07
  let g33 := g32 - (v 1)
  let g34 := g11 * g11
  let g35 := (v 3) * g34
  let g36 := g35 * g20
  let g37 := g13 * g16
  let g38 := g37 * g36
  let g39 := g38 * g35
  let g40 := g39 + 1
  let g41 := g39 * g40
  let g42 := 4 * g41
  let g43 := g39 + g40
  let g44 := g37 * g42
  let g45 := g11 * (v 4)
  let g46 := g45 - g28
  let g47 := g43 * g46
  let g48 := g47 - g11
  let g49 := g48 * g48
  let g50 := g01 * g12
  let g51 := g15 * (v 7)
  let g52 := 3 * g11
  let g53 := 2 * g08
  let g54 := g52 - g53
  let g55 := g08 * g54
  let g56 := g55 + 2
  let g57 := g51 + g56
  let g58 := g50 * g57
  let g59 := g12 * g33
  let g60 := g01 * g30
  let g61 := g59 + g60
  let g62 := g15 * g61
  let g63 := g58 - g62
  let g64 := g50 * g15
  let g65 := g64 * g64
  let g66 := g20 * g40
  let g67 := g63 * g63
  let g68 := g65 * g66
  let g69 := g68 * g49
  let g70 := g67 - g69
  let g71 := g44 * g70
  let g72 := g68 - g67
  let g73 := g71 + g72
  g73

theorem literal_eq (p : Fin 4 → R) (v : Fin 10 → R) :
    graph73 p v = Trace73Center.value73 p v := by
  rfl

theorem parent_substitution (p : Fin 4 → R) (v : Fin 10 → R) :
    DiophantineConsistency.TenPositiveTrace75.value75 p (Trace73Center.lift p v) = graph73 p v := by
  rw [Trace73Center.substitution, literal_eq]

#print axioms Trace73Literal.literal_eq
#print axioms Trace73Literal.parent_substitution
end Trace73Literal
