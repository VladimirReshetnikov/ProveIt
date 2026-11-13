module
public import M6.Source.AXSymbolicResult
public import M6.Source.ActualAXCode
@[expose] public section
namespace M6.Source.AXSymbolic

def valuation (t c d h y x : Nat) : Fin 6 → Nat := fun i => [t,c,d,h,y,x][i.val]!

theorem actual_spec (t c d h y x tail : Nat) :
    materialize (valuation t c d h y x) tail actualResult =
      ⟨ActualAXCode.bundle (d+x) (h+y) c,c,d+x,h+y,tail,
        ActualAXCode.pa135Heads (d+x) (h+y) c d h ++ [t]⟩ := by rfl

/-- Exact natural evaluation of the proposed macro program. It is not yet
an execution theorem for the whole primitive-source AX block. -/
theorem macro_actual (t c d h y x tail : Nat) :
    AXMacro.run AXMacro.program ⟨t,c,d,h,Cantor.pair y (Cantor.pair x tail),[]⟩ =
      some ⟨ActualAXCode.bundle (d+x) (h+y) c,c,d+x,h+y,tail,
        ActualAXCode.pa135Heads (d+x) (h+y) c d h ++ [t]⟩ := by
  have hh := run_sound AXMacro.program initial actualResult program_actual
    (valuation t c d h y x) tail
  rw [actual_spec] at hh
  exact hh

#print axioms actual_spec
#print axioms macro_actual
end M6.Source.AXSymbolic

