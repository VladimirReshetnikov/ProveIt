import MoserWorm.Common.Interval.Basic

/-! Outward dyadic enclosures of rational constants. -/

namespace MoserWorm.DIval

def ratio (num den : Int) : DIval :=
  ⟨(num * dfxOne).fdiv den, -((-num * dfxOne).fdiv den)⟩

end MoserWorm.DIval
