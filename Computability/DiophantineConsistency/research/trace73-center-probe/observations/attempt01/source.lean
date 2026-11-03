import DiophantineConsistency.TenPositiveTrace75

/-! Exact all-ring 75-to-73 center substitution; positivity is separate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace73Center
open DiophantineConsistency.TenPositiveTrace75
variable {R : Type*} [CommRing R]

def centerZ (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  r.h*r.D*(r.H*(v 7)+r.K)-r.H*(r.D*r.B+r.h*r.e)

def value73 (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  let Z := centerZ p v
  r.Q*(Z*Z-r.M*r.M*r.Gn*(r.V*r.V))+(r.M*r.M*r.Gn-Z*Z)

def lift (p : Fin 4 → R) (v : Fin 10 → R) : Fin 10 → R :=
  let r := regs p v
  ![v 0,v 1,v 2,v 3,v 4,v 5,v 6,v 7+r.V*r.V*r.B,v 8,v 9]

theorem centerZ_shift (p : Fin 4 → R) (v : Fin 10 → R) :
    (regs p (lift p v)).Z = centerZ p v := by
  let r := regs p v
  have hc : (v 7+r.V*r.V*r.B)-r.V*r.V*r.B=v 7 := by ring
  change r.h*r.D*(r.H*((v 7+r.V*r.V*r.B)-r.V*r.V*r.B)+r.K)-r.H*(r.D*r.B+r.h*r.e) =
    r.h*r.D*(r.H*(v 7)+r.K)-r.H*(r.D*r.B+r.h*r.e)
  rw [hc]

theorem substitution (p : Fin 4 → R) (v : Fin 10 → R) :
    value75 p (lift p v) = value73 p v := by
  unfold value75 value73
  rw [centerZ_shift]
  rfl

#print axioms Trace73Center.centerZ_shift
#print axioms Trace73Center.substitution
end Trace73Center
