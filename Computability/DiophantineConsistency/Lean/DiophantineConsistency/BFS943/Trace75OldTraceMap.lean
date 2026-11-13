import DiophantineConsistency.TenPositiveTrace75

/-! Squared-to-linear trace substitution as an identity over any commutative ring. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace75OldTraceMap
open DiophantineConsistency.TenPositiveTrace75
variable {R : Type*} [CommRing R]

def shift (p : Fin 4 → R) (v : Fin 10 → R) : Fin 10 → R :=
  let r := regs p v
  let d := 2*r.Delta*(v 3)^2*r.c^3*r.E
  Function.update v 4 (r.f*v 4-d*r.rank)

def oldV (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  r.f*r.f*r.b-r.c

def oldZ (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  let V := oldV p v
  r.h*r.D*(r.H*(v 7-V*V*r.B)+r.K)-r.H*(r.D*r.B+r.h*r.e)

def oldValue (p : Fin 4 → R) (v : Fin 10 → R) : R :=
  let r := regs p v
  let V := oldV p v
  let Z := oldZ p v
  r.Q*(Z*Z-r.M*r.M*r.Gn*(V*V))+(r.M*r.M*r.Gn-Z*Z)

theorem V_shift (p : Fin 4 → R) (v : Fin 10 → R) :
    (regs p (shift p v)).V = oldV p v := by
  let r := regs p v
  let d := 2*r.Delta*(v 3)^2*r.c^3*r.E
  have hshape : r.f = 1+r.c*d := f_one_mod_c p v
  change r.f*(r.c*(r.f*v 4-d*r.rank)-r.rank)-r.c =
    r.f*r.f*(r.c*v 4-r.rank)-r.c
  rw [hshape]
  ring

theorem Z_shift (p : Fin 4 → R) (v : Fin 10 → R) :
    (regs p (shift p v)).Z = oldZ p v := by
  have hV := V_shift p v
  change (regs p v).h*(regs p v).D*((regs p v).H*(v 7-
      (regs p (shift p v)).V*(regs p (shift p v)).V*(regs p v).B)+(regs p v).K)-
      (regs p v).H*((regs p v).D*(regs p v).B+(regs p v).h*(regs p v).e) = oldZ p v
  rw [hV]
  rfl

theorem value_shift (p : Fin 4 → R) (v : Fin 10 → R) :
    value75 p (shift p v) = oldValue p v := by
  simp only [value75,oldValue]
  rw [Z_shift,V_shift]
  have hQ : (regs p (shift p v)).Q = (regs p v).Q := rfl
  have hM : (regs p (shift p v)).M = (regs p v).M := rfl
  have hG : (regs p (shift p v)).Gn = (regs p v).Gn := rfl
  rw [hQ,hM,hG]

#print axioms Trace75OldTraceMap.value_shift
end Trace75OldTraceMap
