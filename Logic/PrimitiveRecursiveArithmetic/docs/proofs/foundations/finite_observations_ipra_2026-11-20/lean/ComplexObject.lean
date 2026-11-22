import IPRADerivations.Core.Integers

/-! Oriented strips in object-language iPRA. The path fixes the finite
syntax externally. Every incidence evaluation is an arbitrary pair of
ordinary object terms and can contain any of the n free variables. -/
namespace ResidueObject
open LeanProofs.ConciseIPRA LeanProofs.IPRA
open scoped Fm Prf

variable {V : Type} {n : Nat}

def triangle (E : V → V → ZT n) (a b c : V) : ZT n :=
  E a b + E b c - E a c

def panel (E : V → V → ZT n) (p q : V × V) : ZT n :=
  triangle E p.1 q.1 q.2 - triangle E p.1 p.2 q.2

def edges (E : V → V → ZT n) (f : V × V → V) (p : V × V) :
    List (V × V) → ZT n
  | [] => ZT.natLit 0
  | q :: qs => E (f p) (f q) + edges E f q qs

def panels (E : V → V → ZT n) (p : V × V) : List (V × V) → ZT n
  | [] => ZT.natLit 0
  | q :: qs => panel E p q + panels E q qs

def endpoint (p : V × V) : List (V × V) → V × V
  | [] => p
  | q :: qs => endpoint q qs

variable (Γ : List (Fm PTm n)) (E : V → V → ZT n)

private theorem strip_eq (p : V × V) (rest : List (V × V)) :
    ZT.toZ Γ (panels E p rest) =
      ZT.toZ Γ (edges E Prod.fst p rest) - ZT.toZ Γ (edges E Prod.snd p rest)
        + ZT.toZ Γ (E (endpoint p rest).1 (endpoint p rest).2)
        - ZT.toZ Γ (E p.1 p.2) := by
  induction rest generalizing p with
  | nil => simp [panels, edges, endpoint]
  | cons q qs ih =>
    simp only [panels, edges, endpoint, panel, triangle,
      ZT.toZ_add, ZT.toZ_sub, ih q]
    ring

/-- The exposed boundary of a finite strip, including connector end edges. -/
theorem strip_boundary (p : V × V) (rest : List (V × V)) :
    Γ ⊢[PRAAx] ZT.eq (panels E p rest)
      (edges E Prod.fst p rest - edges E Prod.snd p rest
        + E (endpoint p rest).1 (endpoint p rest).2 - E p.1 p.2) := by
  apply ZT.derive
  simp only [ZT.toZ_sub, ZT.toZ_add]
  exact strip_eq Γ E p rest

/-- For a closed strip only the lower path minus the upper path remains. -/
theorem closed_strip (p : V × V) (rest : List (V × V))
    (closed : endpoint p rest = p) :
    Γ ⊢[PRAAx] ZT.eq (panels E p rest)
      (edges E Prod.fst p rest - edges E Prod.snd p rest) := by
  apply ZT.derive
  rw [strip_eq, closed, ZT.toZ_sub]
  ring

/-- The eight signed triangles between the two square contours. -/
theorem square_strip (p₀ p₁ p₂ p₃ : V × V) :
    Γ ⊢[PRAAx] ZT.eq (panels E p₀ [p₁,p₂,p₃,p₀])
      (edges E Prod.fst p₀ [p₁,p₂,p₃,p₀] - edges E Prod.snd p₀ [p₁,p₂,p₃,p₀]) :=
  closed_strip Γ E p₀ [p₁,p₂,p₃,p₀] rfl

#print axioms strip_boundary
#print axioms closed_strip
#print axioms square_strip
end ResidueObject
