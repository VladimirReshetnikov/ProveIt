import DiophantineConsistency.Carrier66Source

/-!
# Focused audit of the canonical parent-to-source bridge

The complete coordinate order is fixed below. The two auxiliary coordinate
checks prevent the tempting substitutions x8=f*T and x6=i. The row identities
are checked over arbitrary commutative rings by the imported theorem; the
positivity and arithmetic-window endpoints are audited for their axiom sets.
-/

namespace DiophantineConsistency.Carrier66SourceChecks

open Carrier66Source

example (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) :
    source p v =
      let b := Carrier66.core p v
      ![v 0,v 1,v 2,v 3,v 4,v 5,v 6*b.delta,v 4*auxGap p v,
        v 7+b.delta*(v 6)^2*b.c^3*auxGap p v-1,v 8,v 9,v 10,v 11,v 12,v 13,v 14,
        b.q^3,b.E,b.ell+b.k,b.c,b.a,b.X,b.D,b.c^2,b.q^2-1,(v 4)^2,b.V,
        (v 13)^2-b.V^2,b.S,b.S^2,b.delta] := by
  funext j
  fin_cases j <;> rfl

example (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) :
    (Carrier66.core p v).c*source p v 8-source p v 26 =
      (Carrier66.core p v).rank-strongError p v*auxGap p v := by
  have h := rank_identity p v
  linear_combination h

example (p : Fin 4 → ℤ) (v : Fin 15 → ℤ) :
    source p v 6 = v 6*(Carrier66.core p v).delta ∧
    source p v 3 = v 3 ∧ source p v 12 = v 11 ∧ source p v 13 = v 12 := by
  exact ⟨rfl,rfl,rfl,rfl⟩

example {R : Type*} [CommRing R] (p : Fin 4 → R) (v : Fin 15 → R) :
    SplitCertificate59.sourceRows p (source p v) 12 =
      Carrier66.index p v-1+strongError p v*auxGap p v := row_formula p v 12

example {R : Type*} [CommRing R] (p : Fin 4 → R) (v : Fin 15 → R) :
    SplitCertificate59.sourceRows p (source p v) 20 =
      -(Carrier66.core p v).delta*strongError p v := row_formula p v 20

/-- These positive inputs are deliberately not canonical: the old auxiliary
slot is not f*T, and the restored V need not be positive without the norms. -/
example : source ![1,1,1,1] (fun _ => (1:ℤ)) 6 = 675 ∧
    source ![1,1,1,1] (fun _ => (1:ℤ)) 8 = 26530200 ∧
    source ![1,1,1,1] (fun _ => (1:ℤ)) 26 = -9 := by
  decide

#print axioms row_formula
#print axioms canonical_strong_error
#print axioms canonical_rows
#print axioms source_pos
#print axioms sourceNat_rows
#print axioms canonical_window
#print axioms positive_carrier_zero_source

end DiophantineConsistency.Carrier66SourceChecks
