import DiophantineConsistency.CurrentWordScalarWitness2011

namespace DiophantineConsistency.CurrentWordScalarWitness2011Checks

open CurrentWordScalarWitness2011 CurrentWordClause2011 CurrentMasks2011

set_option Elab.async false
set_option maxRecDepth 10000

-- The positive witness includes a zero quotient; no A>=q-1 premise is hidden.
example : quotientWitness 10 4=1 := by decide
example : 4=4+(quotientWitness 10 4-1)*(10-1) :=
  quotient_transport (by decide) (by decide)
example : (4 : ℤ)+(10-4)-1*(10-1)=1 :=
  transport_factor_eq_one (q := 10) (A := 4) (F := 4) (z := 1)
    (by decide) (by decide) (by decide)

-- A nonzero quotient has the same exact successor convention.
example : quotientWitness 10 22=3 := by decide
example : 22=4+(quotientWitness 10 22-1)*(10-1) :=
  quotient_transport (by decide) (by decide)
example : (22 : ℤ)+(10-4)-3*(10-1)=1 :=
  transport_factor_eq_one (q := 10) (A := 22) (F := 4) (z := 3)
    (by decide) (by decide) (by decide)
example : (22 : ℤ)+(10-4)-2*(10-1)≠1 := by decide

-- Congruence alone would permit the excluded noncanonical representative.
example : 18 ≡ 9 [MOD 9] := by decide
example : 18%9≠9 := by decide
example : ¬ (9<10-1) := by decide

-- The signed unit factor is not a zero residual.
example {q A F z : ℕ} (hq : 0<q) (hz : 0<z)
    (ht : A=F+(z-1)*(q-1)) :
    (A : ℤ)+((q : ℤ)-F)-z*((q : ℤ)-1)≠0 := by
  rw [transport_factor_eq_one hq hz ht]
  decide

-- The prefix estimate is already enough at rho=9, while much smaller
-- radix values need not satisfy the requested strong slack.
example : 3*(2*1+1)<18 :=
  slack_of_prefix (q := 18) (C := 1) (F := 1) (P := 2) (ρ := 9)
    (by decide) (by decide) (by decide) (by decide)
example : ¬ (3*(2*99+99)<300) := by decide

-- N=1 and a stride of seventeen full periods are admitted. The constant
-- Start assignment is not supplied as a matching tableau.
example (dummy marker : ZMod 1 → ℕ)
    (hd : ∀ j, dummy j≤1) (hm : ∀ j, marker j≤1) :
    ∃ k digits : ZMod (1*2011) → ℕ,
      CurrentCarryConstruction2011.Facts
        (CurrentWordConstruction2011.word (fun _ => 0) dummy marker)
        (displacement 17) k digits ∧
      ScalarFacts (q 1) (source (fun _ : ZMod 1 => 0) dummy marker)
        (normalized digits) (multiplier 17)
        (alpha (q 1) (source (fun _ : ZMod 1 => 0) dummy marker) (normalized digits))
        (quotientWitness (q 1) ((CurrentKernel2011.K+multiplier 17)*
          source (fun _ : ZMod 1 => 0) dummy marker)) ∧
      (source (fun _ : ZMod 1 => 0) dummy marker-1) &&&
        (lowPort*NativeMaskPopulation.repunit width 1+1)=0 :=
  exists_scalar_witness (fun _ => 0) dummy marker hd hm rfl 17

-- Every reconstructed source is exactly q-F-alpha in signed arithmetic.
example {q C F w alpha z : ℕ} (h : ScalarFacts q C F w alpha z) :
    (q : ℤ)-F-alpha=C ∧
      ((CurrentKernel2011.K : ℤ)+w)*((q : ℤ)-F-alpha)+
        ((q : ℤ)-F)-z*((q : ℤ)-1)=1 := by
  exact ⟨h.signed_source_recovery,by rw [h.signed_source_recovery]; exact h.transport_unit⟩

#print axioms slack_of_prefix
#print axioms quotientWitness_pos
#print axioms quotient_transport
#print axioms transport_factor_eq_one
#print axioms q_pos
#print axioms q_prefix
#print axioms strong_slack
#print axioms scalar_witness
#print axioms exists_scalar_witness

end DiophantineConsistency.CurrentWordScalarWitness2011Checks
