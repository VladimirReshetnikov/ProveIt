module
public import M6PA.Theory
public import PA196.Arithmetic.Transport.FoundationRelationalSequentHighVacuity
public import PA196.Arithmetic.Transport.ActualCertificateSeparationRaw
public import PA196.Arithmetic.Certificates.Interface
@[expose] public section
open M6.PA PA196.Arithmetic
open PA196.Arithmetic.Certificates.Logic
open M6.PA.RelationalSource
open M6.PA.RelationalSource.Numeric


/-! Raw numeric separation for an arbitrary covered source property. Padding
is above the fixed reserve; source parameters are not changed circularly. -/
namespace PA196.Arithmetic.Transport.RelationalSource.Numeric
open FFL FFL.FirstOrder FFL.FirstOrder.Arithmetic
open scoped FFL.FirstOrder.Arithmetic FFL.FirstOrder.Bounding
open PA196.Arithmetic.Certificates PA196.Arithmetic.Certificates.Dominated
open ActualCertificateEquivalence PA196.Arithmetic.Checker
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁] [V↓[ℒₒᵣ] ⊧* theory]

noncomputable def separationPadding (a b z property : V) : V :=
  wal (z+1) (wa (wel a b) property)

theorem separationPadding_above (a b z property : V) : z<separationPadding a b z property :=
  lt_trans (lt_add_one z) (padding_code_above (z+1) _)

theorem covered_raw_separation (p a d b f lo z : V) (hc : FormulaCovered b f lo z p)
    (ha : a≤z) (hd : d≤z) :
    ∃ code, verifyValue code=separationValue a d
      (separationPadding a d z (translate (parameters b f lo z) p))
      (translate (parameters b f lo z) p)+1 := by
  obtain ⟨cv,hcv⟩ := formula_high_vacuity_certificate p (z+1) b f lo z hc (lt_add_one z)
  have hxa : z+1≠a := Ne.symm (ne_of_lt (lt_of_le_of_lt ha (lt_add_one z)))
  have hxd : z+1≠d := Ne.symm (ne_of_lt (lt_of_le_of_lt hd (lt_add_one z)))
  let hv := conjunctionVacuity (z+1) (wel a d) (translate (parameters b f lo z) p)
    (membershipVacuity a d (z+1) hxa hxd) ⟨cv,hcv⟩
  let out := paddedSeparationAbove a d (translate (parameters b f lo z) p) (z+1)
    (le_trans ha (by simp)) (le_trans hd (by simp)) hv
  exact ⟨out.code,out.accepted⟩

/-- The same original property is vacuous at the actual padded output code.
This follows from the numeric bound, not an external Named freshness claim. -/
theorem covered_padding_vacuity (p a d b f lo z : V) (hc : FormulaCovered b f lo z p) :
    ∃ code, verifyValue code=wim (translate (parameters b f lo z) p)
      (wal (separationPadding a d z (translate (parameters b f lo z) p))
        (translate (parameters b f lo z) p))+1 :=
  formula_high_vacuity_certificate p _ b f lo z hc (separationPadding_above a d z _)

#print axioms separationPadding_above
#print axioms covered_raw_separation
#print axioms covered_padding_vacuity
end PA196.Arithmetic.Transport.RelationalSource.Numeric

