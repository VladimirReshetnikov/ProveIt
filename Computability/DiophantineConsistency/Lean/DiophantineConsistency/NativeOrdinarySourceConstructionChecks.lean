import DiophantineConsistency.NativeOrdinarySourceConstruction
set_option Elab.async false

namespace DiophantineConsistency.NativeOrdinarySourceConstructionChecks
open NativeOrdinarySourceConstruction NativePellBootstrap NativeBinaryScale

/-- The Data has the original source coordinates, including old z unchanged. -/
theorem literal_scalar_fields (p : Fin 4 → ℤ) (hp : PortBox p) (hβ : 15 ≤ p 0)
    (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0)
    (u : ℕ) (hq : sourceQ p x = 2^u) :
    let d := sourceData p hp hβ x hx hs u hq
    d.J=x 0 ∧ d.F=x 1 ∧ d.alpha=x 2 ∧ d.z=x 3 ∧ d.w=x 10 ∧
      d.C=NativeSourceMask.gap p x := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

/-- No normalization/divisibility premise about the supplied ordinary i occurs. -/
theorem all_positive_source (p : Fin 4 → ℤ) {d MC MF : ℕ}
    (hi : NativeSourceMask.Interface p d MC MF) (hMC4 : MC%4=2)
    (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0) :
    ∃ v : Fin 14 → ℤ, (∀ j, 0 < v j) ∧
      MvPolynomial.eval v (Carrier65.polynomial p)=0 ∧ v 3=x 3 ∧ v 8=x 10 := by
  obtain ⟨v,hv,hz,_,_,_,h3,h8⟩ := source_constructs_carrier65 p hi hMC4 x hx hs
  exact ⟨v,hv,hz,h3,h8⟩

theorem same_rank_and_transport (p : Fin 4 → ℤ) (hp : PortBox p) (hβ : 15 ≤ p 0)
    (x : Fin 31 → ℕ) (hx : ∀ j, 0 < x j)
    (hs : ∀ j, SplitCertificate59.sourceRows p (fun k => (x k : ℤ)) j = 0)
    (u : ℕ) (hq : sourceQ p x = 2^u) :
    let d := sourceData p hp hβ x hx hs u hq
    NativeRankVariation.windowRank ((2^u : ℕ) : ℤ) d.C d.F (p 2) (p 3) d.J =
      ((nativeRank x).toNat : ℤ) ∧
      (p 1+(d.w : ℤ))*d.C+((2^u : ℕ)-(d.F : ℤ))-
        (d.z : ℤ)*((2^u : ℕ)-(1 : ℤ))=1 := by
  exact ⟨(sourceData p hp hβ x hx hs u hq).rank,
    (sourceData p hp hβ x hx hs u hq).transport⟩

theorem actual_external_endpoint :
    (¬ CurrentPositiveSource) ↔ DiophantineConsistency.ConZFC := no_current_source_iff_conZFC

#print axioms source_rank_window
#print axioms source_rank_cast
#print axioms sourceData
#print axioms source_constructs_carrier65
#print axioms literal_scalar_fields
#print axioms all_positive_source
#print axioms same_rank_and_transport
#print axioms current_source_positive_zero
#print axioms current_positive_zero_source
#print axioms current_source_iff_positive_zero
#print axioms current_source_iff_not_conZFC
#print axioms actual_external_endpoint
end DiophantineConsistency.NativeOrdinarySourceConstructionChecks
