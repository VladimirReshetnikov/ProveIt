import DiophantineConsistency.ThirteenScaledNormSyzygy86
set_option Elab.async false
namespace DiophantineConsistency.ThirteenScaledNormSyzygy86Checks
open ThirteenScaledNormSyzygy86 ThirteenCarrierSoundness

theorem scale_from_only_main (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) (hQ : (data p v).Q=1) :
    0 < scale p v := scale_pos_of_main p v hb hv hQ

theorem corrected_auxiliary_on_units (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hP : (data p v).P=1) (hQ : (data p v).Q=1) :
    ThirteenScaledNormSyzygy86.auxiliary p v=scale p v*ThirteenGroupedSquares96.auxiliary p v := by
  simp [ThirteenScaledNormSyzygy86.auxiliary,syzygy,hP,hQ]

theorem same_positive_assignment (p : Fin 4 → ℤ) (v : Fin 13 → ℤ)
    (hb : 0 < p 0) (hv : ∀ j, 0 < v j) :
    value p v=0 ↔ ThirteenSecondFirstNormCorrections.value true p v=0 :=
  positive_zero_iff88 p v hb hv

theorem actual_ports : currentPolynomial =
    polynomial (CurrentMasks2011.ports (CurrentKernel2011.K : ℤ)) := rfl

theorem actual_endpoint :
    (¬ CurrentCarrierArithmetic2011.PositiveZero currentPolynomial) ↔
      DiophantineConsistency.ConZFC := no_current_positive_zero_iff_conZFC

/-- A positive assignment alone does not make the multiplier positive. -/
theorem scale_can_be_negative (p : Fin 4 → ℤ) :
    scale p (fun _ => 1)=-2 := by norm_num [scale,data,Carrier65.core,parent]

/-- Scaling inside the old sphere without changing its unit target fails. -/
theorem unadjusted_sphere_is_wrong :
    ((1 : ℤ)*1)^2+(2*1)^2+1^2-3 ≠ 0 ∧
      ((1 : ℤ)*1-1)^2+(1-1)^2+(2*1-2)^2=0 := by norm_num

#print axioms main_unit_scale_pos
#print axioms scale_pos_of_main
#print axioms residuals_zero_iff
#print axioms positive_zero_iff75
#print axioms positive_zero_iff88
#print axioms value_map
#print axioms eval_polynomial
#print axioms exists_positive_zero_iff88
#print axioms actual_ports
#print axioms actual_endpoint
#print axioms scale_can_be_negative
#print axioms unadjusted_sphere_is_wrong
end DiophantineConsistency.ThirteenScaledNormSyzygy86Checks
