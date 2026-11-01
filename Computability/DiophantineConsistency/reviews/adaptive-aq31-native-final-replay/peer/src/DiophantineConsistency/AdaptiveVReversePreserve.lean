import DiophantineConsistency.AdaptiveDirectOrdinate86Reverse
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 8000000
noncomputable section
namespace DiophantineConsistency.AdaptiveDirectOrdinate86Reverse.VPreserveProbe
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open AdaptiveEquationSyntax2011 ArithmeticSignedPairs ArithmeticAdaptiveFactorMagnitude2011
open ArithmeticAdaptiveAuxNorm2011 ArithmeticAdaptiveTransport2011
open AdaptiveFirstRootFactor87Syntax AdaptiveDirectOrdinate86Literal AdaptiveDirectOrdinate86Lift AdaptiveDirectOrdinate86Witness
open AdaptiveDirectOrdinate86AuxNorm AdaptiveDirectOrdinate86SignedV AdaptiveDirectOrdinate86Reverse
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]
theorem old_positive_zero_to_new_with_coordinates (p : Fin 4 → ℕ) (v : Fin 14 → V)
    (hb : 0<(p 0:V)) (hv : ∀i : Fin 13,0<v (oldIndex i))
    (hz : InternalZero (AdaptiveFirstRootFactor87Literal.expressionAt87 (fun j => (p j:ℤ)))
      (fun i => v (oldIndex i))) :
    ∃ w : Fin 13 → V, (∀ i, 0 < w i) ∧ InternalZero (expressionAt86 (fun j => (p j:ℤ))) w ∧
      ∀ i, i ≠ 11 → w i = v (oldIndex i) := by
  let u : Fin 13 → V := fun i => v (oldIndex i)
  let q : V := 1+u 0*(p 0:V)
  let k : V := u 9+u 10
  let c : V := u 9+u 7*k
  let I : V := (c*c)*u 4
  let R : V := ((q-1)*(q-u 1)+u 2)*(q^2-1)+((p 2:V)+q*(p 3:V))*u 0
  let L : V := (u 3*u 3)*u 5*c
  let M : V := (u 3*u 3)*R+c
  let z : V := magnitude (L,M)
  have hzero : InternalZero (AdaptiveEquationSyntax2011.expressionAt (fun j => (p j:ℤ))) u := by
    change (splitEval (AdaptiveEquationSyntax2011.expressionAt (fun j => (p j:ℤ))) u).1 =
      (splitEval (AdaptiveEquationSyntax2011.expressionAt (fun j => (p j:ℤ))) u).2
    rw [AdaptiveFirstRootFactor87Literal.split_expression_eq]
    exact hz
  have hg := expressionAt_transport_positive p u hb hv hzero
  have hgap : u 1+u 2<q := tsub_pos_iff_lt.mp hg.2
  have hF : u 1≤q := le_trans (by simp : u 1≤u 1+u 2) (le_of_lt hgap)
  have hrep := signedV_rep p u hF
  rw [show pairEval (eV (fun j => (p j:ℤ))) u = splitEval (signedV (fun j => (p j:ℤ))) v by
    exact signedV_eval_old _ v] at hrep
  have hu : u 11=v 13 := by simp [u,oldIndex]
  have hyrep : Equivalent ((splitEval (signedV (fun j => (p j:ℤ))) v).1+v 13,
      (splitEval (signedV (fun j => (p j:ℤ))) v).2) (L+v 13,M) := by
    change (splitEval (signedV (fun j => (p j:ℤ))) v).1+M =
      (splitEval (signedV (fun j => (p j:ℤ))) v).2+L at hrep
    change ((splitEval (signedV (fun j => (p j:ℤ))) v).1+v 13)+M =
      (splitEval (signedV (fun j => (p j:ℤ))) v).2+(L+v 13)
    calc
      _=((splitEval (signedV (fun j => (p j:ℤ))) v).1+M)+v 13 := by ring
      _=((splitEval (signedV (fun j => (p j:ℤ))) v).2+L)+v 13 := by rw [hrep]
      _=_ := by ring
  have hmag := magnitude_equivalent hyrep
  have hk : 0<k := add_pos (hv 9) (hv 10)
  have hc : 0<c := add_pos (hv 9) (mul_pos (hv 7) hk)
  have hc2 : 2≤c := by
    have h := add_le_add (pos_iff_one_le.mp (hv 9))
      (one_le_mul (pos_iff_one_le.mp (hv 7)) (pos_iff_one_le.mp hk))
    simpa only [one_add_one_eq_two] using h
  have hI : 2≤I := calc
    2≤c := hc2
    _≤c*c := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hc)
    _≤c*c*u 4 := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 4))
    _=I := rfl
  have hn := expressionAt_aux_norm p u hb hv hzero
  change I*I*z*z+magnitude (L+u 11,M)*magnitude (L+u 11,M) =
    1+I*I*magnitude (L+u 11,M)*magnitude (L+u 11,M) at hn
  rw [hu,←hmag] at hn
  have hpos := ordinate_positive_of_norm hI hn
  obtain ⟨y,hy,hnew⟩ := old_zero_to_new_of_positive_magnitude (fun j => (p j:ℤ)) v hpos hz
  let w : Fin 13 → V := fun i => if i=11 then y else v (embed i)
  have hw : ∀ i, 0<w i := by
    intro i
    by_cases hi : i=11
    · simpa [w,hi] using hy
    · simpa [w,hi,oldIndex] using hv i
  refine ⟨w,hw,hnew,?_⟩
  intro i hi
  simp [w,hi,oldIndex]
#print axioms old_positive_zero_to_new_with_coordinates
end DiophantineConsistency.AdaptiveDirectOrdinate86Reverse.VPreserveProbe
