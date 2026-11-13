import DiophantineConsistency.ArithmeticOddOrdinateResidue

/-! Draft: model-internal negative ordinate residue. No graph or port bridge. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace ModelBNegativeResidue
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency.ArithmeticPellRecurrence
open DiophantineConsistency.ArithmeticOddOrdinateResidue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- A phase-3 ordinate is −1 modulo four times any divisor of its base. -/
theorem ordinate_plus_one_dvd (I R b : V) (hI : 2≤I) (hbI : b∣I)
    (hphase : R%4=3) : ∃ h : V, ycoord R (I-2)+1=4*b*h := by
  have hbase : I-2+2=I := tsub_add_cancel_of_le hI
  have hphaseindex : 2*(2*(R/4)+1)+1=R := by
    have he : R=4*(R/4)+3 := by simpa only [hphase] using (div_add_mod R 4).symm
    calc 2*(2*(R/4)+1)+1=4*(R/4)+3 := by ring
      _=R := he.symm
  have hy : (ycoord R (I-2)+1)%(4*I*I)=0 := by
    simpa only [hphaseindex,hbase] using (DiophantineConsistency.ArithmeticOddOrdinateResidue.pair (I-2) (R/4)).2
  obtain ⟨k,hk⟩ := hbI
  have hd : 4*b∣4*I*I := by
    refine ⟨k*I,?_⟩
    rw [hk]
    ring
  exact hd.trans (mod_eq_zero_iff_dvd.mp hy)
end ModelBNegativeResidue
#print axioms ModelBNegativeResidue.ordinate_plus_one_dvd
