import Direct80FixedDigits

/-! Compact radix-aligned transport for the actual 80 graph. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Direct80FixedCongruence
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency AdaptiveEquationSyntax2011
open CompactFixedBeta CompactSymbolicPorts ArithmeticRepunit ArithmeticWindowDigits
open TenPositive80Graph TenPositive80Factors TenPositive80NaturalRank TenPositive80NaturalTransport
attribute [local irreducible] CompactFixedBeta.betaNat Nat.ofDigits lowNat highNat
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem graph_fixed_congruence (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hp0 : p 0=betaNat) (hp2 : p 2=lowNat) (hp3 : p 3=betaNat+highNat)
    (hv : ∀j,0<v j) (hz : InternalZero (graph (integerPorts p)).output v) :
    ∃ N : V, 0<N ∧ v 0=rep (67*8807) N ∧ q p v=Exp.exp ((67*8807)*N) ∧
      (67*8807)*N≤rankNat p v ∧ v 5=Exp.exp (rankNat p v-(67*8807)*N) ∧
      0<b p v ∧ v 1<b p v ∧ (((p 1:V)+v 5)*Cnat p v)%(b p v)=v 1 ∧
      dig 67 (Cnat p v) 0=1 ∧ ∀ j<8807*N, dig 67 (Cnat p v) j≤3 := by
  obtain ⟨h31,hl,hh,hodd⟩ := TenPositive80SymbolicPortBounds.fixed_bounds (V:=V) p hp0 hp2 hp3
  have hb : (p 0:V)+1=Exp.exp ((67:V)*8807) := by rw [hp0]; exact beta_identity
  obtain ⟨N,t,hN,hJ,hq,_hC,ht,hzero,hdigits,_⟩ :=
    Direct80FixedDigits.graph_fixed_digits p v hp0 hp2 hp3 hv hz
  obtain ⟨N',_hN',hq',hle,hw⟩ := Direct80RadixAlignment.graph_radix_alignment p v
    ((67:V)*8807) h31 hl hh hv hz hodd (by norm_num) hb
  have hNN : N'=N := by
    apply mul_left_cancel₀ (by norm_num : ((67*8807):V)≠0)
    exact exp_inj (hq'.symm.trans hq)
  subst N'
  have hbpos : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) h31
  have hb0 : 0<b p v := mul_pos hbpos (hv 0)
  have hgap := (TenPositive80TransportModel.graph_transport_and_mask p v hbpos hv hz).2
  have hF : v 1<b p v := by
    have hle : v 1+1≤v 1+v 2 := by
      simpa only [add_comm] using add_le_add_left (pos_iff_one_le.mp (hv 2)) (v 1)
    have h := lt_of_le_of_lt hle hgap
    change v 1+1<b p v+1 at h
    exact (add_lt_add_iff_right 1).mp h
  have hmod : (((p 1:V)+v 5)*Cnat p v)%(b p v)=v 1 := by
    rw [ht,mod_add_mul' _ _ hb0,mod_eq_self_of_lt hF]
  exact ⟨N,hN,hJ,hq,hle,hw,hb0,hF,hmod,hzero,hdigits⟩

#print axioms Direct80FixedCongruence.graph_fixed_congruence
end Direct80FixedCongruence
