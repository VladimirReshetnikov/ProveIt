import DiophantineConsistency.BFS943.Centred87Regs
import DiophantineConsistency.BFS943.Trace87Projection

/-! # Positive centred zeros from positive 87 zeros

Package 179 §4: keep every coordinate of a positive 87/214 zero except `n` and
put `n_new = n + ĝ V`. Then `n_new - V (b B + ĝ) = n - b V B`, so the centred
carrier at `n_new` is the 87 carrier at `n` and the norm value is unchanged
(`TenPositiveCentred87.valueAt_shift`). This needs `V ≥ 0` at the 87 zero,
read here from the 87 soundness layer rather than from the construction: with
the mask (`Trace87Transport.graph_zero_data`), `R = rank` and
`c = ψ_A(R) ≥ R` (`Trace87NormRank.graph_rank_exact`,
`ArithmeticPellRecurrence.time_le_y`), so `b = c T - R ≥ 0`; and
`b V > 2 τ f y > 0` (`Trace87Transport.graph_bv_bound`), hence `b > 0` and
`V > 0`. The centre `ĝ ≥ 0` is an arbitrary natural (it may depend on every
coordinate except `n`, which is how the published centres are used). -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Centred87Complete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87 TenPositiveTrace76
open Trace87Factors Trace87Residue Trace87NormRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- At a positive 87 zero, `V` is a positive natural. -/
theorem V_positive (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value87 (ports p) (fun j => ι (v j)) = 0) :
    ∃ V' : V, 0<V' ∧ (regs (ports p) (fun j => ι (v j))).V=ι V' := by
  let rr := regs (ports p) (fun j => ι (v j))
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  have hzn : normValue rr rr.Z = 0 := hz
  obtain ⟨_z,_tau,_f,_y,_,_,_,_,_,_,_,hm,_⟩ := Trace87Transport.graph_zero_data p v hb hv hz
  obtain ⟨hrank,_,_,hc,_⟩ := graph_rank_exact p v _ hb31 hl hh hv hzn hm
  obtain ⟨tau,f,_Z0,y,ht,hf,hy,_,_,_,hbound,_hL,_⟩ := Trace87Transport.graph_bv_bound p v rr.Z hb hv hzn
  have hpos : (0:DiffRing V)<rr.b*rr.V := by
    have h0 : (0:DiffRing V)<ι (tau*f*y) := by
      rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact mul_pos (mul_pos ht hf) hy
    linarith
  have hRc : rankNat p v≤c p v := by
    rw [hc]; exact ArithmeticPellRecurrence.time_le_y _ _
  have hT : (1:DiffRing V)≤ι (v 4) := by
    rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]
    exact pos_iff_one_le.mp (hv 4)
  have hC0 : (0:DiffRing V)≤ι (c p v) := ι_nonneg _
  have hRcR : (ι (rankNat p v):DiffRing V)≤ι (c p v) := ι_le_ι.mpr hRc
  have beval : rr.b=ι (c p v)*ι (v 4)-ι (rankNat p v) := by
    dsimp [rr]
    rw [b_def,c_eval,hrank]
  have hb0 : 0≤rr.b := by
    rw [beval]
    have := le_mul_of_one_le_right hC0 hT
    linarith
  have hbpos : 0<rr.b := by
    rcases lt_or_eq_of_le hb0 with h|h
    · exact h
    · rw [←h,zero_mul] at hpos; exact absurd hpos (lt_irrefl _)
  have hVpos : 0<rr.V := pos_of_mul_pos_right hpos (le_of_lt hbpos)
  obtain ⟨V',hV'⟩ := nonneg_iff.mp (le_of_lt hVpos)
  refine ⟨V',?_,hV'⟩
  rw [hV',←map_zero (ι : V →+* DiffRing V),ι_lt_ι] at hVpos
  exact hVpos

/-- A positive 87 zero gives a positive zero of the centred circuit at any
natural centre `ĝ` that does not read `n`: replace `n` by `n + ĝ V`. -/
theorem centred_zero (p : Fin 4 → ℕ) (v : Fin 10 → V) (gn V' : V)
    (hv : ∀j,0<v j) (hV : (regs (ports p) (fun j => ι (v j))).V=ι V')
    (hz : value87 (ports p) (fun j => ι (v j)) = 0) :
    (∀ j, 0<Function.update v 7 (v 7+gn*V') j) ∧
      TenPositiveCentred87.valueAt (ports p)
        (fun j => ι (Function.update v 7 (v 7+gn*V') j)) (ι gn) = 0 := by
  have hcast : (fun j => ι (Function.update v 7 (v 7+gn*V') j))=
      Function.update (fun j => (ι (v j):DiffRing V)) 7
        (ι (v 7)+ι gn*(regs (ports p) (fun j => ι (v j))).V) := by
    funext j
    rw [hV]
    fin_cases j <;> simp
  refine ⟨?_,?_⟩
  · intro j
    by_cases h : j=7
    · subst h
      rw [Function.update_self]
      exact add_pos_of_pos_of_nonneg (hv 7) (by simp)
    · rw [Function.update_of_ne h]
      exact hv j
  · rw [hcast,TenPositiveCentred87.valueAt_shift]
    exact hz

#print axioms Centred87Complete.V_positive
#print axioms Centred87Complete.centred_zero
end Centred87Complete
