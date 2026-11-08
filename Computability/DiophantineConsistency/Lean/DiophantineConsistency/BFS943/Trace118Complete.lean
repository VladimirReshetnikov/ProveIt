import DiophantineConsistency.BFS943.Trace118Regs
import DiophantineConsistency.BFS943.Scaled87Complete
import DiophantineConsistency.BFS943.Centred87Complete

/-! # Positive 118 zeros from positive 87 zeros

Package 193 §6 (`193-transport-and-pell-reuse/positive/PROOF.md`), read at an
arbitrary positive 87/214 zero instead of the canonical witnesses. Keep every
coordinate except `n`. At the 87 zero the carrier is `Z₈₇ = M z` with
`z = ±g y`, `g = τ f`, `E = τ²` (`Trace87NormRoots.graph_adjacent`),
`B ≥ 0` and the mask (`Trace87Transport.graph_zero_data`), `V > 0`
(`Centred87Complete.V_positive`), hence `b ≥ 1`, `Ω ≥ 0` and `L ≥ 0`
(`Trace118Omega.omega_nonneg`). Put

  `n' = n + (OmegaFold - b V B) + 3 g y`   if `z = g y`,
  `n' = n + (OmegaFold - b V B) + 5 g y`   if `z = -g y`.

Then the 118 carrier at `n'` is `4 Z₈₇(n)` resp. `-4 Z₈₇(n)`
(`TenPositiveScaled87.Z_update`), so the root-scale-four norm there is
`16 value87 = 0` (`TenPositiveTrace118.norm16_four`). Clearing the
denominators, `M n' = 4 M g y + M OmegaFold - h D K + H D B + H h eclear`,
which is positive because `OmegaFold = Ω + L B ≥ 0`, `B ≥ 0`, `y ≥ 1` and
`K < 2 g`, `-eclear < 2 g` (`Trace118Estimate.complete_bounds`, from the
first-index size `8 v + 4 ≤ k`, `R ≤ c` and `c² E ≤ g`); this is package 193's
`|ρ| + κ + σ < g`, used only in the weak form `κ - ρ + σ < 2 g`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace118Complete
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace87 TenPositiveTrace76
open Trace87Factors Trace87Residue Trace87NormRoots Trace87NormKpos Trace87NormRank
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

set_option maxHeartbeats 4000000 in
/-- A positive 87 zero gives a positive zero of the 118 circuit by moving `n`. -/
theorem zero118 (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value87 (ports p) (fun j => ι (v j)) = 0) :
    ∃ n' : V, 0<n' ∧ TenPositiveTrace118.value118 (ports p)
      (fun j => ι (Function.update v 7 n' j)) = 0 := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  let rr := regs (ports p) (fun j => ι (v j))
  have hzn : normValue rr rr.Z = 0 := hz
  obtain ⟨_z,_tau,_f,_y,_,_,_,_,_,_,hB0,hm,_⟩ := Trace87Transport.graph_zero_data p v hb hv hz
  obtain ⟨hrank,_,_,hcR,_⟩ := graph_rank_exact p v rr.Z hb31 hl hh hv hzn hm
  have hsize := graph_rank_size p v rr.Z hb hv hzn
  obtain ⟨V',hV'pos,hVeq⟩ := Centred87Complete.V_positive p v hb31 hl hh hv hz
  have hVpos : 0<rr.V := by
    change 0<(regs (ports p) (fun j => ι (v j))).V
    rw [hVeq,←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hV'pos
  obtain ⟨hOm0,hL0,_hb1⟩ := Trace118Omega.omega_nonneg p v hb hv hVpos
  obtain ⟨tau,f,_V0,Z0,y,ht,hf,_,hy,hE,hf2,_,hZs,hZeq,_⟩ := graph_adjacent p v rr.Z hb hv hzn
  -- the 87 root `z = ±τ f y`
  let mz : DiffRing V := ι (M p v)*ι (tau*f*y)
  have hsq : rr.Z*rr.Z=mz*mz := by
    calc
      rr.Z*rr.Z=ι (Z0*Z0) := hZs
      _=mz*mz := by rw [hZeq]; dsimp [mz]; simp only [map_mul]; ring
  have hfactor : (rr.Z-mz)*(rr.Z+mz)=0 := by
    rw [show (rr.Z-mz)*(rr.Z+mz)=rr.Z*rr.Z-mz*mz by ring,hsq]; ring
  have hMr : rr.M=ι (M p v) := M_eval p v hb hv
  have hMd : rr.M=rr.h*rr.D*rr.H := M_def _ _
  -- positivity data
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hX : 0<X p v := mul_pos hq (hv 5)
  have hYp : 0<Y p v := mul_pos hq (hv 6)
  have hA : 0<A p v := add_pos (mul_pos hX hYp) hYp
  have hhr : rr.h=ι (b p v) := by
    dsimp [rr]
    simp only [h_def,ports,b,map_mul,map_natCast]
  have hqr : rr.q=ι (q p v) := by
    dsimp [rr]
    simp only [q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
  have hAr : rr.Am1=ι (A p v) := by
    dsimp [rr]
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,A,X,Y,q,b,map_mul,map_add,map_one,
      map_natCast]
  have hXr : rr.X=ι (X p v) := by
    dsimp [rr]; simp only [X_def,q_def,h_def,ports,X,q,b,map_mul,map_add,map_one,map_natCast]
  have hYr : rr.Y=ι (Y p v) := by
    dsimp [rr]; simp only [Y_def,q_def,h_def,ports,Y,q,b,map_mul,map_add,map_one,map_natCast]
  have hkr : rr.k=ι (k v) := by
    dsimp [rr]; rw [k_def]; simp only [k,map_add]
  have hcr : rr.c=ι (c p v) := c_eval p v
  have hh0 : 0<rr.h := by rw [hhr,←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hb0
  have hq1 : (1:DiffRing V)≤ι (q p v) := by
    rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact pos_iff_one_le.mp hq
  have hD7 : rr.D=6*ι (q p v)^7 := by rw [D_def,hqr]; ring
  have hD1 : 1≤rr.D := by
    rw [hD7]
    have : (1:DiffRing V)≤ι (q p v)^7 := one_le_pow₀ hq1
    linarith
  have hH1 : 1≤rr.H := by
    dsimp [rr]
    rw [H_def,hAr]
    have hA1 : (1:DiffRing V)≤ι (A p v) := by
      rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]
      exact pos_iff_one_le.mp hA
    linarith
  have hM0 : 0<rr.M := by
    rw [hMd]; exact mul_pos (mul_pos hh0 (by linarith)) (by linarith)
  -- `g = τ f ≥ c² E`
  obtain ⟨hD0,hU0,hE0,_⟩ := factors_positive p v hb hv
  have hC : 0<c p v := add_pos (mul_pos (add_pos (hv 8) (hv 9)) (hv 6)) (hv 8)
  have pos1 : ∀ w : V, 0<w → (1:DiffRing V)≤ι w := fun w hw => by
    rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact pos_iff_one_le.mp hw
  have hgg0 : (ι (tau*f):DiffRing V)*ι (tau*f)=
      ι (E p v)*(1+ι (delta p v)*(ι (U p v)*ι (U p v))*ι (E p v)) := by
    have h1 := congrArg (ι : V →+* DiffRing V) hf2
    have h2 := congrArg (ι : V →+* DiffRing V) hE
    simp only [map_add,map_mul,map_one] at h1 h2
    have h3 : (ι (tau*f):DiffRing V)*ι (tau*f)=(ι tau*ι tau)*(ι f*ι f) := by
      simp only [map_mul]; ring
    rw [h3,←h1,←h2]
    ring
  set g : DiffRing V := ι (tau*f) with hgdef
  set cc : DiffRing V := ι (c p v) with hccdef
  set ee : DiffRing V := ι (E p v) with heedef
  set uu : DiffRing V := ι (U p v) with huudef
  set dd : DiffRing V := ι (delta p v) with hdddef
  have hgg : g*g=ee*(1+dd*(uu*uu)*ee) := hgg0
  have hg0 : 0≤g := ι_nonneg _
  have huc : cc*cc≤uu := by
    rw [hccdef,huudef,←map_mul,ι_le_ι]
    exact le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp (hv 3))
  have hcc0 : 0≤cc*cc := mul_self_nonneg _
  have hee1 : 1≤ee := pos1 _ hE0
  have hdd1 : 1≤dd := pos1 _ hD0
  have hcE : cc*cc*ee≤g := by
    have h0 : 0≤cc*cc*ee := mul_nonneg hcc0 (by linarith)
    apply (mul_self_le_mul_self_iff h0 hg0).mpr
    rw [hgg]
    have huu0 : 0≤uu := le_trans hcc0 huc
    have h1 : cc*cc*(cc*cc)≤uu*uu := mul_le_mul huc huc hcc0 huu0
    have h2 : uu*uu≤dd*(uu*uu) := le_mul_of_one_le_left (mul_nonneg huu0 huu0) hdd1
    have h3 : cc*cc*(cc*cc)*(ee*ee)≤dd*(uu*uu)*(ee*ee) :=
      mul_le_mul_of_nonneg_right (le_trans h1 h2) (mul_self_nonneg ee)
    nlinarith
  -- the completeness bounds `K < 2 g`, `-eclear < 2 g`
  have hRc : rankNat p v≤c p v := by rw [hcR]; exact ArithmeticPellRecurrence.time_le_y _ _
  have hbounds := Trace118Estimate.complete_bounds (ι (q p v)) (ι (v 6)) (ι (v 5)) (ι (X p v))
    (ι (Y p v)) (ι (firstParam p v)) (ι (k v)) cc (ι (rankNat p v)) ee g hq1 (pos1 _ (hv 6))
    (pos1 _ (hv 5)) (by simp only [X,map_mul]) (by simp only [Y,map_mul])
    (by simp only [firstParam,map_mul]; ring)
    (by have h := ι_le_ι.mpr hsize; simpa only [map_add,map_mul,map_ofNat] using h)
    (by
      have h1 : k v≤k v*v 6 := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 6))
      have h2 : k v*v 6+1≤c p v := by
        change k v*v 6+1≤k v*v 6+v 8
        exact add_le_add (le_refl _) (pos_iff_one_le.mp (hv 8))
      have h := ι_le_ι.mpr (le_trans (add_le_add h1 (le_refl 1)) h2)
      simpa only [map_add,map_one] using h)
    (ι_le_ι.mpr hRc)
    (by simp only [heedef,E,firstParam,map_add,map_mul,map_one]; ring) hcE
  obtain ⟨hKb,hEb⟩ := hbounds
  have hKr : rr.K=ι (X p v)*(3*cc-2*ι (X p v))+2 := by rw [K_def,hXr,hcr]
  have hecl : -ecl (ports p) (fun j => ι (v j))=
      6*(ι (rankNat p v)+1+ι (q p v)*ι (q p v)*(ι (q p v)*ι (q p v))*ι (v 6)-ι (k v))+
        ι (firstParam p v)*ι (k v)*(ι (k v)*ι (k v)-4) := by
    have heclN := ecl_def (ports p) (fun j => ι (v j))
    have hPr : rr.X*rr.Y*rr.Y=ι (firstParam p v) := by
      rw [hXr,hYr]; simp only [firstParam,map_mul]; ring
    have he : rr.e=ι (k v)-ι (rankNat p v)-1 := by
      change rr.e=_
      rw [e_def,hkr,hrank]
    change -ecl (ports p) (fun j => ι (v j))=_
    rw [heclN]
    change -(6*(rr.e-rr.q*rr.q*(rr.q*rr.q)*ι (v 6))-rr.X*rr.Y*rr.Y*rr.k*(rr.k*rr.k-4))=_
    rw [hPr,he,hqr,hkr]
    ring
  have hK2 : rr.K<2*g := by rw [hKr]; exact hKb
  have hE2 : -ecl (ports p) (fun j => ι (v j))<2*g := by rw [hecl]; exact hEb
  -- the moved coordinate
  let OF : DiffRing V := TenPositiveTrace118.omegaFold (ports p) (fun j => ι (v j))
  have hOF : 0≤OF := by
    change 0≤TenPositiveTrace118.omegaFold (ports p) (fun j => ι (v j))
    rw [TenPositiveTrace118.omegaFold_eq]
    exact add_nonneg hOm0 (mul_nonneg hL0 hB0)
  have hZdef : rr.Z=rr.h*rr.D*(rr.H*(ι (v 7)-rr.b*rr.V*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*ecl (ports p) (fun j => ι (v j))) := Z_def _ _
  have hy1 : (1:DiffRing V)≤ι y := pos1 _ hy
  have hgy : g≤ι (tau*f*y) := by
    have h : g≤g*ι y := le_mul_of_one_le_right hg0 hy1
    have he : (ι (tau*f*y):DiffRing V)=g*ι y := by rw [hgdef,map_mul]
    rw [he]; exact h
  -- `M n' > 0` in the cleared form
  have hcleared : 0<4*(rr.M*ι (tau*f*y))+rr.M*OF-rr.h*rr.D*rr.K+rr.H*rr.D*rr.B+
      rr.H*rr.h*ecl (ports p) (fun j => ι (v j)) := by
    have h1 : 0≤rr.M*OF := mul_nonneg (le_of_lt hM0) hOF
    have h2 : 0≤rr.H*rr.D*rr.B := mul_nonneg (mul_nonneg (by linarith) (by linarith)) hB0
    have h3 : rr.M*g≤rr.M*ι (tau*f*y) := mul_le_mul_of_nonneg_left hgy (le_of_lt hM0)
    have h4 : 0<rr.D*(2*rr.H*g-rr.K) := by
      have : 2*g≤2*rr.H*g := by
        have := mul_le_mul_of_nonneg_right hH1 (show (0:DiffRing V)≤2*g by linarith); linarith
      exact mul_pos (by linarith) (by linarith)
    have h5 : 0<rr.H*(2*rr.D*g+ecl (ports p) (fun j => ι (v j))) := by
      have : 2*g≤2*rr.D*g := by
        have := mul_le_mul_of_nonneg_right hD1 (show (0:DiffRing V)≤2*g by linarith); linarith
      exact mul_pos (by linarith) (by linarith)
    have h6 : 0<rr.h*(rr.D*(2*rr.H*g-rr.K)+rr.H*(2*rr.D*g+ecl (ports p) (fun j => ι (v j)))) :=
      mul_pos hh0 (by linarith)
    have hexp : 4*(rr.M*g)-rr.h*rr.D*rr.K+rr.H*rr.h*ecl (ports p) (fun j => ι (v j))=
        rr.h*(rr.D*(2*rr.H*g-rr.K)+rr.H*(2*rr.D*g+ecl (ports p) (fun j => ι (v j)))) := by
      rw [hMd]; ring
    linarith
  have hcast := Scaled87Complete.cast_update v
  have hval : ∀ x : V, TenPositiveTrace118.value118 (ports p) (fun j => ι (Function.update v 7 x j)) =
      TenPositiveTrace118.norm16 rr (rr.Z+rr.M*(ι x-ι (v 7))-rr.M*(OF-rr.b*rr.V*rr.B)) := by
    intro x
    rw [hcast,TenPositiveTrace118.value118_update,TenPositiveScaled87.Z_update]
  have hmove : ∀ (m z : DiffRing V), rr.Z=rr.M*z →
      rr.M*(ι (v 7)+(OF-rr.b*rr.V*rr.B)+m)=
        rr.M*(z+m)+rr.M*OF-rr.h*rr.D*rr.K+rr.H*rr.D*rr.B+
          rr.H*rr.h*ecl (ports p) (fun j => ι (v j)) := by
    intro m z hZ
    have h := hZdef
    rw [hZ,hMd] at h
    rw [hMd]
    linear_combination -h
  have key : ∀ m : DiffRing V, 0<rr.M*(ι (v 7)+(OF-rr.b*rr.V*rr.B)+m) →
      TenPositiveTrace118.norm16 rr (rr.Z+rr.M*m) = 0 →
      ∃ n' : V, 0<n' ∧ TenPositiveTrace118.value118 (ports p)
        (fun j => ι (Function.update v 7 n' j)) = 0 := by
    intro m hpos hzero
    have hnn : 0<ι (v 7)+(OF-rr.b*rr.V*rr.B)+m := pos_of_mul_pos_right hpos (le_of_lt hM0)
    obtain ⟨n',hn'⟩ := nonneg_iff.mp (le_of_lt hnn)
    refine ⟨n',?_,?_⟩
    · rw [hn',←map_zero (ι : V →+* DiffRing V),ι_lt_ι] at hnn; exact hnn
    · rw [hval n']
      have hc : rr.Z+rr.M*(ι n'-ι (v 7))-rr.M*(OF-rr.b*rr.V*rr.B)=rr.Z+rr.M*m := by
        rw [←hn']; ring
      rw [hc]
      exact hzero
  let t : DiffRing V := ι (tau*f*y)
  rcases mul_eq_zero.mp hfactor with h|h
  · have hZ1 : rr.Z=rr.M*t := by rw [hMr]; exact sub_eq_zero.mp h
    apply key (3*t)
    · rw [hmove (3*t) t hZ1]
      have : rr.M*(t+3*t)=4*(rr.M*t) := by ring
      linarith
    · rw [show rr.Z+rr.M*(3*t)=4*rr.Z by rw [hZ1]; ring,TenPositiveTrace118.norm16_four,hzn,
        mul_zero]
  · have hZ2 : rr.Z=rr.M*(-t) := by
      have heq : rr.Z= -mz := eq_neg_of_add_eq_zero_left h
      rw [heq,hMr]; ring
    apply key (5*t)
    · rw [hmove (5*t) (-t) hZ2]
      have : rr.M*(-t+5*t)=4*(rr.M*t) := by ring
      linarith
    · rw [show rr.Z+rr.M*(5*t)=4*(-rr.Z) by rw [hZ2]; ring,TenPositiveTrace118.norm16_four,
        TenPositiveScaled87.normValue_neg,hzn,mul_zero]

#print axioms Trace118Complete.zero118
end Trace118Complete
