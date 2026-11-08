import DiophantineConsistency.BFS943.Trace77Transport
import DiophantineConsistency.BFS943.TraceNormOffset

/-! # Every positive 77/348 zero gives a positive 75/402 zero

At a positive zero of `value77` (`Trace77Transport.graph_zero_data`) the 75
output vanishes at the carrier `w s Z77 = M z`, `B ≥ 0`, the mask holds and
`q⁴ ∣ e`. The carrier-generic first-index alignment
(`TraceNormOffset.graph_offset_exact`) then gives `e = XY ρ` with
`ρ = 4 Y s ≥ 0`. Put `g = τ f y = |z|` and

  `n' = n + (V² - bV) B - (w s - 1) ρ + (g - z)`.

The ring identity `TenPositiveTrace77.Z75_shift` makes the 75 carrier at `n'`
equal to `M g`, whose square is `(M z)²`, so the 75 output at `n'` is the 75
output at `w s Z77`, which is zero. Positivity: `h H n' = h H g + h H V² B +
H B + h H ρ - h K`, and `H g > K` because `g ≥ f > c` (from `f² = 1 + a`,
`a ≥ c²`) and `H ≥ 4X + 3`. Taking `|z|` rather than `z` is what makes `n'`
positive without any sign information on the carrier. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace77ToTrace75
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 TenPositiveTrace76 TenPositiveTrace77
open Trace75Factors Trace75Pell Trace75Residue
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

theorem positive75_of_positive77 (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value77 (ports p) (fun j => ι (v j)) = 0) :
    ∃ w : Fin 10 → V, (∀j,0<w j) ∧ value75 (ports p) (fun j => ι (w j)) = 0 := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨z,tau,f,y,ht,hf,hy,hf2,hzpm,hzn,hZ,hB,_hd,hm,hq4⟩ :=
    Trace77Transport.graph_zero_data p v hb hv hz
  let rr := regs (ports p) (fun j => ι (v j))
  let Zs : DiffRing V := ι (v 5)*ι (v 6)*Z77 (ports p) (fun j => ι (v j))
  obtain ⟨_n,s,_hn,_halign,_hk,he⟩ :=
    TraceNormOffset.graph_offset_exact p v Zs hb31 hl hh hv hzn hm hq4
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  have hXr : rr.X=ι (X p v) := by
    dsimp [rr]
    simp only [X_def,q_def,h_def,ports,X,q,b,map_mul,map_add,map_one,map_natCast]
  have hYr : rr.Y=ι (Y p v) := by
    dsimp [rr]
    simp only [Y_def,q_def,h_def,ports,Y,q,b,map_mul,map_add,map_one,map_natCast]
  have hhr : rr.h=ι (b p v) := by
    dsimp [rr]
    simp only [h_def,ports,b,map_mul,map_natCast]
  have hAr : rr.Am1=ι (A p v) := by
    dsimp [rr]
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,A,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
  let rho : DiffRing V := ι (4*Y p v*s)
  have heXY : rr.e=rr.X*rr.Y*rho := by
    change rr.e=_ at he
    rw [he,hXr,hYr]
    dsimp [rho,firstParam]
    simp only [map_mul,map_ofNat]
    ring
  let g : DiffRing V := ι (tau*f*y)
  let d : DiffRing V := g-z
  let x : DiffRing V := ι (v 7)+(rr.V*rr.V-rr.b*rr.V)*rr.B-(ι (v 5)*ι (v 6)-1)*rho+d
  have hZ75 : (regs (ports p) (Function.update (fun j => ι (v j)) 7 x)).Z=rr.M*(z+d) :=
    Z75_shift (ports p) (fun j => ι (v j)) rho z d x heXY hZ rfl
  -- positivity of the moved coordinate
  have hS := scaled_shape (ports p) (fun j => ι (v j))
  change Zs=rr.h*rr.D*(rr.H*(ι (v 7)-rr.b*rr.V*rr.B)+rr.K)-
    rr.H*(rr.D*rr.B+rr.h*(ι (v 5)*ι (v 6)*rr.e)) at hS
  have hDr : rr.D=rr.X*rr.Y := D_def _ _
  have hMr : rr.M=rr.h*(rr.X*rr.Y)*rr.H := M_def _ _
  have hXYpos : 0<rr.X*rr.Y := by
    rw [hXr,hYr,←map_mul,←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact mul_pos hX hY
  have hkey : rr.h*rr.H*x=rr.h*rr.H*g+rr.h*rr.H*(rr.V*rr.V)*rr.B+rr.H*rr.B+
      rr.h*rr.H*rho-rr.h*rr.K := by
    apply mul_left_cancel₀ (ne_of_gt hXYpos)
    rw [hDr,heXY] at hS
    rw [hMr] at hZ
    change Zs=_ at hZ
    dsimp [x,d]
    linear_combination hZ-hS
  -- the inequality `H g > K`
  obtain ⟨hD0,hU0,hE0,_hM0⟩ := factors_positive p v hb hv
  have hC : 0<c p v := add_pos (mul_pos (add_pos (hv 8) (hv 9)) hY) (hv 8)
  have hcU : c p v*c p v≤U p v :=
    le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp (hv 3))
  have hUa : U p v≤delta p v*U p v*U p v*E p v := by
    calc
      U p v≤delta p v*U p v := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hD0)
      _≤delta p v*U p v*U p v := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hU0)
      _≤delta p v*U p v*U p v*E p v := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hE0)
  have hcf : c p v<f := by
    by_contra hn
    have hfc : f≤c p v := le_of_not_gt hn
    have hsq : f*f≤c p v*c p v := mul_le_mul hfc hfc (by simp) (by simp)
    have h1 : 1+delta p v*U p v*U p v*E p v≤delta p v*U p v*U p v*E p v := by
      rw [hf2]; exact le_trans hsq (le_trans hcU hUa)
    exact absurd h1 (not_le_of_gt (lt_add_of_pos_left _ (by simp)))
  have hfg : f≤tau*f*y := by
    calc
      f≤tau*f := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp ht)
      _≤tau*f*y := le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hy)
  have hcg : c p v+1≤tau*f*y := le_trans (lt_iff_succ_le.mp hcf) hfg
  have hcgR : (ι (c p v):DiffRing V)+1≤g := by
    have h := ι_le_ι.mpr hcg
    simpa only [map_add,map_one] using h
  have hX1 : (1:DiffRing V)≤ι (X p v) := by
    rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact pos_iff_one_le.mp hX
  have hAX : (ι (X p v):DiffRing V)+1≤ι (A p v) := by
    have h : X p v+1≤A p v := by
      change X p v+1≤X p v*Y p v+Y p v
      have hY1 : 1≤Y p v := pos_iff_one_le.mp hY
      exact add_le_add (le_mul_of_one_le_right (by simp) hY1) hY1
    have h' := ι_le_ι.mpr h
    simpa only [map_add,map_one] using h'
  have hHr : rr.H=4*ι (A p v)-1 := by dsimp [rr]; rw [H_def,hAr]
  have hKr : rr.K=ι (X p v)*(3*ι (c p v)-2*ι (X p v))+2 := by
    dsimp [rr]; rw [K_def,c_eval]; rw [hXr]
  have hcR : (1:DiffRing V)≤ι (c p v) := by
    rw [←map_one (ι : V →+* DiffRing V),ι_le_ι]; exact pos_iff_one_le.mp hC
  have hHg : rr.K<rr.H*g := by
    rw [hHr,hKr]
    have hg0 : (0:DiffRing V)≤g := ι_nonneg _
    have h1 : (4*ι (X p v)+3)*(ι (c p v)+1)≤(4*ι (A p v)-1)*g := by
      apply mul_le_mul _ hcgR (by linarith) (by linarith)
      linarith
    nlinarith
  have hh : 0<rr.h := by rw [hhr,←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hb0
  have hH : 0<rr.H := by
    rw [hHr]; linarith
  have hrho : 0≤rho := ι_nonneg _
  have hpos : 0<rr.h*rr.H*x := by
    rw [hkey]
    have h1 : rr.h*rr.K<rr.h*rr.H*g := by rw [mul_assoc]; exact mul_lt_mul_of_pos_left hHg hh
    have h2 : 0≤rr.h*rr.H*(rr.V*rr.V)*rr.B :=
      mul_nonneg (mul_nonneg (le_of_lt (mul_pos hh hH)) (mul_self_nonneg _)) hB
    have h3 : 0≤rr.H*rr.B := mul_nonneg (le_of_lt hH) hB
    have h4 : 0≤rr.h*rr.H*rho := mul_nonneg (le_of_lt (mul_pos hh hH)) hrho
    linarith
  have hxpos : 0<x := pos_of_mul_pos_right hpos (le_of_lt (mul_pos hh hH))
  obtain ⟨t,htx⟩ : ∃ t : V, (ι t:DiffRing V)=x := by
    rcases nonneg_or_nonpos x with ⟨t,ht⟩|⟨t,ht⟩
    · exact ⟨t,ht.symm⟩
    · exact absurd hxpos (not_lt_of_ge (by rw [ht]; exact neg_nonpos.mpr (ι_nonneg t)))
  let w : Fin 10 → V := Function.update v 7 t
  have hw : ∀j,0<w j := by
    intro j
    by_cases hj : j=7
    · subst hj
      simp only [w,Function.update_self]
      have h0 : (ι 0:DiffRing V)<ι t := by rw [map_zero,htx]; exact hxpos
      exact ι_lt_ι.mp h0
    · simp only [w,Function.update_of_ne hj]; exact hv j
  have hcast : (fun j => (ι (w j):DiffRing V)) = Function.update (fun j => ι (v j)) 7 x := by
    funext j
    by_cases hj : j=7
    · subst hj; simp only [w,Function.update_self,htx]
    · simp only [w,Function.update_of_ne hj]
  refine ⟨w,hw,?_⟩
  rw [hcast]
  have hsq : (regs (ports p) (Function.update (fun j => ι (v j)) 7 x)).Z*
      (regs (ports p) (Function.update (fun j => ι (v j)) 7 x)).Z=Zs*Zs := by
    rw [hZ75,show Zs=rr.M*z from hZ]
    dsimp [d]
    rcases hzpm with h|h
    · change z=g at h
      rw [h]; ring
    · change z=-g at h
      rw [h]; ring
  rw [value75_of_carrier_sq (ports p) (fun j => ι (v j)) x Zs hsq]
  exact hzn

#print axioms Trace77ToTrace75.positive75_of_positive77
end Trace77ToTrace75
