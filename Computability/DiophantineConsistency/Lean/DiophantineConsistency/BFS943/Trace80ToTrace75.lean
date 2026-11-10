import DiophantineConsistency.BFS943.Trace80GraphPower
import DiophantineConsistency.BFS943.Trace80NormOffset
import DiophantineConsistency.BFS943.Trace80Parity
import DiophantineConsistency.BFS943.Trace79ToTrace75
import DiophantineConsistency.BFS943.Trace79FromTrace76

/-! # Every positive 80/258 zero gives a positive 75/402 zero

At a positive zero of `value80` (chart q1: `X = q² w`, `Y = q s`, `W = q w`,
`D = q⁶`, offset `N = e - q⁴ s`), `Trace80Transport.graph_zero_data` gives
`Z80 = M z`, `z = ±τ f y`, `B ≥ 0`, the mask, `q⁴ ∣ e` and `q⁶ ∣ N`; the q1
first-index alignment `Trace80NormOffset.graph_offset_exact` gives
`e = 4 X Y² σ = q⁴ s u` with `u = 4 w s σ`, so `q² ∣ s (u - 1)`.

Unlike chart q2 this does not by itself give `q² ∣ s`: the q1 projection
layer gives `X = 2^R` (`Trace80GraphPower.graph_power`), so `q ∣ X` is a
power of two (`Pow2.of_dvd`), and `u + q² - 1` is odd; `Trace80Parity`
cancels it, giving `s = q² s'`.

At `(…, q w, s', n', …)` the q3 chart has `X = (q w) q = q² w`,
`Y = q³ s' = q s` and transport base `q w`: the 75 registers there are the
q1 `regsAt` at the same `X, Y, W` (`regs75_moved`). With `g = τ f y`,
`ρ = 4 Y σ` (`e = XY ρ`) and `N = q⁶ μ`, the coordinate
`n' = n + (g - z) + (V² - bV) B + ρ - μ` makes the 75 carrier `M75 g`, and the
75 output vanishes as in `Trace79ToTrace75`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace80ToTrace75
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace80 TenPositiveTrace76
open Trace80Factors Trace80Residue
open Trace79ToTrace75 (norm_bracket)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Ring
variable {R : Type*} [CommRing R]

/-- The 75 registers at `(…, q w, s', x, …)` with `s = q² s'` are the q1
registers of `regsAt` at `n = x`. -/
theorem regs75_moved (p : Fin 4 → R) (v : Fin 10 → R) (s' x : R)
    (hs : v 6 = (p 0 * v 0 + 1) * (p 0 * v 0 + 1) * s') :
    TenPositiveTrace75.regs p (Function.update (Function.update (Function.update v 5
        ((p 0 * v 0 + 1) * v 5)) 6 s') 7 x) =
      TenPositiveTrace79.regsAt p (Function.update v 7 x) ((p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * v 5))
        ((p 0 * v 0 + 1) * v 6) ((p 0 * v 0 + 1) * v 5) := by
  have hX : (p 0 * v 0 + 1) * v 5 * (p 0 * v 0 + 1) = (p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * v 5) := by
    ring
  have hY : (p 0 * v 0 + 1) * (p 0 * v 0 + 1) * (p 0 * v 0 + 1) * s' = (p 0 * v 0 + 1) * v 6 := by
    rw [hs]; ring
  calc
    TenPositiveTrace75.regs p (Function.update (Function.update (Function.update v 5
        ((p 0 * v 0 + 1) * v 5)) 6 s') 7 x) =
        TenPositiveTrace79.regsAt p (Function.update v 7 x) ((p 0 * v 0 + 1) * v 5 * (p 0 * v 0 + 1))
          ((p 0 * v 0 + 1) * (p 0 * v 0 + 1) * (p 0 * v 0 + 1) * s') ((p 0 * v 0 + 1) * v 5) := rfl
    _ = _ := by rw [hX, hY]

end Ring

theorem positive75_of_positive80 (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (hv : ∀j,0<v j) (hz : value80 (ports p) (fun j => ι (v j)) = 0) :
    ∃ w : Fin 10 → V, (∀j,0<w j) ∧
      TenPositiveTrace75.value75 (Trace75Factors.ports p) (fun j => ι (w j)) = 0 := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  obtain ⟨z,tau,f,y,ht,hf,hy,hf2,hzpm,hZ,hB,hm,hq4,hq6⟩ :=
    Trace80Transport.graph_zero_data p v hb hv hz
  let rr := regs (ports p) (fun j => ι (v j))
  obtain ⟨_n,σ,_hn,_halign,_hk,he⟩ :=
    Trace80NormOffset.graph_offset_exact p v rr.Z hb31 hl hh hv hz hm hq4
  have hpow := Trace80GraphPower.graph_power p v hb31 hl hh hv hz
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hY : 0<Y p v := mul_pos hq (hv 6)
  have hX : 0<X p v := mul_pos hq (mul_pos hq (hv 5))
  have hqr : rr.q=ι (q p v) := by
    dsimp [rr]
    simp only [q_def,h_def,ports,q,b,map_mul,map_add,map_one,map_natCast]
  have hXr : rr.X=ι (X p v) := by
    dsimp [rr]
    simp only [X_def,q_def,h_def,ports,X,q,b,map_mul,map_add,map_one,map_natCast]
  have hYr : rr.Y=ι (Y p v) := by
    dsimp [rr]
    simp only [Y_def,q_def,h_def,ports,Y,q,b,map_mul,map_add,map_one,map_natCast]
  have hhr : rr.h=ι (b p v) := by
    dsimp [rr]
    simp only [h_def,ports,b,map_mul,map_natCast]
  -- `q` is a power of two
  have hP2 : Pow2 (q p v) :=
    Pow2.of_dvd (show q p v∣Exp.exp (Trace80NormRank.rankNat p v) from
      hpow ▸ ⟨q p v*v 5,rfl⟩) (exp_pow2 _)
  have hq2 : (2:V)≤q p v := by
    have hb1 : 1≤b p v := pos_iff_one_le.mp hb0
    simpa only [q,show (2:V)=1+1 by ring,add_comm] using _root_.add_le_add_right hb1 (1:V)
  have hqeven : (2:V)∣q p v := Pow2.two_dvd' hP2 (ne_of_gt (lt_of_lt_of_le (by norm_num) hq2))
  -- `q² ∣ s (u - 1)` with `u = 4 w s σ`
  have hq0 : (ι (q p v):DiffRing V)≠0 := by
    apply ne_of_gt; rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hq
  let u : V := 4*v 5*v 6*σ
  have heu : rr.e-(ι (q p v))^4*ι (v 6)=(ι (q p v))^4*(ι (v 6)*(ι u-1)) := by
    change rr.e=_ at he
    rw [he]
    dsimp [u,firstParam,X,Y]
    simp only [map_mul,map_ofNat]
    ring
  have hs2 : (ι (q p v):DiffRing V)^2∣ι (v 6)*(ι u-1) := by
    rw [heu] at hq6
    have h6 : (ι (q p v):DiffRing V)^6=(ι (q p v))^4*(ι (q p v))^2 := by ring
    rw [h6] at hq6
    exact (mul_dvd_mul_iff_left (pow_ne_zero 4 hq0)).mp hq6
  have hqq1 : 1≤u+q p v*q p v :=
    le_trans (pos_iff_one_le.mp (mul_pos hq hq)) (by simp)
  let a : V := u+q p v*q p v-1
  have hacast : (ι a:DiffRing V)=ι u+ι (q p v)^2-1 := by
    apply eq_sub_iff_add_eq.mpr
    rw [←map_one (ι : V →+* DiffRing V),←map_add,tsub_add_cancel_of_le hqq1]
    simp only [map_add,map_mul,pow_two]
  have hodd : ¬ (2:V)∣a := Trace80Parity.odd_pred u (q p v*q p v)
    ⟨2*v 5*v 6*σ,by dsimp [u]; ring⟩ (dvd_mul_of_dvd_left hqeven _) hqq1
  have hda : (ι (q p v*q p v):DiffRing V)∣ι a*ι (v 6) := by
    rw [hacast,map_mul,←pow_two]
    have h2 : (ι u+ι (q p v)^2-1)*ι (v 6)=ι (v 6)*(ι u-1)+(ι (q p v))^2*ι (v 6) := by ring
    rw [h2]
    exact dvd_add hs2 (dvd_mul_right _ _)
  have hs5 : (ι (q p v*q p v):DiffRing V)∣ι (v 6) :=
    Trace80Parity.pow2_cancel_odd (q p v*q p v) a (ι (v 6)) (Pow2.mul hP2 hP2) hodd hda
  obtain ⟨t,htq⟩ := hs5
  have hst : (ι (v 6):DiffRing V)=ι (q p v)*ι (q p v)*t := by rw [htq,map_mul]
  have htpos : 0<t := by
    have h6 : (0:DiffRing V)<ι (v 6) := by rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hv 6
    rw [hst] at h6
    exact pos_of_mul_pos_right h6 (by rw [←map_mul]; exact ι_nonneg _)
  obtain ⟨s',hs'⟩ : ∃ s' : V, (ι s':DiffRing V)=t := by
    rcases nonneg_or_nonpos t with ⟨u,hu⟩|⟨u,hu⟩
    · exact ⟨u,hu.symm⟩
    · exact absurd htpos (not_lt_of_ge (by rw [hu]; exact neg_nonpos.mpr (ι_nonneg u)))
  have hs'pos : 0<s' := by
    have h0 : (ι 0:DiffRing V)<ι s' := by rw [map_zero,hs']; exact htpos
    exact ι_lt_ι.mp h0
  -- the offsets `e = XY ρ` and `N = q⁶ μ`
  let rho : DiffRing V := ι (4*Y p v*σ)
  have heXY : rr.e=rr.X*rr.Y*rho := by
    change rr.e=_ at he
    rw [he,hXr,hYr]
    dsimp [rho,firstParam]
    simp only [map_mul,map_ofNat]
    ring
  obtain ⟨μ,hμ⟩ := hq6
  have hNμ : rr.e-rr.q*rr.q*(rr.q*rr.q)*ι (v 6)=rr.D*μ := by
    rw [D_def,hqr]
    linear_combination hμ
  -- the moved coordinate
  let g : DiffRing V := ι (tau*f*y)
  let x : DiffRing V := ι (v 7)+(g-z)+(rr.V*rr.V-rr.b*rr.V)*rr.B+rho-μ
  have hshape : rr.Z=rr.h*rr.D*(rr.H*(ι (v 7)-(rr.b*rr.V)*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*(rr.e-rr.q*rr.q*(rr.q*rr.q)*ι (v 6))) := Z_def (ports p) (fun j => ι (v j))
  have hZ'' : rr.Z=rr.h*rr.D*rr.H*z := by rw [hZ,M_def]
  have hD0 : rr.D≠0 := by
    rw [D_def,hqr]
    exact mul_ne_zero (mul_ne_zero (mul_ne_zero hq0 hq0) (mul_ne_zero hq0 hq0)) (mul_ne_zero hq0 hq0)
  have hkey : rr.h*rr.H*x=rr.h*rr.H*g+rr.h*rr.H*(rr.V*rr.V)*rr.B+rr.H*rr.B+
      rr.h*rr.H*rho-rr.h*rr.K := by
    apply mul_left_cancel₀ hD0
    dsimp [x]
    linear_combination hZ''-hshape+rr.h*rr.H*hNμ
  -- positivity, as in `Trace79ToTrace75`
  obtain ⟨hD0',hU0,hE0,_hM0⟩ := factors_positive p v hb hv
  have hC : 0<c p v := add_pos (mul_pos (add_pos (hv 8) (hv 9)) hY) (hv 8)
  have hcU : c p v*c p v≤U p v :=
    le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp (hv 3))
  have hUa : U p v≤delta p v*U p v*U p v*E p v := by
    calc
      U p v≤delta p v*U p v := le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp hD0')
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
  have hAr : rr.Am1=ι (A p v) := by
    dsimp [rr]
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,A,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
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
    exact Trace79FromTrace76.K_lt_Hg (ι (X p v)) (ι (c p v)) (ι (A p v)) g hX1 hcR hAX hcgR
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
  obtain ⟨n',hn'⟩ : ∃ n' : V, (ι n':DiffRing V)=x := by
    rcases nonneg_or_nonpos x with ⟨u,hu⟩|⟨u,hu⟩
    · exact ⟨u,hu.symm⟩
    · exact absurd hxpos (not_lt_of_ge (by rw [hu]; exact neg_nonpos.mpr (ι_nonneg u)))
  have hn'pos : 0<n' := by
    have h0 : (ι 0:DiffRing V)<ι n' := by rw [map_zero,hn']; exact hxpos
    exact ι_lt_ι.mp h0
  -- the 75 point
  let w : Fin 10 → V :=
    Function.update (Function.update (Function.update v 5 (q p v*v 5)) 6 s') 7 n'
  have hw : ∀j,0<w j := by
    intro j
    by_cases h7 : j=7
    · subst h7; simp only [w,Function.update_self]; exact hn'pos
    · by_cases h6 : j=6
      · subst h6; simp only [w,Function.update_of_ne h7,Function.update_self]; exact hs'pos
      · by_cases h5 : j=5
        · subst h5
          simp only [w,Function.update_of_ne h7,Function.update_of_ne h6,Function.update_self]
          exact mul_pos hq (hv 5)
        · simp only [w,Function.update_of_ne h7,Function.update_of_ne h6,Function.update_of_ne h5]
          exact hv j
  have hcast : (fun j => (ι (w j):DiffRing V)) =
      Function.update (Function.update (Function.update (fun j => ι (v j)) 5
        (((ports p) 0*(fun j => (ι (v j):DiffRing V)) 0+1)*ι (v 5))) 6 (ι s')) 7 x := by
    funext j
    by_cases h7 : j=7
    · subst h7; simp only [w,Function.update_self,hn']
    · by_cases h6 : j=6
      · subst h6; simp only [w,Function.update_of_ne h7,Function.update_self]
      · by_cases h5 : j=5
        · subst h5
          simp only [w,Function.update_of_ne h7,Function.update_of_ne h6,Function.update_self,map_mul]
          rw [←hqr]; rfl
        · simp only [w,Function.update_of_ne h7,Function.update_of_ne h6,Function.update_of_ne h5]
  refine ⟨w,hw,?_⟩
  rw [hcast]
  have hsq : (fun j => (ι (v j):DiffRing V)) 6 =
      ((ports p) 0*(fun j => (ι (v j):DiffRing V)) 0+1)*
        ((ports p) 0*(fun j => (ι (v j):DiffRing V)) 0+1)*ι s' := by
    change ι (v 6)=_
    rw [hst,←hs',←hqr]; rfl
  have hR := regs75_moved (ports p) (fun j => ι (v j)) (ι s') x hsq
  -- the bracket vanishes at the 80 zero
  have hzz : z*z=g*g := by
    rcases hzpm with h|h
    · change z=g at h
      rw [h]
    · change z=-g at h
      rw [h]; ring
  have hM0 : rr.M≠0 := by
    rw [M_eval p v hb hv]
    apply ne_of_gt
    rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]
    exact (factors_positive p v hb hv).2.2.2
  have hbr : rr.Q*(g*g-rr.Gn*(rr.V*rr.V))+(rr.Gn-g*g)=0 := by
    have h1 : normValue rr (rr.M*z)=0 := by rw [←hZ]; exact hz
    rw [norm_bracket,hzz] at h1
    exact (mul_eq_zero.mp h1).resolve_left (mul_ne_zero hM0 hM0)
  have hfin : ∀ RA : TenPositiveTrace75.Regs (DiffRing V), RA.Z=(rr.h*(rr.X*rr.Y)*rr.H)*g →
      RA.M=rr.h*(rr.X*rr.Y)*rr.H → RA.Q=rr.Q → RA.Gn=rr.Gn → RA.V=rr.V → normValue RA RA.Z=0 := by
    intro RA h1 h5 h2 h3 h4
    rw [h1,←h5,norm_bracket,h2,h3,h4,hbr,mul_zero]
  show TenPositiveTrace75.value75 (ports p)
    (Function.update (Function.update (Function.update (fun j => (ι (v j):DiffRing V)) 5
      (((ports p) 0*(fun j => (ι (v j):DiffRing V)) 0+1)*ι (v 5))) 6 (ι s')) 7 x) = 0
  rw [value75_norm,hR]
  apply hfin
  · change rr.h*(rr.X*rr.Y)*(rr.H*(x-rr.V*rr.V*rr.B)+rr.K)-rr.H*(rr.X*rr.Y*rr.B+rr.h*rr.e)=_
    linear_combination (rr.X*rr.Y)*hkey-rr.h*rr.H*heXY
  all_goals rfl

#print axioms Trace80ToTrace75.positive75_of_positive80
end Trace80ToTrace75
