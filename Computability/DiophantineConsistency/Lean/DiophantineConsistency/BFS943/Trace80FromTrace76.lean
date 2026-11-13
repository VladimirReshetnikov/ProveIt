import DiophantineConsistency.BFS943.Trace80Regs
import DiophantineConsistency.BFS943.Trace80Factors
import DiophantineConsistency.BFS943.Trace79FromTrace76
import DiophantineConsistency.BFS943.Trace75RadixAlignment

/-! # Every positive 76/352 zero gives a positive 80/258 zero

The completeness map for chart q1. At a positive 76 zero `(…, w, s, n, …)`
everything up to `σ ≥ 1` is as in `Trace79FromTrace76`: the carrier quotient
`Z76 = M z`, `B ≥ 0`, `bV ≥ 0`, and at the moved 75 zero `e = 4 X Y² σ`
with `σ ≥ 1`. In addition the q1 chart needs `q ∣ w`: at the moved 75 zero,
`Trace75RadixAlignment.graph_radix_alignment` (with `β + 1 = 2^d`) gives
`q = 2^{dN}` and `w = 2^{R - dN}`, and `dN < 2^{dN} = q < 3q < R` gives
`w = q w''` with `w'' = 2^{R - 2dN}`.

At `(…, w'', q² s, n'', …)` the q1 chart has `X = q (q w'') = w q`,
`Y = q (q² s) = q³ s` and transport base `q w'' = w`: the q1 `regsAt` there is
the q3 `regsAt` at `(…, w, s, …)` (`regsAt_moved`). The denominator is `q⁶`
and the offset `e - q⁴ (q² s) = q⁶ μ` with `μ = 4 w q s² σ - s ≥ 0`. With
`g = τ f y` the coordinate `n'' = n + (g - z) - ρ + μ` (`ρ = 4 Y σ`) makes
the 80 carrier `M80 g`, so the 80 output vanishes; positivity is that of
`Trace79FromTrace76`. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 16384
noncomputable section
namespace Trace80FromTrace76
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder LO.FirstOrder.Arithmetic
open DiophantineConsistency ModelDifferenceRing TenPositiveTrace75 TenPositiveTrace76
open Trace75Factors Trace75Residue Trace75Pell
open Trace75Rank (rankNat)
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

section Ring
variable {R : Type*} [CommRing R]

/-- The q1 `regsAt` at `(…, w'', q² s, x, …)` with `w = q w''` is the q3
`regsAt` at `(…, w, s, x, …)`. -/
theorem regsAt_moved (p : Fin 4 → R) (v : Fin 10 → R) (w2 x : R)
    (hw : v 5 = (p 0 * v 0 + 1) * w2) :
    TenPositiveTrace79.regsAt p
      (Function.update (Function.update (Function.update v 5 w2) 6
        ((p 0 * v 0 + 1) * (p 0 * v 0 + 1) * v 6)) 7 x)
      ((p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * w2))
      ((p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * (p 0 * v 0 + 1) * v 6))
      ((p 0 * v 0 + 1) * w2) =
    TenPositiveTrace79.regsAt p (Function.update v 7 x)
      (v 5 * (p 0 * v 0 + 1)) ((p 0 * v 0 + 1) * (p 0 * v 0 + 1) * (p 0 * v 0 + 1) * v 6) (v 5) := by
  have hX : (p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * w2) = v 5 * (p 0 * v 0 + 1) := by rw [hw]; ring
  have hY : (p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * (p 0 * v 0 + 1) * v 6) =
      (p 0 * v 0 + 1) * (p 0 * v 0 + 1) * (p 0 * v 0 + 1) * v 6 := by ring
  calc
    _ = TenPositiveTrace79.regsAt p (Function.update v 7 x)
      ((p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * w2))
      ((p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * (p 0 * v 0 + 1) * v 6))
      ((p 0 * v 0 + 1) * w2) := rfl
    _ = _ := by rw [hX, hY, ← hw]

/-- The 80 registers built from a q1 `regsAt` record, its `s` and its `n`. -/
def build80 (r : Regs R) (s6 x : R) : Regs R :=
  let D := r.q * r.q * (r.q * r.q) * (r.q * r.q)
  { r with D := D,
           Z := r.h * D * (r.H * (x - r.b * r.V * r.B) + r.K) -
             r.H * (D * r.B + r.h * (r.e - r.q * r.q * (r.q * r.q) * s6)),
           M := r.h * D * r.H }

theorem regs80_moved (p : Fin 4 → R) (v : Fin 10 → R) (w2 x : R)
    (hw : v 5 = (p 0 * v 0 + 1) * w2) :
    TenPositiveTrace80.regs p (Function.update (Function.update (Function.update v 5 w2) 6
        ((p 0 * v 0 + 1) * (p 0 * v 0 + 1) * v 6)) 7 x) =
      build80 (TenPositiveTrace79.regsAt p (Function.update v 7 x)
        (v 5 * (p 0 * v 0 + 1)) ((p 0 * v 0 + 1) * (p 0 * v 0 + 1) * (p 0 * v 0 + 1) * v 6) (v 5))
        ((p 0 * v 0 + 1) * (p 0 * v 0 + 1) * v 6) x := by
  show build80 (TenPositiveTrace79.regsAt p
      (Function.update (Function.update (Function.update v 5 w2) 6
        ((p 0 * v 0 + 1) * (p 0 * v 0 + 1) * v 6)) 7 x)
      ((p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * w2))
      ((p 0 * v 0 + 1) * ((p 0 * v 0 + 1) * (p 0 * v 0 + 1) * v 6))
      ((p 0 * v 0 + 1) * w2))
      ((p 0 * v 0 + 1) * (p 0 * v 0 + 1) * v 6) x = _
  rw [regsAt_moved p v w2 x hw]

/-- The 80 registers at `(…, w'', q² s, x, …)` in terms of the 75 registers at `(…, w, s, …)`. -/
theorem moved_fields (p : Fin 4 → R) (v : Fin 10 → R) (w2 x : R)
    (hw : v 5 = (p 0 * v 0 + 1) * w2) :
    let r80 := TenPositiveTrace80.regs p (Function.update (Function.update (Function.update v 5 w2) 6
        ((p 0 * v 0 + 1) * (p 0 * v 0 + 1) * v 6)) 7 x)
    let r := regs p v
    let D := r.q * r.q * (r.q * r.q) * (r.q * r.q)
    r80.Q = r.Q ∧ r80.Gn = r.Gn ∧ r80.V = r.V ∧ r80.M = r.h * D * r.H ∧
    r80.Z = r.h * D * (r.H * (x - r.b * r.V * r.B) + r.K) -
        r.H * (D * r.B + r.h * (r.e - r.q * r.q * (r.q * r.q) * (r.q * r.q * v 6))) := by
  intro r80 r D
  have h := regs80_moved p v w2 x hw
  simp only [r80]
  rw [h]
  exact ⟨rfl,rfl,rfl,rfl,rfl⟩

end Ring

theorem positive80_of_positive76 (p : Fin 4 → ℕ) (v : Fin 10 → V)
    (hb31 : (31:V)≤(p 0:V)) (hl : (p 2:V)<(p 0:V)) (hh : (p 3:V)<2*(p 0:V))
    (d : V) (hd : 2≤d) (hbeta : (p 0:V)+1=Exp.exp d)
    (hv : ∀j,0<v j) (hz : value76 (ports p) (fun j => ι (v j)) = 0) :
    ∃ w : Fin 10 → V, (∀j,0<w j) ∧
      TenPositiveTrace80.value80 (Trace80Factors.ports p) (fun j => ι (w j)) = 0 := by
  have hb : 0<(p 0:V) := lt_of_lt_of_le (by norm_num : (0:V)<31) hb31
  let rr := regs (ports p) (fun j => ι (v j))
  let Z : DiffRing V := Z76 (ports p) (fun j => ι (v j))
  have hzn : normValue rr Z = 0 := hz
  obtain ⟨tau,f,Z0,y,ht,hf,hy,hf2,hZsq,hZeq,_hbound,hL,_hsign⟩ :=
    Trace77Transport.graph_bv_bound p v Z hb hv hzn
  have hB : 0≤rr.B := (Trace76Transport.graph_transport p v hb hv hz).1
  -- the carrier quotient
  let g : DiffRing V := ι (tau*f*y)
  let mz : DiffRing V := ι (M p v)*g
  have hsq : Z*Z=mz*mz := by
    calc
      Z*Z=ι (Z0*Z0) := hZsq
      _=mz*mz := by rw [hZeq]; dsimp [mz,g]; simp only [map_mul]; ring
  have hfactor : (Z-mz)*(Z+mz)=0 := by rw [show (Z-mz)*(Z+mz)=Z*Z-mz*mz by ring,hsq]; ring
  have hcarrier : ∃ z : DiffRing V, Z=rr.M*z ∧ z*z=g*g := by
    rcases mul_eq_zero.mp hfactor with h|h
    · exact ⟨g,by rw [M_eval p v hb hv]; exact sub_eq_zero.mp h,rfl⟩
    · refine ⟨-g,?_,by ring⟩
      have heq : Z= -mz := eq_neg_of_add_eq_zero_left h
      rw [M_eval p v hb hv]
      dsimp [mz] at heq
      simpa only [mul_neg] using heq
  obtain ⟨z,hZ,hzz⟩ := hcarrier
  -- the 75 zero with the same offset, `σ ≥ 1`, and `q ∣ w`
  let dd : DiffRing V := (rr.V*rr.V-rr.b*rr.V)*rr.B
  have hdd : 0≤dd := (Trace76Transport.graph_transport p v hb hv hz).2
  obtain ⟨t,htd⟩ : ∃ t : V, (ι t:DiffRing V)=dd := by
    rcases nonneg_or_nonpos dd with ⟨t,ht⟩|⟨t,ht⟩
    · exact ⟨t,ht.symm⟩
    · refine ⟨t,?_⟩
      have h0 : (ι t:DiffRing V)≤0 := by linarith
      have h1 : (ι t:DiffRing V)=0 := le_antisymm h0 (ι_nonneg t)
      rw [ht,h1]; simp
  let w0 : Fin 10 → V := Function.update v 7 (v 7+t)
  have hw0 : ∀j,0<w0 j := by
    intro j
    by_cases hj : j=7
    · subst hj; simp only [w0,Function.update_self]; exact add_pos_of_pos_of_nonneg (hv 7) (by simp)
    · simp only [w0,Function.update_of_ne hj]; exact hv j
  have hcast0 : (fun j => (ι (w0 j):DiffRing V)) =
      Function.update (fun j => ι (v j)) 7 (ι (v 7)+dd) := by
    funext j
    by_cases hj : j=7
    · subst hj; simp only [w0,Function.update_self,map_add,htd]
    · simp only [w0,Function.update_of_ne hj]
  have hz75 : value75 (ports p) (fun j => ι (w0 j)) = 0 := by
    rw [hcast0,value75_update (ports p) (fun j => ι (v j)) (ι (v 7)+dd) rfl]
    exact hz
  obtain ⟨_n0,σ,_hn0,_halign,hk,he⟩ := Trace75OffsetExact.graph_offset_exact p w0 hb31 hl hh hw0 hz75
  have hew : (regs (ports p) (fun j => ι (w0 j))).e=rr.e := by rw [hcast0]; rfl
  rw [hew] at he
  change rr.e=ι ((4*firstParam p v)*σ) at he
  change k v=rankNat p v+1+(4*firstParam p v)*σ at hk
  have hsize := (Trace75Size.graph_rank_size p w0 hb hw0 hz75).1
  change 8*firstParam p v+4≤k v at hsize
  have hwin := (Trace75Rank.graph_rank_window p w0 hb31 hl hh hw0 hz75).2.2.2.1
  change rankNat p v+q p v^3+q p v+1≤q p v^4 at hwin
  have h3q := (Trace75RankExact.graph_rank_exact p w0 hb31 hl hh hw0 hz75).2.1
  change 3*q p v<rankNat p v at h3q
  obtain ⟨N,_hN,hqN,hdNR,hw5⟩ :=
    Trace75RadixAlignment.graph_radix_alignment p w0 d hb31 hl hh hw0 hz75 hd hbeta
  change q p v=Exp.exp (d*N) at hqN
  change d*N≤rankNat p v at hdNR
  change v 5=Exp.exp (rankNat p v-d*N) at hw5
  have hb0 : 0<b p v := mul_pos hb (hv 0)
  have hq : 0<q p v := add_pos hb0 (by simp)
  have hq1 : 1≤q p v := pos_iff_one_le.mp hq
  have hY : 0<Y p v := mul_pos (mul_pos (mul_pos hq hq) hq) (hv 6)
  have hX : 0<X p v := mul_pos (hv 5) hq
  let w2 : V := Exp.exp (rankNat p v-d*N-d*N)
  have hvw : v 5=q p v*w2 := by
    have hlt : d*N<q p v := by rw [hqN]; exact lt_exp _
    have h2 : d*N+d*N≤rankNat p v := by
      have h' : d*N+d*N<3*q p v := calc
        d*N+d*N<q p v+q p v := add_lt_add hlt hlt
        _≤3*q p v := by
          have : q p v+q p v=2*q p v := by ring
          rw [this]; exact mul_le_mul_of_nonneg_right (by norm_num) (by simp)
      exact le_of_lt (lt_trans h' h3q)
    have hsplit : rankNat p v-d*N=d*N+(rankNat p v-d*N-d*N) := by
      have h4 : d*N≤rankNat p v-d*N := le_tsub_of_add_le_left h2
      exact (add_tsub_cancel_of_le h4).symm
    rw [hw5,hsplit,exp_add,←hqN]
  have hw2 : 0<w2 := exp_pos _
  have hσ : 1≤σ := by
    by_contra hn
    have h0 : σ=0 := by
      by_contra hne
      exact hn (pos_iff_one_le.mp (pos_iff_ne_zero.mpr hne))
    rw [h0,mul_zero,add_zero] at hk
    have hq4P : q p v^4≤firstParam p v := by
      have hqX : q p v≤X p v := by
        change q p v≤v 5*q p v
        exact le_mul_of_one_le_left (by simp) (pos_iff_one_le.mp (hv 5))
      have hqY : q p v*q p v*q p v≤Y p v := by
        change q p v*q p v*q p v≤(q p v*q p v*q p v)*v 6
        exact le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp (hv 6))
      calc
        q p v^4=q p v*(q p v*q p v*q p v) := by ring
        _≤X p v*Y p v := mul_le_mul hqX hqY (by simp) (by simp)
        _≤X p v*(Y p v*Y p v) := mul_le_mul_of_nonneg_left
            (le_mul_of_one_le_right (by simp) (pos_iff_one_le.mp hY)) (by simp)
    have h1 : rankNat p v+1≤q p v^4 := by
      have h0 : rankNat p v+1≤rankNat p v+q p v^3+q p v+1 := by
        have : rankNat p v≤rankNat p v+q p v^3+q p v :=
          le_add_of_le_of_nonneg (le_add_of_nonneg_right (by simp)) (by simp)
        exact add_le_add this le_rfl
      exact le_trans h0 hwin
    have h2 : 8*q p v^4+4≤k v :=
      le_trans (add_le_add (mul_le_mul_of_nonneg_left hq4P (by simp)) le_rfl) hsize
    have h3 : q p v^4<8*q p v^4+4 :=
      lt_of_lt_of_le (lt_add_of_pos_right _ (by norm_num : (0:V)<4))
        (add_le_add (le_mul_of_one_le_left (by simp) (by norm_num)) le_rfl)
    rw [hk] at h2
    exact absurd (lt_of_lt_of_le h3 (le_trans h2 h1)) (_root_.lt_irrefl _)
  -- the offsets
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
  have hAr : rr.Am1=ι (A p v) := by
    dsimp [rr]
    simp only [Am1_def,X_def,Y_def,q_def,h_def,ports,A,X,Y,q,b,map_mul,map_add,map_one,map_natCast]
  let rho : DiffRing V := ι (4*Y p v*σ)
  have heXY : rr.e=rr.X*rr.Y*rho := by
    rw [he,hXr,hYr]
    dsimp [rho,firstParam]
    simp only [map_mul,map_ofNat]
    ring
  have hμle : v 6≤4*v 5*q p v*v 6*v 6*σ := by
    have h1 : 1≤4*v 5*q p v*v 6*σ :=
      pos_iff_one_le.mp (mul_pos (mul_pos (mul_pos (mul_pos (by norm_num) (hv 5)) hq)
        (hv 6)) (lt_of_lt_of_le (by simp) hσ))
    calc
      v 6=1*v 6 := (one_mul _).symm
      _≤(4*v 5*q p v*v 6*σ)*v 6 := mul_le_mul_of_nonneg_right h1 (by simp)
      _=4*v 5*q p v*v 6*v 6*σ := by ring
  let μn : V := 4*v 5*q p v*v 6*v 6*σ-v 6
  let μ : DiffRing V := ι μn
  have hμcast : μ=ι (4*v 5*q p v*v 6*v 6*σ)-ι (v 6) := by
    change (ι (4*v 5*q p v*v 6*v 6*σ-v 6):DiffRing V)=_
    apply eq_sub_iff_add_eq.mpr
    rw [←map_add]
    exact congrArg _ (tsub_add_cancel_of_le hμle)
  let D : DiffRing V := rr.q*rr.q*(rr.q*rr.q)*(rr.q*rr.q)
  have hNμ : rr.e-rr.q*rr.q*(rr.q*rr.q)*(rr.q*rr.q*ι (v 6))=D*μ := by
    rw [heXY,hXr,hYr,hμcast]
    dsimp [D,rho]
    rw [hqr]
    simp only [X,Y,map_mul,map_ofNat]
    ring
  -- the 76 carrier relation
  have hshape : Z=rr.h*rr.D*(rr.H*(ι (v 7)-rr.b*rr.V*rr.B)+rr.K)-
      rr.H*(rr.D*rr.B+rr.h*rr.e) := Z76_def (ports p) (fun j => ι (v j))
  have hDr : rr.D=rr.X*rr.Y := D_def _ _
  have hMr : rr.M=rr.h*(rr.X*rr.Y)*rr.H := M_def _ _
  have hXYpos : 0<rr.X*rr.Y := by
    rw [hXr,hYr,←map_mul,←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact mul_pos hX hY
  have h76 : rr.h*rr.H*ι (v 7)=rr.h*rr.H*z+rr.h*rr.H*(rr.b*rr.V)*rr.B-rr.h*rr.K+rr.H*rr.B+
      rr.h*rr.H*rho := by
    apply mul_left_cancel₀ (ne_of_gt hXYpos)
    rw [hDr,heXY] at hshape
    rw [hMr] at hZ
    linear_combination hZ-hshape
  -- the moved 80 coordinate
  let x : DiffRing V := ι (v 7)+(g-z)-rho+μ
  have hkey : rr.h*rr.H*x=rr.h*rr.H*g+rr.h*rr.H*(rr.b*rr.V)*rr.B+rr.H*rr.B+
      rr.h*rr.H*μ-rr.h*rr.K := by
    dsimp [x]
    linear_combination h76
  -- positivity, as in `Trace79FromTrace76`
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
    have hsq' : f*f≤c p v*c p v := mul_le_mul hfc hfc (by simp) (by simp)
    have h1 : 1+delta p v*U p v*U p v*E p v≤delta p v*U p v*U p v*E p v := by
      rw [hf2]; exact le_trans hsq' (le_trans hcU hUa)
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
    exact Trace79FromTrace76.K_lt_Hg (ι (X p v)) (ι (c p v)) (ι (A p v)) g hX1 hcR hAX hcgR
  have hh' : 0<rr.h := by rw [hhr,←map_zero (ι : V →+* DiffRing V),ι_lt_ι]; exact hb0
  have hH : 0<rr.H := by
    rw [hHr]; linarith
  have hμ0 : 0≤μ := ι_nonneg _
  have hpos : 0<rr.h*rr.H*x := by
    rw [hkey]
    have h1 : rr.h*rr.K<rr.h*rr.H*g := by rw [mul_assoc]; exact mul_lt_mul_of_pos_left hHg hh'
    have h2 : 0≤rr.h*rr.H*(rr.b*rr.V)*rr.B :=
      mul_nonneg (mul_nonneg (le_of_lt (mul_pos hh' hH)) hL) hB
    have h3 : 0≤rr.H*rr.B := mul_nonneg (le_of_lt hH) hB
    have h4 : 0≤rr.h*rr.H*μ := mul_nonneg (le_of_lt (mul_pos hh' hH)) hμ0
    linarith
  have hxpos : 0<x := pos_of_mul_pos_right hpos (le_of_lt (mul_pos hh' hH))
  obtain ⟨n',hn'⟩ : ∃ n' : V, (ι n':DiffRing V)=x := by
    rcases nonneg_or_nonpos x with ⟨u,hu⟩|⟨u,hu⟩
    · exact ⟨u,hu.symm⟩
    · exact absurd hxpos (not_lt_of_ge (by rw [hu]; exact neg_nonpos.mpr (ι_nonneg u)))
  have hn'pos : 0<n' := by
    have h0 : (ι 0:DiffRing V)<ι n' := by rw [map_zero,hn']; exact hxpos
    exact ι_lt_ι.mp h0
  -- the 80 point
  let w : Fin 10 → V :=
    Function.update (Function.update (Function.update v 5 w2) 6 (q p v*q p v*v 6)) 7 n'
  have hw : ∀j,0<w j := by
    intro j
    by_cases h7 : j=7
    · subst h7; simp only [w,Function.update_self]; exact hn'pos
    · by_cases h6 : j=6
      · subst h6; simp only [w,Function.update_of_ne h7,Function.update_self]
        exact mul_pos (mul_pos hq hq) (hv 6)
      · by_cases h5 : j=5
        · subst h5
          simp only [w,Function.update_of_ne h7,Function.update_of_ne h6,Function.update_self]
          exact hw2
        · simp only [w,Function.update_of_ne h7,Function.update_of_ne h6,Function.update_of_ne h5]
          exact hv j
  have hcast : (fun j => (ι (w j):DiffRing V)) =
      Function.update (Function.update (Function.update (fun j => ι (v j)) 5 (ι w2)) 6
        (((ports p) 0*ι (v 0)+1)*((ports p) 0*ι (v 0)+1)*ι (v 6))) 7 x := by
    funext j
    by_cases h7 : j=7
    · subst h7; simp only [w,Function.update_self,hn']
    · by_cases h6 : j=6
      · subst h6
        simp only [w,Function.update_of_ne h7,Function.update_self,map_mul]
        rw [←hqr]; rfl
      · by_cases h5 : j=5
        · subst h5
          simp only [w,Function.update_of_ne h7,Function.update_of_ne h6,Function.update_self]
        · simp only [w,Function.update_of_ne h7,Function.update_of_ne h6,Function.update_of_ne h5]
  refine ⟨w,hw,?_⟩
  have hwR : (fun j => (ι (v j):DiffRing V)) 5 =
      ((ports p) 0*(fun j => (ι (v j):DiffRing V)) 0+1)*ι w2 := by
    change ι (v 5)=_
    rw [hvw,map_mul,←hqr]; rfl
  -- the bracket vanishes at the 76 zero
  have hM0 : rr.M≠0 := by
    rw [M_eval p v hb hv]
    apply ne_of_gt
    rw [←map_zero (ι : V →+* DiffRing V),ι_lt_ι]
    exact (factors_positive p v hb hv).2.2.2
  have hbr : rr.Q*(g*g-rr.Gn*(rr.V*rr.V))+(rr.Gn-g*g)=0 := by
    have h1 : normValue rr (rr.M*z)=0 := by rw [←hZ]; exact hzn
    rw [Trace79ToTrace75.norm_bracket,hzz] at h1
    exact (mul_eq_zero.mp h1).resolve_left (mul_ne_zero hM0 hM0)
  have hfin : ∀ RA : Regs (DiffRing V),
      RA.Z=rr.h*D*(rr.H*(x-rr.b*rr.V*rr.B)+rr.K)-
        rr.H*(D*rr.B+rr.h*(rr.e-rr.q*rr.q*(rr.q*rr.q)*(rr.q*rr.q*ι (v 6)))) →
      RA.M=rr.h*D*rr.H → RA.Q=rr.Q → RA.Gn=rr.Gn → RA.V=rr.V → normValue RA RA.Z=0 := by
    intro RA h1 h5 h2 h3 h4
    have hZg : RA.Z=RA.M*g := by
      rw [h1,h5]
      linear_combination D*hkey-rr.h*rr.H*hNμ
    rw [hZg,Trace79ToTrace75.norm_bracket,h2,h3,h4,hbr,mul_zero]
  rw [hcast,TenPositiveTrace80.value80_norm]
  obtain ⟨hQ,hG,hV,hM,hZ80⟩ := moved_fields (ports p) (fun j => (ι (v j):DiffRing V)) (ι w2) x hwR
  exact hfin _ hZ80 hM hQ hG hV

#print axioms Trace80FromTrace76.positive80_of_positive76
end Trace80FromTrace76
