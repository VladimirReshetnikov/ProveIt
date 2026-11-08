import DiophantineConsistency.BFS943.TransportOrder

/-! # The signed transport estimate at root scale two, weight `L = b V`

Ordered-ring core of package 194's (9) and its product2 analogue. Hypotheses
as in `Centred87Estimate.centred_estimate` (the adjacent Pell norm
`(1+B) V0² = 1 + B y²` at `V0 = |V|`, `V = F b - c`, `c < B`, `2c < F`,
`F² + F ≤ 4B`), with `64 g ≤ F` and an arbitrary shift `ws ≤ 5 g V0`
(no sign assumed). Then

  `2 (2 g y + ws) < b V` and `0 ≤ b V`.

As before `b = 0` is excluded by the norm; for `b ≠ 0`, `V0 > 2B` and
`y < 2 V0` come from the norm alone, and
`F |b| ≥ V0 - c > 2B - c > F²/2 ≥ 32 g F`, so `|b| > 32 g`. Hence
`4 g y + 2 ws < 8 g V0 + 10 g V0 < |b| V0 = b V`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Scaled87Estimate
variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

theorem scaled_estimate (Bq F c b Vs V0 y g ws : K)
    (hB : 0<Bq) (hBc : c<Bq) (hc : 1<c) (hcF : 2*c<F) (hgF : 64*g≤F) (hg : 0<g)
    (hws : ws≤5*g*V0)
    (hy : 0≤y) (hQF : F*F+F≤4*Bq) (hV : Vs=F*b-c) (hV0 : Vs*Vs=V0*V0) (hV0n : 0≤V0)
    (hnorm : (1+Bq)*(V0*V0)=1+Bq*(y*y)) (hdisc : ∀ x : K, 0<x → 1≤x) :
    2*(2*(g*y)+ws)<b*Vs ∧ 0≤b*Vs := by
  have hcpos : 0<c := lt_trans zero_lt_one hc
  have hFpos : 0<F := by linarith
  have hgap : Bq*(y*y-V0*V0)=V0*V0-1 := by linear_combination -hnorm
  -- b = 0 is impossible
  have hb0 : b≠0 := by
    intro hb
    have hVc : Vs=-c := by rw [hV,hb]; ring
    have hsq : (V0-c)*(V0+c)=0 := by
      have h := hV0
      rw [hVc] at h
      linear_combination -h
    have hV0c : V0=c := by
      rcases mul_eq_zero.mp hsq with h|h
      · linear_combination h
      · exfalso; linarith
    rw [hV0c] at hgap
    have hpos : 0<Bq*(y*y-c*c) := by rw [hgap]; nlinarith
    have hyy : c*c<y*y := by
      have := pos_of_mul_pos_right hpos (le_of_lt hB)
      linarith
    have hyc : c<y := lt_of_mul_self_lt_mul_self₀ hy hyy
    have hy1 : c+1≤y := by linarith [hdisc (y-c) (by linarith)]
    have hsq1 : (c+1)*(c+1)≤y*y := mul_self_le_mul_self (by linarith) hy1
    have h1 : Bq*(2*c+1)≤Bq*(y*y-c*c) :=
      mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hB)
    have h2 : c*(2*c+1)<Bq*(2*c+1) := mul_lt_mul_of_pos_right hBc (by linarith)
    nlinarith [mul_pos hcpos hcpos]
  -- unify the two signs of b
  have hW : ∃ W : K, 1≤W ∧ b*Vs=W*V0 ∧ V0-c≤F*W ∧ F-c≤V0 := by
    rcases lt_or_gt_of_ne hb0 with hneg|hpos
    · have hb1 : 1≤-b := hdisc (-b) (by linarith)
      have hFb := mul_le_mul_of_nonneg_left hb1 (le_of_lt hFpos)
      have hVneg : Vs≤-F-c := by rw [hV]; linarith
      have hV0eq : V0=-Vs := by
        have hsq : (V0-(-Vs))*(V0+(-Vs))=0 := by linear_combination -hV0
        rcases mul_eq_zero.mp hsq with h|h
        · linear_combination h
        · exfalso; linarith
      refine ⟨-b,hb1,by rw [hV0eq]; ring,?_,?_⟩
      · rw [hV0eq,hV]; linarith
      · rw [hV0eq]; linarith
    · have hb1 : 1≤b := hdisc b hpos
      have hFb := mul_le_mul_of_nonneg_left hb1 (le_of_lt hFpos)
      have hVpos : F-c≤Vs := by rw [hV]; linarith
      have hV0eq : V0=Vs := by
        have hsq : (V0-Vs)*(V0+Vs)=0 := by linear_combination -hV0
        rcases mul_eq_zero.mp hsq with h|h
        · linear_combination h
        · exfalso; linarith
      refine ⟨b,hb1,by rw [hV0eq],?_,?_⟩
      · rw [hV0eq,hV]; linarith
      · rw [hV0eq]; exact hVpos
  obtain ⟨W,_hW1,hbW,hFW,hFV⟩ := hW
  have hV01 : 1<V0 := by linarith
  have hV0pos : 0<V0 := by linarith
  -- the adjacent norm: y ≥ V0 + 1, hence V0 > 2 Bq, and y < 2 V0
  have hpos : 0<Bq*(y*y-V0*V0) := by rw [hgap]; nlinarith
  have hyy : V0*V0<y*y := by
    have := pos_of_mul_pos_right hpos (le_of_lt hB)
    linarith
  have hyV : V0<y := lt_of_mul_self_lt_mul_self₀ hy hyy
  have hy1 : V0+1≤y := by linarith [hdisc (y-V0) (by linarith)]
  have hsq1 : (V0+1)*(V0+1)≤y*y := mul_self_le_mul_self (by linarith) hy1
  have h1 : Bq*(2*V0+1)≤Bq*(y*y-V0*V0) :=
    mul_le_mul_of_nonneg_left (by linarith) (le_of_lt hB)
  have h3 : (2*Bq)*V0<V0*V0 := by linarith
  have hV0big : 2*Bq<V0 := lt_of_mul_lt_mul_right h3 (le_of_lt hV0pos)
  have hy2 : y<2*V0 := by
    have hB1 : 1≤Bq := hdisc Bq hB
    have hle := mul_le_mul_of_nonneg_right (show 1+Bq≤4*Bq by linarith) (mul_self_nonneg V0)
    have hlt : Bq*(y*y)<Bq*((2*V0)*(2*V0)) := by linarith
    have hyy2 : y*y<(2*V0)*(2*V0) := lt_of_mul_lt_mul_left hlt (le_of_lt hB)
    exact lt_of_mul_self_lt_mul_self₀ (by linarith) hyy2
  -- |b| > 32 g
  have h64 : 64*g*F≤F*F := mul_le_mul_of_nonneg_right hgF (le_of_lt hFpos)
  have hWg : 32*g<W := by
    have hlt : F*(32*g)<F*W := by linarith
    exact lt_of_mul_lt_mul_left hlt (le_of_lt hFpos)
  rw [hbW]
  have h2 := mul_lt_mul_of_pos_left hy2 hg
  have h5 : 32*g*V0<W*V0 := mul_lt_mul_of_pos_right hWg hV0pos
  have h6 : 0<g*V0 := mul_pos hg hV0pos
  exact ⟨by linarith,mul_nonneg (by linarith) (le_of_lt hV0pos)⟩

/-- `64 τ f ≤ 1 + 2a` for `a = D U² τ²`, `f² = 1 + a`, `D U² ≥ 1024`. -/
theorem sixtyfour_le {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]
    (D U tau f : K) (hDU : 1024≤D*(U*U)) (ht : 1≤tau) (hf0 : 0≤f)
    (hf : f*f=1+D*U*U*tau*tau) (hdisc : ∀ x : K, 0<x → 1≤x) :
    64*tau*f≤1+2*(D*U*U*tau*tau) := by
  have htt : 0≤tau*tau := mul_self_nonneg tau
  have h1 : 1024*(tau*tau)≤D*(U*U)*(tau*tau) := mul_le_mul_of_nonneg_right hDU htt
  have hsq : (32*tau)*(32*tau)<f*f := by
    rw [hf]
    have : D*U*U*tau*tau=D*(U*U)*(tau*tau) := by ring
    rw [this]; linarith
  have h32 : 32*tau<f := lt_of_mul_self_lt_mul_self₀ hf0 hsq
  have h32' : 32*tau+1≤f := by linarith [hdisc (f-32*tau) (by linarith)]
  have h2 : 2*f*(32*tau+1)≤2*f*f := mul_le_mul_of_nonneg_left h32' (by linarith)
  have hf1 : 1≤f := by linarith
  have h3 : 2*f*(32*tau+1)=64*(tau*f)+2*f := by ring
  have h4 : 64*tau*f=64*(tau*f) := by ring
  rw [h4]
  linarith

#print axioms Scaled87Estimate.scaled_estimate
#print axioms Scaled87Estimate.sixtyfour_le
end Scaled87Estimate
