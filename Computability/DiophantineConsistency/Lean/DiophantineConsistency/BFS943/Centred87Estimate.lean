import DiophantineConsistency.BFS943.TransportOrder

/-! # The centred signed transport estimate for the weight `L = b V`

Ordered-ring core of package 179's late-front bound (its (3)–(4)) for the
centred carriers `n ↦ n - V (b B + ĝ)`. Hypotheses as in
`Trace76Estimate.bv_estimate` (the adjacent Pell norm
`(1+B) V0² = 1 + B y²` at `V0 = |V|`, `V = F b - c`, `c < B`, `2c < F`,
`F² + F ≤ 4B`), but with `16 g ≤ F` in place of `8 g ≤ F`, and a centre
`0 ≤ ĝ < 2 g`. Then

  `2 (g y + ĝ V0) < b V` and `0 ≤ b V`.

As in `bv_estimate`, `b = 0` is excluded by the norm; for `b ≠ 0`,
`V0 > 2B` and `y < 2 V0` come from the norm alone, and
`F |b| ≥ V0 - c > 2B - c ≥ (F² + F)/2 - c > F²/2 ≥ 8 g F`, so `|b| > 8 g`.
Hence `2 g y + 2 ĝ V0 < 4 g V0 + 4 g V0 < |b| V0 = b V`. No index-three
exclusion is used. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Centred87Estimate
variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

theorem centred_estimate (Bq F c b Vs V0 y g gc : K)
    (hB : 0<Bq) (hBc : c<Bq) (hc : 1<c) (hcF : 2*c<F) (hgF : 16*g≤F) (hg : 0<g)
    (hgc0 : 0≤gc) (hgc : gc<2*g)
    (hy : 0≤y) (hQF : F*F+F≤4*Bq) (hV : Vs=F*b-c) (hV0 : Vs*Vs=V0*V0) (hV0n : 0≤V0)
    (hnorm : (1+Bq)*(V0*V0)=1+Bq*(y*y)) (hdisc : ∀ x : K, 0<x → 1≤x) :
    2*(g*y+gc*V0)<b*Vs ∧ 0≤b*Vs := by
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
  -- |b| > 8 g
  have h16 : 16*g*F≤F*F := mul_le_mul_of_nonneg_right hgF (le_of_lt hFpos)
  have hWg : 8*g<W := by
    have hlt : F*(8*g)<F*W := by linarith
    exact lt_of_mul_lt_mul_left hlt (le_of_lt hFpos)
  rw [hbW]
  have h2 := mul_lt_mul_of_pos_left hy2 hg
  have h4 : gc*V0≤(2*g)*V0 := mul_le_mul_of_nonneg_right (le_of_lt hgc) (le_of_lt hV0pos)
  have h5 : 8*g*V0<W*V0 := mul_lt_mul_of_pos_right hWg hV0pos
  exact ⟨by linarith,mul_nonneg (by linarith) (le_of_lt hV0pos)⟩

#print axioms Centred87Estimate.centred_estimate
end Centred87Estimate
