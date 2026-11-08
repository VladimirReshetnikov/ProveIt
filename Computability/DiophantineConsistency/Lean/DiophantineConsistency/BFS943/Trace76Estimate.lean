import DiophantineConsistency.BFS943.TransportOrder

/-! # The signed transport estimate for the weight `L = b V`

Ordered-ring core of package 163's §4 for the `bV` weight (the 76/352
circuit). With `V = F b - c`, the adjacent Pell norm
`(1+B) V0² = 1 + B y²` at `V0 = |V|` and the elementary sizes
`c < B`, `2c < F`, `8g ≤ F`, `F² + F ≤ 4B`, one has

  `2 g y < b V`, `0 ≤ b V`, `0 ≤ V² - b V`.

The proof does not classify the auxiliary Pell index. `b = 0` is excluded
by the norm (it would force `c < y` and `B(2c+1) ≤ c² - 1`). For `b ≠ 0`,
`V0 ≥ F - c > 1`, and the norm alone gives `V0 > 2B` (from `y ≥ V0 + 1`)
and `y < 2 V0`; then `F |b| ≥ V0 - c > 4 g F`, so `|b| > 4g` and
`2 g y < 4 g V0 < |b| V0 = b V`. (Package 163's PROOF.md derives
`|b| > 4g` through the index-three exclusion (4.2) and `|V| > 8Q²`; the
bound `V0 > 2B`, read off the norm, is already enough.)

`bv_offset` is the sign-free offset estimate `2e < b V m` for `e < b`. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace Trace76Estimate
variable {K : Type*} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

theorem bv_estimate (Bq F c b Vs V0 y g : K)
    (hB : 0<Bq) (hBc : c<Bq) (hc : 1<c) (hcF : 2*c<F) (hgF : 8*g≤F) (hg : 0<g)
    (hy : 0≤y) (hQF : F*F+F≤4*Bq) (hV : Vs=F*b-c) (hV0 : Vs*Vs=V0*V0) (hV0n : 0≤V0)
    (hnorm : (1+Bq)*(V0*V0)=1+Bq*(y*y)) (hdisc : ∀ x : K, 0<x → 1≤x) :
    2*(g*y)<b*Vs ∧ 0≤b*Vs ∧ 0≤Vs*Vs-b*Vs := by
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
  have hW : ∃ W : K, 1≤W ∧ b*Vs=W*V0 ∧ V0-c≤F*W ∧ F-c≤V0 ∧ 0≤Vs*Vs-b*Vs := by
    rcases lt_or_gt_of_ne hb0 with hneg|hpos
    · have hb1 : 1≤-b := hdisc (-b) (by linarith)
      have hFb := mul_le_mul_of_nonneg_left hb1 (le_of_lt hFpos)
      have hVneg : Vs≤-F-c := by rw [hV]; linarith
      have hV0eq : V0=-Vs := by
        have hsq : (V0-(-Vs))*(V0+(-Vs))=0 := by linear_combination -hV0
        rcases mul_eq_zero.mp hsq with h|h
        · linear_combination h
        · exfalso; linarith
      refine ⟨-b,hb1,by rw [hV0eq]; ring,?_,?_,?_⟩
      · rw [hV0eq,hV]; linarith
      · rw [hV0eq]; linarith
      · have hF1 := mul_le_mul_of_nonneg_left hb1 (show (0:K)≤F-1 by linarith)
        have h1 : Vs-b≤-c := by rw [hV]; linarith
        have : Vs*Vs-b*Vs=Vs*(Vs-b) := by ring
        rw [this]
        exact mul_nonneg_of_nonpos_of_nonpos (by linarith) (by linarith)
    · have hb1 : 1≤b := hdisc b hpos
      have hFb := mul_le_mul_of_nonneg_left hb1 (le_of_lt hFpos)
      have hVpos : F-c≤Vs := by rw [hV]; linarith
      have hV0eq : V0=Vs := by
        have hsq : (V0-Vs)*(V0+Vs)=0 := by linear_combination -hV0
        rcases mul_eq_zero.mp hsq with h|h
        · linear_combination h
        · exfalso; linarith
      refine ⟨b,hb1,by rw [hV0eq],?_,?_,?_⟩
      · rw [hV0eq,hV]; linarith
      · rw [hV0eq]; exact hVpos
      · have hF1 := mul_le_mul_of_nonneg_left hb1 (show (0:K)≤F-1 by linarith)
        have h1 : 0≤Vs-b := by rw [hV]; linarith
        have : Vs*Vs-b*Vs=Vs*(Vs-b) := by ring
        rw [this]
        exact mul_nonneg (by linarith) h1
  obtain ⟨W,hW1,hbW,hFW,hFV,hsign⟩ := hW
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
  -- |b| > 4 g
  have h8 : 8*g*F≤F*F := mul_le_mul_of_nonneg_right hgF (le_of_lt hFpos)
  have hsmall : 2*(4*g*F+c)<4*Bq := by linarith
  have hWg : 4*g<W := by
    have hlt : F*(4*g)<F*W := by linarith
    exact lt_of_mul_lt_mul_left hlt (le_of_lt hFpos)
  refine ⟨?_,?_,hsign⟩
  · rw [hbW]
    have h2 := mul_lt_mul_of_pos_left hy2 hg
    have h3 : 4*g*V0<W*V0 := mul_lt_mul_of_pos_right hWg hV0pos
    linarith
  · rw [hbW]
    exact mul_nonneg (by linarith) (le_of_lt hV0pos)

theorem bv_offset (b c F e Vs m : K) (hc : 0<c) (hF : c+1<F)
    (he : e<b) (hV : Vs=F*b-c) (hm : 2≤m)
    (hdisc : 0<b → 1≤b) : 2*e<b*Vs*m := by
  by_cases hb : b≤0
  · have he0 : e<0 := lt_of_lt_of_le he hb
    have hVs : Vs<0 := by rw [hV]; nlinarith
    have hbV : 0≤b*Vs := mul_nonneg_of_nonpos_of_nonpos hb (le_of_lt hVs)
    have hnonneg : 0≤b*Vs*m := mul_nonneg hbV (le_trans (by norm_num) hm)
    linarith
  · have hbpos : 0<b := lt_of_not_ge hb
    have hb1 : 1≤b := hdisc hbpos
    have hFb := mul_le_mul_of_nonneg_left hb1 (show (0:K)≤F by linarith)
    have hVs : 1≤Vs := by rw [hV]; linarith
    have h1 : b*1≤b*Vs := mul_le_mul_of_nonneg_left hVs (le_of_lt hbpos)
    have h2 := mul_le_mul_of_nonneg_left hm (mul_nonneg (le_of_lt hbpos) (by linarith : (0:K)≤Vs))
    linarith

end Trace76Estimate
