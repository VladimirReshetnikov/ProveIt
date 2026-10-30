import DiophantineConsistency.ArithmeticPellHalfIndex
import DiophantineConsistency.ArithmeticSignedPairs

/-! Order lemmas for a possible direct auxiliary ordinate. These are generic
    conditional lemmas and do not assert an equation reduction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace DiophantineConsistency.ArithmeticAdaptiveOrdinateGap2011
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open ArithmeticPellHalfIndex ArithmeticSignedPairs

variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The signed rank residue rules out both small magnitudes. -/
theorem magnitude_ge_two {c z R : V} (hR : 2 ≤ R) (hhalf : 2*R < c)
    (hmod : SignMod c z R) : 2 ≤ z := by
  have hRpos : 0<R := lt_of_lt_of_le (by simp : (0:V)<2) hR
  have hRle : R≤2*R := by simpa only [two_mul] using (show R≤R+R by simp)
  have hRc : R<c := lt_of_le_of_lt hRle hhalf
  have hzpos : 0<z := pos_iff_ne_zero.mpr (by
    intro hz
    have hmod0 : R%c=0 := by
      rcases hmod with h | h
      · simpa only [hz,zero_mod] using h.symm
      · simpa only [hz,zero_add] using h
    rw [mod_eq_self_of_lt hRc] at hmod0
    exact (ne_of_gt hRpos) hmod0)
  by_contra hn
  have hzlt : z<2 := lt_of_not_ge hn
  have hzR : z<R := lt_of_lt_of_le hzlt hR
  have hzhalf : 2*z<c := lt_of_le_of_lt
    (mul_le_mul_of_nonneg_left (le_of_lt hzR) (by simp)) hhalf
  have he : z=R := sign_eq_of_half hzpos hRpos hzhalf hhalf hmod
  exact (ne_of_lt hzR) he

/-- The auxiliary norm has an ordinate strictly above its magnitude, once
    the coefficient and magnitude are at least two. -/
theorem ordinate_gt_magnitude {I z y : V} (hI : 2≤I) (hz : 2≤z)
    (hn : I*I*z*z+y*y=1+I*I*y*y) : z<y := by
  by_contra hnlt
  have hyz : y≤z := le_of_not_gt hnlt
  have hsq : y*y≤z*z := mul_le_mul hyz hyz (by simp) (by simp)
  let d : V := z*z-y*y
  have hd : y*y+d=z*z := by dsimp [d]; rw [add_comm,tsub_add_cancel_of_le hsq]
  have hIone : (1:V)≤I*I := by
    have hi : (1:V)≤I := le_trans (by simp : (1:V)≤2) hI
    simpa only [one_mul] using mul_le_mul hi hi (by simp) (by simp)
  have hdle : d≤(I*I)*d := by
    simpa only [one_mul] using mul_le_mul_of_nonneg_right hIone (Arithmetic.zero_le d)
  have hle : (I*I)*(y*y)+z*z≤1+(I*I)*(y*y) := calc
    (I*I)*(y*y)+z*z=(I*I)*(y*y)+(y*y+d) := by rw [hd]
    _≤(I*I)*(y*y)+(y*y+(I*I)*d) := _root_.add_le_add (le_refl _) (_root_.add_le_add (le_refl _) hdle)
    _=(I*I)*(y*y+d)+y*y := by ring
    _=I*I*z*z+y*y := by rw [hd]; ring
    _=1+(I*I)*(y*y) := by simpa only [mul_assoc] using hn
  have hzsq : z*z≤1 := by
    apply (add_le_add_iff_left ((I*I)*(y*y))).mp
    simpa only [add_comm] using hle
  have htwo : (2:V)≤z*z := le_trans hz (le_mul_of_one_le_right (by simp)
    (le_trans (by simp : (1:V)≤2) hz))
  exact (not_le_of_gt (by simp : (1:V)<2)) (le_trans htwo hzsq)

/-- A strict magnitude gap reconstructs a positive offset and orients the
    represented signed ordinate as the chosen positive value. -/
theorem positive_offset_of_gap {L M y : V} (hgap : magnitude (L,M)<y) :
    ∃ u : V, 0<u ∧ L+u=M+y ∧ magnitude (L+u,M)=y := by
  have hy : 0<y := lt_of_le_of_lt (Arithmetic.zero_le (magnitude (L,M))) hgap
  by_cases h : L≤M
  · let u : V := (M-L)+y
    have hu : 0<u := lt_of_lt_of_le hy (by dsimp [u]; simp)
    have he : L+u=M+y := by
      dsimp [u]
      rw [←add_assoc,add_comm L (M-L),tsub_add_cancel_of_le h]
    exact ⟨u,hu,he,magnitude_of_add he⟩
  · have hML : M≤L := le_of_not_ge h
    let d : V := L-M
    have hd : d≤magnitude (L,M) := by
      dsimp only [d,magnitude]
      simp
    have hdy : d<y := lt_of_le_of_lt hd hgap
    let u : V := y-d
    have hu : 0<u := tsub_pos_iff_lt.mpr hdy
    have hdecomp : M+d=L := by dsimp [d]; rw [add_comm,tsub_add_cancel_of_le hML]
    have he : L+u=M+y := calc
      L+u=(M+d)+(y-d) := by rw [hdecomp]
      _=M+((y-d)+d) := by ring
      _=M+y := by rw [tsub_add_cancel_of_le (le_of_lt hdy)]
    exact ⟨u,hu,he,magnitude_of_add he⟩

/-- Under the auxiliary norm and signed residue, the direct ordinate has a
    positive offset representation; no standard-model or gcd assumption is used. -/
theorem positive_offset_of_norm_residue {I L M y c R : V}
    (hI : 2≤I) (hR : 2≤R) (hhalf : 2*R<c)
    (hmod : SignMod c (magnitude (L,M)) R)
    (hn : I*I*magnitude (L,M)*magnitude (L,M)+y*y =
      1+I*I*y*y) :
    ∃ u : V, 0<u ∧ L+u=M+y ∧ magnitude (L+u,M)=y := by
  have hz := magnitude_ge_two hR hhalf hmod
  exact positive_offset_of_gap (ordinate_gt_magnitude hI hz hn)

end DiophantineConsistency.ArithmeticAdaptiveOrdinateGap2011
