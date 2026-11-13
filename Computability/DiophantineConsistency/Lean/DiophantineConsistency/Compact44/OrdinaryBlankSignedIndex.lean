import DiophantineConsistency.AdaptiveGap85GenericSignedHalfIndex

/-! # The signed half-index argument for the ordinary-blank auxiliary ordinate

Packages 50, 57 and 62 use the auxiliary ordinate `V = c(Tf − 1) − Rf²`. That
is `V ≡ −c (mod f)` only, not the squared-modulus form
`V = f²(Tc − R) − c` of `AdaptiveGap85GenericSignedHalfIndex`. The Pell
half-index theorem `ArithmeticPellHalfIndex.half_index` consumes only two
residues of `z = |V|`:

* `z ≡ ±c (mod f)`. Here `cTf ≡ 0` and `Rf² + c ≡ c (mod f)`;
* `z ≡ ±R (mod c)`. Here `cTf ≡ 0` and `Rf² + c ≡ R (mod c)`, because the
  ordinary strong norm gives `f² ≡ 1 (mod c)`.

So the same conclusion `m = R` holds for this ordinate. -/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 4000000
noncomputable section
namespace OrdinaryBlankSignedIndex
open LO LO.FirstOrder LO.FirstOrder.Arithmetic
open scoped LO.FirstOrder.Arithmetic
open DiophantineConsistency
open DiophantineConsistency.ArithmeticPellRecurrence DiophantineConsistency.ArithmeticPellClassification
open DiophantineConsistency.ArithmeticPellHalfIndex DiophantineConsistency.ArithmeticPellCongruences
open DiophantineConsistency.ArithmeticPellResidueAux
variable {V : Type*} [ORingStructure V] [V↓[ℒₒᵣ] ⊧* 𝗜𝚺₁]

/-- The rank is the Pell index, for the ordinate `|cTf − (f²R + c)|`. -/
theorem signed_half_index_blank (a c d f i T R y m : V)
    (hc : 0 < c) (hi : 0 < i) (hf : 0 < f) (hm : 0 < m) (hy : 0 < y)
    (hmy : ycoord m a = c) (hR : 0 < R) (hhalf : 2 * R < c)
    (hmain : d * d = 1 + delta a * c * c)
    (hstrong : (i * c * c) * (i * c * c) + delta a = delta a * (f * f))
    (hbig : (a + 2) * delta a * delta a < c)
    (haux : (i * c * c) * (i * c * c) * absdiff (c * T * f) (f * f * R + c) *
        absdiff (c * T * f) (f * f * R + c) + y * y = 1 + (i * c * c) * (i * c * c) * y * y) :
    m = R := by
  have hfmod := square_mod_one_of_relaxed_auxiliary a c m i f hm hi hf hc hmy hstrong hbig
  have huf : SignMod f (absdiff (c * T * f) (f * f * R + c)) c := by
    apply absdiff_residue f (c * T * f) (f * f * R + c) c hf
    have hd1 : f ∣ c * T * f := ⟨c * T, by ring⟩
    have hd2 : f ∣ f * f * R := ⟨f * R, by ring⟩
    calc (c * T * f + c) % f = c % f := mod_add_remove_left_of_dvd hd1 hf
      _ = (f * f * R + c) % f := (mod_add_remove_left_of_dvd hd2 hf).symm
  have huc : SignMod c (absdiff (c * T * f) (f * f * R + c)) R := by
    apply absdiff_residue c (c * T * f) (f * f * R + c) R hc
    have hd1 : c ∣ c * T * f := ⟨T * f, by ring⟩
    have hmul : (f * f * R) % c = R % c := by
      rw [mod_mul hc, hfmod, ← mod_mul hc, one_mul]
    calc (c * T * f + R) % c = R % c := mod_add_remove_left_of_dvd hd1 hc
      _ = (f * f * R) % c := hmul.symm
      _ = (f * f * R + c) % c := by
        rw [add_comm]; exact (mod_add_remove_left_of_dvd (dvd_refl c) hc).symm
  have hs : (i * c * c) * (i * c * c) + delta a = delta a * f * f := by
    simpa only [mul_assoc] using hstrong
  obtain ⟨_, hcr⟩ := half_index a c d f i R y (absdiff (c * T * f) (f * f * R + c)) hc hi hf hR hy
    hmain hs hbig hhalf haux huf huc
  exact index_unique a m R (hmy.trans hcr)

/-- The same for the ordinate `cTf + (f²R + c)`, which arises when the strong root
is negative: its residues are `c` modulo `f` and `R` modulo `c` directly. -/
theorem signed_half_index_blank_plus (a c d f i T R y m : V)
    (hc : 0 < c) (hi : 0 < i) (hf : 0 < f) (hm : 0 < m) (hy : 0 < y)
    (hmy : ycoord m a = c) (hR : 0 < R) (hhalf : 2 * R < c)
    (hmain : d * d = 1 + delta a * c * c)
    (hstrong : (i * c * c) * (i * c * c) + delta a = delta a * (f * f))
    (hbig : (a + 2) * delta a * delta a < c)
    (haux : (i * c * c) * (i * c * c) * (c * T * f + (f * f * R + c)) *
        (c * T * f + (f * f * R + c)) + y * y = 1 + (i * c * c) * (i * c * c) * y * y) :
    m = R := by
  have hfmod := square_mod_one_of_relaxed_auxiliary a c m i f hm hi hf hc hmy hstrong hbig
  have huf : SignMod f (c * T * f + (f * f * R + c)) c := by
    left
    rw [show c * T * f + (f * f * R + c) = c + f * (c * T + f * R) by ring, mod_add_mul' _ _ hf]
  have huc : SignMod c (c * T * f + (f * f * R + c)) R := by
    left
    have hmul : (f * f * R) % c = R % c := by
      rw [mod_mul hc, hfmod, ← mod_mul hc, one_mul]
    rw [show c * T * f + (f * f * R + c) = f * f * R + c * (T * f + 1) by ring, mod_add_mul' _ _ hc, hmul]
  have hs : (i * c * c) * (i * c * c) + delta a = delta a * f * f := by
    simpa only [mul_assoc] using hstrong
  obtain ⟨_, hcr⟩ := half_index a c d f i R y (c * T * f + (f * f * R + c)) hc hi hf hR hy
    hmain hs hbig hhalf haux huf huc
  exact index_unique a m R (hmy.trans hcr)

end OrdinaryBlankSignedIndex

#print axioms OrdinaryBlankSignedIndex.signed_half_index_blank
#print axioms OrdinaryBlankSignedIndex.signed_half_index_blank_plus
