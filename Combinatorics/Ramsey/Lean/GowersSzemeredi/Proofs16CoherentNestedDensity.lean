import GowersSzemeredi.Proofs16CoherentWordFamily

/-! The first rich anchor set supplies a dense exact quadruple family
for the second extraction. No arbitrary restriction of the original family is used. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def coherentNestedDensity (kappa : Real) : Real :=
  (((9*kappa^2/1024)^2)*coherentRobustWalkDensity kappa)^2/2

def coherentNestedDensityCoefficient : Real := coherentRobustWalkCoefficient^2*(9/1024)^4/2

theorem coherentNestedDensityCoefficient_pos : 0 < coherentNestedDensityCoefficient := by
  have hc := coherentRobustWalkCoefficient_pos
  unfold coherentNestedDensityCoefficient
  positivity

theorem coherentNestedDensity_pos {kappa : Real} (hk : 0 < kappa) : 0 < coherentNestedDensity kappa := by
  have hw := coherentRobustWalkDensity_pos hk
  unfold coherentNestedDensity
  positivity

theorem coherentNestedDensity_eq (kappa : Real) :
    coherentNestedDensity kappa = coherentNestedDensityCoefficient*kappa^28 := by
  unfold coherentNestedDensity coherentNestedDensityCoefficient
  rw [coherentRobustWalkDensity_eq]
  ring

theorem ThresholdColumnRichness.anchor_quadruples {N : Nat} [NeZero N]
    {A P : Finset (ZMod N)} {T : ZMod N → Finset (ZMod N)}
    {F : ZMod N → ZMod N → ZMod N} {r kappa : Real} {K : Nat}
    (h : ThresholdColumnRichness A T F r (coherentWordDensity kappa K/2) (coherentRobustWalkDensity kappa))
    (hk : 0 < kappa) (hk1 : kappa ≤ 1) (hP : P ⊆ A)
    (hmass : (9*kappa^2/1024)*N ≤ (P.card : Real)) :
    coherentNestedDensity kappa*(N : Real)^3 ≤ (exactColumnQuadruples P T F r).card := by
  have hcut : coherentWordDensity kappa K/2 ≤ 9*kappa^2/1024 := by
    have hd := coherentWordDensity_antitone hk hk1 (Nat.zero_le K)
    have hl := coherentAnchorTripleDensity_le_set_density hk hk1
    change coherentWordDensity kappa K ≤ coherentAnchorTripleDensity kappa at hd
    linarith
  have hm := h P P hP hP _ _ hcut hcut hmass hmass
  rw [mixedExactColumnQuadruples_self] at hm
  simpa only [coherentNestedDensity,pow_two,div_mul_eq_mul_div] using hm

theorem CoherentFrequencyFamily.exact_subfamily {N ell : Nat} [NeZero N]
    {X P B : Finset (ZMod N)} {theta : Fin ell → ZMod N → ZMod N}
    {F : ZMod N → ZMod N → ZMod N} {sigma tau : Real} {Q : Finset (Fin 4 → ZMod N)}
    (h : CoherentFrequencyFamily X B theta F sigma Q) (hP : P ⊆ X) (ht : tau ≤ sigma) :
    CoherentFrequencyFamily P B theta F tau
      (exactColumnQuadruples P (fun u => B ∪ Finset.univ.image (fun j => theta j u)) F tau) := by
  refine ⟨fun x hx => ⟨(h.1 x (hP hx)).1.mono (bohr_mono_radius _ ht),(h.1 x (hP hx)).2⟩,?_⟩
  intro a ha
  obtain ⟨_,hA,hadd,hval⟩ := Finset.mem_filter.mp ha
  exact ⟨hadd,hA,hval⟩

end LeanProofs.GowersSzemeredi
