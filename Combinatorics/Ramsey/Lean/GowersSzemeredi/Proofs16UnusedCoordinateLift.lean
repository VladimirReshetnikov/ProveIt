import GowersSzemeredi.Proofs16UnusedCoordinateCover
import GowersSzemeredi.Proofs16CoarseFunctionCover
import GowersSzemeredi.Proofs16UnusedCoordinateBudget

/-! All-scale lifting across an unused coordinate, with the actual ambient
control functions. A sufficient lower bound on the iteration parameter
pays for the finite coarse-cover branch. No sampling argument is involved. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- A lower-dimensional multiply-linear partial function extends across one
unused coordinate with the same gamma and iteration parameter. The stated
parameter reserve covers small boxes uniformly, while the dimension exponent
gap absorbs the compatible-tiling width loss on large boxes. -/
theorem MultiplyLinearFunction.lift_last {N k : Nat} [NeZero N] [Fact N.Prime]
    {gamma s : Real} {B : Finset (Point N k)} {phi : Point N k → ZMod N}
    (hML : MultiplyLinearFunction gamma s B phi)
    (hg : 0 < gamma) (hg1 : gamma ≤ 1) (hs : 2 ≤ s)
    (hgraphs : (3 ^ (k + 1) : Nat) ≤ s) (hk : 0 < k) :
    MultiplyLinearFunction gamma s (lastProductSet B Finset.univ)
      (fun z => phi (section16Init z)) := by
  classical
  intro theta ht ht1 P hP
  obtain ⟨ha, ha1, hA, hgap⟩ := section16_dimension_exponent_gap k hg hg1 ht ht1 hs
  let a := (multipleC (s⁻¹ * theta) gamma k) ^ s
  let A := (multipleC (s⁻¹ * theta) gamma (k + 1)) ^ s
  have hs1 : 1 ≤ s := by linarith
  have hQ := multipleQ_rpow_ge_parameter (k + 1) hg hg1 ht ht1 hs1
  have hQ1 : 1 ≤ (multipleQ (s⁻¹ * theta) gamma (k + 1)) ^ s := hs1.trans hQ
  have hQcoarse : ((3 ^ (k + 1) : Nat) : Real) ≤
      (multipleQ (s⁻¹ * theta) gamma (k + 1)) ^ s := hgraphs.trans hQ
  have hmass : (1 - theta) * (P.carrier.card : Real) ≤ P.carrier.card := by
    have hnonneg : (0 : Real) ≤ P.carrier.card := by positivity
    nlinarith
  have hgraph : ∀ z y, (z, y) ∈ partialGraph (lastProductSet B Finset.univ)
      (fun z => phi (section16Init z)) → y = phi (section16Init z) ∧ section16Init z ∈ B := by
    intro z y hz
    obtain ⟨w, hw, hwy⟩ := Finset.mem_image.mp hz
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hwy
    exact ⟨rfl, (Finset.mem_filter.mp hw).2.1⟩
  by_cases hsmall : (P.width : Real) ^ A ≤ 2
  · by_cases htwo : 2 ≤ P.width
    · obtain ⟨M, Q, mu, hpart, hproper, hmu, hc⟩ :=
        section16_coarse_function_cover P hP (by omega) htwo (fun z => phi (section16Init z))
      refine ⟨M, 3 ^ (k + 1), P.carrier, Q, mu, Finset.Subset.rfl, hmass, hpart,
        fun j => (hproper j).1, hQcoarse, ?_, hmu, ?_⟩
      · intro j
        exact hsmall.trans (by exact_mod_cast (hproper j).2)
      · intro j z hz _ y hy
        rw [(hgraph z y hy).1]
        exact hc j z hz
    · obtain ⟨M, Q, mu, hpart, hproper, hmu, hc⟩ :=
        section16_singleton_function_cover P (by omega) (fun z => phi (section16Init z))
      refine ⟨M, 1, P.carrier, Q, mu, Finset.Subset.rfl, hmass, hpart,
        fun j => (hproper j).1, by simpa using hQ1, ?_, hmu, ?_⟩
      · intro j
        rw [(hproper j).2, Nat.cast_one]
        exact Real.rpow_le_one (Nat.cast_nonneg _) (by exact_mod_cast (show P.width ≤ 1 by omega)) hA.le
      · intro j z hz _ y hy
        rw [(hgraph z y hy).1]
        exact hc j z hz
  · have hlarge : 2 < (P.width : Real) ^ A := lt_of_not_ge hsmall
    have hw1 : (1 : Real) ≤ P.width := by
      by_contra hh
      have hw0 : P.width = 0 := by
        have hn : P.width < 1 := by exact_mod_cast lt_of_not_ge hh
        omega
      simp only [hw0, Nat.cast_zero, A, Real.zero_rpow hA.ne'] at hlarge
      linarith
    obtain ⟨hm4, hscale, hwidth⟩ := section16_unused_coordinate_width_budget hw1 ha ha1 hA hgap hlarge
    have hm : 4 ≤ P.width := by exact_mod_cast hm4
    let T := boxInit P
    let I := P.axis (Fin.last k)
    have hI : I.IsProper := hP _
    have hmI : P.width ≤ I.length := P.width_le_axis_length _
    obtain ⟨u, hu⟩ := I.step_isUnit_of_prime hI (by omega)
    have hstep : I.step = T.commonDiff := P.axis_step _
    obtain ⟨q, G, M, Q, mu, hq, hG, hGm, hpart, hproper, hmu, hc⟩ :=
      hML.unused_coordinate_cover_sqrt theta ht ht1 T I (boxInit_isProper P hP) hI
        hstep u hu.symm hk hm (boxInit_width P hk) hmI hscale
    have hprod : lastProductSet T.carrier I.carrier = P.carrier := (boxInit_last_product P).1.symm
    rw [hprod] at hG hGm hpart
    have hqq : (multipleQ (s⁻¹ * theta) gamma k) ^ s ≤
        (multipleQ (s⁻¹ * theta) gamma (k + 1)) ^ s := by
      have hb : 0 < gamma * (s⁻¹ * theta) := by positivity
      have hc : 0 ≤ multipleC (s⁻¹ * theta) gamma k := pow_nonneg hb.le _
      have hc' : 0 ≤ multipleC (s⁻¹ * theta) gamma (k + 1) := pow_nonneg hb.le _
      rw [multipleQ, multipleQ, Real.inv_rpow hc, Real.inv_rpow hc']
      exact inv_anti₀ hA (by nlinarith only [hgap, hA])
    refine ⟨M, q, G, Q, mu, hG, hGm, hpart, fun j => (hproper j).1,
      hq.trans hqq, fun j => hwidth.trans (hproper j).2, hmu, ?_⟩
    intro j z hz hzG y hy
    obtain ⟨hyval, hzB⟩ := hgraph z y hy
    rw [hyval]
    exact hc j z hz hzB hzG

end LeanProofs.GowersSzemeredi
