import GowersSzemeredi.Proofs16PolynomialAllScaleParameters
import GowersSzemeredi.Proofs16PolynomialLemma6

/-! An all-scale polynomial spectrum-count bound for Lemma 16.6.

The minimum width is a power of the input width with a polynomial prefactor
in the spectrum-count bound. A target above one supplies the localized
recurrence threshold; otherwise singleton cells suffice. Spectrum structure
and induced selection remain hypotheses, as in the original assembly.
-/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The all-scale width: with `b=C*(q+1)` and
`E=2*p*(q+1)^(2^(k+2))`, this is `(zeta/(4*b))*m^(a/(4*E))`. -/
def section16PolynomialLinearityWidth (m k C p q : Nat) (a zeta : Real) : Real :=
  (zeta / (4 * ((C * (q + 1) : Nat) : Real))) *
    (m : Real) ^ (a / (4 * ((2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1)))) : Nat) : Real)))

/-- Lemma 16.6 with a polynomial spectrum-count width at every input scale.
The prefactor absorbs the recurrence threshold; no large-width hypothesis
is imposed on the input box. -/
theorem exists_all_scale_polynomial_lemma_16_6 (k : Nat) :
  ∃ C p : Nat, 2 ≤ C ∧ 0 < p ∧
  ∀ (N m : Nat) [NeZero N] [Fact N.Prime], 1 ≤ k →
    ∀ (theta gamma sigma : Real),
    0 < theta → theta ≤ 1 → 0 < gamma → gamma ≤ 1 →
    0 < sigma → sigma ≤ 1 →
    ∀ (Qb Eb : Real → Real), 0 ≤ Qb sigma → 0 < Eb sigma → Eb sigma ≤ 1 →
    ∀ (B : Finset (Point N (k + 1)))
      (phi : Point N (k + 1) → ZMod N)
      (H Jbase H1 : Finset (Point N k))
      (Y : (h : Point N k) → Finset (Section16CubeElement B h))
      (phiPrime : Point N k → ZMod N → ZMod N),
    let theta1 := section16ThetaOne theta gamma k
    let delta := section16Delta theta1
    let zeta := section16Zeta theta gamma k
    H1 = H ∩ Jbase →
    MultiplyLinearWith Qb Eb
      (restrictRelation (section16SpectrumRelation B delta) Jbase) →
    Section16InducedSelection B phi H Y
      (fun h => section16LargeSpectrum B h delta) zeta phiPrime →
    ∀ (P : Box N (k + 1)) (Q : Box N k) (I : ModAP N),
      P.IsProper → IsLastCoordinateBoxProduct P Q I → m ≤ P.width →
      ∃ G : Finset (Point N k), ∃ M : Nat,
          ∃ S : Fin M → Box N (k + 1),
            ∃ T : Fin M → Box N k, ∃ A : Fin M → ModAP N,
              G ⊆ Q.carrier ∧
              (1 - sigma) * Q.carrier.card ≤ G.card ∧
              IsBoxPartition S P ∧ (∀ u, (S u).IsProper) ∧
              (∀ u, IsLastCoordinateBoxProduct (S u) (T u) (A u)) ∧
              (∀ u, section16PolynomialLinearityWidth m k C p (Nat.floor (Qb sigma)) (Eb sigma) zeta ≤ (S u).width) ∧
              ∀ u h, h ∈ G → h ∈ H1 → h ∈ (T u).carrier →
                LinearOn ((A u).carrier.filter fun x =>
                  (h, x) ∈ section16InducedDomain B H Y) (phiPrime h) := by
  obtain ⟨C, p, hC, hp, hlemma6⟩ := exists_polynomial_lemma_16_6 k
  refine ⟨C, p, hC, hp, ?_⟩
  intro N m _ _ hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha ha1
    B phi H Jbase H1 Y phiPrime
  dsimp only
  intro hH1 hML hselection P Q I hP hproduct hmP
  classical
  let zeta := section16Zeta theta gamma k
  let l := section16PolynomialLinearityWidth m k C p (Nat.floor (Qb sigma)) (Eb sigma) zeta
  let D (x : Point N k) := Finset.univ.filter (fun y => (x, y) ∈ section16InducedDomain B H Y)
  by_cases hl : l ≤ 1
  · obtain ⟨M, S, hpart, hproper, hwidth, hlin⟩ :=
      section16_local_linearity_singletons P l hl D phiPrime
    refine ⟨Q.carrier, M, S, (fun j => boxInit (S j)),
      (fun j => (S j).axis (Fin.last k)), Finset.Subset.refl _, ?_, hpart, hproper,
      (fun j => boxInit_last_product (S j)), hwidth, ?_⟩
    · have hcard : (0 : Real) ≤ Q.carrier.card := Nat.cast_nonneg _
      nlinarith
    · intro j x _ _ _
      simpa only [D, Finset.mem_filter, Finset.mem_univ, true_and] using hlin j x
  · have hlarge : 1 < l := lt_of_not_ge hl
    let q := Nat.floor (Qb sigma)
    let b := C * (q + 1)
    let E := 2 * (p * (q + 1) ^ (2 * (2 ^ (k + 1))))
    have hb : 2 ≤ b := hC.trans (Nat.le_mul_of_pos_right C (by omega))
    have hE : 0 < E := by dsimp [E]; positivity
    obtain ⟨hz, hzHalf⟩ := section16Zeta_pos_le_half k ht ht1 hg hg1
    change 1 < (zeta / (4 * (b : Real))) * (m : Real) ^ (Eb sigma / (4 * (E : Real))) at hlarge
    have hm : 1 ≤ m := by
      by_contra hm
      have hm0 : m = 0 := by omega
      have he : 0 < Eb sigma / (4 * (E : Real)) := by positivity
      rw [hm0, Nat.cast_zero, Real.zero_rpow he.ne', mul_zero] at hlarge
      norm_num at hlarge
    obtain ⟨n, hm4, hn, hnscale, hnthreshold, htarget⟩ :=
      polynomial_localized_recurrence_parameters hm hb hE ha ha1 hz hzHalf hlarge
    obtain ⟨G, M, S, T, A, hGsub, hGmass, hpart, hproper, hproduct', hwidth, hlin⟩ :=
      hlemma6 N m n hk theta gamma sigma ht ht1 hg hg1 hs hs1 Qb Eb hQ ha.le
        hm4 hn hnscale hnthreshold B phi H Jbase H1 Y phiPrime hH1 hML hselection
        P Q I hP hproduct hmP
    exact ⟨G, M, S, T, A, hGsub, hGmass, hpart, hproper, hproduct',
      fun j => htarget.trans (hwidth j), hlin⟩

end LeanProofs.GowersSzemeredi
