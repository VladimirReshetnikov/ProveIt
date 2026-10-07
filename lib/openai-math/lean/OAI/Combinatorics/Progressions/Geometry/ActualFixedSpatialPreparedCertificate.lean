import OAI.Combinatorics.Progressions.Sampling.ActualForecastModelPrecision

namespace OAI

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

theorem exists_actualFixedSpatialPreparedParameters
    {m : ℕ} (Dmod d : ℕ)
    {X : Type*} [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P δslice : ℝ} (hP : 1 ≤ P) (hδslice : 0 < δslice)
    (hδsliceInv : δslice⁻¹ ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    (forward : Fin m → ℝ≥0) (K r : ℝ≥0)
    {D pcap Pscale Pbad Ppres E Pτ PK PF τ : ℝ}
    (hD : 0 ≤ D) (hDP : D ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (hdim : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ D)
    (hpcap : 0 ≤ pcap) (hscale : 0 ≤ Pscale)
    (hbad : 0 ≤ Pbad) (hpres : 0 ≤ Ppres) (hE : 0 ≤ E)
    (hPτ : 0 ≤ Pτ) (hPK : 0 ≤ PK) (hPF : 0 ≤ PF)
    (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Pτ)
    (hforward : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (hK : (K : ℝ) ≤ Real.exp PK) (hr : 1 ≤ r) :
    let q := actualFixedSpatialForecastLogs m Dmod d P D pcap Pscale Pbad Ppres E Pτ PK PF
    ∃ (T : ℕ) (δ : ℝ), 0 < T ∧ (T : ℝ) ≤ Real.exp q.V ∧
      0 < δ ∧ δ ≤ 1 ∧ δ⁻¹ ≤ Real.exp q.Esite ∧
      ∀ A₀ A₁ : (X → ℝ) ≃L[ℝ] (X → ℝ),
        inverseJacobian A₁ ≤ Real.exp P → ‖A₀.symm.toContinuousLinearMap‖ ≤ Real.exp P →
        let H := (fixedSpatialOriginalForecastCap B A₁ hδslice : ℝ) + 1
        let L := fixedSpatialOriginalForecastLip B A₀ A₁ hδslice
        H ≤ Real.exp q.sm ∧ (L : ℝ) ≤ Real.exp q.sm ∧
        (∀ (Rbad Qpres : ℕ) (Icap : ℝ), Icap ≤ Real.exp q.Pin →
          (Rbad : ℝ) ≤ Real.exp Pbad → (Qpres : ℝ) ≤ Real.exp Ppres →
          H * (Icap * ((((Rbad * Qpres : ℕ) : ℝ) ^
            (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
              modularRankChargeFactor m)) / T) + (T : ℝ) ^ d * δ) ≤ Real.exp (-E)) ∧
        (∀ a : ℕ, (a : ℝ) ≤ D →
          2 * H * ((T : ℝ) ^ d * Real.exp (a * q.O)) ≤ Real.exp q.mass) ∧
        (∀ (a period : ℕ), (a : ℝ) ≤ D → (period : ℝ) ≤ Real.exp (q.V + a * q.O) →
          (period : ℝ) ≤ Real.exp q.native ∧
          (((L + a * ⟨Real.exp q.O, Real.exp_nonneg _⟩) *
            max ⟨8 / τ, by positivity⟩ 1 : ℝ≥0) : ℝ) ≤ Real.exp q.native) ∧
        ((K * ∑ j, forward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp q.native ∧
        (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
          (K * ∑ j, forward j * Fintype.card (J j)) : ℝ≥0) : ℝ) ≤ Real.exp q.native := by
  intro q
  obtain ⟨_, _, _, _, _, T, δ, hT, hTv, hδ, hδ1, hδb, hprepared⟩ :=
    exists_preparedFixedSpatialForecastParameters Dmod d B hP hδslice hδsliceInv hX hblocks
      forward K r hD hDP haxes hdim hpcap hscale hbad hpres hE hPτ hPK hPF
      hτ hτinv hforward hK hr
  refine ⟨T, δ, hT, hTv, hδ, hδ1, hδb, ?_⟩
  intro A₀ A₁ hjac hinverse H L
  obtain ⟨hH, hL, herror, _, hmass, hfactor, hcoord, hcut⟩ :=
    hprepared A₀ A₁ hjac hinverse
  exact ⟨hH, hL, herror, hmass, hfactor, hcoord, hcut⟩

end Erdos3.VectorPolynomial

end

section

namespace Erdos3.VectorPolynomial

open BooleanCubeKernel
open scoped BigOperators Classical NNReal

structure ActualFixedSpatialPreparedCertificate
    {m : ℕ} {X : Type*} [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {δslice : ℝ} (hδslice : 0 < δslice)
    (forward : Fin m → ℝ≥0) (K r : ℝ≥0)
    (τ : ℝ) (hτ : 0 < τ) (Dmod d : ℕ)
    (P D Pbad Ppres E : ℝ) (q : ActualFixedSpatialForecastLogs)
    (T : ℕ) (δ : ℝ) : Prop where
  hT : 0 < T
  hTv : (T : ℝ) ≤ Real.exp q.V
  hδ : 0 < δ
  hδ1 : δ ≤ 1
  hδb : δ⁻¹ ≤ Real.exp q.Esite
  bounds : ∀ A₀ A₁ : (X → ℝ) ≃L[ℝ] (X → ℝ),
        inverseJacobian A₁ ≤ Real.exp P → ‖A₀.symm.toContinuousLinearMap‖ ≤ Real.exp P →
        let H := (fixedSpatialOriginalForecastCap B A₁ hδslice : ℝ) + 1
        let L := fixedSpatialOriginalForecastLip B A₀ A₁ hδslice
        H ≤ Real.exp q.sm ∧ (L : ℝ) ≤ Real.exp q.sm ∧
        (∀ (Rbad Qpres : ℕ) (Icap : ℝ), Icap ≤ Real.exp q.Pin →
          (Rbad : ℝ) ≤ Real.exp Pbad → (Qpres : ℝ) ≤ Real.exp Ppres →
          H * (Icap * ((((Rbad * Qpres : ℕ) : ℝ) ^
            (modularRankDecayExponent m (modularForecastRankConstant m Dmod : ℝ) *
              modularRankChargeFactor m)) / T) + (T : ℝ) ^ d * δ) ≤ Real.exp (-E)) ∧
        (∀ a : ℕ, (a : ℝ) ≤ D →
          2 * H * ((T : ℝ) ^ d * Real.exp (a * q.O)) ≤ Real.exp q.mass) ∧
        (∀ (a period : ℕ), (a : ℝ) ≤ D → (period : ℝ) ≤ Real.exp (q.V + a * q.O) →
          (period : ℝ) ≤ Real.exp q.native ∧
          (((L + a * ⟨Real.exp q.O, Real.exp_nonneg _⟩) *
            max ⟨8 / τ, by positivity⟩ 1 : ℝ≥0) : ℝ) ≤ Real.exp q.native) ∧
        ((K * ∑ j, forward j * Fintype.card (J j) : ℝ≥0) : ℝ) ≤ Real.exp q.native ∧
        (((Fintype.card (LayerSamplerAxis I n) * normalizedSiteCutoffBound / (2 * r)) *
          (K * ∑ j, forward j * Fintype.card (J j)) : ℝ≥0) : ℝ) ≤ Real.exp q.native

theorem exists_actualFixedSpatialPreparedCertificate
    {m : ℕ} (Dmod d : ℕ)
    {X : Type*} [Fintype X]
    {I : Fin m → Type*} [∀ j, Fintype (I j)] {n : Fin m → ℕ}
    (B : LayerSamplerAxis I n → Type*) [∀ a, Fintype (B a)]
    {J : Fin m → Type*} [∀ j, Fintype (J j)]
    {P δslice : ℝ} (hP : 1 ≤ P) (hδslice : 0 < δslice)
    (hδsliceInv : δslice⁻¹ ≤ Real.exp P)
    (hX : (Fintype.card X : ℝ) ≤ P)
    (hblocks : (∑ a, (Fintype.card (B a) : ℝ)) ≤ P)
    (forward : Fin m → ℝ≥0) (K r : ℝ≥0)
    {D pcap Pscale Pbad Ppres E Pτ PK PF τ : ℝ}
    (hD : 0 ≤ D) (hDP : D ≤ P)
    (haxes : (Fintype.card (LayerSamplerAxis I n) : ℝ) ≤ D)
    (hdim : ((∑ j, Fintype.card (J j) : ℕ) : ℝ) ≤ D)
    (hpcap : 0 ≤ pcap) (hscale : 0 ≤ Pscale)
    (hbad : 0 ≤ Pbad) (hpres : 0 ≤ Ppres) (hE : 0 ≤ E)
    (hPτ : 0 ≤ Pτ) (hPK : 0 ≤ PK) (hPF : 0 ≤ PF)
    (hτ : 0 < τ) (hτinv : τ⁻¹ ≤ Real.exp Pτ)
    (hforward : ∀ j, (forward j : ℝ) ≤ Real.exp PF)
    (hK : (K : ℝ) ≤ Real.exp PK) (hr : 1 ≤ r) :
    let q := actualFixedSpatialForecastLogs m Dmod d P D pcap Pscale Pbad Ppres E Pτ PK PF
    ∃ (T : ℕ) (δ : ℝ),
      ActualFixedSpatialPreparedCertificate (X := X) (J := J) B hδslice forward K r
        τ hτ Dmod d P D Pbad Ppres E q T δ := by
  intro q
  obtain ⟨T, δ, hT, hTv, hδ, hδ1, hδb, hbounds⟩ :=
    exists_actualFixedSpatialPreparedParameters Dmod d B hP hδslice hδsliceInv hX hblocks
      forward K r hD hDP haxes hdim hpcap hscale hbad hpres hE hPτ hPK hPF
      hτ hτinv hforward hK hr
  exact ⟨T, δ, hT, hTv, hδ, hδ1, hδb, hbounds⟩

end Erdos3.VectorPolynomial

end

end OAI
