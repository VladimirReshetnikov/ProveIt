import GowersSzemeredi.Proofs16PropNineThreeDenseDomains
import GowersSzemeredi.Proofs16CompleteDenseIndexWindow
import GowersSzemeredi.Proofs16DensePropCoherenceBudget

/-! Proposition 9.3 with a completed coherent common-domain chart output.
Uniform chart density is constructed by the iteration. Only unused padding
is replaced. The original selected source maps and good quadruples survive
on the recorded translated indices. Final Gowers budgets remain separate. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def propNineThreeGoodQuadCoefficient (eps eps1 eps2 : Real) : Real :=
  (1-2*(5*eps1+eps))^3-2*(5*eps1+eps)-16*(eps+2*eps2)

def propNineThreeDenseChartDelta (eps : Real) (R d : Nat) : Real :=
  min (claimNineFourDensity eps R d) (claimNineFiveDensity eps R d)

theorem propNineThreeDenseChartDelta_pos {eps : Real} (he : 0 < eps) (R d : Nat) :
    0 < propNineThreeDenseChartDelta eps R d := by
  unfold propNineThreeDenseChartDelta
  apply lt_min
  · unfold claimNineFourDensity
    positivity
  · unfold claimNineFiveDensity
    positivity

def activeChosenQuadruples {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r eta : Real) (theta : Nat → ZMod N → ZMod N)
    (I : ZMod N → ZMod N → Finset Nat) (c : ZMod N → ZMod N × ZMod N)
    (X : Finset (ZMod N)) : Finset (Fin 4 → ZMod N) :=
  (additiveQuadruplesIn X).filter fun q => ∀ w,
    (∀ j, w ∈ bohr ((chosenIndices I c (q j)).image fun i => theta i (q j)) eta) →
      chosenGlued T L r c (q 0) w+chosenGlued T L r c (q 1) w =
        chosenGlued T L r c (q 2) w+chosenGlued T L r c (q 3) w

/-- Construct a genuinely coherent Bohr chart family from the standard
Proposition 9.3 inputs and explicit positivity/modulus conditions. -/
theorem milicevic_prop_9_3_coherent_charts {N : Nat} [NeZero N] [Fact N.Prime] (T : ZMod N → Finset (ZMod N))
    {d : Nat} (hT : ∀ z, (T z).card ≤ d) (L : ZMod N → ZMod N → ZMod N) {r : Real}
    (hr : 0 < r) (hr4 : r < 4) (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x))
    (hL0 : ∀ x, L x 0 = 0) {rk : Nat} (hrk : 8 * d ≤ rk) (M : Nat) [NeZero M]
    (hM : 2 ≤ r / 4 * M) {s₀ : Nat}
    (hs₀ : ∀ s, 2 ^ s ≤ (2 * s * (2 * propNineThreeRadius rk M (r / 4)) + 1) ^ (2 * d) →
      s ≤ s₀)
    {η : Real} (hη0 : 0 ≤ η) (hη : 32 * (s₀ : Real) * η ≤ 1 / 4) {ε ε₁ ε₂ : Real}
    (hε : 0 < ε) (hsmall : 5 * ε₁ + ε ≤ 1 / 2)
    (h1 : ((incompatibleTriples (colComp T L r)).card : Real) ≤ ε₁ * (N : Real) ^ 3)
    (h2x : ((Finset.univ.filter fun u : Fin 11 → ZMod N =>
      ¬ ColumnTupleRespected T L r (twelveXSide u)).card : Real) ≤ ε₂ * (N : Real) ^ 11)
    (h2y : ((Finset.univ.filter fun u : Fin 11 → ZMod N =>
      ¬ ColumnTupleRespected T L r (twelveYSide u)).card : Real) ≤ ε₂ * (N : Real) ^ 11)
    (hcoefficient : 0 < propNineThreeGoodQuadCoefficient ε ε₁ ε₂)
    (hNquad : 12 ≤ propNineThreeGoodQuadCoefficient ε ε₁ ε₂*(N : Real))
    (hNchart : 8 ≤
      (densePropQuadDensity (propNineThreeGoodQuadCoefficient ε ε₁ ε₂)
        (propNineThreeDenseChartDelta ε (propNineThreeRadius rk M (r/4)) d) s₀ /
        (coherentChartCells (denseChartLog (propNineThreeDenseChartDelta ε (propNineThreeRadius rk M (r/4)) d)) : Real)^
          (4*coherentChartRankCap (8*s₀) (denseChartLog (propNineThreeDenseChartDelta ε (propNineThreeRadius rk M (r/4)) d)))) * N) :
    let delta := propNineThreeDenseChartDelta ε (propNineThreeRadius rk M (r/4)) d
    let p := denseChartLog delta
    let kappa := densePropQuadDensity (propNineThreeGoodQuadCoefficient ε ε₁ ε₂) delta s₀
    ∃ (m : Nat) (theta : Nat → ZMod N → ZMod N) (D : Nat → Finset (ZMod N))
      (I : ZMod N → ZMod N → Finset Nat) (J : Finset Nat) (X : Finset (ZMod N))
      (c : ZMod N → ZMod N × ZMod N) (Gamma : Finset (ZMod N))
      (psi : Fin J.card → ZMod N → ZMod N) (t : Fin 4 → ZMod N)
      (color : ZMod N → Fin 4) (V : Finset (ZMod N)) (Q : Finset (Fin 4 → ZMod N))
      (B : Finset (ZMod N)),
      J.card = 8*s₀ ∧ m ≤ ⌈(s₀ : Real)/delta⌉₊ ∧
      (∀ i < m, FreimanHom 8 (D i) (theta i)) ∧
      (∀ i < m, delta*(N : Real) ≤ ((D i).card : Real)) ∧
      (∀ a ∈ X, ∀ i ∈ chosenIndices I c a, i ∈ J ∧ i < m ∧ a ∈ D i) ∧
      Gamma.card ≤ coherentChartRankCap (8*s₀) p ∧ B.card ≤ 32*s₀ ∧
      t ∈ activeChosenQuadruples T L r η theta I c X ∧ V ⊆ bohr Gamma (sandersChartRadius p/4) ∧
      coherentChartDensity kappa (8*s₀) p*N ≤ (V.card : Real) ∧
      coherentChartDensity kappa (8*s₀) p*(N : Real)^3 ≤ Q.card ∧
      (∀ i, FreimanHom 2 (bohr Gamma (sandersChartRadius p)) (psi i) ∧ psi i 0 = 0) ∧
      (∀ a ∈ X, (N : Real)/2 ≤ (Finset.univ.filter fun z => colComp T L r (c a).1 z a).card ∧
        ∀ z, colComp T L r (c a).1 z a →
          ∀ w ∈ bohr (columnDifferenceSpectrum T (colPair (c a).1 a)) (r/4),
            w ∈ bohr (columnDifferenceSpectrum T (colPair z a)) (r/4) →
            chosenGlued T L r c a w = columnDifferenceMap L (colPair z a) w) ∧
      (∀ u ∈ V, t (color u)+u ∈ X ∧
        IsFreimanLinearOn (freimanFrequencyBohr B psi (η/2) u) (chosenGlued T L r c (t (color u)+u)) ∧
        chosenGlued T L r c (t (color u)+u) 0 = 0) ∧
      ∀ b ∈ Q, b 0+b 1 = b 2+b 3 ∧ Function.Injective b ∧
        (∀ j, b j ∈ V ∧ color (b j) = j) ∧
        (fun j => t j+b j) ∈ activeChosenQuadruples T L r η theta I c X ∧
        ∀ z, (∀ j, z ∈ freimanFrequencyBohr B psi (η/2) (b j)) →
          chosenGlued T L r c (t (color (b 0))+b 0) z+chosenGlued T L r c (t (color (b 1))+b 1) z =
            chosenGlued T L r c (t (color (b 2))+b 2) z+chosenGlued T L r c (t (color (b 3))+b 3) z := by
  intro delta p kappa
  have hd : 0 < delta := propNineThreeDenseChartDelta_pos hε _ _
  obtain ⟨m,theta,D,I,J,X,c,hJ,hF,hD,hactive,hlocal,hrelate,hcount,hm⟩ :=
    milicevic_prop_9_3_dense_active_domains T hT L hr hr4 hL hL0 hrk M hM hs₀ hη0 hη hε hsmall h1 h2x h2y
  have hmBound := dense_chart_family_size_bound hd hm
  let Qgood := activeChosenQuadruples T L r η theta I c X
  have hmass : kappa*(N : Real)^3 ≤ (Qgood.card : Real) :=
    dense_prop_quadruple_mass Qgood hd hm hcount hNquad
  have hk : 0 < kappa := densePropQuadDensity_pos hcoefficient delta s₀
  have hQgood : ∀ q ∈ Qgood, q 0+q 1 = q 2+q 3 ∧ (∀ j, q j ∈ X) ∧
      ∀ z, (∀ j, z ∈ bohr (∅ ∪ (chosenIndices I c (q j)).image fun i => theta i (q j)) η) →
        chosenGlued T L r c (q 0) z+chosenGlued T L r c (q 1) z =
          chosenGlued T L r c (q 2) z+chosenGlued T L r c (q 3) z := by
    intro q hq
    obtain ⟨hqm,hqr⟩ := Finset.mem_filter.mp hq
    have hbase := (Finset.mem_filter.mp hqm).2
    refine ⟨hbase.1,hbase.2,?_⟩
    intro z hz
    exact hqr z (fun j => by simpa only [Finset.empty_union] using hz j)
  have hNactual : 8 ≤ (kappa/(coherentChartCells p : Real)^(4*coherentChartRankCap J.card p))*N := by
    simpa only [hJ] using hNchart
  obtain ⟨Gamma,psi,t,color,V,Q,B,hGamma,hdiff,ht,hBB,hB,hV,hVmass,hQmass,hparts,hlocal',hquad'⟩ :=
    complete_dense_index_window_charts Qgood X ∅ J D (chosenIndices I c) theta (chosenGlued T L r c)
      hd hη0 hk hF hD hactive (by simpa only [Finset.empty_union] using hlocal)
      hQgood hmass hNactual
  have hcard : B.card ≤ 32*s₀ := by
    have hh := hB
    rw [Finset.card_empty,hJ,zero_add] at hh
    omega
  have hGamma' : Gamma.card ≤ coherentChartRankCap (8*s₀) p := by simpa only [hJ] using hGamma
  have hVmass' : coherentChartDensity kappa (8*s₀) p*N ≤ (V.card : Real) := by simpa only [hJ] using hVmass
  have hQmass' : coherentChartDensity kappa (8*s₀) p*(N : Real)^3 ≤ Q.card := by simpa only [hJ] using hQmass
  exact ⟨m,theta,D,I,J,X,c,Gamma,psi,t,color,V,Q,B,hJ,hmBound,hF,hD,hactive,hGamma',hcard,
    ht,hV,hVmass',hQmass',hparts,hrelate,hlocal',hquad'⟩

end LeanProofs.GowersSzemeredi
