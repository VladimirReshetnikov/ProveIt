import GowersSzemeredi.Proofs16DenseIndexWindow

/-! Feed the actual uniformly dense active window into coherent completion.
Only unused padding is changed to zero; the original active frequency
images, source maps and quadruples are retained exactly. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- A uniformly dense actual chart family supplies completed coherent charts
on its finite window, including unused padded indices. -/
theorem complete_dense_index_window_charts {N m : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (X B : Finset (ZMod N)) (J : Finset Nat)
    (D : Nat → Finset (ZMod N)) (S : ZMod N → Finset Nat)
    (theta : Nat → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    {delta eta kappa : Real} (hd : 0 < delta) (heta : 0 ≤ eta) (hk : 0 < kappa)
    (hF : ∀ i < m, FreimanHom 8 (D i) (theta i))
    (hD : ∀ i < m, delta*(N : Real) ≤ ((D i).card : Real))
    (hactive : ∀ x ∈ X, ∀ i ∈ S x, i ∈ J ∧ i < m ∧ x ∈ D i)
    (hlocal : ∀ x ∈ X, IsFreimanLinearOn (bohr (B ∪ (S x).image fun i => theta i x) eta) (F x) ∧ F x 0 = 0)
    (hquad : ∀ q ∈ Q, q 0+q 1 = q 2+q 3 ∧ (∀ j, q j ∈ X) ∧
      ∀ z, (∀ j, z ∈ bohr (B ∪ (S (q j)).image fun i => theta i (q j)) eta) →
        F (q 0) z+F (q 1) z = F (q 2) z+F (q 3) z)
    (hmass : kappa*(N : Real)^3 ≤ Q.card)
    (hN : 8 ≤ (kappa/(coherentChartCells (denseChartLog delta) : Real)^
      (4*coherentChartRankCap J.card (denseChartLog delta)))*N) :
    let p := denseChartLog delta
    ∃ (Gamma : Finset (ZMod N)) (psi : Fin J.card → ZMod N → ZMod N)
      (t : Fin 4 → ZMod N) (color : ZMod N → Fin 4) (V : Finset (ZMod N))
      (R : Finset (Fin 4 → ZMod N)) (B' : Finset (ZMod N)),
      Gamma.card ≤ coherentChartRankCap J.card p ∧
      (∀ i, ∀ a ∈ denseWindowDomain J m D i, ∀ b ∈ denseWindowDomain J m D i, denseWindowMap J m theta i a-denseWindowMap J m theta i b = psi i (a-b)) ∧
      t ∈ Q ∧ B ⊆ B' ∧ B'.card ≤ B.card+4*J.card ∧ V ⊆ bohr Gamma (sandersChartRadius p/4) ∧
      coherentChartDensity kappa J.card p*N ≤ (V.card : Real) ∧
      coherentChartDensity kappa J.card p*(N : Real)^3 ≤ R.card ∧
      (∀ i, FreimanHom 2 (bohr Gamma (sandersChartRadius p)) (psi i) ∧ psi i 0 = 0) ∧
      (∀ u ∈ V, t (color u)+u ∈ X ∧
        IsFreimanLinearOn (freimanFrequencyBohr B' psi (eta/2) u) (F (t (color u)+u)) ∧
        F (t (color u)+u) 0 = 0) ∧
      ∀ b ∈ R, b 0+b 1 = b 2+b 3 ∧ Function.Injective b ∧
        (∀ j, b j ∈ V ∧ color (b j) = j) ∧ (fun j => t j+b j) ∈ Q ∧
        ∀ z, (∀ j, z ∈ freimanFrequencyBohr B' psi (eta/2) (b j)) →
          F (t (color (b 0))+b 0) z+F (t (color (b 1))+b 1) z =
            F (t (color (b 2))+b 2) z+F (t (color (b 3))+b 3) z := by
  intro p
  have hp := (denseChartLog_spec hd).1
  have hexp := (denseChartLog_spec hd).2
  let Dom := denseWindowDomain J m D
  let Theta := denseWindowMap J m theta
  let Active := fun x => denseWindowActive J (S x)
  have hFreiman : ∀ i, FreimanHom 8 (Dom i) (Theta i) := dense_window_freiman J D theta hF
  have hDense : ∀ i, Real.exp (-p)*N ≤ ((Dom i).card : Real) :=
    dense_window_domain_density J D hp hexp hD
  have hImages : ∀ x ∈ X, (Active x).image (fun i => Theta i x) = (S x).image (fun i => theta i x) := by
    intro x hx
    exact dense_window_active_image J (S x) theta x (fun i hi => (hactive x hx i hi).1)
      (fun i hi => (hactive x hx i hi).2.1)
  have hActive : ∀ x ∈ X, ∀ i ∈ Active x, x ∈ Dom i := by
    intro x hx i hi
    exact dense_window_active_domain_mem J (S x) D
      (fun j hj => (hactive x hx j hj).2) hi
  have hLocal : ∀ x ∈ X, IsFreimanLinearOn (bohr (B ∪ (Active x).image fun i => Theta i x) eta) (F x) ∧ F x 0 = 0 := by
    intro x hx
    rw [hImages x hx]
    exact hlocal x hx
  have hQuad : ∀ q ∈ Q, q 0+q 1 = q 2+q 3 ∧ (∀ j, q j ∈ X) ∧
      ∀ z, (∀ j, z ∈ bohr (B ∪ (Active (q j)).image fun i => Theta i (q j)) eta) →
        F (q 0) z+F (q 1) z = F (q 2) z+F (q 3) z := by
    intro q hq
    have h := hquad q hq
    refine ⟨h.1,h.2.1,?_⟩
    intro z hz
    apply h.2.2 z
    intro j
    rw [← hImages (q j) (h.2.1 j)]
    exact hz j
  exact exists_coherent_completed_sanders_charts Q X B Dom Active Theta F hp heta hk
    hFreiman hDense hActive hLocal hQuad hmass hN

end LeanProofs.GowersSzemeredi
