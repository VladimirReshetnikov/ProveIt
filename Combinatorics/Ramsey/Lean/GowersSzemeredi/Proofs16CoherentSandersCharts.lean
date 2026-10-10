import GowersSzemeredi.Proofs16ChartCoherenceLocalization

/-! A complete coherent chart construction from dense order-eight domains.
The domains are allowed to differ; they need not intersect. Rank, cell count,
retained density and the required modulus condition are uniform in the data. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def coherentChartRankCap (ell : Nat) (p : Real) : Nat :=
  ⌈(ell : Real)*(1+OAI.Erdos3.CyclicCrootSisask.quarticBogolyubovConstant*(p+1)^4)⌉₊

def coherentChartCells (p : Real) : Nat := refinementCells (sandersChartRadius p/4)

def coherentChartDensity (kappa : Real) (ell : Nat) (p : Real) : Real :=
  kappa/(512*(coherentChartCells p : Real)^(4*coherentChartRankCap ell p))

theorem coherentChartCells_pos (p : Real) : 0 < coherentChartCells p := by
  have hr := sandersChartRadius_pos p
  exact Nat.ceil_pos.mpr (by positivity)

theorem coherentChartDensity_pos {kappa : Real} (hk : 0 < kappa) (ell : Nat) (p : Real) :
    0 < coherentChartDensity kappa ell p := by
  have hM : (0 : Real) < coherentChartCells p := by exact_mod_cast coherentChartCells_pos p
  unfold coherentChartDensity
  positivity

/-- Construct a common coherent Bohr family with explicit uniform rank and
mass controls, retaining actual active chart values and original quadruples. -/
theorem exists_coherent_completed_sanders_charts {N ell : Nat} [NeZero N]
    (Q : Finset (Fin 4 → ZMod N)) (X B : Finset (ZMod N))
    (D : Fin ell → Finset (ZMod N)) (S : ZMod N → Finset (Fin ell))
    (theta : Fin ell → ZMod N → ZMod N) (F : ZMod N → ZMod N → ZMod N)
    {p eta kappa : Real} (hp : 0 ≤ p) (heta : 0 ≤ eta) (hk : 0 < kappa)
    (hF : ∀ i, FreimanHom 8 (D i) (theta i)) (hD : ∀ i, Real.exp (-p)*N ≤ ((D i).card : Real))
    (hactive : ∀ x ∈ X, ∀ i ∈ S x, x ∈ D i)
    (hlocal : ∀ x ∈ X, IsFreimanLinearOn (bohr (B ∪ (S x).image fun i => theta i x) eta) (F x) ∧ F x 0 = 0)
    (hquad : ∀ q ∈ Q, q 0+q 1 = q 2+q 3 ∧ (∀ j, q j ∈ X) ∧
      ∀ z, (∀ j, z ∈ bohr (B ∪ (S (q j)).image fun i => theta i (q j)) eta) →
        F (q 0) z+F (q 1) z = F (q 2) z+F (q 3) z)
    (hmass : kappa*(N : Real)^3 ≤ Q.card)
    (hN : 8 ≤ (kappa/(coherentChartCells p : Real)^(4*coherentChartRankCap ell p))*N) :
    ∃ (Gamma : Finset (ZMod N)) (psi : Fin ell → ZMod N → ZMod N)
      (t : Fin 4 → ZMod N) (color : ZMod N → Fin 4) (V : Finset (ZMod N))
      (R : Finset (Fin 4 → ZMod N)) (B' : Finset (ZMod N)),
      Gamma.card ≤ coherentChartRankCap ell p ∧
      (∀ i, ∀ a ∈ D i, ∀ b ∈ D i, theta i a-theta i b = psi i (a-b)) ∧
      t ∈ Q ∧ B ⊆ B' ∧ B'.card ≤ B.card+4*ell ∧ V ⊆ bohr Gamma (sandersChartRadius p/4) ∧
      coherentChartDensity kappa ell p*N ≤ (V.card : Real) ∧
      coherentChartDensity kappa ell p*(N : Real)^3 ≤ R.card ∧
      (∀ i, FreimanHom 2 (bohr Gamma (sandersChartRadius p)) (psi i) ∧ psi i 0 = 0) ∧
      (∀ u ∈ V, t (color u)+u ∈ X ∧
        IsFreimanLinearOn (freimanFrequencyBohr B' psi (eta/2) u) (F (t (color u)+u)) ∧
        F (t (color u)+u) 0 = 0) ∧
      ∀ b ∈ R, b 0+b 1 = b 2+b 3 ∧ Function.Injective b ∧
        (∀ j, b j ∈ V ∧ color (b j) = j) ∧ (fun j => t j+b j) ∈ Q ∧
        ∀ z, (∀ j, z ∈ freimanFrequencyBohr B' psi (eta/2) (b j)) →
          F (t (color (b 0))+b 0) z+F (t (color (b 1))+b 1) z =
            F (t (color (b 2))+b 2) z+F (t (color (b 3))+b 3) z := by
  obtain ⟨Gamma,psi,hGamma,hpsi,hdiff⟩ := exists_common_sanders_chart_data D theta hp hF hD
  have hrank : Gamma.card ≤ coherentChartRankCap ell p := by
    have hreal : (Gamma.card : Real) ≤ (coherentChartRankCap ell p : Real) := by
      apply hGamma.trans
      simpa only [coherentChartRankCap,Fintype.card_fin] using
        Nat.le_ceil ((ell : Real)*(1+OAI.Erdos3.CyclicCrootSisask.quarticBogolyubovConstant*(p+1)^4))
    exact_mod_cast hreal
  let M := coherentChartCells p
  letI : NeZero M := ⟨ne_of_gt (coherentChartCells_pos p)⟩
  have hMR : (0 : Real) < M := by exact_mod_cast coherentChartCells_pos p
  have hMone : (1 : Real) ≤ M := by exact_mod_cast coherentChartCells_pos p
  have hr : 0 < sandersChartRadius p := sandersChartRadius_pos p
  have hcell : 1 ≤ (sandersChartRadius p/4)*M := by
    have h := Nat.le_ceil (1/(sandersChartRadius p/4))
    rw [div_le_iff₀ (by positivity)] at h
    simpa only [M,coherentChartCells,refinementCells,mul_comm] using h
  have hpow : (M : Real)^(4*Gamma.card) ≤ (M : Real)^(4*coherentChartRankCap ell p) :=
    pow_le_pow_right₀ hMone (Nat.mul_le_mul_left 4 hrank)
  have hNactual : 8 ≤ (kappa/(M : Real)^(4*Gamma.card))*N :=
    hN.trans (mul_le_mul_of_nonneg_right
      (div_le_div_of_nonneg_left hk.le (by positivity) hpow) (Nat.cast_nonneg _))
  obtain ⟨t,color,V,R,B',ht,hBB,hB,hV,hVmass,hRmass,hparts,hlocal',hquad'⟩ :=
    coherent_chart_localization Q X Gamma B D S theta psi F hr heta hk hcell hpsi hdiff
      hactive hlocal hquad hmass hNactual
  have hdensity : coherentChartDensity kappa ell p ≤ kappa/(512*(M : Real)^(4*Gamma.card)) := by
    unfold coherentChartDensity
    exact div_le_div_of_nonneg_left hk.le (by positivity)
      (mul_le_mul_of_nonneg_left hpow (by norm_num))
  refine ⟨Gamma,psi,t,color,V,R,B',hrank,hdiff,ht,hBB,hB,hV,?_,?_,hparts,hlocal',hquad'⟩
  · exact (mul_le_mul_of_nonneg_right hdensity (Nat.cast_nonneg _)).trans hVmass
  · exact (mul_le_mul_of_nonneg_right hdensity (by positivity)).trans hRmass

end LeanProofs.GowersSzemeredi
