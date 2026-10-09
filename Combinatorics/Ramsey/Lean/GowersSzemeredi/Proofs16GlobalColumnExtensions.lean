import GowersSzemeredi.Proofs16ColumnDifferenceExtension
import GowersSzemeredi.Proofs16ZeroColumnsBihomomorphism

/-! Apply bounded-span map extension to the actual dense global core,
retaining its quantitative witnesses from the original map. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

/-- Each two representations of the same column-index difference admit
a common local extension on their bounded-span intersection domain. -/
theorem global_column_difference_extensions {N : Nat} [NeZero N] [Fact N.Prime]
    (A : Finset (ZMod N × ZMod N)) (phi : ZMod N × ZMod N → ZMod N)
    {alpha : Real} (ha : 0 < alpha) (ha1 : alpha ≤ 1)
    (hA : alpha*(N : Real)^2 ≤ A.card) (hphi : IsEBihomomorphism A phi {0})
    (hN : globalColumnZeroModulusBound alpha ≤ N) :
    let d := globalColumnModelRank alpha+columnSpectrumCap (columnEightDensity alpha)
    let r := globalColumnZeroRadius alpha
    ∃ (X P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
      (L : ZMod N → ZMod N → ZMod N) (W : ZMod N → Finset (Fin 4 → ZMod N)),
      IsColumnWitnessSystem A phi X T L W (1/(4*Real.pi)) ∧
      (∀ x ∈ X, columnWitnessDensity (columnEightDensity alpha)*(N : Real)^4 ≤ (W x).card) ∧
      P ⊆ X ∧ P.Nonempty ∧ globalColumnZeroDensity alpha*N ≤ (P.card : Real) ∧
      (∀ x ∈ P, (Gamma ∪ T x).card ≤ d) ∧
      (∀ x ∈ P, L x 0 = 0) ∧
      IsEBihomomorphism (columnBohrDomain P (fun x => Gamma ∪ T x) r) (fun p => L p.1 p.2) {0} ∧
      ∀ p ∈ P ×ˢ P, ∀ q ∈ P ×ˢ P, p.1-p.2 = q.1-q.2 →
        let S := fun x => Gamma ∪ T x
        let K := bohrExtensionSpectrum (columnDifferenceSpectrum S p) (columnDifferenceSpectrum S q) (2*d) r
        K.card ≤ (2*bohrExtensionCutoff (2*d) r+1)^(2*d) ∧
          ∃ f : ZMod N → ZMod N, IsFreimanLinearOn (bohr K (1/(4*Real.pi))) f ∧ f 0 = 0 ∧
            (∀ y ∈ bohr (columnDifferenceSpectrum S p) (r/4), f y = columnDifferenceMap L p y) ∧
            (∀ y ∈ bohr (columnDifferenceSpectrum S q) (r/4), f y = columnDifferenceMap L q y) := by
  obtain ⟨X,P,Gamma,T,L,W,hsys,_,hW,hPX,hPne,hP,hT,hzero,hL,_⟩ :=
    global_column_core_bihomomorphism A phi ha ha1 hA hphi hN
  refine ⟨X,P,Gamma,T,L,W,hsys,hW,hPX,hPne,hP,hT,hzero,hL,?_⟩
  have hr := globalColumnZeroRadius_pos ha ha1
  have hr4 : globalColumnZeroRadius alpha < 4 := by
    have hle := (globalColumnZeroRadius_le ha ha1).trans (globalColumnIdentityRadius_le ha ha1)
    have hpi := Real.pi_gt_three
    have hdiv : 1/(4*Real.pi) < 4 := (div_lt_iff₀ (by positivity)).mpr (by nlinarith)
    exact hle.trans_lt hdiv
  intro p hp q hq he
  exact column_differences_span_extension P (fun x => Gamma ∪ T x) L hr hr4 hT hzero hL p q hp hq he

end LeanProofs.GowersSzemeredi
