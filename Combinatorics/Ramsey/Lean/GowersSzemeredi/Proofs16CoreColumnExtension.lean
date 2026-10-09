import GowersSzemeredi.Proofs16SupportedCoherentAnchorSelection
import GowersSzemeredi.Proofs16GlobalEvenZeroColumnCore

/-! Add the common core spectrum to every retained column, and extend
unused columns by the normalized zero map. This supplies the global
local-map hypotheses of the anchor construction from supported data. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def coreColumnSpectrum {N : Nat} (P Gamma : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (x : ZMod N) : Finset (ZMod N) :=
  if x ∈ P then Gamma ∪ T x else ∅
def coreColumnMap {N : Nat} (P : Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (x y : ZMod N) : ZMod N :=
  if x ∈ P then L x y else 0

theorem coreColumnSpectrum_mem {N : Nat} [NeZero N]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    {x y : ZMod N} {r : Real} (hx : x ∈ P) :
    y ∈ bohr (coreColumnSpectrum P Gamma T x) r ↔
      y ∈ bohr Gamma r ∧ y ∈ bohr (T x) r := by
  simp only [coreColumnSpectrum,if_pos hx,bohr_union,Finset.mem_inter]

theorem coreColumnSpectrum_card_le {N g d : Nat}
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (hG : Gamma.card ≤ g) (hT : ∀ x ∈ P, (T x).card ≤ d) :
    ∀ x, (coreColumnSpectrum P Gamma T x).card ≤ g+d := by
  intro x
  by_cases hx : x ∈ P
  · simp only [coreColumnSpectrum,if_pos hx]
    exact (Finset.card_union_le _ _).trans (Nat.add_le_add hG (hT x hx))
  · simp [coreColumnSpectrum,hx]

theorem coreColumnMap_freiman {N : Nat} [NeZero N]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r rho : Real} (hr : r ≤ rho)
    (hL : ∀ x ∈ P, IsFreimanLinearOn (bohr (T x) rho) (L x)) :
    ∀ x, IsFreimanLinearOn (bohr (coreColumnSpectrum P Gamma T x) r) (coreColumnMap P L x) := by
  intro x
  by_cases hx : x ∈ P
  · have hsub : bohr (coreColumnSpectrum P Gamma T x) r ⊆ bohr (T x) rho := by
      intro y hy
      exact bohr_mono_radius _ hr ((coreColumnSpectrum_mem P Gamma T hx).mp hy).2
    simpa only [IsFreimanLinearOn,coreColumnMap,if_pos hx] using (hL x hx).mono hsub
  · intro a b c d ha hb hc hd he
    simp [coreColumnMap,hx]

theorem coreColumnMap_zero {N : Nat} (P : Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (hzero : ∀ x ∈ P, L x 0 = 0) :
    ∀ x, coreColumnMap P L x 0 = 0 := by
  intro x
  by_cases hx : x ∈ P
  · simp [coreColumnMap,hx,hzero x hx]
  · simp [coreColumnMap,hx]

end LeanProofs.GowersSzemeredi
