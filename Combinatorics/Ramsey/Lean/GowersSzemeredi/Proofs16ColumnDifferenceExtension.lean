import GowersSzemeredi.Proofs16BohrSpanExtension
import GowersSzemeredi.Proofs16PrimeColumnIdentities

/-! Equal column-index differences give compatible local maps, hence
extensions on intersections of their bounded frequency spans. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnDifferenceSpectrum {N : Nat} (T : ZMod N → Finset (ZMod N)) (p : ZMod N × ZMod N) :=
  T p.1 ∪ T p.2

def columnDifferenceMap {N : Nat} (L : ZMod N → ZMod N → ZMod N) (p : ZMod N × ZMod N)
    (y : ZMod N) := L p.1 y-L p.2 y

theorem columnDifferenceMap_freiman {N : Nat} [NeZero N]
    (P : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real)
    (hL : IsEBihomomorphism (columnBohrDomain P T r) (fun p => L p.1 p.2) {0})
    (p : ZMod N × ZMod N) (hp : p ∈ P ×ˢ P) :
    IsFreimanLinearOn (bohr (columnDifferenceSpectrum T p) r) (columnDifferenceMap L p) := by
  have hm : ∀ y ∈ bohr (columnDifferenceSpectrum T p) r,
      (p.1,y) ∈ columnBohrDomain P T r ∧ (p.2,y) ∈ columnBohrDomain P T r := by
    intro y hy
    have hy' : y ∈ bohr (T p.1) r ∧ y ∈ bohr (T p.2) r := by
      simpa only [columnDifferenceSpectrum,bohr_union,Finset.mem_inter] using hy
    exact ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_product.mp hp).1,hy'.1⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_product.mp hp).2,hy'.2⟩⟩
  intro a b c d ha hb hc hd he
  have h1 := Set.mem_singleton_iff.mp (hL.2 p.1 a b c d he (hm a ha).1 (hm b hb).1 (hm c hc).1 (hm d hd).1)
  have h2 := Set.mem_singleton_iff.mp (hL.2 p.2 a b c d he (hm a ha).2 (hm b hb).2 (hm c hc).2 (hm d hd).2)
  dsimp [columnDifferenceMap]
  linear_combination h1-h2

theorem columnDifferenceMap_compatible {N : Nat} [NeZero N]
    (P : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (r : Real)
    (hL : IsEBihomomorphism (columnBohrDomain P T r) (fun p => L p.1 p.2) {0})
    (p q : ZMod N × ZMod N) (hp : p ∈ P ×ˢ P) (hq : q ∈ P ×ˢ P)
    (he : p.1-p.2 = q.1-q.2) :
    ∀ y ∈ bohr (columnDifferenceSpectrum T p) r, y ∈ bohr (columnDifferenceSpectrum T q) r →
      columnDifferenceMap L p y = columnDifferenceMap L q y := by
  intro y hyp hyq
  have hp' : y ∈ bohr (T p.1) r ∧ y ∈ bohr (T p.2) r := by
    simpa only [columnDifferenceSpectrum,bohr_union,Finset.mem_inter] using hyp
  have hq' : y ∈ bohr (T q.1) r ∧ y ∈ bohr (T q.2) r := by
    simpa only [columnDifferenceSpectrum,bohr_union,Finset.mem_inter] using hyq
  have h := Set.mem_singleton_iff.mp (hL.1 p.1 q.2 p.2 q.1 y (by linear_combination he)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_product.mp hp).1,hp'.1⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_product.mp hq).2,hq'.2⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_product.mp hp).2,hp'.2⟩)
    (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_product.mp hq).1,hq'.1⟩))
  dsimp [columnDifferenceMap]
  linear_combination h

/-- Equal index differences extend coherently from both pair domains
onto a Bohr set with an explicit modulus-independent spectral cap. -/
theorem column_differences_span_extension {N d : Nat} [NeZero N] [Fact N.Prime]
    (P : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r : Real} (hr : 0 < r) (hr4 : r < 4)
    (hT : ∀ x ∈ P, (T x).card ≤ d) (hzero : ∀ x ∈ P, L x 0 = 0)
    (hL : IsEBihomomorphism (columnBohrDomain P T r) (fun p => L p.1 p.2) {0})
    (p q : ZMod N × ZMod N) (hp : p ∈ P ×ˢ P) (hq : q ∈ P ×ˢ P)
    (he : p.1-p.2 = q.1-q.2) :
    let K := bohrExtensionSpectrum (columnDifferenceSpectrum T p) (columnDifferenceSpectrum T q) (2*d) r
    K.card ≤ (2*bohrExtensionCutoff (2*d) r+1)^(2*d) ∧
      ∃ f : ZMod N → ZMod N, IsFreimanLinearOn (bohr K (1/(4*Real.pi))) f ∧ f 0 = 0 ∧
        (∀ y ∈ bohr (columnDifferenceSpectrum T p) (r/4), f y = columnDifferenceMap L p y) ∧
        (∀ y ∈ bohr (columnDifferenceSpectrum T q) (r/4), f y = columnDifferenceMap L q y) := by
  have hcap (a : ZMod N × ZMod N) (ha : a ∈ P ×ˢ P) : (columnDifferenceSpectrum T a).card ≤ 2*d := by
    exact (Finset.card_union_le _ _).trans ((Nat.add_le_add
      (hT a.1 (Finset.mem_product.mp ha).1) (hT a.2 (Finset.mem_product.mp ha).2)).trans (by omega))
  have hz (a : ZMod N × ZMod N) (ha : a ∈ P ×ˢ P) : columnDifferenceMap L a 0 = 0 := by
    simp only [columnDifferenceMap,hzero a.1 (Finset.mem_product.mp ha).1,
      hzero a.2 (Finset.mem_product.mp ha).2,sub_self]
  have hf := columnDifferenceMap_freiman P T L r hL p hp
  have hg := columnDifferenceMap_freiman P T L r hL q hq
  have hfg := columnDifferenceMap_compatible P T L r hL p q hp hq he
  refine ⟨bohrExtensionSpectrum_card_le _ _ r (hcap p hp),
    bohrSumExtension _ _ (columnDifferenceMap L p) (columnDifferenceMap L q) r,
    bohrSumExtension_freiman_span _ _ _ _ hr hr4 (hcap p hp) (hcap q hq) hf hg (hz p hp) (hz q hq) hfg,?_⟩
  exact bohrSumExtension_restrict _ _ _ _ hr.le hf hg (hz p hp) (hz q hq) hfg

end LeanProofs.GowersSzemeredi
