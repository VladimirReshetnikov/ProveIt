import GowersSzemeredi.Proofs16SmallImageRelations

/-! Bounded-image column quadruples become exact identities in prime cyclic
targets. When every additive index quadruple has a bounded image, the
restricted column family is a Freiman bihomomorphism. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def columnQuadrupleDefect {N : Nat} (L : ZMod N → ZMod N → ZMod N)
    (q : Fin 4 → ZMod N) (y : ZMod N) : ZMod N :=
  L (q 0) y + L (q 1) y - L (q 2) y - L (q 3) y

def columnQuadrupleSpectrum {N : Nat} (T : ZMod N → Finset (ZMod N))
    (q : Fin 4 → ZMod N) : Finset (ZMod N) :=
  Finset.univ.biUnion (fun i => T (q i))

/-- The quadruple defect is Freiman-linear on the common domain. -/
theorem columnQuadrupleDefect_freiman {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (q : Fin 4 → ZMod N) {rho : Real}
    (hL : ∀ i, IsFreimanLinearOn (bohr (T (q i)) rho) (L (q i))) :
    IsFreimanLinearOn (bohr (columnQuadrupleSpectrum T q) rho) (columnQuadrupleDefect L q) := by
  intro a b c d ha hb hc hd heq
  have h (i : Fin 4) := hL i a b c d
    ((mem_bohr_family_union (fun i => T (q i)) rho a).mp ha i)
    ((mem_bohr_family_union (fun i => T (q i)) rho b).mp hb i)
    ((mem_bohr_family_union (fun i => T (q i)) rho c).mp hc i)
    ((mem_bohr_family_union (fun i => T (q i)) rho d).mp hd i) heq
  dsimp [columnQuadrupleDefect]
  linear_combination h 0 + h 1 - h 2 - h 3

/-- A small-image quadruple becomes an exact identity on the shrunken
intersection, with the same frequency sets. -/
theorem small_image_column_quadruple {N K : Nat} [NeZero N] [Fact N.Prime]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (q : Fin 4 → ZMod N) {rho : Real} (hrho : 0 ≤ rho)
    (hL : ∀ i, IsFreimanLinearOn (bohr (T (q i)) rho) (L (q i)))
    (hzero : ∀ i, L (q i) 0 = 0)
    (himage : ((bohr (columnQuadrupleSpectrum T q) rho).image
      (columnQuadrupleDefect L q)).card ≤ K) (hKN : K < N) :
    ∀ y, (∀ i, y ∈ bohr (T (q i)) (rho / K)) →
      L (q 0) y + L (q 1) y = L (q 2) y + L (q 3) y := by
  intro y hy
  have h := freiman_small_image_zero _ hrho _ (columnQuadrupleDefect_freiman T L q hL)
    (by simp only [columnQuadrupleDefect, hzero, add_zero, sub_zero]) himage hKN y
    ((mem_bohr_family_union (fun i => T (q i)) _ y).mpr hy)
  dsimp [columnQuadrupleDefect] at h
  linear_combination h

/-- The domain of a local column family. -/
def columnBohrDomain {N : Nat} [NeZero N] (X : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (rho : Real) : Finset (ZMod N × ZMod N) :=
  Finset.univ.filter fun p => p.1 ∈ X ∧ p.2 ∈ bohr (T p.1) rho

/-- All bounded-image additive quadruples yield an actual bihomomorphism
on a uniform restriction of the column domains. -/
theorem bounded_image_columns_bihomomorphism {N K : Nat} [NeZero N] [Fact N.Prime]
    (X : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {rho : Real} (hrho : 0 ≤ rho)
    (hK : 0 < K) (hKN : K < N)
    (hL : ∀ x ∈ X, IsFreimanLinearOn (bohr (T x) rho) (L x))
    (hzero : ∀ x ∈ X, L x 0 = 0)
    (himage : ∀ q : Fin 4 → ZMod N, (∀ i, q i ∈ X) → IsAdditiveQuadruple q →
      ((bohr (columnQuadrupleSpectrum T q) rho).image (columnQuadrupleDefect L q)).card ≤ K) :
    IsEBihomomorphism (columnBohrDomain X T (rho / K)) (fun p => L p.1 p.2) {0} := by
  have hradius : rho / K ≤ rho := div_le_self hrho (by exact_mod_cast hK)
  constructor
  · intro a b c d y heq ha hb hc hd
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have hc' := (Finset.mem_filter.mp hc).2
    have hd' := (Finset.mem_filter.mp hd).2
    let q : Fin 4 → ZMod N := ![a, b, c, d]
    have hq : ∀ i, q i ∈ X := by
      intro i; fin_cases i
      · exact ha'.1
      · exact hb'.1
      · exact hc'.1
      · exact hd'.1
    have hqy : ∀ i, y ∈ bohr (T (q i)) (rho / K) := by
      intro i; fin_cases i
      · exact ha'.2
      · exact hb'.2
      · exact hc'.2
      · exact hd'.2
    have h := small_image_column_quadruple T L q hrho (fun i => hL _ (hq i))
      (fun i => hzero _ (hq i)) (himage q hq heq) hKN y hqy
    change L a y + L b y - L c y - L d y ∈ ({0} : Set (ZMod N))
    simp only [Set.mem_singleton_iff]
    dsimp [q] at h
    linear_combination h
  · intro x a b c d heq ha hb hc hd
    have ha' := (Finset.mem_filter.mp ha).2
    have hb' := (Finset.mem_filter.mp hb).2
    have hc' := (Finset.mem_filter.mp hc).2
    have hd' := (Finset.mem_filter.mp hd).2
    have h := hL x ha'.1 a b c d (bohr_mono_radius _ hradius ha'.2)
      (bohr_mono_radius _ hradius hb'.2) (bohr_mono_radius _ hradius hc'.2)
      (bohr_mono_radius _ hradius hd'.2) heq
    change L x a + L x b - L x c - L x d ∈ ({0} : Set (ZMod N))
    simp only [Set.mem_singleton_iff]
    linear_combination h

end LeanProofs.GowersSzemeredi
