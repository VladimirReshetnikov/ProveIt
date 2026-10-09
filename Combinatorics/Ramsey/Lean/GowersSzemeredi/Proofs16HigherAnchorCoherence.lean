import GowersSzemeredi.Proofs16HigherAnchorSpectra
import GowersSzemeredi.Proofs16BohrGluingQuadruples

/-! Higher containment gives coherence of four actual column-pair
extensions. Pair compatibility and the two original eight-column
identities are explicit hypotheses, rather than global assumptions. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def higherAnchorExtension {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N)
    (r : Real) (p : HigherArrangementParameter N) (j : Fin 4) : ZMod N → ZMod N :=
  columnPairExtension T L r (higherArrangementEndpointPair p (Fin.castAdd 4 j))
    (higherArrangementEndpointPair p (Fin.natAdd 4 j))

def ColumnDifferenceQuadruple {N : Nat} (L : ZMod N → ZMod N → ZMod N)
    (e : Fin 4 → ZMod N × ZMod N) (y : ZMod N) : Prop :=
  columnDifferenceMap L (e 0) y+columnDifferenceMap L (e 1) y =
    columnDifferenceMap L (e 2) y+columnDifferenceMap L (e 3) y

theorem higher_anchor_extensions_coherent {N : Nat} [NeZero N]
    (T : ZMod N → Finset (ZMod N)) (F : (ZMod N × ZMod N) → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) (p : HigherArrangementParameter N)
    {r sigma : Real} (hr : 0 ≤ r)
    (hL : ∀ x, IsFreimanLinearOn (bohr (T x) r) (L x)) (hzero : ∀ x, L x 0 = 0)
    (hcompat : ∀ j : Fin 4, ColumnPairCompatible T L r
      (higherArrangementEndpointPair p (Fin.castAdd 4 j)) (higherArrangementEndpointPair p (Fin.natAdd 4 j)))
    (hcontain : bohr (higherSelectedPairFrequencies F p) sigma ⊆
      bohrQuarterSum (higherLeftFrequencies T (higherArrangementEndpoints p))
        (higherRightFrequencies T (higherArrangementEndpoints p)) r)
    (hleft : ∀ y ∈ bohr (higherLeftFrequencies T (higherArrangementEndpoints p)) (r/4),
      ColumnDifferenceQuadruple L (fun j : Fin 4 => higherArrangementEndpointPair p (Fin.castAdd 4 j)) y)
    (hright : ∀ y ∈ bohr (higherRightFrequencies T (higherArrangementEndpoints p)) (r/4),
      ColumnDifferenceQuadruple L (fun j : Fin 4 => higherArrangementEndpointPair p (Fin.natAdd 4 j)) y) :
    ∀ y ∈ bohr (higherSelectedPairFrequencies F p) sigma,
      higherAnchorExtension T L r p 0 y+higherAnchorExtension T L r p 1 y =
        higherAnchorExtension T L r p 2 y+higherAnchorExtension T L r p 3 y := by
  rw [higherLeftFrequencies_eq_pair_union,higherRightFrequencies_eq_pair_union] at hcontain
  rw [higherLeftFrequencies_eq_pair_union] at hleft
  rw [higherRightFrequencies_eq_pair_union] at hright
  exact bohr_sum_extensions_preserve_quadruple
    (fun j : Fin 4 => columnDifferenceSpectrum T (higherArrangementEndpointPair p (Fin.castAdd 4 j)))
    (fun j : Fin 4 => columnDifferenceSpectrum T (higherArrangementEndpointPair p (Fin.natAdd 4 j)))
    (fun j : Fin 4 => columnDifferenceMap L (higherArrangementEndpointPair p (Fin.castAdd 4 j)))
    (fun j : Fin 4 => columnDifferenceMap L (higherArrangementEndpointPair p (Fin.natAdd 4 j)))
    (bohr (higherSelectedPairFrequencies F p) sigma) hr
    (fun _ => columnDifferenceMap_freiman_of_local T L r hL _)
    (fun _ => columnDifferenceMap_freiman_of_local T L r hL _)
    (fun _ => columnDifferenceMap_zero_of_local L hzero _)
    (fun _ => columnDifferenceMap_zero_of_local L hzero _) hcompat hcontain hleft hright

end LeanProofs.GowersSzemeredi
