import GowersSzemeredi.Proofs16CoreColumnExtension

/-! The even core identities imply exact compatibility of every
supported pair of column differences after adding the common spectrum. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi
open Classical

def EvenColumnCoreRelations {N : Nat} [NeZero N] (P Gamma : Finset (ZMod N))
    (T : ZMod N → Finset (ZMod N)) (L : ZMod N → ZMod N → ZMod N) (r : Real) (k : Nat) : Prop :=
  ∀ m ≤ k, ∀ as : List (ZMod N), as.length = 2*m → (∀ x ∈ as, x ∈ P) →
    columnAnchorEval id as = 0 → ∀ y ∈ bohr Gamma r,
      (∀ x ∈ as, y ∈ bohr (T x) r) → columnAnchorEval (fun x => L x y) as = 0

theorem even_core_anchor_compatible {N : Nat} [NeZero N]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r : Real}
    (hrel : EvenColumnCoreRelations P Gamma T L r 4)
    {q : Fin 4 → ZMod N} (hq : q ∈ supportedAnchorQuadruples P) :
    ColumnPairCompatible (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r (q 0,q 1) (q 2,q 3) := by
  obtain ⟨hqP,hadd⟩ := Finset.mem_filter.mp hq
  have hP := Fintype.mem_piFinset.mp hqP
  intro y hy01 hy23
  have h01 : y ∈ bohr (coreColumnSpectrum P Gamma T (q 0)) r ∧
      y ∈ bohr (coreColumnSpectrum P Gamma T (q 1)) r := by
    simpa only [columnDifferenceSpectrum,bohr_union,Finset.mem_inter] using hy01
  have h23 : y ∈ bohr (coreColumnSpectrum P Gamma T (q 2)) r ∧
      y ∈ bohr (coreColumnSpectrum P Gamma T (q 3)) r := by
    simpa only [columnDifferenceSpectrum,bohr_union,Finset.mem_inter] using hy23
  have h0 := (coreColumnSpectrum_mem P Gamma T (hP 0)).mp h01.1
  have h1 := (coreColumnSpectrum_mem P Gamma T (hP 1)).mp h01.2
  have h2 := (coreColumnSpectrum_mem P Gamma T (hP 2)).mp h23.1
  have h3 := (coreColumnSpectrum_mem P Gamma T (hP 3)).mp h23.2
  have h := hrel 2 (by omega) [q 0,q 1,q 3,q 2] (by rfl)
    (by simpa only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] using
      And.intro (hP 0) (And.intro (hP 1) (And.intro (hP 3) (hP 2))))
    (by dsimp [columnAnchorEval]; linear_combination hadd) y h0.1
    (by simpa only [List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq] using
      And.intro h0.2 (And.intro h1.2 (And.intro h3.2 h2.2)))
  dsimp [columnAnchorEval] at h
  simp only [columnDifferenceMap,coreColumnMap,if_pos (hP 0),if_pos (hP 1),if_pos (hP 2),if_pos (hP 3)]
  linear_combination h

theorem even_core_incompatible_anchor_quadruples_empty {N : Nat} [NeZero N]
    (P Gamma : Finset (ZMod N)) (T : ZMod N → Finset (ZMod N))
    (L : ZMod N → ZMod N → ZMod N) {r : Real}
    (hrel : EvenColumnCoreRelations P Gamma T L r 4) :
    incompatibleAnchorQuadruples (supportedAnchorQuadruples P)
      (coreColumnSpectrum P Gamma T) (coreColumnMap P L) r = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  obtain ⟨hq,hn⟩ := Finset.mem_filter.mp hq
  exact hn (even_core_anchor_compatible P Gamma T L hrel hq)

end LeanProofs.GowersSzemeredi
