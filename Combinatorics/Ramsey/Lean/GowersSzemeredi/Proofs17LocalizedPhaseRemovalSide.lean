import GowersSzemeredi.Proofs17LocalizedPhaseRemoval

/-! Declarations of `Proofs17LocalizedPhaseRemoval` that the final route does not use (moved here so
that the route keeps only what it uses). -/

set_option autoImplicit false

noncomputable section

open scoped BigOperators ZMod
open Finset

namespace LeanProofs.GowersSzemeredi

private lemma prop177_boundary_zero (N M : Nat) :
    prop177Boundary N M 0 = 0 := by
  simp [prop177Boundary, prop177CellWidth]

private lemma prop177_balancedCell_partition {N M : Nat} [NeZero N]
    (hM : 0 < M) :
    IsPartition (fun i : Fin M => (prop177BalancedCell N M i).carrier)
      Finset.univ := by
  constructor
  · intro x
    simp only [Finset.mem_univ, true_iff]
    exact ⟨prop177CellIndex hM x,
      (prop177_balancedCell_mem_iff_index hM _ _).mpr rfl⟩
  · intro i j hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have hi := (prop177_balancedCell_mem_iff_index hM i x).mp hxi
    have hj := (prop177_balancedCell_mem_iff_index hM j x).mp hxj
    exact bne_iff_ne.mp hij (hi.symm.trans hj)

private def prop177Monomial {N k : Nat} (e : Fin k → Bool)
    (x : Point N k) : ZMod N := ∏ i, if e i then x i else 1

private lemma prop177Monomial_cons {N k : Nat} (b : Bool)
    (e : Fin k → Bool) (z : Point N (k + 1)) :
    prop177Monomial (Fin.cons b e) z =
      (if b then z 0 else 1) * prop177Monomial e (Fin.tail z) := by
  simp [prop177Monomial, Fin.prod_univ_succ, Fin.tail]

private lemma prop177_affineEquiv_apply {N : Nat} [NeZero N] [Fact N.Prime]
    (d offset : ZMod N) (hd : d ≠ 0) (u : ZMod N) :
    prop177AffineEquiv d offset hd u = d * u - offset := rfl

/-- **Gowers, Proposition 17.7.** The catalogue conclusion follows from
 the stronger construction, retaining its original statement. -/
theorem proposition_17_7_holds : proposition_17_7 := by
  intro N k m _ _ f P sigma alpha hα hk hm hwidth haxes hd hmsqrt hf hsigma henergy
  obtain ⟨phi, M, l, Q, hpoly, hpart, hproper, hlower, _, hfail⟩ :=
    proposition_17_7_with_upper N k m f P sigma alpha hα hk hm hwidth haxes hd hmsqrt hf hsigma henergy
  exact ⟨phi, M, l, Q, hpoly, hpart, hproper, hlower, hfail⟩

end LeanProofs.GowersSzemeredi
