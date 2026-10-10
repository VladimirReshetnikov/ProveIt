import GowersSzemeredi.Proofs16RetiledRecurrence

/-! The statement shape of the retiled linearity argument (single box).

`Section16RetiledLinearityBound k q ε t` is the single-box core of
Lemma 16.6. A frequency family covered by `q` multilinear graphs on a set
`G`, together with linearity on short Bohr progressions, gives a partition of
`P × I` into proper product cells of width `≥ (ζ/2)·√(m^ε)`. On these cells
the final-coordinate function is linear for `h ∈ G`.
`exists_polynomial_retiled_linearity_profile` (in
`Proofs16PolynomialRetiledLinearity`) supplies it at a reciprocal-polynomial
exponent `ε`. The definition lives here, apart from that proof's heavy
import closure, so that consumers can take it as a hypothesis. -/
set_option autoImplicit false
noncomputable section
namespace LeanProofs.GowersSzemeredi

/-- The quantitative conclusion of the retiled linearity argument at a
specified width exponent and integer input threshold. -/
def Section16RetiledLinearityBound (k q : Nat) (epsilon : Real) (threshold : Nat) : Prop :=
  ∀ (N m : Nat) [NeZero N] (P : Box N k) (B I : ModAP N) (i : Fin k) (u : (ZMod N)ˣ),
    P.IsProper → I.IsProper → B.step = (↑u : ZMod N) → I.step = B.step →
    (P.axis i).carrier ⊆ B.carrier → 2 * B.length ≤ N → B.length ≤ I.length →
    ∀ mu : Fin q → Point N k → ZMod N, (∀ a, IsMultilinear (mu a)) →
    threshold ≤ m → m ≤ P.width →
    ∀ (K : Point N k → Finset (ZMod N)) (G : Finset (Point N k))
      (A : Point N k → Finset (ZMod N)) (f : Point N k → ZMod N → ZMod N)
      (zeta : Real), 0 < zeta → zeta ≤ 1 / 2 →
    (∀ x ∈ P.carrier, x ∈ G → ∀ r ∈ K x, ∃ a, r = mu a x) →
    (∀ x ∈ G, ∀ v : Nat, 0 < v → ∀ J : ModAP N, J.length ≤ v →
      J.step ∈ bohr (K x) (zeta / v) → LinearOn (J.carrier ∩ A x) (f x)) →
    1 < (zeta / 2) * Real.sqrt ((m : Real) ^ epsilon) →
    ∃ M : Nat, ∃ S : Fin M → Box N (k + 1), ∃ T : Fin M → Box N k,
      ∃ J : Fin M → ModAP N,
      IsPartition (fun j => (S j).carrier) (lastProductSet P.carrier I.carrier) ∧
      (∀ j, (S j).IsProper ∧ (zeta / 2) * Real.sqrt ((m : Real) ^ epsilon) ≤ (S j).width) ∧
      (∀ j, IsLastCoordinateBoxProduct (S j) (T j) (J j)) ∧
      ∀ j x, x ∈ (T j).carrier → x ∈ G → LinearOn ((J j).carrier ∩ A x) (f x)

end LeanProofs.GowersSzemeredi
