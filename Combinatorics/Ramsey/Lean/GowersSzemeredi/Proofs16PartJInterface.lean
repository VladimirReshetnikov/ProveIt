import GowersSzemeredi.Proofs16BaseCaseCubicExtraction
import GowersSzemeredi.Proofs16CubicUniformControls
import GowersSzemeredi.Proofs16WithUnion

/-! Part J of the Section 16 research notes: the stackable structure input.

Theorem 16.2 in dimension `d+1` is proved from dimension `d` by the cubic
affine lift (`Section16AllBoxLineCoversWith.cubic_multiplyLinearWith`). The
lift needs its stacked final-coordinate slices covered with controls
polynomial in the number of slices. Dimension one supplies this through
Freiman families and Corollary 7.11. The research notes (Parts H and J)
show that dimension two, as proved, does not: its counts are exponential in
a polynomial, and it unites pieces only sequentially.

This module states the missing input as a precise proposition.

* `CubicStackableClass d q S`: any `n` members of `S`, which are partial
  functions on `Z_N^d`, have a union of graphs that is multiply multilinear
  with count `3*n*q` and exponent `cubicBaseExponent (n*q)`. These are the
  exact controls of the dimension-one slice provider.
* `StackableStructureAt d Q q`: after removing a `theta` fraction of base
  points, every product relation in dimension `d` is covered by `Q gamma
  theta` members of such a class, with stacking parameter `q gamma theta`.

`stackableStructureAt_one` proves the dimension-one instance from the
Freiman-family extraction, with `q = 1`. So the proposition asks of
dimension two exactly what dimension one already provides. Milicevic's
structure theorem for Freiman bihomomorphisms (research notes H.5) is the
expected source of the dimension-two instance; that derivation is not
formalized here. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace LeanProofs.GowersSzemeredi
open BaseCase

/-- A class of partial functions on `Z_N^d` whose finite unions of graphs
have the cubic stacking controls with parameter `q`. -/
def CubicStackableClass {N : Nat} [NeZero N] (d q : Nat)
    (S : Set (Finset (Point N d) × (Point N d → ZMod N))) : Prop :=
  ∀ (n : Nat), 0 < n → ∀ (D : Fin n → Finset (Point N d) × (Point N d → ZMod N)),
    (∀ i, D i ∈ S) → ∀ Gamma : Finset (Point N d × ZMod N),
      Gamma ⊆ section16FinsetUnion (fun i => partialGraph (D i).1 (D i).2) →
      MultiplyLinearWith (fun _ => ((3 * (n * q) : Nat) : Real)) (cubicBaseExponent (n * q))
        Gamma

/-- **Part J, input (S)+(R).** After an outer removal, product relations
in dimension `d` are covered by a bounded number of members of a stackable
class. -/
def StackableStructureAt (d : Nat) (Q q : Real → Real → Nat) : Prop :=
  ∀ gamma theta : Real, 0 < gamma → gamma ≤ 1 → 0 < theta → theta ≤ 1 →
    0 < Q gamma theta ∧ 0 < q gamma theta ∧
    ∃ N0 : Nat, ∀ (N : Nat) [NeZero N] [Fact N.Prime], N0 ≤ N →
      ∃ S : Set (Finset (Point N d) × (Point N d → ZMod N)),
        CubicStackableClass d (q gamma theta) S ∧
        ∀ Gamma : Finset (Point N d × ZMod N),
          (Gamma.card : Real) ≤ gamma ^ (-(2 : Int)) * (N : Real) ^ d →
          RelationProductProperty gamma Gamma →
          ∃ J : Finset (Point N d), (1 - theta) * (N : Real) ^ d ≤ J.card ∧
            ∃ D : Fin (Q gamma theta) → Finset (Point N d) × (Point N d → ZMod N),
              (∀ i, D i ∈ S) ∧
              restrictRelation Gamma J ⊆
                section16FinsetUnion (fun i => partialGraph (D i).1 (D i).2)

/-- A cover by `n` members may be reported with any larger member count. -/
theorem CubicStackableClass.cover_le {N : Nat} [NeZero N] {d q : Nat}
    {S : Set (Finset (Point N d) × (Point N d → ZMod N))}
    (hS : CubicStackableClass d q S) (hq : 0 < q) {n m : Nat} (hn : 0 < n) (hnm : n ≤ m)
    (D : Fin n → Finset (Point N d) × (Point N d → ZMod N)) (hD : ∀ i, D i ∈ S)
    (Gamma : Finset (Point N d × ZMod N))
    (hG : Gamma ⊆ section16FinsetUnion (fun i => partialGraph (D i).1 (D i).2)) :
    MultiplyLinearWith (fun _ => ((3 * (m * q) : Nat) : Real)) (cubicBaseExponent (m * q))
      Gamma := by
  apply (hS n hn D hD Gamma hG).weaken
  · intro s _ _
    exact_mod_cast Nat.mul_le_mul_left 3 (Nat.mul_le_mul_right q hnm)
  · intro s hs _
    exact cubicBaseExponent_pos (Nat.mul_pos (hn.trans_le hnm) hq) hs
  · intro s hs _
    exact cubicBaseExponent_antitone_count (Nat.mul_pos hn hq)
      (Nat.mul_le_mul_right q hnm) hs.le

/-- A cover indexed by any finite type, reindexed through `Fin`. -/
theorem CubicStackableClass.cover_fintype {N : Nat} [NeZero N] {d q : Nat}
    {S : Set (Finset (Point N d) × (Point N d → ZMod N))}
    (hS : CubicStackableClass d q S) {ι : Type} [Fintype ι] [DecidableEq ι]
    (hι : 0 < Fintype.card ι)
    (D : ι → Finset (Point N d) × (Point N d → ZMod N)) (hD : ∀ i, D i ∈ S)
    (Gamma : Finset (Point N d × ZMod N))
    (hG : Gamma ⊆ section16FinsetUnion (fun i => partialGraph (D i).1 (D i).2)) :
    MultiplyLinearWith
      (fun _ => ((3 * (Fintype.card ι * q) : Nat) : Real))
      (cubicBaseExponent (Fintype.card ι * q)) Gamma := by
  classical
  let e := Fintype.equivFin ι
  apply hS (Fintype.card ι) hι (fun j => D (e.symm j)) (fun j => hD _) Gamma
  intro z hz
  obtain ⟨i, -, hi⟩ := Finset.mem_biUnion.mp (hG hz)
  exact Finset.mem_biUnion.mpr ⟨e i, Finset.mem_univ _, by simpa using hi⟩

/-- Freiman 8-homomorphism graphs on `Z_N` form a stackable class with
parameter one, by simultaneous linearization (Corollary 7.11). -/
def freimanOneClass (N : Nat) [NeZero N] :
    Set (Finset (Point N 1) × (Point N 1 → ZMod N)) :=
  {D | FreimanHom 8 (pointOneDomain D.1) (pointOneMap D.2)}

theorem freimanOneClass_stackable {N : Nat} [Fact N.Prime] :
    CubicStackableClass 1 1 (freimanOneClass N) := by
  intro n hn D hD Gamma hG
  simpa only [Nat.mul_one] using
    section16_freiman_family_cubic_cover hn (fun i => (D i).1) (fun i => (D i).2) hD Gamma hG

/-- **The dimension-one instance.** Dimension one has the stackable
structure, with `Q = section16BaseFamilyBound` and stacking parameter one. -/
theorem stackableStructureAt_one :
    StackableStructureAt 1 (fun gamma theta => section16BaseFamilyBound gamma theta)
      (fun _ _ => 1) := by
  intro gamma theta hg hg1 ht ht1
  refine ⟨section16BaseFamilyBound_pos gamma theta, Nat.one_pos, 0, ?_⟩
  intro N _ _ _
  refine ⟨freimanOneClass N, freimanOneClass_stackable, ?_⟩
  intro Gamma hsize hprod
  obtain ⟨J, D, f, hJ, hfreiman, hcover⟩ :=
    section16_extract_uniform_base_family hg hg1 ht ht1 Gamma
      (by simpa only [pow_one] using hsize) hprod
  exact ⟨J, by simpa only [pow_one] using hJ, fun i => (D i, f i), hfreiman, hcover⟩

end LeanProofs.GowersSzemeredi
