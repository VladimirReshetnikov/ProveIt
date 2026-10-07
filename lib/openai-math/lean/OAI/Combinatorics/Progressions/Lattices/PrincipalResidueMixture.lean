import OAI.Combinatorics.Progressions.Estimates.CoefficientRowReindex

namespace OAI

section

namespace Erdos3

noncomputable def integerMappedCubeTuple {Z X K α : Type*}
    (input : K → Option α → Z ⊕ X) (z : Z → ℤ) (x : X → ℤ) : Finset α → K → ℤ :=
  integerAffineCube (fun k => Sum.elim z x (input k none))
    (fun i k => Sum.elim z x (input k (some i)))

theorem integerMappedCubeTuple_residue {Z X K α : Type*}
    (input : K → Option α → Z ⊕ X) (z : Z → ℤ) (x y : X → ℤ) (m : ℕ)
    (hxy : integerResidueMap X m x = integerResidueMap X m y) (t : Finset α) :
    integerResidueMap K m (integerMappedCubeTuple input z x t) =
      integerResidueMap K m (integerMappedCubeTuple input z y t) := by
  apply integerAffineCube_residue_eq
  · funext k
    change ((Sum.elim z x (input k none) : ℤ) : ZMod m) =
      ((Sum.elim z y (input k none) : ℤ) : ZMod m)
    cases input k none with
    | inl j => rfl
    | inr j => exact congrFun hxy j
  · funext i k
    change ((Sum.elim z x (input k (some i)) : ℤ) : ZMod m) =
      ((Sum.elim z y (input k (some i)) : ℤ) : ZMod m)
    cases input k (some i) with
    | inl j => rfl
    | inr j => exact congrFun hxy j

noncomputable def integerMappedJetMatrix {Z X K α I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : I → Finset α) (x : X → ℤ) : Matrix I N ℤ :=
  integerJetMatrix (fun n => MvPolynomial.monomial (e n) 1) (integerMappedCubeTuple input z x) rows

theorem integerMappedJetMatrix_residue {Z X K α I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X) (z : Z → ℤ)
    (rows : I → Finset α) (x y : X → ℤ) (m : ℕ)
    (hxy : integerResidueMap X m x = integerResidueMap X m y) :
    integerResidueMatrix (integerMappedJetMatrix e input z rows x) m =
      integerResidueMatrix (integerMappedJetMatrix e input z rows y) m :=
  monomialCoefficientMatrix_residue_eq e _ _ rows m (integerMappedCubeTuple_residue input z x y m hxy)

theorem integerMappedCubeTuple_normalized {Z X K α : Type*} [Fintype α] [DecidableEq α]
    (input : K → Option α → Z ⊕ X) (z : Z → ℤ) (x : X → ℤ)
    (zr : Z → ℝ) (xr : X → ℝ) (T : K → ℝ)
    (hn : ∀ k a, ((Sum.elim z x (input k a) : ℤ) : ℝ)/T k = Sum.elim zr xr (input k a))
    (t : Finset α) (k : K) :
    (integerMappedCubeTuple input z x t k : ℝ)/T k = normalizedCubeTuple input zr xr t k := by
  exact (normalizedCubeTuple_eq_integerAffineCube input zr xr
    (fun k => Sum.elim z x (input k none)) (fun i k => Sum.elim z x (input k (some i))) T
    (fun k => (hn k none).symm) (fun i k => (hn k (some i)).symm) t k).symm

end Erdos3

end

section

namespace Erdos3

theorem integerMappedCubeTuple_residue_both {Z X K α : Type*}
    (input : K → Option α → Z ⊕ X) (z w : Z → ℤ) (x y : X → ℤ) (q : ℕ)
    (hzw : integerResidueMap Z q z = integerResidueMap Z q w)
    (hxy : integerResidueMap X q x = integerResidueMap X q y) (t : Finset α) :
    integerResidueMap K q (integerMappedCubeTuple input z x t) =
      integerResidueMap K q (integerMappedCubeTuple input w y t) := by
  apply integerAffineCube_residue_eq
  · funext k
    change ((Sum.elim z x (input k none) : ℤ) : ZMod q) =
      ((Sum.elim w y (input k none) : ℤ) : ZMod q)
    cases input k none with
    | inl j => exact congrFun hzw j
    | inr j => exact congrFun hxy j
  · funext i k
    change ((Sum.elim z x (input k (some i)) : ℤ) : ZMod q) =
      ((Sum.elim w y (input k (some i)) : ℤ) : ZMod q)
    cases input k (some i) with
    | inl j => exact congrFun hzw j
    | inr j => exact congrFun hxy j

theorem integerMappedJetMatrix_residue_both {Z X K α I N : Type*} [DecidableEq α]
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ X)
    (z w : Z → ℤ) (rows : I → Finset α) (x y : X → ℤ) (q : ℕ)
    (hzw : integerResidueMap Z q z = integerResidueMap Z q w)
    (hxy : integerResidueMap X q x = integerResidueMap X q y) :
    integerResidueMatrix (integerMappedJetMatrix e input z rows x) q =
      integerResidueMatrix (integerMappedJetMatrix e input w rows y) q :=
  monomialCoefficientMatrix_residue_eq e _ _ rows q
    (integerMappedCubeTuple_residue_both input z w x y q hzw hxy)

end Erdos3

end

section

namespace Erdos3

abbrev PrincipalIntegerTuples {D : Type*} (B : D → Type*) (h : D → ℕ) (α : Type*)
    (L : PrincipalTupleIndex B h → ℕ) := ∀ j, IntegerScalarCubeBox α (L j)

def principalTupleIntegers {D α : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} (y : PrincipalIntegerTuples B h α L) :
    JointBlockParameter B h α → ℤ :=
  fun a => (y ⟨a.1, a.2.1, a.2.2.1⟩ a.2.2.2 : ℤ)

noncomputable def principalTupleNormalized {D α : Type*} {B : D → Type*} {h : D → ℕ}
    (L : PrincipalTupleIndex B h → ℕ) (y : PrincipalIntegerTuples B h α L) :
    JointBlockParameter B h α → ℝ :=
  fun a => (principalTupleIntegers y a : ℝ)/L ⟨a.1, a.2.1, a.2.2.1⟩

def principalTupleResidues {D α : Type*} {B : D → Type*} {h : D → ℕ} {m : ℕ}
    (r : PrincipalTupleIndex B h → Option α → ZMod m) : JointBlockParameter B h α → ZMod m :=
  fun a => r ⟨a.1, a.2.1, a.2.2.1⟩ a.2.2.2

noncomputable def principalResidueWeights {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : ℕ) (hm : 0 < m) (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j) : FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) :=
  FiniteProbabilityWeights.pi (fun j => scalarCubeResidueWeights α (L j) m (hL j)
    (fun _ => m) (r j) (fun _ => hm) (fun _ => le_rfl) (hsize j))

theorem principalResidueWeights_support {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : ℕ) (hm : 0 < m) (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j) (y : PrincipalIntegerTuples B h α L)
    (hy : (principalResidueWeights B h L hL m hm r hsize).weight y ≠ 0) :
    integerResidueMap (JointBlockParameter B h α) m (principalTupleIntegers y) = principalTupleResidues r := by
  have hr := scalarCubeResiduePi_support L (fun _ => m) hL (fun _ _ => m) r
    (fun _ _ => hm) (fun _ _ => le_rfl) hsize y hy
  funext a
  exact hr ⟨a.1, a.2.1, a.2.2.1⟩ a.2.2.2

theorem principalResidueWeights_matrix {Z K D α I N : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j)
    (m : ℕ) (hm : 0 < m) (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j)
    (e : N → K →₀ ℕ) (input : K → Option α → Z ⊕ JointBlockParameter B h α)
    (z : Z → ℤ) (rows : I → Finset α) (ref : JointBlockParameter B h α → ℤ)
    (href : integerResidueMap _ m ref = principalTupleResidues r)
    (y : PrincipalIntegerTuples B h α L)
    (hy : (principalResidueWeights B h L hL m hm r hsize).weight y ≠ 0) :
    integerResidueMatrix (integerMappedJetMatrix e input z rows (principalTupleIntegers y)) m =
      integerResidueMatrix (integerMappedJetMatrix e input z rows ref) m := by
  apply integerMappedJetMatrix_residue
  exact (principalResidueWeights_support B h L hL m hm r hsize y hy).trans href.symm

end Erdos3

end

section

namespace Erdos3

open scoped BigOperators

noncomputable def principalTupleWeights {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) :
    FiniteProbabilityWeights (PrincipalIntegerTuples B h α L) :=
  FiniteProbabilityWeights.pi (fun j => integerScalarCubeWeights α (L j) (hL j))

def principalResidueLabel {D α : Type*} {B : D → Type*} {h : D → ℕ}
    {L : PrincipalTupleIndex B h → ℕ} (m : ℕ) (y : PrincipalIntegerTuples B h α L) :
    PrincipalTupleIndex B h → Option α → ZMod m := fun j i => ((y j i : ℤ) : ZMod m)

theorem principalResidueCell_eq {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (m : ℕ)
    (r : PrincipalTupleIndex B h → Option α → ZMod m) :
    Finset.univ.filter (fun y : PrincipalIntegerTuples B h α L => principalResidueLabel m y = r) =
      FiniteProbabilityWeights.piRestrictionSet
        (fun j => scalarCubeResidueSet α (L j) (fun _ => m) (r j)) := by
  classical
  ext y
  simp only [Finset.mem_filter, Finset.mem_univ, true_and,
    FiniteProbabilityWeights.mem_piRestrictionSet, mem_scalarCubeResidueSet]
  exact ⟨fun he j i => congrFun (congrFun he j) i, fun he => funext (fun j => funext (he j))⟩

theorem principalResidueCell_mass_pos {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) (hm : 0 < m)
    (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j) :
    0 < (principalTupleWeights (α := α) B h L hL).mass
      (Finset.univ.filter (fun y => principalResidueLabel m y = r)) := by
  rw [principalResidueCell_eq]
  exact FiniteProbabilityWeights.piRestriction_mass_pos _ _
    (fun j => scalarCubeResidue_mass_pos α (L j) m (hL j) (fun _ => m) (r j)
      (fun _ => hm) (fun _ => le_rfl) (hsize j))

theorem principalResidueWeights_eq_condition {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) (hm : 0 < m)
    (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j) :
    principalResidueWeights B h L hL m hm r hsize =
      (principalTupleWeights (α := α) B h L hL).condition
        (Finset.univ.filter (fun y => principalResidueLabel m y = r))
        (principalResidueCell_mass_pos B h L hL m hm r hsize) := by
  classical
  simp only [principalResidueCell_eq]
  exact scalarCubeResiduePi_condition L (fun _ => m) hL (fun _ _ => m) r
    (fun _ _ => hm) (fun _ _ => le_rfl) hsize

theorem principalResidue_fiberMean {D α : Type*} [Fintype D] [DecidableEq D]
    [Fintype α] [DecidableEq α] (B : D → Type*) [∀ d, Fintype (B d)] [∀ d, DecidableEq (B d)]
    (h : D → ℕ) (L : PrincipalTupleIndex B h → ℕ) (hL : ∀ j, 0 < L j) (m : ℕ) (hm : 0 < m)
    (r : PrincipalTupleIndex B h → Option α → ZMod m)
    (hsize : ∀ j, (Fintype.card α+1)*m ≤ L j) (f : PrincipalIntegerTuples B h α L → ℝ) :
    (principalTupleWeights (α := α) B h L hL).fiberMean (principalResidueLabel m) r f =
      (principalTupleWeights (α := α) B h L hL).mass
        (Finset.univ.filter (fun y => principalResidueLabel m y = r)) *
        (principalResidueWeights B h L hL m hm r hsize).mean f := by
  classical
  rw [principalResidueWeights_eq_condition]
  exact FiniteProbabilityWeights.fiberMean_eq_mass_mul_condition _ _ _ _ _

end Erdos3

end

end OAI
